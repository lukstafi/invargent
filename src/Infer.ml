(** Inferring and normalizing formulas for InvarGenT.

    Released under the GNU General Public Licence (version 2 or
    higher), NO WARRANTY of correctness etc. (C) Lukasz Stafiniak 2013
    @author Lukasz Stafiniak lukstafi (AT) gmail.com
    @since Mar 2013
*)
open Terms

exception Contradiction of string * (typ * typ) option * loc

type cnstrnt =
| And of cnstrnt list
| Or of atom list
| Impl of atom list * cnstrnt
| All of VarSet.t * cnstrnt
| Ex of VarSet.t * cnstrnt

(** {2 Constraint inference} *)

let cn_and cn1 cn2 =
  match cn1, cn2 with
  | And cns1, And cns2 -> And (cns1 @ cns2)
  | And cns, cn | cn, And cns -> And (cn::cns)
  | _ -> And [cn1; cn2]

(* Global state for fresh variable guarantees: not re-entrant. *)
let fresh_var_id = ref 0
let fresh_chi_id = ref 0

let freshen_typ env = function
  | TVar v ->
    (try env, TVar (List.assoc v env)
     with Not_found ->
       incr fresh_var_id;
       let v' = TVar (VId (var_sort v, !fresh_var_id)) in
       (v, v')::env, TVar v')
  | TCons (n, tys) ->
    let env, tys = Aux.fold_map freshen_typ env tys in
    env, TCons (n, tys)
  | Fun (t1, t2) ->
    let env, t1 = freshen_typ env t1 in
    let env, t2 = freshen_typ env t2 in
    env, Fun (t1, t2)
  | NCst _ as c -> c
  | Nadd tys ->
    let env, tys = Aux.fold_map freshen_typ env tys in
    env, Nadd tys

let freshen_atom env = function
  | Eqty (t1, t2, loc) ->
    let env, t1 = freshen_typ env t1 in
    let env, t2 = freshen_typ env t2 in
    Eqty (t1, t2, loc)
  | Leq (t1, t2, loc) ->
    let env, t1 = freshen_typ env t1 in
    let env, t2 = freshen_typ env t2 in
    Leq (t1, t2, loc)
  | CFalse _ as a -> a
  | PredVar (i, t) ->
    let env, t = freshen_typ env t in
    env, PredVar (i, t)

let freshen_cns_scheme (vs, phi, argtys, res) =
  let env, res = freshen_typ [] res in
  let env, argtys = Aux.fold_map freshen_typ env argtys in
  let env, phi = Aux.fold_map freshen_atom phi in
  let vs = Aux.map_some
    (fun v->try Some (List.assoc v env) with Not_found -> None) vs in
  vs, phi, argtys, res

let freshen_val_scheme (vs, phi, res) =
  let env, res = freshen_typ [] res in
  let env, phi = Aux.fold_map freshen_atom phi in
  let vs = Aux.map_some
    (fun v->try Some (List.assoc v env) with Not_found -> None) vs in
  vs, phi, argtys, res

let constr_gen_pat sigma tau =
  let rec aux tau = function
    | Zero | One _ | PVar _ -> And []
    | PAnd (p1, p2, _) -> cn_and (aux tau p1) (aux tau p2)
    | PCons (n, args, _) ->
      let abvs, phi, argtys, res =
        freshen_env_scheme (Hashtbl.find sigma n) in
      let avs = fvs_typ res in
      let bvs = VarSet.diff (vars_of_list abvs) avs in
      let argphi =
        List.fold_left cn_add (And [])
          (List.map2 aux argtys args) in
      Ex (avs, And [Eqty (res, tau);
                   All (bvs, Impl (phi, argphi))])
  

let envfrag_gen_pat p =
  ()

let constr_gen_expr e =
  ()

(** {2 Postprocessing and printing} *)

type nicevars_env = {
  nvs_env : (int, string) list;
  last_typ : int;
  last_num : int
}
let typvars = "abcdefghorstuvw"
let numvars = "nkijmlpqxyz"
let typvars_n = String.length typvars
let numvars_n = String.length numvars

let next_typ env id =
  let ch, n = env.last_typ mod typvars_n, env.last_typ / typvars_n in
  let v =
    Char.escaped typvars.[ch] ^ (if n>0 then string_of_int n else "") in
  {nvs_env = (id, v)::env.nvs_env;
   last_typ = env.last_typ+1; last_num = env.last_num}

let next_num env id =
  let ch, n = env.last_num mod numvars_n, env.last_num / numvars_n in
  let v =
    Char.escaped numvars.[ch] ^ (if n>0 then string_of_int n else "") in
  {nvs_env = (id, v)::env.nvs_env;
   last_typ = env.last_typ+1; last_num = env.last_num}

let nicevars_typ env t =
  let rec aux = function
    | TVar (VNam _) as v -> v
    | TVar (VId (s, id)) as v ->
      (try TVar (VNam (s, List.assoc id env))
       with Not_found -> v)
    | TCons (n, tys) -> TCons (n, List.map aux tys)
    | Fun (t1, t2) -> Fun (aux t1, aux t2)
    | NCst _ as c -> c
    | Nadd tys -> Nadd (List.map aux tys) in
  aux t

let nicevars_atom env = function
  | Eqty (t1, t2, loc) ->
    Eqty (nicevars_typ env t1, nicevars_typ env t2, loc)
  | Leq (t1, t2, loc) ->
    Leq (nicevars_typ env t1, nicevars_typ env t2, loc)
  | CFalse _ as a -> a
  | PredVar (i, t) -> PredVar (i, nicevars_typ env t)

let nicevars_cnstrnt c =
  let rec aux env = function
    | And cns -> And (List.map (aux env) cns)
    | Or disjs -> Or (List.map (nicevars_atom env) disjs)
    | Impl (prem, concl) ->
      Impl (List.map (nicevars_atom env) prem, aux env concl)
    | All (vs, cn) ->
      let vs = Aux.map_some
        (function VNam _ -> None | VId (s,id) -> Some (s,id))
        (VarSet.elements vs) in
      let env = List.fold_left (fun env ->
        function Num_sort,id->next_num env id
        | Type_sort,id->next_typ env id) vs in
      let vs = List.map
        (function VNam _ as v -> v
        | VId (s, id) -> VId (s, List.assoc id env.nvs_env)) vs in
      All (vs, aux env cn)
    | Ex (vs, cn) ->
      let vs = Aux.map_some
        (function VNam _ -> None | VId (s,id) -> Some (s,id))
        (VarSet.elements vs) in
      let env = List.fold_left (fun env ->
        function Num_sort,id->next_num env id
        | Type_sort,id->next_typ env id) vs in
      let vs = List.map
        (function VNam _ as v -> v
        | VId (s, id) -> VId (s, List.assoc id env.nvs_env)) vs in
      Ex (vs, aux env cn) in
  aux {nvs_env = []; last_typ = 0; last_num = 0} c

let rec pr_cnstrnt ppf = function
  | And cns -> fprintf ppf "@[<2>";
    pr_more_sep_list "∧" pr_cnstrnt ppf cns; fprintf ppf "@]"
  | Or disjs -> fprintf ppf "@[<2>";
    pr_more_sep_list "∨" pr_atom ppf cns; fprintf ppf "@]"
  | Impl (prem,concl) -> fprintf ppf "@[<2>";
    pr_formula ppf prem; fprintf "@ ⟹@ %a@]" pr_cnstrnt concl
  | All (vs, cn) -> fprintf ppf "@[<2>";
    fprintf ppf "@[<2>∀%a.@ %a@]"
      (pr_more_sep_list "," pr_tyvar) vs pr_cnstrnt cn
  | Ex (vs, cn) -> fprintf ppf "@[<2>";
    fprintf ppf "@[<2>∃%a.@ %a@]"
      (pr_more_sep_list "," pr_tyvar) vs pr_cnstrnt cn
