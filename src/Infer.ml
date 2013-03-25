(** Inferring and normalizing formulas for InvarGenT.

    Released under the GNU General Public Licence (version 2 or
    higher), NO WARRANTY of correctness etc. (C) Lukasz Stafiniak 2013
    @author Lukasz Stafiniak lukstafi (AT) gmail.com
    @since Mar 2013
*)
open Terms

exception Contradiction of string * (typ * typ) option * loc

type cnstrnt =
| A of atom list
| And of cnstrnt list
| Or1 of atom list
| Impl of atom list * cnstrnt
| ImplOr2 of (atom * atom) list * cnstrnt
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


let fresh_typ_var () =
  incr fresh_var_id; VId (Type_sort, !fresh_var_id)  

let freshen_var v =
  incr fresh_var_id; VId (var_sort v, !fresh_var_id)  

let rec freshen_typ env = function
  | TVar v as tv ->
    (try TVar (List.assoc v env) with Not_found -> tv)
  | TCons (n, tys) -> TCons (n, List.map (freshen_typ env) tys)
  | Fun (t1, t2) -> Fun (freshen_typ env t1, freshen_typ env t2)
  | NCst _ as c -> c
  | Nadd tys -> Nadd (List.map (freshen_typ env) tys)

let freshen_atom env = function
  | Eqty (t1, t2, loc) ->
    Eqty (freshen_typ env t1, freshen_typ env t2, loc)
  | Leq (t1, t2, loc) ->
    Leq (freshen_typ env t1, freshen_typ env t2, loc)
  | CFalse _ as a -> a
  | PredVarU (i, t) -> PredVarU (i, freshen_typ env t)
  | PredVarB (i, t1, t2) ->
    PredVarB (i, freshen_typ env t1, freshen_typ env t2)

let freshen_cns_scheme (vs, phi, argtys, res) =
  let env = List.map (fun v->v, freshen_var v) vs in
  let res = freshen_typ env res in
  let argtys = List.map (freshen_typ env) argtys in
  let phi = List.map (freshen_atom env) phi in
  let vs = List.map snd env in
  vs, phi, argtys, res

let freshen_val_scheme (vs, phi, res) =
  let vs, phi, _, res = freshen_cns_scheme (vs, phi, [], res) in
  vs, phi, res

let constr_gen_pat sigma p tau =
  let rec aux tau = function
    | Zero | One _ | PVar _ -> And []
    | PAnd (p1, p2, _) -> cn_and (aux tau p1) (aux tau p2)
    | PCons (k, args, loc) ->
      let abvs, phi, argtys, res =
        freshen_cns_scheme (Hashtbl.find sigma k) in
      let avs = fvs_typ res in
      let bvs = VarSet.diff (vars_of_list abvs) avs in
      let argphi =
        List.fold_left cn_and (And [])
          (List.map2 aux argtys args) in
      Ex (avs, And [A [Eqty (res, tau, loc)];
                   All (bvs, Impl (phi, argphi))]) in
  aux tau p
  
type envfrag = VarSet.t * formula * (string * typ) list

let envfrag_x (vs1, phi1, env1) (vs2, phi2, env2) =
  VarSet.union vs1 vs2, phi1 @ phi2, env1 @ env2
let envfrag_empty = VarSet.empty, [], []
let typ_to_sch (x, ty) = x, ([], [], ty)

let rec envfrag_gen_pat sigma p t =
  let rec aux t = function
    | Zero | One _ -> envfrag_empty
    | PVar (x, _) -> VarSet.empty, [], [x, t]
    | PAnd (p1, p2, _) ->
      envfrag_x (aux t p1) (aux t p2)
    | PCons (k, ps, loc) ->
      let vs, phi, args, res =
        freshen_cns_scheme (Hashtbl.find sigma k) in
      let ef0 = vars_of_list vs, Eqty (res, t, loc)::phi, [] in
      List.fold_left envfrag_x ef0 (List.map2 aux args ps) in
  aux t p

let constr_gen_expr gamma sigma ex_types e t =
  let rec aux gamma t = function
    | Var (x, loc) when not (List.mem_assoc x gamma) ->
      raise (Report_toplevel ("Undefined variable "^x, Some loc))
    | Var (x, loc) ->
      let vs, phi, res = freshen_val_scheme (List.assoc x gamma) in
      Ex (vars_of_list vs, cn_and (A [Eqty (res, t, loc)]) (A phi))
    | Num (i, loc) -> A [Eqty (TCons (CNam "Num", [NCst i]), t, loc)]
    | Cons (k, args, loc) when not (Hashtbl.mem sigma k)->
      raise (Report_toplevel ("Undefined constructor "^k, Some loc))
    | Cons (k, args, loc)->
      let vs, phi, argtys, res =
        freshen_cns_scheme (Hashtbl.find sigma k) in
      let cn = List.fold_left cn_and (A (Eqty (res, t, loc)::phi))
        (List.map2 (aux gamma) argtys args) in
      Ex (vars_of_list vs, cn)
    | App (e1, e2, loc) ->
      let a = fresh_typ_var () in
      Ex (VarSet.singleton a,
          cn_and (aux gamma (Fun (TVar a, t)) e1) (aux gamma (TVar a) e2))
    | Lam (cls, loc) ->
      let a1 = fresh_typ_var () in
      let t1 = TVar a1 in
      let a2 = fresh_typ_var () in
      let t2 = TVar a2 in
      let cn = List.fold_left cn_and
        (A [Eqty (Fun (t1, t2), t, loc)])
        (List.map (aux_cl gamma t1 t2) cls) in
      Ex (vars_of_list [a1; a2], cn)
    | ExLam (ety_id, cls, loc) ->
      let a1 = fresh_typ_var () in
      let t1 = TVar a1 in
      let a2 = fresh_typ_var () in
      let t2 = TVar a2 in
      let ety_cn = Extype ety_id in
      let ety = TCons (ety_cn, [t2]) in
      incr fresh_chi_id;
      ex_types := (ety_cn, !fresh_chi_id) :: !ex_types;
      let cn = List.fold_left cn_and
        (A [Eqty (Fun (t1, ety), t, loc)])
        (List.map (aux_ex_cl gamma !fresh_chi_id t1 t2) cls) in
      Ex (vars_of_list [a1; a2], cn)      
    | Letrec (x, e1, e2, loc) ->
      let a = fresh_typ_var () in
      let b = fresh_typ_var () in
      incr fresh_chi_id;
      let tb = TVar b in
      let chi_b = PredVarU (!fresh_chi_id, tb) in
      let chi_a = PredVarU (!fresh_chi_id, TVar a) in
      let gamma = (x, ([b], [chi_b], tb))::gamma in
      let def_cn =
        All (vars_of_list [b],
             Impl ([chi_b], aux gamma tb e1)) in
      cn_and def_cn (cn_and (Ex (vars_of_list [a], A [chi_a]))
                       (aux gamma t e2))
    | Letin (p, e1, e2, loc) ->
      let a0 = fresh_typ_var () in
      let t0 = TVar a0 in
      let a2 = fresh_typ_var () in
      let t2 = TVar a2 in
      let disj = List.map
        (fun (ety_cn, chi) -> Eqty (TCons (ety_cn, [t2]), t0, loc))
        !ex_types in
      let cn0 = aux gamma t0 e1 in
      let a3 = fresh_typ_var () in
      let t3 = TVar a3 in
      let disj_prem = List.map
        (fun (ety_cn, chi) ->
          Eqty (TCons (ety_cn, [t2]), t0, loc), PredVarB (chi, t2, t3))
        !ex_types in
      let concl = aux_cl gamma t3 t (p, e2) in
      Ex (vars_of_list [a0; a2],
          cn_and (cn_and (A disj) cn0)
            (All (vars_of_list [a3], ImplOr2 (disj_prem, concl))))

  and aux_cl gamma t1 t2 (p, e) =
    let pcns = constr_gen_pat sigma p t1 in
    let bs, prem, env = envfrag_gen_pat sigma p t1 in
    let concl = aux (List.map typ_to_sch env @ gamma) t2 e in
    cn_and pcns (All (bs, Impl (prem, concl)))

  and aux_ex_cl gamma chi_id t1 t2 (p, e) =
    let pcns = constr_gen_pat sigma p t1 in
    let bs, prem, env = envfrag_gen_pat sigma p t1 in
    let a3 = fresh_typ_var () in
    let t3 = TVar a3 in
    let concl = aux (List.map typ_to_sch env @ gamma) t3 e in
    let chi = PredVarB (chi_id, t2, t3) in
    cn_and pcns (All (bs, Impl (prem, cn_and (A [chi]) concl))) in
  
  aux gamma t e

let constr_gen_letrec gamma sigma ex_types x e t =
  let a = fresh_typ_var () in
  let b = fresh_typ_var () in
  incr fresh_chi_id;
  let tb = TVar b in
  let chi_b = PredVarU (!fresh_chi_id, tb) in
  let chi_a = PredVarU (!fresh_chi_id, TVar a) in
  let def_typ = [b], [chi_b], tb in
  let gamma = (x, def_typ)::gamma in
  let def_cn =
    All (vars_of_list [b],
         Impl ([chi_b], aux gamma tb e1)) in
  def_typ,
  cn_and def_cn (Ex (vars_of_list [a], A [chi_a]))
(*
let constr_gen_let gamma sigma ex_types p e =
  let a = fresh_typ_var () in
  let ta = TVar a in
  let pcns = constr_gen_pat sigma p ta in
  let bs, prem, env = envfrag_gen_pat sigma p ta in
  let cn = constr_gen_expr gamma sigma ex_types e ta in
  env, cn_and pcns cn

let infer_prog solver prog =
  let gamma = ref [] in
  let sigma = Hashtbl.create 127 in
  let ex_types = ref [] in

  List.map (function
  | TypConstr () of cns_name * sort list * loc
  | ValConstr of cns_name * var_name list * formula * typ list * typ * loc
  | PrimVal of string * typ_scheme * loc
  | LetRecVal of string * expr * loc
  | LetVal of string * expr * loc
  ) prog
*)
(** {2 Postprocessing and printing} *)

type nicevars_env = {
  nvs_env : (int * string) list;
  last_typ : int;
  last_num : int
}
let typvars = "abcdefghorstuvw"
let numvars = "nkijmlpqxyz"
let typvars_n = String.length typvars
let numvars_n = String.length numvars
let nicevars_empty = {nvs_env = []; last_typ = 0; last_num = 0}

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
      (try TVar (VNam (s, List.assoc id env.nvs_env))
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
  | PredVarU (i, t) -> PredVarU (i, nicevars_typ env t)
  | PredVarB (i, t1, t2) ->
    PredVarB (i, nicevars_typ env t1, nicevars_typ env t2)

let nicevars_cnstrnt c =
  let rec aux env = function
    | A atoms -> A (List.map (nicevars_atom env) atoms)
    | And cns -> And (List.map (aux env) cns)
    | Or1 disjs -> Or1 (List.map (nicevars_atom env) disjs)
    | ImplOr2 (disjs, concl) -> ImplOr2
      (List.map (fun (a,b)->nicevars_atom env a, nicevars_atom env b)
         disjs, aux env concl)
    | Impl (prem, concl) ->
      Impl (List.map (nicevars_atom env) prem, aux env concl)
    | All (vs, cn) ->
      let vs' = Aux.map_some
        (function VNam _ -> None | VId (s,id) -> Some (s,id))
        (VarSet.elements vs) in
      let env = List.fold_left (fun env ->
        function Num_sort,id -> next_num env id
        | Type_sort,id -> next_typ env id
        | Undefined_sort,_ -> assert false) nicevars_empty vs' in
      let vs = List.map
        (function VNam _ as v -> v
        | VId (s, id) -> VNam (s, List.assoc id env.nvs_env))
        (VarSet.elements vs) in
      All (vars_of_list vs, aux env cn)
    | Ex (vs, cn) ->
      let vs' = Aux.map_some
        (function VNam _ -> None | VId (s,id) -> Some (s,id))
        (VarSet.elements vs) in
      let env = List.fold_left (fun env ->
        function Num_sort,id -> next_num env id
        | Type_sort,id -> next_typ env id
        | Undefined_sort,_ -> assert false) env vs' in
      let vs = List.map
        (function VNam _ as v -> v
        | VId (s, id) -> VNam (s, List.assoc id env.nvs_env))
        (VarSet.elements vs) in
      Ex (vars_of_list vs, aux env cn) in
  aux {nvs_env = []; last_typ = 0; last_num = 0} c

open Format

let pr_2atoms ppf (a, b) =
  fprintf ppf "%a@ ∧@ %a" pr_atom a pr_atom b  

let rec pr_cnstrnt ppf = function
  | A atoms -> pr_formula ppf atoms
  | And cns -> fprintf ppf "@[<2>";
    pr_more_sep_list "∧" pr_cnstrnt ppf cns; fprintf ppf "@]"
  | Or1 disjs -> fprintf ppf "@[<2>";
    pr_more_sep_list "∨" pr_atom ppf disjs; fprintf ppf "@]"
  | Impl (prem,concl) -> fprintf ppf "@[<2>";
    pr_formula ppf prem; fprintf ppf "@ ⟹@ %a@]" pr_cnstrnt concl
  | ImplOr2 (disjs, concl) -> fprintf ppf "@[<2>";
    pr_more_sep_list "∨" pr_2atoms ppf disjs;
    fprintf ppf "@ ⟹@ %a@]" pr_cnstrnt concl
  | All (vs, cn) -> fprintf ppf "@[<2>";
    fprintf ppf "@[<2>∀%a.@ %a@]"
      (pr_more_sep_list "," pr_tyvar) (VarSet.elements vs) pr_cnstrnt cn
  | Ex (vs, cn) -> fprintf ppf "@[<2>";
    fprintf ppf "@[<2>∃%a.@ %a@]"
      (pr_more_sep_list "," pr_tyvar) (VarSet.elements vs) pr_cnstrnt cn
