(** Data structures and printing for InvarGenT.

    Released under the GNU General Public Licence (version 2 or
    higher), NO WARRANTY of correctness etc. (C) Lukasz Stafiniak 2013
    @author Lukasz Stafiniak lukstafi (AT) gmail.com
    @since Mar 2013
*)
(** {2 Definitions} *)

let debug = ref false

open Lexing
open Aux

type loc = {beg_pos : position; end_pos : position}
let dummy_loc =
  {beg_pos = dummy_pos; end_pos = dummy_pos}

exception Report_toplevel of string * loc option

let min_pos p1 p2 =
  if p1.pos_cnum <> -1 && p1.pos_cnum < p2.pos_cnum then p1 else p2
let max_pos p1 p2 =
  if p2.pos_cnum < p1.pos_cnum then p1 else p2
let loc_union ?loc loc1 loc2 =
  match loc with
    | Some loc -> loc
    | None ->
      if loc1 = dummy_loc then loc2
      else if loc2 = dummy_loc then loc1
      else
	{beg_pos = min_pos loc1.beg_pos loc2.beg_pos;
	 end_pos = max_pos loc1.end_pos loc2.end_pos}
let loc_tighter loc1 loc2 =
  if loc1.end_pos.pos_cnum - loc1.beg_pos.pos_cnum <
    loc2.end_pos.pos_cnum - loc2.beg_pos.pos_cnum &&
    loc1.beg_pos.pos_cnum <> -1
  then loc1 else loc2
let interloc loc1 loc2 =
  not (loc1.end_pos.pos_cnum < loc2.beg_pos.pos_cnum ||
         loc1.beg_pos.pos_cnum > loc2.end_pos.pos_cnum)

type cns_name =
| CNam of string
| Extype of int

let tuple = CNam "Tuple"
let numtype = CNam "Num"
let boolean = CNam "Boolean"

type pat =
| Zero
| One of loc
| PVar of string * loc
| PAnd of pat * pat * loc
| PCons of cns_name * pat list * loc

let pat_loc = function
  | Zero -> dummy_loc
  | One loc -> loc
  | PVar (_, loc) -> loc
  | PAnd (_, _, loc) -> loc
  | PCons (_, _, loc) -> loc

type ('a, 'b) expr =
| Var of string * loc
| Num of int * loc
| Cons of cns_name * ('a, 'b) expr list * loc
| App of ('a, 'b) expr * ('a, 'b) expr * loc
| Lam of 'b * ('a, 'b) clause list * loc
| ExLam of int * ('a, 'b) clause list * loc
| Letrec of 'a * string * ('a, 'b) expr * ('a, 'b) expr * loc
| Letin of pat * ('a, 'b) expr * ('a, 'b) expr * loc
| AssertFalse of loc
| AssertLeq of ('a, 'b) expr * ('a, 'b) expr * ('a, 'b) expr * loc
| AssertEqty of ('a, 'b) expr * ('a, 'b) expr * ('a, 'b) expr * loc

and ('a, 'b) clause = pat * ('a, 'b) expr

let expr_loc = function
  | Var (_, loc)
  | Num (_, loc)
  | Cons (_, _, loc)
  | App (_, _, loc)
  | Lam (_, _, loc)
  | ExLam (_, _, loc)
  | Letrec (_, _, _, _, loc)
  | Letin (_, _, _, loc)
  | AssertFalse loc
  | AssertLeq (_, _, _, loc)
  | AssertEqty (_, _, _, loc)
    -> loc

let clause_loc (pat, exp) =
  loc_union (pat_loc pat) (expr_loc exp)

type sort = Num_sort | Type_sort

let sort_str = function
  | Num_sort -> "num"
  | Type_sort -> "type"


(** Type variables (and constants) remember their sort. Sort
    inference is performed on user-supplied types and constraints. *)
type var_name =
| VNam of sort * string
| VId of sort * int

let delta = VId (Type_sort, -1)
let delta' = VId (Type_sort, -2)

let var_sort = function VNam (s,_) -> s | VId (s,_) -> s
let var_str = function
  | VNam (_,v) -> v
  | VId _ as d when d = delta -> "δ"
  | VId _ as d when d = delta' -> "δ'"
  | VId (s,i) -> Char.escaped (sort_str s).[0]^string_of_int i
let cns_str = function
  | CNam c -> c
  | Extype i -> "Ex"^string_of_int i

type typ =
| TVar of var_name
| TCons of cns_name * typ list
| Fun of typ * typ
| NCst of int
| Nadd of typ list

let tdelta = TVar delta
let tdelta' = TVar delta'

module VarSet =
    Set.Make (struct type t = var_name let compare = Pervasives.compare end)
let vars_of_list l =
  List.fold_right VarSet.add l VarSet.empty
let add_vars l vs =
  List.fold_right VarSet.add l vs
let no_vs = VarSet.empty

let rec return_type = function
  | Fun (_, r) -> return_type r
  | t -> t

let rec arg_types = function
  | Fun (a, r) -> a::arg_types r
  | t -> []

type uexpr = (unit, unit) expr
type iexpr = (int list, (var_name * var_name) list) expr

let fuse_exprs =
  let rec aux e1 e2 =
    match e1, e2 with
    | Cons (n1, es, lc1), Cons (n2, fs, lc2) ->
      assert (n1==n2 && lc1==lc2);
      Cons (n1, combine es fs, lc1)
    | App (e1, e2, lc1), App (f1, f2, lc2) ->
      assert (lc1==lc2);
      App (aux e1 f1, aux e2 f2, lc1)
    | Lam (ms, cls1, lc1), Lam (ns, cls2, lc2) ->
      assert (lc1==lc2);
      Lam (ms@ns, combine_cls cls1 cls2, lc1)
    | ExLam (k1, cls1, lc1), ExLam (k2, cls2, lc2) ->
      assert (k1==k2 && lc1==lc2);
      ExLam (k1, combine_cls cls1 cls2, lc1)
    | Letrec (ms, x, e1, e2, lc1), Letrec (ns, y, f1, f2, lc2) ->
      assert (x==y && lc1==lc2);
      Letrec (ms@ns, x, aux e1 f1, aux e2 f2, lc1)
    | Letin (p1, e1, e2, lc1), Letin (p2, f1, f2, lc2) ->
      assert (p1==p2 && lc1==lc2);
      Letin (p1, aux e1 f1, aux e2 f2, lc1)
    | AssertLeq (e1, e2, e3, lc1), AssertLeq (f1, f2, f3, lc2) ->
      assert (lc1==lc2);
      AssertLeq (aux e1 f1, aux e2 f2, aux e3 f3, lc1)
    | AssertEqty (e1, e2, e3, lc1), AssertEqty (f1, f2, f3, lc2) ->
      assert (lc1==lc2);
      AssertEqty (aux e1 f1, aux e2 f2, aux e3 f3, lc1)
    | (Var _ as e), f
    | (Num _ as e), f
    | (AssertFalse _ as e), f ->
      assert (e==f); e
    | _ -> assert false

  and combine es fs = List.map2 aux es fs
  and aux_cl (p1, e1) (p2, e2) =
    assert (p1 = p2);
    p1, aux e1 e2
  and combine_cls es fs =
    List.map2 aux_cl es fs in
  function
  | [] -> assert false
  | [e] -> e
  | e::es -> List.fold_left aux e es

(** {3 Mapping and folding} *)

type typ_map = {
  map_tvar : var_name -> typ;
  map_tcons : string -> typ list -> typ;
  map_exty : int -> typ list -> typ;
  map_fun : typ -> typ -> typ;
  map_ncst : int -> typ;
  map_nadd : typ list -> typ
}

type 'a typ_fold = {
  fold_tvar : var_name -> 'a;
  fold_tcons : string -> 'a list -> 'a;
  fold_exty : int -> 'a list -> 'a;
  fold_fun : 'a -> 'a -> 'a;
  fold_ncst : int -> 'a;
  fold_nadd : 'a list -> 'a
}

let typ_id_map = {
  map_tvar = (fun v -> TVar v);
  map_tcons = (fun n tys -> TCons (CNam n, tys));
  map_exty = (fun i tys -> TCons (Extype i, tys));
  map_fun = (fun t1 t2 -> Fun (t1, t2));
  map_ncst = (fun i -> NCst i);
  map_nadd = (fun tys -> Nadd tys)
}

let typ_make_fold op base = {
  fold_tvar = (fun _ -> base);
  fold_tcons = (fun _ tys -> List.fold_left op base tys);
  fold_exty = (fun _ tys -> List.fold_left op base tys);
  fold_fun = (fun t1 t2 -> op t1 t2);
  fold_ncst = (fun _ -> base);
  fold_nadd = (fun tys -> List.fold_left op base tys)
}

let typ_map tmap t =
  let rec aux = function
    | TVar v -> tmap.map_tvar v
    | TCons (CNam n, tys) -> tmap.map_tcons n (List.map aux tys)
    | TCons (Extype i, tys) -> tmap.map_exty i (List.map aux tys)
    | Fun (t1, t2) -> tmap.map_fun (aux t1) (aux t2)
    | NCst i -> tmap.map_ncst i
    | Nadd tys -> tmap.map_nadd (List.map aux tys) in
  aux t

let typ_fold tfold t =
  let rec aux = function
    | TVar v -> tfold.fold_tvar v
    | TCons (CNam n, tys) -> tfold.fold_tcons n (List.map aux tys)
    | TCons (Extype i, tys) -> tfold.fold_exty i (List.map aux tys)
    | Fun (t1, t2) -> tfold.fold_fun (aux t1) (aux t2)
    | NCst i -> tfold.fold_ncst i
    | Nadd tys -> tfold.fold_nadd (List.map aux tys) in
  aux t


let sb_typ_unary arg =
  typ_map {typ_id_map with map_tvar = fun v ->
    if v = delta then arg else TVar v}  

let sb_typ_binary arg1 arg2 =
  typ_map {typ_id_map with map_tvar = fun v ->
    if v = delta then arg1 else if v = delta' then arg2 else TVar v}  


(** {3 Zipper} *)
type typ_dir =
| TCons_dir of cns_name * typ list * typ list
| Fun_left of typ
| Fun_right of typ
| Nadd_dir of typ list * typ list
type typ_loc = {typ_sub : typ; typ_ctx : typ_dir list}

let typ_up t =
  match t.typ_sub with
  | TVar v -> None
  | TCons (_, []) -> None
  | TCons (n, t1::ts) ->
    Some {typ_sub = t1; typ_ctx = TCons_dir (n, [], ts) :: t.typ_ctx}
  | Fun (t1, t2) ->
    Some {typ_sub = t1; typ_ctx = Fun_left t2 :: t.typ_ctx}
  | NCst i -> None
  | Nadd [] -> None
  | Nadd (t1::ts) ->
    Some {typ_sub = t1; typ_ctx = Nadd_dir ([], ts) :: t.typ_ctx}

let typ_down t =
  match t.typ_ctx with
  | [] -> None
  | TCons_dir (n, ts_l, ts_r)::ctx ->
    Some {typ_sub=TCons (n, ts_l@[t.typ_sub]@ts_r); typ_ctx=ctx}
  | Fun_left t2::ctx ->
    Some {typ_sub=Fun (t.typ_sub, t2); typ_ctx=ctx}
  | Fun_right t1::ctx ->
    Some {typ_sub=Fun (t1, t.typ_sub); typ_ctx=ctx}
  | Nadd_dir (ts_l, ts_r)::ctx ->
    Some {typ_sub=Nadd (ts_l@[t.typ_sub]@ts_r); typ_ctx=ctx}   

let rec typ_next ?(same_level=false) t =
  match t.typ_ctx with
  | [] -> None
  | (TCons_dir (n, ts_l, []))::_ when not same_level ->
    bind_opt (typ_down t) (typ_next ~same_level)
  | (TCons_dir (n, ts_l, []))::_ (* when same_level *) -> None
  | (TCons_dir (n, ts_l, t_r::ts_r))::ctx ->
    Some {typ_sub=t_r; typ_ctx=TCons_dir (n, ts_l@[t.typ_sub], ts_r)::ctx}
  | Fun_left t2::ctx ->
    Some {typ_sub = t2; typ_ctx = Fun_right t.typ_sub::ctx}
  | Fun_right _ :: _ when not same_level ->
    bind_opt (typ_down t) (typ_next ~same_level)
  | Fun_right _ :: _ (* when same_level *) -> None
  | (Nadd_dir (ts_l, []))::_ when not same_level ->
    bind_opt (typ_down t) (typ_next ~same_level)
  | (Nadd_dir (ts_l, []))::_ (* when same_level *) -> None
  | (Nadd_dir (ts_l, t_r::ts_r))::ctx ->
    Some {typ_sub=t_r; typ_ctx=Nadd_dir (ts_l@[t.typ_sub], ts_r)::ctx}

let rec typ_out t =
  if t.typ_ctx = [] then t.typ_sub
  else match typ_down t with Some t -> typ_out t | None -> assert false

(** {3 Substitutions} *)

let typ_size = typ_fold (typ_make_fold (fun i j -> i+j+1) 1)

let fvs_typ =
  typ_fold {(typ_make_fold VarSet.union VarSet.empty)
  with fold_tvar = (fun v -> VarSet.singleton v)}

type subst = (var_name * (typ * loc)) list
type hvsubst = (var_name * var_name) list

let subst_typ sb =
  typ_map {typ_id_map with map_tvar =
      fun v -> try fst (List.assoc v sb) with Not_found -> TVar v}

let hvsubst_typ sb =
  typ_map {typ_id_map with map_tvar =
      fun v -> TVar (try List.assoc v sb with Not_found -> v)}

let subst_one v s t =
  let modif = ref false in
  let res = typ_map
    {typ_id_map with map_tvar =
        fun w -> if v = w then (modif:=true; s) else TVar w} t in
  !modif, res

let subst_sb ~sb =
  List.map (fun (w,(t,loc)) -> w, (subst_typ sb t, loc))

let hvsubst_sb sb =
  List.map (fun (w,(t,loc)) -> w, (hvsubst_typ sb t, loc))

let update_sb ~more_sb sb =
  map_append (fun (w,(t,loc)) -> w, (subst_typ more_sb t, loc)) sb
    more_sb

let c_subst_typ sb t =
  let rec aux t =
    try fst (List.assoc t sb)
    with Not_found ->
      match t with
      | TVar _ -> t
      | TCons (n, args) -> TCons (n, List.map aux args)
      | Fun (t1, t2) -> Fun (aux t1, aux t2)
      | NCst _ -> t
      | Nadd args -> Nadd (List.map aux args) in
  aux t

let n_subst_typ sb t =
  let rec aux = function
    | TVar _ as t -> t
    | TCons (n, args) ->
      (try List.assoc n sb args
       with Not_found -> TCons (n, List.map aux args))
    | Fun (t1, t2) -> Fun (aux t1, aux t2)
    | NCst _ as n -> n
    | Nadd args -> Nadd (List.map aux args) in
  aux t


let map_in_subst f =
  List.map (fun (v,(t,lc)) -> v, (f t, lc))


(** {3 Formulas} *)

type atom =
| Eqty of typ * typ * loc
| Leq of typ * typ * loc
| CFalse of loc
| PredVarU of int * typ * loc
| PredVarB of int * typ * typ * loc
| NotEx of typ * loc

let fvs_atom = function
  | Eqty (t1, t2, _) | Leq (t1, t2, _) ->
    VarSet.union (fvs_typ t1) (fvs_typ t2)
  | CFalse _ -> VarSet.empty
  | PredVarU (_, t, _) -> fvs_typ t
  | PredVarB (_, t1, t2, _) ->
    VarSet.union (fvs_typ t1) (fvs_typ t2)
  | NotEx (t, _) -> fvs_typ t

let atom_loc = function
  | Eqty (_, _, loc) | Leq (_, _, loc) | CFalse loc
  | PredVarU (_, _, loc) | PredVarB (_, _, _, loc) | NotEx (_, loc)
    -> loc

let replace_loc_atom loc = function
  | Eqty (t1, t2, _) -> Eqty (t1, t2, loc)
  | Leq (t1, t2, _) -> Leq (t1, t2, loc)
  | CFalse _ -> CFalse loc
  | PredVarU (n, t, _) -> PredVarU (n, t, loc)
  | PredVarB (n, t1, t2, _) -> PredVarB (n, t1, t2, loc)
  | NotEx (t, _) -> NotEx (t, loc)

let eq_atom a1 a2 =
  match a1, a2 with
  | Eqty (t1, t2, _), Eqty (t3, t4, _)
    when t1=t3 && t2=t4 || t1=t4 && t2=t3 -> true
  | Leq (t1, t2, _), Leq (t3, t4, _)
    when t1=t3 && t2=t4 -> true
  | CFalse _, CFalse _ -> true
  | PredVarU (n1, t1, _), PredVarU (n2, t2, _)
    when n1=n2 && t1=t2 -> true
  | PredVarB (n1, t1, t2, _), PredVarB (n2, t3, t4, _)
    when n1=n2 && t1=t3 && t2=t4 -> true
  | _ -> false

(* TODO: optimize *)
let subformula phi1 phi2 =
  List.for_all (fun a1 -> List.exists (eq_atom a1) phi2) phi1
let formula_inter cnj1 cnj2 =
    List.filter (fun a -> List.exists (eq_atom a) cnj2) cnj1


let subst_atom sb = function
  | Eqty (t1, t2, loc) -> Eqty (subst_typ sb t1, subst_typ sb t2, loc)
  | Leq (t1, t2, loc) -> Leq (subst_typ sb t1, subst_typ sb t2, loc)
  | CFalse _ as a -> a
  | PredVarU (n, t, lc) -> PredVarU (n, subst_typ sb t, lc)
  | PredVarB (n, t1, t2, lc) ->
    PredVarB (n, subst_typ sb t1, subst_typ sb t2, lc)
  | NotEx (t, lc) -> NotEx (subst_typ sb t, lc)

let hvsubst_atom sb = function
  | Eqty (t1, t2, loc) -> Eqty (hvsubst_typ sb t1, hvsubst_typ sb t2, loc)
  | Leq (t1, t2, loc) -> Leq (hvsubst_typ sb t1, hvsubst_typ sb t2, loc)
  | CFalse _ as a -> a
  | PredVarU (n, t, lc) -> PredVarU (n, hvsubst_typ sb t, lc)
  | PredVarB (n, t1, t2, lc) ->
    PredVarB (n, hvsubst_typ sb t1, hvsubst_typ sb t2, lc)
  | NotEx (t, lc) -> NotEx (hvsubst_typ sb t, lc)

let sb_atom_unary arg = function
  | Eqty (t1, t2, lc) ->
    Eqty (sb_typ_unary arg t1, sb_typ_unary arg t2, lc)
  | Leq (t1, t2, lc) ->
    Leq (sb_typ_unary arg t1, sb_typ_unary arg t2, lc)
  | CFalse _ as a -> a
  | PredVarU (_, t, _) -> assert false
  | PredVarB (_, t1, t2, _) -> assert false
  | NotEx _ -> assert false

let sb_atom_binary arg1 arg2 = function
  | Eqty (t1, t2, lc) ->
    Eqty (sb_typ_binary arg1 arg2 t1, sb_typ_binary arg1 arg2 t2, lc)
  | Leq (t1, t2, lc) ->
    Leq (sb_typ_binary arg1 arg2 t1, sb_typ_binary arg1 arg2 t2, lc)
  | CFalse _ as a -> a
  | PredVarU (_, t, _) -> assert false
  | PredVarB (_, t1, t2, _) -> assert false
  | NotEx _ -> assert false

let subst_fo_atom sb = function
  | Eqty (t1, t2, loc) -> Eqty (subst_typ sb t1, subst_typ sb t2, loc)
  | Leq (t1, t2, loc) -> Leq (subst_typ sb t1, subst_typ sb t2, loc)
  | CFalse _ as a -> a
  | (PredVarU _ | PredVarB _ | NotEx _) as a -> a

let atom_size = function
  | Eqty (t1, t2, _) | Leq (t1, t2, _) -> typ_size t1 + typ_size t2 + 1
  | CFalse _ -> 1
  | PredVarU (_, t, _) -> typ_size t + 1
  | PredVarB (_, t1, t2, _) -> typ_size t1 + typ_size t2 + 1
  | NotEx (t, _) -> typ_size t + 1

let map_in_atom f = function
  | Eqty (t1, t2, loc) -> Eqty (f t1, f t2, loc)
  | Leq (t1, t2, loc) -> Leq (f t1, f t2, loc)
  | CFalse _ as a -> a
  | PredVarU (n, t, lc) -> PredVarU (n, f t, lc)
  | PredVarB (n, t1, t2, lc) ->
    PredVarB (n, f t1, f t2, lc)
  | NotEx (t, lc) -> NotEx (f t, lc)

type formula = atom list

let fvs_formula phi =
  List.fold_left VarSet.union VarSet.empty (List.map fvs_atom phi)

let fvs_sb sb =
  List.fold_left VarSet.union
    (vars_of_list (List.map fst sb))
    (List.map (fun (_,(t,_))->fvs_typ t) sb)

let subst_formula sb phi =
  if sb=[] then phi else List.map (subst_atom sb) phi

let hvsubst_formula sb phi =
  List.map (hvsubst_atom sb) phi

let replace_loc loc phi =
  List.map (replace_loc_atom loc) phi

let formula_loc phi =
  List.fold_left loc_union dummy_loc
    (List.map atom_loc phi)

let subst_fo_formula sb phi =
  if sb=[] then phi else List.map (subst_fo_atom sb) phi

let map_in_formula f = List.map (map_in_atom f)

let sb_phi_unary arg = List.map (sb_atom_unary arg)

let sb_phi_binary arg1 arg2 = List.map (sb_atom_binary arg1 arg2)

type typ_scheme = var_name list * formula * typ
type answer = var_name list * formula
(** The annotation, besides providing the type scheme, tells whether
    nested type schemes have free variables in scope of the
    scheme. On [Lam] annotations, provides the argument and the
    return type separately. *)
type texpr = (typ_scheme * bool, (typ * typ) option) expr

let extype_id = ref 0
let predvar_id = ref 0

type struct_item =
| TypConstr of cns_name * sort list * loc
| ValConstr of cns_name * var_name list * formula * typ list
  * cns_name * var_name list * loc
| PrimVal of string * typ_scheme * loc
| LetRecVal of string * uexpr * typ_scheme option * uexpr list * loc
| LetVal of pat * uexpr * typ_scheme option * uexpr list * loc

type annot_item =
| ITypConstr of cns_name * sort list * loc
| IValConstr of cns_name * var_name list * formula * typ list
  * cns_name * typ list * loc
| IPrimVal of string * typ_scheme * loc
| ILetRecVal of string * texpr * typ_scheme *
                  texpr list * (pat * int option) list * loc
| ILetVal of pat * texpr * typ_scheme * (string * typ_scheme) list *
               texpr list * (pat * int option) list * loc

let rec enc_funtype res = function
  | [] -> res
  | arg::args -> Fun (arg, enc_funtype res args)

let ty_add t1 t2 =
  match t1, t2 with
  | Nadd ds, Nadd es -> Nadd (ds @ es)
  | Nadd es, t | t, Nadd es -> Nadd (t::es)
  | _ -> Nadd [t1; t2]

let typ_scheme_of_item ?(env=[]) = function
| TypConstr _ -> raise Not_found
| ValConstr (_, vs, phi, args, c_n, c_args, _) ->
  vs, phi, enc_funtype (TCons (c_n, List.map (fun v->TVar v) c_args)) args
| PrimVal (_, t, _) -> t
| LetRecVal (name, _, _, _, _)
| LetVal (PVar (name, _), _, _, _, _) -> List.assoc name env
| LetVal _ -> raise Not_found

type var_scope =
| Left_of | Same_quant | Right_of

type quant_ops = {
  cmp_v : var_name -> var_name -> var_scope;
  uni_v : var_name -> bool;
  same_as : var_name -> var_name -> unit;
}

let empty_q = {
  cmp_v = (fun _ _ -> Same_quant);
  uni_v = (fun _ -> false);
  same_as = (fun _ _ -> ());
}
  

let var_scope_str = function
| Left_of -> "left_of"
| Same_quant -> "same_quant"
| Right_of -> "right_of"

exception Contradiction of sort * string * (typ * typ) option * loc
exception NoAnswer of sort * string * (typ * typ) option * loc
exception Suspect of formula * loc

let convert = function
  | NoAnswer (sort, msg, tys, lc) ->
    Contradiction (sort, msg, tys, lc)
  | Contradiction (sort, msg, tys, lc) ->
    NoAnswer (sort, msg, tys, lc)
  | e -> e

let typ_sort = function
  | TCons _ | Fun _ |
      TVar (VNam (Type_sort, _) | VId (Type_sort, _)) -> Type_sort
  | NCst _ | Nadd _ |
      TVar (VNam (Num_sort, _)
                 | VId (Num_sort, _)) -> Num_sort

let atom_sort = function
  | Eqty (t1, t2, lc) ->
    let s1 = typ_sort t1 and s2 = typ_sort t2 in
    if s1 = s2 then s1
    else raise
        (Contradiction (s1, "Sort mismatch", Some (t1, t2), lc))
  | Leq _ -> Num_sort
  | CFalse _ -> Type_sort
  | PredVarU _ -> Type_sort
  | PredVarB _ -> Type_sort
  | NotEx _ -> Type_sort

(** {2 Global tables} *)

type sigma =
  (cns_name, var_name list * formula * typ list * cns_name * var_name list)
    Hashtbl.t

let sigma : sigma = Hashtbl.create 128
let all_ex_types = ref []

(** {2 Printing} *)
let current_file_name = ref ""

open Format

let pr_loc_pos_only ppf loc =
  fprintf ppf "@[<1>:%d@,-%d:@]"
    loc.beg_pos.pos_cnum loc.end_pos.pos_cnum

let pr_loc_short ppf loc =
  let clbeg = loc.beg_pos.pos_cnum - loc.beg_pos.pos_bol in
  fprintf ppf "@[<1>%s:%d:%d@,-%d:I:@]"
  !current_file_name loc.beg_pos.pos_lnum clbeg
  (clbeg+(loc.end_pos.pos_cnum - loc.beg_pos.pos_cnum))

let pr_loc_long ppf loc =
  if loc = dummy_loc then fprintf ppf "@[<0>{no@ loc}@]" else
    let clbeg = loc.beg_pos.pos_cnum - loc.beg_pos.pos_bol in
    fprintf ppf "@[<2>File@ \"%s\",@ line@ %d,@ characters@ %d-%d:@]"
      !current_file_name loc.beg_pos.pos_lnum clbeg
      (clbeg+(loc.end_pos.pos_cnum - loc.beg_pos.pos_cnum))

let pr_loc_emb ppf loc =
  let clbeg = loc.beg_pos.pos_cnum - loc.beg_pos.pos_bol in
  let clend = loc.end_pos.pos_cnum - loc.end_pos.pos_bol in
  fprintf ppf "@[<1>{%d:%d@,-%d:%d}@]"
    loc.beg_pos.pos_lnum clbeg loc.end_pos.pos_lnum clend

let pr_loc ppf loc = pr_loc_long ppf loc

let pr_sep_list sep ?pr_hd pr_tl ppf l =
  let pr_hd = match pr_hd with
    | None -> pr_tl | Some pr_a -> pr_a in
  let rec aux = function
    | [] -> ()
    | [hd] -> pr_hd ppf hd
    | hd::tl ->
      fprintf ppf "%a%s@ %a" pr_hd hd sep more_aux tl
  and more_aux ppf = function
    | [] -> ()
    | [hd] -> pr_tl ppf hd
    | hd::tl ->
      fprintf ppf "%a%s@ %a" pr_tl hd sep more_aux tl in
  aux l

let rec pr_pre_sep_list sep pr_a ppf = function
  | [] -> ()
  | [hd] -> pr_a ppf hd
  | hd::tl ->
      fprintf ppf "%a@ %s%a" pr_a hd sep (pr_pre_sep_list sep pr_a) tl

let rec pr_line_list sep pr_a ppf = function
  | [] -> ()
  | [hd] -> pr_a ppf hd
  | hd::tl ->
      fprintf ppf "%a@\n%s%a" pr_a hd sep (pr_line_list sep pr_a) tl

let rec pr_pat ppf = function
  | Zero -> fprintf ppf "%s" "!"
  | One _ -> fprintf ppf "%s" "_"
  | PVar (x, _) -> fprintf ppf "%s" x
  | PAnd (pat1, pat2, _) ->
      fprintf ppf "@[<2>%a@ as@ %a@]"
	pr_pat pat1 pr_more_pat pat2
  | PCons (CNam "Tuple", pats, _) ->
    fprintf ppf "@[<2>(%a)@]"
      (pr_sep_list "," ~pr_hd:pr_pat pr_more_pat) pats
  | PCons (x, [], _) ->
      fprintf ppf "%s" (cns_str x)
  | PCons (x, [pat], _) ->
      fprintf ppf "@[<2>%s@ %a@]" (cns_str x) pr_one_pat pat
  | PCons (x, pats, _) ->
      fprintf ppf "@[<2>%s@ (%a)@]" (cns_str x)
	(pr_sep_list "," ~pr_hd:pr_pat pr_more_pat) pats

and pr_more_pat ppf = function
  | PAnd _ as p ->
      fprintf ppf "(%a)" (pr_pat) p
  | p -> pr_pat ppf p

and pr_one_pat ppf = function
  | Zero -> fprintf ppf "%s" "!"
  | One _ -> fprintf ppf "%s" "_"
  | PVar (x, _) -> fprintf ppf "%s" x
  | PCons (x, [], _) ->
      fprintf ppf "%s" (cns_str x)
  | p -> fprintf ppf "(%a)" pr_pat p


let collect_lambdas e =
  let rec aux pats = function
    | Lam (_, [pat, exp], _) -> aux (pat::pats) exp
    | expr -> List.rev pats, expr in
  aux [] e

let rec collect_apps e =
  let rec aux args = function
    | App (f, arg, _) -> aux (arg::args) f
    | expr -> expr::args in
  aux [] e

let pr_tyvar ppf v = pp_print_string ppf (var_str v)

let pr_vars ppf vs =
  pr_sep_list "," pr_tyvar ppf (VarSet.elements vs)

type ('a, 'b) pr_expr_annot =
  | LetRecNode of 'a
  | LamNode of 'b
  | MatchVal of 'b
  | MatchRes of 'b
  | LamOpen of 'b
  | MatchValOpen of 'b
  | MatchResOpen of 'b
  | LetInOpen of 'b
  | LetInNode of 'b

let rec pr_expr pr_ann ppf = function
  | Var (s, _) -> fprintf ppf "%s" s
  | Num (i, _) -> fprintf ppf "%d" i
  | Cons (CNam "Tuple", exps, _) ->
    fprintf ppf "@[<2>(%a)@]"
      (pr_sep_list "," (pr_expr pr_ann)) exps
  | Cons (x, [], _) ->
    fprintf ppf "%s" (cns_str x)
  | Cons (x, [exp], _) ->
    fprintf ppf "@[<2>%s@ %a@]" (cns_str x) (pr_one_expr pr_ann) exp
  | Cons (x, exps, _) ->
    fprintf ppf "@[<2>%s@ (%a)@]" (cns_str x)
      (pr_sep_list "," (pr_expr pr_ann)) exps
  | Lam (_, [_], _) as exp ->
    let pats, expr = collect_lambdas exp in
    fprintf ppf "@[<2>(fun@ %a@ ->@ %a)@]"
      (pr_sep_list "" pr_one_pat) pats
      (pr_expr pr_ann) expr
  | Lam (ann, cs, _) ->
    fprintf ppf "@[<2>%a(function@ %a)%a@]"
      pr_ann (LamOpen ann)
      (pr_pre_sep_list "| " (pr_clause pr_ann)) cs
      pr_ann (LamNode ann)
  | ExLam (_, cs, _) ->
    fprintf ppf "@[<0>(efunction@ %a)@]"
      (pr_pre_sep_list "| " (pr_clause pr_ann)) cs
  | App (Lam (ann, [(v,body)], _), def, _) ->
    fprintf ppf "@[<0>let@ @[<4>%a%a%a@] =@ @[<2>%a@]@ in@ @[<0>%a@]@]"
      pr_ann (LetInOpen ann)
      pr_more_pat v pr_ann (LetInNode ann)
      (pr_expr pr_ann) def
      (pr_expr pr_ann) body
  | App (Lam (ann, cls, _), def, _) ->
    fprintf ppf "@[<0>%amatch@ @[<4>%a%a%a@] with@ @[<2>%a@]%a@]"
      pr_ann (MatchResOpen ann)
      pr_ann (MatchValOpen ann)
      (pr_expr pr_ann) def
      pr_ann (MatchVal ann)
      (pr_pre_sep_list "| " (pr_clause pr_ann)) cls
      pr_ann (MatchRes ann)
  | App _ as exp ->
    let fargs = collect_apps exp in
    fprintf ppf "@[<2>%a@]"
      (pr_sep_list "" (pr_one_expr pr_ann)) fargs
  | Letrec (ann, x, exp, range, _) ->
    fprintf ppf "@[<0>let rec %s@ %a=@ @[<2>%a@] in@ @[<0>%a@]@]"
      x pr_ann (LetRecNode ann)
      (pr_expr pr_ann) exp (pr_expr pr_ann) range
  | Letin (pat, exp, range, _) ->
    fprintf ppf "@[<0>let %a =@ @[<2>%a@] in@ @[<0>%a@]@]"
      pr_pat pat (pr_expr pr_ann) exp
      (pr_expr pr_ann) range
  | AssertFalse _ -> fprintf ppf "assert false"
  | AssertLeq (e1, e2, range, _) ->
    fprintf ppf "@[<0>assert@[<2>@ %a@ ≤@ %a@];@ %a@]"
      (pr_expr pr_ann) e1 (pr_expr pr_ann) e2
      (pr_expr pr_ann) range
  | AssertEqty (e1, e2, range, _) ->
    fprintf ppf "@[<0>assert@ = type@[<2>@ %a@ %a@];@ %a@]"
      (pr_expr pr_ann) e1 (pr_expr pr_ann) e2
      (pr_expr pr_ann) range

and pr_clause pr_ann ppf (pat, exp) =
  fprintf ppf "@[<2>%a@ ->@ %a@]"
    pr_pat pat (pr_expr pr_ann) exp

and pr_one_expr pr_ann ppf exp = match exp with
  | Var _
  | Num _
  | Cons (_, [], _) -> pr_expr pr_ann ppf exp
  | _ ->
    fprintf ppf "(%a)" (pr_expr pr_ann) exp

let pr_uexpr ppf = pr_expr (fun ppf _ -> fprintf ppf "") ppf
let pr_iexpr ppf = pr_expr (fun ppf _ -> fprintf ppf "") ppf

let collect_argtys ty =
  let rec aux args = function
    | Fun (arg, res) -> aux (arg::args) res
    | res -> res::args in
  List.rev (aux [] ty)

let pr_exty = ref (fun ppf (i, rty) -> failwith "not implemented")

(* Using "X" because "script chi" is not available on all systems. *)
let rec pr_atom ppf = function
  | Eqty (t1, t2, _) ->
    fprintf ppf "@[<2>%a@ =@ %a@]" pr_one_ty t1 pr_one_ty t2
  | Leq (t1, t2, _) ->
    fprintf ppf "@[<2>%a@ ≤@ %a@]" pr_one_ty t1 pr_one_ty t2
  | CFalse _ -> pp_print_string ppf "FALSE"
  | PredVarU (i,ty,lc) -> fprintf ppf "@[<2>X%d(%a)@]" i pr_ty ty
  | PredVarB (i,t1,t2,lc) ->
    fprintf ppf "@[<2>X%d(%a,@ %a)@]" i pr_ty t1 pr_ty t2
  | NotEx (t,lc) ->
    fprintf ppf "@[<2>NotEx(%a)@]" pr_ty t

and pr_formula ppf atoms =
  pr_sep_list " ∧" pr_atom ppf atoms

and pr_ty ppf = function
  | TVar v -> fprintf ppf "%s" (var_str v)
  | NCst i -> fprintf ppf "%d" i
  | TCons (CNam c, []) -> fprintf ppf "%s" c
  | TCons (CNam "Tuple", exps) ->
    fprintf ppf "@[<2>(%a)@]" (pr_sep_list "," pr_ty) exps
  | TCons (CNam c, [ty]) ->
    fprintf ppf "@[<2>%s@ %a@]" c pr_one_ty ty
  | TCons (CNam c, exps) ->
    fprintf ppf "@[<2>%s@ (%a)@]" c (pr_sep_list "," pr_ty ) exps
  | TCons (Extype i, args) -> !pr_exty ppf (i, args)
  | Nadd []  -> fprintf ppf "0"
  | Nadd [ty] -> pr_ty ppf ty
  | Nadd tys ->
    fprintf ppf "@[<2>%a@]" (pr_sep_list " +" pr_ty) tys
  | Fun _ as ty ->
    let tys = collect_argtys ty in
    fprintf ppf "@[<2>%a@]"
      (pr_sep_list " →" pr_fun_ty) tys
    
    
and pr_one_ty ppf ty = match ty with
  | TVar _ | NCst _ | Nadd [] | Nadd [_]
  | TCons (_, []) -> pr_ty ppf ty
  | _ ->
    fprintf ppf "(%a)" pr_ty ty

and pr_fun_ty ppf ty = match ty with
  | Fun _ ->
    fprintf ppf "(%a)" pr_ty ty
  | _ -> pr_ty ppf ty

let pr_sort ppf = function
  | Num_sort -> fprintf ppf "num"
  | Type_sort -> fprintf ppf "type"

let pr_typscheme ppf = function
  | [], [], ty -> pr_ty ppf ty
  | vs, [], ty ->
    fprintf ppf "@[<0>∀%a.@ %a@]"
      (pr_sep_list "," pr_tyvar) vs pr_ty ty
  | vs, phi, ty ->
    fprintf ppf "@[<0>∀%a[%a].@ %a@]"
      (pr_sep_list "," pr_tyvar) vs
      pr_formula phi pr_ty ty

let pr_ans ppf = function
  | [], ans -> pr_formula ppf ans
  | vs, ans ->
    fprintf ppf "@[<2>∃%a.@ %a@]"
      (pr_sep_list "," pr_tyvar) vs pr_formula ans

  
let pr_subst ppf sb =
  pr_sep_list ";" (fun ppf (v,(t,_)) ->
    fprintf ppf "%s:=%a" (var_str v) pr_ty t) ppf sb
  
let pr_hvsubst ppf sb =
  pr_sep_list ";" (fun ppf (v,t) ->
    fprintf ppf "%s:=%s" (var_str v) (var_str t)) ppf sb

  

let pr_typ_dir ppf = function
  | TCons_dir (n, ts_l, []) ->
    fprintf ppf "@[<2>%s@ (%a,@ ^)@]" (cns_str n)
      (pr_sep_list "," pr_ty) ts_l
  | TCons_dir (n, ts_l, ts_r) ->
    fprintf ppf "@[<2>%s@ (%a,@ ^,@ %a)@]" (cns_str n)
      (pr_sep_list "," pr_ty) ts_l
      (pr_sep_list "," pr_ty) ts_r
  | Fun_left t2 ->
    fprintf ppf "@[<2>^ →@ %a@]" pr_ty t2
  | Fun_right t1 ->
    fprintf ppf "@[<2>%a →@ ^@]" pr_ty t1
  | Nadd_dir (ts_l, []) ->
    fprintf ppf "@[<2>%a@ + ^@]"
      (pr_sep_list " +" pr_ty) ts_l
  | Nadd_dir (ts_l, ts_r) ->
    fprintf ppf "@[<2>%a@ + ^@ + %a@]"
      (pr_sep_list " +" pr_ty) ts_l
      (pr_sep_list " +" pr_ty) ts_r

let pr_typ_loc ppf t =
  fprintf ppf "@[<2>%a@ <-@ [%a]@]" pr_ty t.typ_sub
    (pr_sep_list ";" pr_typ_dir) t.typ_ctx

let pr_opt_sig_tysch ppf = function
  | None -> ()
  | Some tysch -> fprintf ppf "@ :@ %a" pr_typscheme tysch

let pr_opt_tests pr_ann ppf = function
  | [] -> ()
  | tests ->
    fprintf ppf "@\n@[<2>test@ %a@]"
      (pr_sep_list ";" (pr_expr pr_ann)) tests

let pr_opt_utests = pr_opt_tests (fun ppf _ -> fprintf ppf "")

let pr_sig_item ppf = function
  | ITypConstr (name, [], _) ->
    fprintf ppf "@[<2>newtype@ %s@]" (cns_str name)
  | ITypConstr (name, sorts, _) ->
    fprintf ppf "@[<2>newtype@ %s@ :@ %a@]" (cns_str name)
      (pr_sep_list " *" pr_sort) sorts
  | IValConstr (Extype _ as name, vs, phi, [arg],
               Extype j, [c_arg], _) ->
    fprintf ppf "@[<2>newcons@ %s@ :@ ∀%a[%a].%a@ ⟶@ Ex%d %a@]"
      (cns_str name)
      (pr_sep_list "," pr_tyvar) vs
      pr_formula phi pr_ty arg j pr_ty c_arg
  | IValConstr (name, [], [], [], c_n, c_args, _) ->
    let res = TCons (c_n, c_args) in
    fprintf ppf "@[<2>newcons@ %s@ :@ %a@]" (cns_str name)
      pr_ty res
  | IValConstr (name, [], [], args, c_n, c_args, _) ->
    let res = TCons (c_n, c_args) in
    fprintf ppf "@[<2>newcons@ %s@ :@ %a@ ⟶@ %a@]" (cns_str name)
      (pr_sep_list " *" pr_ty) args pr_ty res
  | IValConstr (name, vs, [], [], c_n, c_args, _) ->
    let res = TCons (c_n, c_args) in
    fprintf ppf "@[<2>newcons@ %s@ :@ ∀%a.@ %a@]" (cns_str name)
      (pr_sep_list "," pr_tyvar) vs
      pr_ty res
  | IValConstr (name, vs, phi, [], c_n, c_args, _) ->
    let res = TCons (c_n, c_args) in
    fprintf ppf "@[<2>newcons@ %s@ :@ ∀%a[%a].@ %a@]" (cns_str name)
      (pr_sep_list "," pr_tyvar) vs
      pr_formula phi pr_ty res
  | IValConstr (name, vs, [], args, c_n, c_args, _) ->
    let res = TCons (c_n, c_args) in
    fprintf ppf "@[<2>newcons@ %s@ :@ ∀%a.%a@ ⟶@ %a@]" (cns_str name)
      (pr_sep_list "," pr_tyvar) vs
      (pr_sep_list " *" pr_ty) args pr_ty res
  | IValConstr (name, vs, phi, args, c_n, c_args, _) ->
    let res = TCons (c_n, c_args) in
    fprintf ppf "@[<2>newcons@ %s@ :@ ∀%a[%a].%a@ ⟶@ %a@]" (cns_str name)
      (pr_sep_list "," pr_tyvar) vs
      pr_formula phi
      (pr_sep_list " *" pr_ty) args pr_ty res
  | IPrimVal (name, tysch, _) ->
    fprintf ppf "@[<2>external@ %s@ :@ %a@]" name pr_typscheme tysch
  | ILetRecVal (name, expr, tysch, tests, _, _) ->
    fprintf ppf "@[<2>val@ %s :@ %a@]" name pr_typscheme tysch
  | ILetVal (_, _, _, tyschs, _, _, _) ->
    pr_line_list "\n" 
      (fun ppf (name,tysch) ->
         fprintf ppf "@[<2>val@ %s :@ %a@]" name pr_typscheme tysch)
      ppf tyschs

let pr_signature ppf p =
  pr_line_list "\n" pr_sig_item ppf p

let pr_struct_item ppf = function
  | TypConstr (name, sorts, lc) ->
    pr_sig_item ppf (ITypConstr (name, sorts, lc))
  | ValConstr (name, vs, phi, args, c_n, c_args, lc) ->
    let c_args = List.map (fun v -> TVar v) c_args in
    pr_sig_item ppf (IValConstr (name, vs, phi, args, c_n, c_args, lc))
  | PrimVal (name, tysch, lc) ->
    pr_sig_item ppf (IPrimVal (name, tysch, lc))
  | LetRecVal (name, expr, tysch, tests, _) ->
    fprintf ppf "@[<2>let rec@ %s%a@ =@ %a@]%a" name
      pr_opt_sig_tysch tysch pr_uexpr expr pr_opt_utests tests
  | LetVal (pat, expr, tysch, tests, _) ->
    fprintf ppf "@[<2>let@ %a@%a@ =@ %a@]%a" pr_pat pat
      pr_opt_sig_tysch tysch pr_uexpr expr pr_opt_utests tests

let pr_program ppf p =
  pr_line_list "\n" pr_struct_item ppf p

let pr_exception ppf = function
  | Report_toplevel (what, None) ->
    Format.fprintf ppf "%!\n%s\n%!" what
  | Report_toplevel (what, Some where) ->
    pr_loc_long ppf where;
    Format.fprintf ppf "%!\n%s\n%!" what
  | Contradiction (sort, what, None, where) ->
    pr_loc_long ppf where;
    Format.fprintf ppf "%!\nContradiction in %s: %s\n%!"
      (sort_str sort) what
  | Contradiction (sort, what, Some (ty1, ty2), where) ->
    pr_loc_long ppf where;
    Format.fprintf ppf
      "%!\nContradiction in %s: %s\ntypes involved:\n%a\n%a\n%!"
      (sort_str sort) what pr_ty ty1 pr_ty ty2
  | NoAnswer (sort, what, None, where) ->
    pr_loc_long ppf where;
    Format.fprintf ppf "%!\nNo answer in %s: %s\n%!"
      (sort_str sort) what
  | NoAnswer (sort, what, Some (ty1, ty2), where) ->
    pr_loc_long ppf where;
    Format.fprintf ppf
      "%!\nNo answer in %s: %s\ntypes involved:\n%a\n%a\n%!"
      (sort_str sort) what pr_ty ty1 pr_ty ty2
  | exn -> raise exn


let pr_to_str pr_f e =
  ignore (Format.flush_str_formatter ());
  pr_f Format.str_formatter e;
  Format.flush_str_formatter ()

(** {2 Unification} *)

let split_sorts cnj =
  let cnj_typ, cnj = List.partition
    (function
    | Eqty (_,t,_) when typ_sort t = Type_sort -> true
    | _ -> false) cnj in
  let cnj_num, cnj = List.partition
    (function
    | Eqty (_,t,_) when typ_sort t = Num_sort -> true
    | Leq _ -> true
    | _ -> false) cnj in
  assert (cnj=[]);
  [Type_sort, cnj_typ; Num_sort, cnj_num]

let connected ?(validate=fun _ -> ()) target (vs, phi) =
  let phi = List.sort (fun a b -> atom_size a - atom_size b) phi in
  (*[* Format.printf "connected: target=%a@ vs=%a@\nphi=%a@\n%!"
    pr_vars (vars_of_list target) pr_vars (vars_of_list vs)
    pr_formula phi; *]*)
  let nodes = List.map
      (function
        | Eqty (TVar _, TVar _, _) as c ->
          let cvs = fvs_atom c in c, cvs, cvs
        | (Eqty (TVar v, t, _) | Eqty (t, TVar v, _)) as c
          when typ_sort t = Type_sort ->
          c, VarSet.singleton v, fvs_typ t
        | c -> let cvs = fvs_atom c in c, cvs, cvs)
      phi in
  let rec loop acc vs nvs rem =
    let more, rem = List.partition
      (fun (c, ivs, ovs) -> List.exists (flip VarSet.mem ivs) nvs) rem in
    let mvs = List.fold_left VarSet.union VarSet.empty
      (List.map thr3 more) in
    let nvs = VarSet.elements
        (VarSet.diff mvs (VarSet.union vs (vars_of_list nvs))) in
    let acc = List.fold_left
        (fun acc (c,_,_) ->
           let acc' = c::acc in
           try validate acc'; acc'
           with Contradiction _ -> acc)
        acc more in
    (*[* Format.printf "connected-loop: nvs=%a@\nacc=%a@\n%!"
      pr_vars (vars_of_list nvs) pr_formula acc; *]*)
    if nvs = [] then acc
    else loop acc (VarSet.union mvs vs) nvs rem in
  let ans = loop [] VarSet.empty target nodes in
  (*[* Format.printf "connected: target=%a@ vs=%a@ phi=%a@ ans=%a@\n%!"
    pr_vars (vars_of_list target) pr_vars (vars_of_list vs) pr_formula phi
    pr_formula ans; *]*)
  VarSet.elements (VarSet.inter (fvs_formula ans) (vars_of_list vs)),
  ans

let var_not_left_of q v t =
  VarSet.for_all (fun w -> q.cmp_v v w <> Left_of) (fvs_typ t)

(* If there are no [bvs] parameters, the LHS variable has to be
   existential and not upstream (i.e. left of) of any RHS variable
   that is not in [pms].

   If [v] is a [bvs] parameter, every universal variable must be
   left of some [bv] parameter. (Note that a [bv] parameter that
   is sufficiently downstream is a "savior".) Existential variables
   are not constrained: do not need to be same as or to the left of [v]. *)
let quant_viol q bvs pms v t =
  let uv = q.uni_v v in
  let pvs, npvs = List.partition (fun v->VarSet.mem v bvs)
    (VarSet.elements (fvs_typ t)) in
  let pvs = if VarSet.mem v bvs then v::pvs else pvs in
  let uni_vs =
    List.filter q.uni_v (if VarSet.mem v bvs then npvs else v::npvs) in
  (*[* Format.printf "quant_viol: vrels %!"; *]*)
  let res =
  if not (VarSet.mem v bvs) then uv ||
    List.exists
    (fun v2 ->
      (*[* Format.printf "%s %s %s; " (var_str v)
        (var_scope_str (q.cmp_v v v2)) (var_str v2); *]*)
      not (VarSet.mem v2 pms) && q.cmp_v v v2 = Left_of) npvs
  else
    not
      (List.for_all
         (fun uv -> q.cmp_v v uv = Same_quant ||
                    List.exists (fun pv -> q.cmp_v uv pv = Left_of) pvs)
         uni_vs) in
  (*[* Format.printf
    "@\nquant_viol: %b; v=%s; uv=%b;@ t=%a;@ bvs=%a;@ pms=%a;@ pvs=%a;@
   uni_vs=%a; npvs=%a@\n%!"
    res (var_str v) uv (pr_ty false) t
    pr_vars bvs pr_vars pms pr_vars (vars_of_list pvs)
    pr_vars (vars_of_list uni_vs) pr_vars (vars_of_list npvs);
  *]*)
  res  

let registered_notex_vars = Hashtbl.create 32
let register_notex v = Hashtbl.add registered_notex_vars v ()
let is_old_notex v = Hashtbl.mem registered_notex_vars v

(** Separate type sort and number sort constraints,  *)
let unify ?use_quants ?bvs ?pms ?(sb=[]) q cnj =
  let new_notex = ref false in
  let use_quants, bvs, pms =
    match use_quants, bvs, pms with
    | None, None, None -> assert false
    | Some false, None, None -> false, VarSet.empty, VarSet.empty
    | (None | Some true), Some bvs, None -> true, bvs, VarSet.empty
    | (None | Some true), None, Some pms -> true, VarSet.empty, pms
    | (None | Some true), Some bvs, Some pms -> true, bvs, pms
    | _ -> assert false in
  let subst_one_sb v s = List.map
      (fun (w,(t,loc)) ->
         let modif, t' = subst_one v s t in
         if use_quants && modif && quant_viol q bvs pms w t'
         then raise
             (Contradiction (Type_sort, "Quantifier violation",
                             Some (TVar w, t'), loc));
         w, (t', loc)) in
  let cnj_typ, more_cnj = partition_map
      (function
        | Eqty (t1, t2, loc) when typ_sort t1 = Type_sort ->
          Left (t1, t2, loc)
        | Eqty (t1, t2, loc) as a when typ_sort t1 = Num_sort ->
          Right (Left a)
        | Leq _ as a -> Right (Left a)
        | (CFalse _ | PredVarU _ | PredVarB _) as a ->
          Right (Right a)
        | NotEx _ as a -> new_notex := true; Right (Right a)
        | Eqty (t1, t2, loc) ->
          raise
            (Contradiction (Type_sort, "Type sort mismatch",
                            Some (t1, t2), loc)))
      cnj in
  let cnj_num, cnj_so = partition_choice more_cnj in
  let rec aux sb num_cn = function
    | [] -> sb, num_cn
    | (t1, t2, loc)::cnj when t1 = t2 -> aux sb num_cn cnj
    | (t1, t2, loc)::cnj ->
      match subst_typ sb t1, subst_typ sb t2 with
      | t1, t2 when t1 = t2 -> aux sb num_cn cnj
      | t1, t2 when typ_sort t1 = Num_sort && typ_sort t2 = Num_sort ->
        aux sb (Eqty (t1, t2, loc)::num_cn) cnj
      | t1, t2 when typ_sort t1 = Num_sort || typ_sort t2 = Num_sort ->
        raise
          (Contradiction (Type_sort, "Type sort mismatch",
                          Some (t1, t2), loc))
      | (TVar v as tv, (TCons (Extype _, _) as t)
                 | (TCons (Extype _, _) as t), (TVar v as tv))
        when is_old_notex v ->
        raise (Contradiction (Type_sort, "Should not be existential",
                              Some (tv, t), loc))        
      | (TVar v as tv, t | t, (TVar v as tv))
        when VarSet.mem v (fvs_typ t) ->
        raise (Contradiction (Type_sort, "Occurs check fail",
                              Some (tv, t), loc))
      | (TVar v, t | t, TVar v)
        when use_quants && quant_viol q bvs pms v t ->
        raise
          (Contradiction (Type_sort, "Quantifier violation",
                          Some (TVar v, t), loc))
      | (TVar v1 as tv1, (TVar v2 as tv2)) ->
        if q.cmp_v v1 v2 = Left_of
        then aux ((v2, (tv1, loc))::subst_one_sb v2 tv1 sb) num_cn cnj
        else aux ((v1, (tv2, loc))::subst_one_sb v1 tv2 sb) num_cn cnj
      | (TVar v, t | t, TVar v) ->
        aux ((v, (t, loc))::subst_one_sb v t sb) num_cn cnj
      | (TCons (f, f_args) as t1,
                              (TCons (g, g_args) as t2)) when f=g ->
        let more_cnj =
          try List.combine f_args g_args
          with Invalid_argument _ ->
            raise
              (Contradiction (Type_sort, "Type arity mismatch",
                              Some (t1, t2), loc)) in
        aux sb num_cn (List.map (fun (t1,t2)->t1,t2,loc) more_cnj @ cnj)
      | Fun (f1, a1), Fun (f2, a2) ->
        let more_cnj = [f1, f2, loc; a1, a2, loc] in
        aux sb num_cn (more_cnj @ cnj)
      | (TCons (f, _) as t1,
                         (TCons (g, _) as t2)) ->
        (*[* Format.printf "unify: mismatch f=%s g=%s@ t1=%a@ t2=%a@\n%!"
          (cns_str f) (cns_str g) (pr_ty false) t1 (pr_ty false) t2; *]*)
        raise
          (Contradiction (Type_sort, "Type mismatch",
                          Some (t1, t2), loc))
      | t1, t2 ->
        (*[* Format.printf "unify: mismatch@ t1=%a@ t2=%a@\n%!"
          (pr_ty false) t1 (pr_ty false) t2; *]*)
        raise
          (Contradiction (Type_sort, "Type mismatch",
                          Some (t1, t2), loc)) in
  let cnj_typ, cnj_num = aux sb cnj_num cnj_typ in
  if !new_notex then List.iter
      (function
        | NotEx (t, loc) ->
          (match subst_typ cnj_typ t with
           | TCons (Extype _, _) as st ->
             raise (Contradiction (Type_sort, "Should not be existential",
                                   Some (t, st), loc))        
           | _ -> ())
        | _ -> ()) cnj_so;
  cnj_typ, cnj_num, cnj_so

let to_formula =
  List.map (fun (v,(t,loc)) -> Eqty (TVar v, t, loc))
    
let subst_of_cnj ?(elim_uni=false) q cnj =
  map_some
    (function
      | Eqty (TVar v, t, lc)
        when (elim_uni || not (q.uni_v v))
          && VarSet.for_all (fun v2 -> q.cmp_v v v2 <> Left_of)
               (fvs_typ t) ->
        Some (v,(t,lc))
      | Eqty (t, TVar v, lc)
        when (elim_uni || not (q.uni_v v))
          && VarSet.for_all (fun v2 -> q.cmp_v v v2 <> Left_of)
               (fvs_typ t) ->
        Some (v,(t,lc))
      | _ -> None)
    cnj

let combine_sbs ?ignore_so ?use_quants ?bvs ?pms q ?(more_phi=[]) sbs =
  let cnj_typ, cnj_num, cnj_so =
    unify ?use_quants ?bvs ?pms q
      (more_phi @ concat_map to_formula sbs) in
  assert (ignore_so<>None || cnj_so = []);
  cnj_typ, cnj_num

let subst_solved ?ignore_so ?use_quants ?bvs ?pms q sb ~cnj =
  let cnj = List.map
    (fun (v,(t,lc)) -> Eqty (subst_typ sb (TVar v), subst_typ sb t, lc))
    cnj in
  let cnj_typ, cnj_num, cnj_so =
    unify ?use_quants ?bvs ?pms q cnj in
  assert (ignore_so<>None || cnj_so = []);
  cnj_typ, cnj_num

let cleanup q vs ans =
  let clean, ans = partition_map
    (function x, _ as sx when List.mem x vs -> Left sx
    | y, (TVar x, lc) when List.mem x vs -> Left (x, (TVar y, lc))
    | sy -> Right sy) ans in
  (* TODO: could use [unify] by treating [vs] as [Downstream] in [q.cmp_v] *)
  let clean, cn_num, cn_so = unify ~use_quants:false q
     (to_formula clean) in
  let sb, more_ans = List.partition
    (function x, _ when List.mem x vs -> true
    | _ -> false) clean in    
  assert (cn_num = []);
  assert (cn_so = []);
  let ans = subst_sb ~sb (more_ans @ ans) in
  let ansvs = fvs_sb ans in
  List.filter (flip VarSet.mem ansvs) vs, ans
  

(** {2 Nice variables} *)

let typvars = "abcrst"
let numvars = "nkijml"
let typvars_n = String.length typvars
let numvars_n = String.length numvars

let next_typ fvs =
  let rec aux i =
    let ch, n = i mod typvars_n, i / typvars_n in
    let v s = VNam (s, Char.escaped typvars.[ch] ^
                         (if n>0 then string_of_int n else "")) in
    if VarSet.mem (v Num_sort) fvs || VarSet.mem (v Type_sort) fvs
    then aux (i+1) else v Type_sort in
  aux 0

let next_num fvs =
  let rec aux i =
    let ch, n = i mod numvars_n, i / numvars_n in
    let v s = VNam (s, Char.escaped numvars.[ch] ^
                         (if n>0 then string_of_int n else "")) in
    if VarSet.mem (v Num_sort) fvs || VarSet.mem (v Type_sort) fvs
    then aux (i+1) else v Num_sort in
  aux 0

let next_var allvs s =
  if s = Type_sort then next_typ allvs else next_num allvs

let nice_ans ?sb ?(fvs=VarSet.empty) (vs, phi) =
  let named_vs, vs =
    List.partition (function VNam _ -> true | _ -> false) vs in
  let fvs = VarSet.union fvs (fvs_formula phi) in
  let fvs =
    match sb with
    | None -> fvs
    | Some sb -> add_vars (List.map snd sb) fvs in
  let allvs, rn = fold_map
      (fun fvs v ->
         let w = next_var fvs (var_sort v) in
         VarSet.add w fvs, (v, w))
      fvs vs in
  let rvs = List.map snd rn in
  let sb = match sb with
    | Some sb -> sb | None -> [] in
  let sb = rn @ sb in
  sb, (named_vs @ rvs, hvsubst_formula sb phi)

let () = pr_exty :=
  fun ppf (i, args) ->
    let vs, phi, ty, ety_n, pvs = Hashtbl.find sigma (Extype i) in
    let ty = match ty with [ty] -> ty | _ -> assert false in
    let sb =
      try List.map2 (fun v t -> v, (t, dummy_loc)) pvs args
      with Invalid_argument("List.map2") -> (* assert false *) [] in
    let phi, ty =
      if sb=[] then phi, ty
      else subst_formula sb phi, subst_typ sb ty in
    (*[* Format.printf
      "@\npr_exty: i=%d ty=%a@ vs=%a@ pvs=%a@ phi=%a@\n%!"
      i (pr_ty false) ty pr_vars (vars_of_list vs) pr_vars
       (vars_of_list pvs) pr_formula phi; *]*)
    let evs = VarSet.elements
        (VarSet.diff (vars_of_list vs) (vars_of_list pvs)) in
    let phi = Eqty (ty, ty, dummy_loc)::phi in
    let _, (evs, phi) = nice_ans (evs, phi) in
    let ty, phi = match phi with
      | Eqty (ty, tv, _)::phi -> ty, phi
      | _ -> assert false in
    (* TODO: "@[<2>∃%d:%a[%a].%a@]" better? *)
    if phi = [] then
      fprintf ppf "∃%d:%a.%a" i
        (pr_sep_list "," pr_tyvar) evs pr_ty ty
    else
      fprintf ppf "∃%d:%a[%a].%a" i
        (pr_sep_list "," pr_tyvar) evs pr_formula phi pr_ty ty

(** {2 Globals} *)

let parser_more_items = ref []
let parser_unary_typs = Hashtbl.create 15
let parser_unary_vals = Hashtbl.create 31
let parser_last_typ = ref 0
let parser_last_num = ref 0

let reset_state () =
  extype_id := 0; all_ex_types := [];
  predvar_id := 0; Hashtbl.clear sigma;
  parser_more_items := [];
  Hashtbl.clear parser_unary_typs;
  Hashtbl.clear parser_unary_vals;
  Hashtbl.clear registered_notex_vars;
  parser_last_typ := 0;
  parser_last_num := 0
