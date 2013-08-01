(** Data structures and printing for InvarGenT.

    Released under the GNU General Public Licence (version 2 or
    higher), NO WARRANTY of correctness etc. (C) Lukasz Stafiniak 2013
    @author Lukasz Stafiniak lukstafi (AT) gmail.com
    @since Mar 2013
*)
(** {2 Definitions} *)

let debug = ref false

open Lexing

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

type pat =
| Zero
| One of loc
| PVar of string * loc
| PAnd of pat * pat * loc
| PCons of string * pat list * loc

let pat_loc = function
  | Zero -> dummy_loc
  | One (loc) -> loc
  | PVar (_, loc) -> loc
  | PAnd (_, _, loc) -> loc
  | PCons (_, _, loc) -> loc

type expr =
| Var of string * loc
| Num of int * loc
| Cons of string * expr list * loc
| App of expr * expr * loc
| Lam of clause list * loc
| ExLam of int * clause list * loc
| Letrec of string * expr * expr * loc
| Letin of pat * expr * expr * loc
| AssertFalse of loc
| AssertLeq of expr * expr * expr * loc
| AssertEqty of expr * expr * expr * loc

and clause = pat * expr

let expr_loc = function
  | Var (_, loc)
  | Num (_, loc)
  | Cons (_, _, loc)
  | App (_, _, loc)
  | Lam (_, loc)
  | ExLam (_, _, loc)
  | Letrec (_, _, _, loc)
  | Letin (_, _, _, loc)
  | AssertFalse loc
  | AssertLeq (_, _, _, loc)
  | AssertEqty (_, _, _, loc)
    -> loc

let clause_loc (pat, exp) =
  loc_union (pat_loc pat) (expr_loc exp)

type sort = Num_sort | Type_sort | Undefined_sort

let sort_str = function
  | Num_sort -> "num"
  | Type_sort -> "type"
  | Undefined_sort -> "undefined"

(** Type variables (and constants) remember their sort. Sort
    inference is performed on user-supplied types and constraints. *)
type var_name =
| VNam of sort * string
| VId of sort * int

type cns_name =
| CNam of string
| Extype of int

let var_sort = function VNam (s,_) -> s | VId (s,_) -> s
let var_str = function
  | VNam (_,v) -> v
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

let delta = VId (Type_sort, -1)
let delta' = VId (Type_sort, -2)

module VarSet =
    Set.Make (struct type t = var_name let compare = Pervasives.compare end)
let vars_of_list l =
  List.fold_right VarSet.add l VarSet.empty
let add_vars l vs =
  List.fold_right VarSet.add l vs

(** {3 Mapping and folding} *)

type typ_map = {
  map_tvar : var_name -> typ;
  map_tcons : cns_name -> typ list -> typ;
  map_fun : typ -> typ -> typ;
  map_ncst : int -> typ;
  map_nadd : typ list -> typ
}

type 'a typ_fold = {
  fold_tvar : var_name -> 'a;
  fold_tcons : cns_name -> 'a list -> 'a;
  fold_fun : 'a -> 'a -> 'a;
  fold_ncst : int -> 'a;
  fold_nadd : 'a list -> 'a
}

let typ_id_map = {
  map_tvar = (fun v -> TVar v);
  map_tcons = (fun n tys -> TCons (n, tys));
  map_fun = (fun t1 t2 -> Fun (t1, t2));
  map_ncst = (fun i -> NCst i);
  map_nadd = (fun tys -> Nadd tys)
}

let typ_make_fold op base = {
  fold_tvar = (fun _ -> base);
  fold_tcons = (fun _ tys -> List.fold_left op base tys);
  fold_fun = (fun t1 t2 -> op t1 t2);
  fold_ncst = (fun _ -> base);
  fold_nadd = (fun tys -> List.fold_left op base tys)
}

let typ_map tmap t =
  let rec aux = function
    | TVar v -> tmap.map_tvar v
    | TCons (n, tys) -> tmap.map_tcons n (List.map aux tys)
    | Fun (t1, t2) -> tmap.map_fun (aux t1) (aux t2)
    | NCst i -> tmap.map_ncst i
    | Nadd tys -> tmap.map_nadd (List.map aux tys) in
  aux t

let typ_fold tfold t =
  let rec aux = function
    | TVar v -> tfold.fold_tvar v
    | TCons (n, tys) -> tfold.fold_tcons n (List.map aux tys)
    | Fun (t1, t2) -> tfold.fold_fun (aux t1) (aux t2)
    | NCst i -> tfold.fold_ncst i
    | Nadd tys -> tfold.fold_nadd (List.map aux tys) in
  aux t

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
    Aux.bind_opt (typ_down t) (typ_next ~same_level)
  | (TCons_dir (n, ts_l, []))::_ (* when same_level *) -> None
  | (TCons_dir (n, ts_l, t_r::ts_r))::ctx ->
    Some {typ_sub=t_r; typ_ctx=TCons_dir (n, ts_l@[t.typ_sub], ts_r)::ctx}
  | Fun_left t2::ctx ->
    Some {typ_sub = t2; typ_ctx = Fun_right t.typ_sub::ctx}
  | Fun_right _ :: _ when not same_level ->
    Aux.bind_opt (typ_down t) (typ_next ~same_level)
  | Fun_right _ :: _ (* when same_level *) -> None
  | (Nadd_dir (ts_l, []))::_ when not same_level ->
    Aux.bind_opt (typ_down t) (typ_next ~same_level)
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
  with fold_tvar = fun v -> VarSet.singleton v}

type subst = (var_name * (typ * loc)) list

let subst_typ sb =
  typ_map {typ_id_map with map_tvar =
      fun v -> try fst (List.assoc v sb) with Not_found -> TVar v}

let subst_one v s =
  typ_map {typ_id_map with map_tvar =
      fun w -> if v = w then s else TVar w}

let subst_one_sb v s =
  List.map (fun (w,(t,loc)) -> w, (subst_one v s t, loc))

let subst_sb ~sb =
  List.map (fun (w,(t,loc)) -> w, (subst_typ sb t, loc))

let update_sb ~more_sb sb =
  Aux.map_append (fun (w,(t,loc)) -> w, (subst_typ more_sb t, loc)) sb
    more_sb

(** {3 Formulas} *)

type atom =
| Eqty of typ * typ * loc
| Leq of typ * typ * loc
| CFalse of loc
| PredVarU of int * typ
| PredVarB of int * typ * typ

let fvs_atom = function
  | Eqty (t1, t2, _) | Leq (t1, t2, _) ->
    VarSet.union (fvs_typ t1) (fvs_typ t2)
  | CFalse _ -> VarSet.empty
  | PredVarU (_, t) -> fvs_typ t
  | PredVarB (_, t1, t2) ->
    VarSet.union (fvs_typ t1) (fvs_typ t2)

let atom_loc = function
  | Eqty (_, _, loc) | Leq (_, _, loc)
  | CFalse loc -> loc
  | PredVarU (_, _) | PredVarB (_, _, _) -> dummy_loc

let subst_atom sb = function
  | Eqty (t1, t2, loc) -> Eqty (subst_typ sb t1, subst_typ sb t2, loc)
  | Leq (t1, t2, loc) -> Leq (subst_typ sb t1, subst_typ sb t2, loc)
  | CFalse _ as a -> a
  | PredVarU (n, t) -> PredVarU (n, subst_typ sb t)
  | PredVarB (n, t1, t2) -> PredVarB (n, subst_typ sb t1, subst_typ sb t2)

let subst_fo_atom sb = function
  | Eqty (t1, t2, loc) -> Eqty (subst_typ sb t1, subst_typ sb t2, loc)
  | Leq (t1, t2, loc) -> Leq (subst_typ sb t1, subst_typ sb t2, loc)
  | CFalse _ as a -> a
  | (PredVarU _ | PredVarB _) as a -> a

type formula = atom list

let fvs_formula phi =
  List.fold_left VarSet.union VarSet.empty (List.map fvs_atom phi)

let fvs_sb sb =
  List.fold_left VarSet.union
    (vars_of_list (List.map fst sb))
    (List.map (fun (_,(t,_))->fvs_typ t) sb)

let subst_formula sb phi = List.map (subst_atom sb) phi

let subst_fo_formula sb phi = List.map (subst_fo_atom sb) phi

type typ_scheme = var_name list * formula * typ

let extype_id = ref 0
let predvar_id = ref 0

type struct_item =
| TypConstr of cns_name * sort list * loc
| ValConstr of cns_name * var_name list * formula * typ list
  * cns_name * var_name list * loc
| PrimVal of string * typ_scheme * loc
| LetRecVal of string * expr * typ_scheme option * expr list * loc
| LetVal of pat * expr * typ_scheme option * expr list * loc

type program = struct_item list

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
| Upstream | Same_quant | Downstream | Not_in_scope

let str_of_cmp = function
| Upstream -> "upstream"
| Same_quant -> "same_quant"
| Downstream -> "downstream"
| Not_in_scope -> "not_in_scope"

exception Contradiction of string * (typ * typ) option * loc
exception Suspect of var_name list * formula * loc

let typ_sort_typ = function
  | TVar (VNam (Undefined_sort, _) | VId (Undefined_sort, _)) ->
    assert false
  | TCons _ | Fun _ |
      TVar (VNam (Type_sort, _) | VId (Type_sort, _)) -> true
  | _ -> false

let num_sort_typ = function
  | TVar (VNam (Undefined_sort, _) | VId (Undefined_sort, _)) ->
    assert false
  | NCst _ | Nadd _ |
      TVar (VNam (Num_sort, _)
                 | VId (Num_sort, _)) -> true
  | _ -> false

(** {2 Printing} *)
let current_file_name = ref ""

open Format

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

let rec pr_pat comma ppf = function
  | Zero -> fprintf ppf "%s" "!"
  | One _ -> fprintf ppf "%s" "_"
  | PVar (x, _) -> fprintf ppf "%s" x
  | PAnd (pat1, pat2, _) ->
      fprintf ppf "@[<2>%a@ as@ %a@]"
	(pr_pat false) pat1 (pr_more_pat false) pat2
  | PCons ("Tuple", pats, _) ->
      if comma then
	fprintf ppf "@[<2>(%a)@]"
	  (pr_sep_list "," ~pr_hd:(pr_pat true)
	      (pr_more_pat true)) pats
      else
	fprintf ppf "@[<2>%a@]"
	  (pr_sep_list "," ~pr_hd:(pr_pat true)
	      (pr_more_pat true)) pats
  | PCons (x, [], _) ->
      fprintf ppf "%s" x
  | PCons (x, [pat], _) ->
      fprintf ppf "@[<2>%s@ %a@]" x pr_one_pat pat
  | PCons (x, pats, _) ->
      fprintf ppf "@[<2>%s@ (%a)@]" x
	(pr_sep_list "," ~pr_hd:(pr_pat true) (pr_more_pat true)) pats

and pr_more_pat comma ppf = function
  | PAnd _ as p ->
      fprintf ppf "(%a)" (pr_pat comma) p
  | p -> pr_pat comma ppf p

and pr_one_pat ppf = function
  | Zero -> fprintf ppf "%s" "!"
  | One _ -> fprintf ppf "%s" "_"
  | PVar (x, _) -> fprintf ppf "%s" x
  | PCons (x, [], _) ->
      fprintf ppf "%s" x
  | p -> fprintf ppf "(%a)" (pr_pat false) p


let collect_lambdas e =
  let rec aux pats = function
    | Lam ([pat, exp], _) -> aux (pat::pats) exp
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

let rec pr_expr comma ppf = function
  | Var (s, _) -> fprintf ppf "%s" s
  | Num (i, _) -> fprintf ppf "%d" i
  | Cons ("Tuple", exps, _) ->
      if comma then
	fprintf ppf "@[<2>(%a)@]"
	  (pr_sep_list "," (pr_expr true)) exps
      else
	fprintf ppf "@[<2>%a@]"
	  (pr_sep_list "," (pr_expr true)) exps
  | Cons (x, [], _) ->
      fprintf ppf "%s" x
  | Cons (x, [exp], _) ->
      fprintf ppf "@[<2>%s@ %a@]" x pr_one_expr exp
  | Cons (x, exps, _) ->
      fprintf ppf "@[<2>%s@ (%a)@]" x
	(pr_sep_list "," (pr_expr true)) exps
  | Lam ([_], _) as exp ->
      let pats, expr = collect_lambdas exp in
      fprintf ppf "@[<2>fun@ %a@ ->@ %a@]"
	(pr_sep_list "" pr_one_pat) pats
	(pr_expr false) expr
  | Lam (cs, _) ->
      fprintf ppf "@[<2>function@ %a@]"
	(pr_pre_sep_list "| " pr_clause) cs
  | ExLam (_, cs, _) ->
      fprintf ppf "@[<0>efunction@ %a@]"
	(pr_pre_sep_list "| " pr_clause) cs
  | App (Lam ([(v,body)], _), def, _) ->
      fprintf ppf "@[<0>let@ @[<4>%a@] =@ @[<2>%a@]@ in@ @[<0>%a@]@]"
	(pr_more_pat false) v (pr_expr false) def (pr_expr false) body
  | App _ as exp ->
      let fargs = collect_apps exp in
      fprintf ppf "@[<2>%a@]"
	(pr_sep_list "" pr_one_expr) fargs
  | Letrec (x, exp, range, _) ->
      fprintf ppf "@[<0>let rec %s =@ @[<2>%a@] in@ @[<0>%a@]@]"
	x (pr_expr false) exp (pr_expr false) range
  | Letin (pat, exp, range, _) ->
      fprintf ppf "@[<0>let %a =@ @[<2>%a@] in@ @[<0>%a@]@]"
	(pr_pat false) pat (pr_expr false) exp (pr_expr false) range
  | AssertFalse _ -> fprintf ppf "assert false"
  | AssertLeq (e1, e2, range, _) ->
      fprintf ppf "@[<0>assert@[<2>@ %a@ ≤@ %a@];@ %a@]"
	(pr_expr false) e1 (pr_expr false) e2 (pr_expr false) range
  | AssertEqty (e1, e2, range, _) ->
      fprintf ppf "@[<0>assert@ = type@[<2>@ %a@ %a@];@ %a@]"
	(pr_expr false) e1 (pr_expr false) e2 (pr_expr false) range

and pr_clause ppf (pat, exp) =
  fprintf ppf "@[<2>%a@ ->@ %a@]"
    (pr_pat false) pat (pr_expr false) exp

and pr_one_expr ppf exp = match exp with
  | Var _
  | Num _
  | Cons (_, [], _) -> pr_expr true ppf exp
  | _ ->
      fprintf ppf "(%a)" (pr_expr false) exp

let collect_argtys ty =
  let rec aux args = function
    | Fun (arg, res) -> aux (arg::args) res
    | res -> res::args in
  List.rev (aux [] ty)


let rec pr_atom ppf = function
  | Eqty (t1, t2, _) ->
    fprintf ppf "@[<2>%a@ =@ %a@]" pr_one_ty t1 pr_one_ty t2
  | Leq (t1, t2, _) ->
    fprintf ppf "@[<2>%a@ ≤@ %a@]" pr_one_ty t1 pr_one_ty t2
  | CFalse _ -> pp_print_string ppf "FALSE"
  | PredVarU (i,ty) -> fprintf ppf "@[<2>𝛘%d(%a)@]" i (pr_ty false) ty
  | PredVarB (i,t1,t2) ->
    fprintf ppf "@[<2>𝛘%d(%a,@ %a)@]" i (pr_ty true) t1 (pr_ty true) t2

and pr_formula ppf atoms =
  pr_sep_list " ∧" pr_atom ppf atoms

and pr_ty comma ppf = function
  | TVar d when d = delta -> fprintf ppf "δ"
  | TVar d when d = delta' -> fprintf ppf "δ'"
  | TVar v -> fprintf ppf "%s" (var_str v)
  | NCst i -> fprintf ppf "%d" i
  | TCons (x, []) -> fprintf ppf "%s" (cns_str x)
  | TCons (CNam "Tuple", exps) ->
    if comma then
      fprintf ppf "@[<2>(%a)@]"
	(pr_sep_list "," (pr_ty true)) exps
    else
      fprintf ppf "@[<2>%a@]"
	(pr_sep_list "," (pr_ty true)) exps
  | TCons (x, [ty]) ->
    fprintf ppf "@[<2>%s@ %a@]" (cns_str x) pr_one_ty ty
  | TCons (x, exps) ->
    fprintf ppf "@[<2>%s@ (%a)@]" (cns_str x)
      (pr_sep_list "," (pr_ty true)) exps
  | Nadd []  -> fprintf ppf "0"
  | Nadd [ty] -> pr_ty comma ppf ty
  | Nadd (tys) ->
    fprintf ppf "@[<2>%a@]"
      (pr_sep_list " +" (pr_ty true)) tys
  | Fun _ as ty ->
    let tys = collect_argtys ty in
    fprintf ppf "@[<2>%a@]"
      (pr_sep_list " →" pr_fun_ty) tys
    
    
and pr_one_ty ppf ty = match ty with
  | TVar _ | NCst _ | Nadd [] | Nadd [_]
  | TCons (_, []) -> pr_ty true ppf ty
  | _ ->
    fprintf ppf "(%a)" (pr_ty false) ty

and pr_fun_ty ppf ty = match ty with
  | Fun _ ->
    fprintf ppf "(%a)" (pr_ty false) ty
  | _ -> pr_ty false ppf ty

let pr_sort ppf = function
  | Num_sort -> fprintf ppf "num"
  | Type_sort -> fprintf ppf "type"
  | Undefined_sort -> fprintf ppf "undefined"

let pr_typscheme ppf = function
  | [], [], ty -> pr_ty false ppf ty
  | vs, [], ty ->
    fprintf ppf "@[<0>∀%a.@ %a@]"
      (pr_sep_list "," pr_tyvar) vs (pr_ty false) ty
  | vs, phi, ty ->
    fprintf ppf "@[<0>∀%a[%a].@ %a@]"
      (pr_sep_list "," pr_tyvar) vs
      pr_formula phi (pr_ty false) ty

let pr_ans ppf = function
  | [], ans -> pr_formula ppf ans
  | vs, ans ->
    fprintf ppf "@[<2>∃%a.@ %a@]"
      (pr_sep_list "," pr_tyvar) vs pr_formula ans
  
let pr_subst ppf sb =
  pr_sep_list ";" (fun ppf (v,(t,_)) ->
    fprintf ppf "%s:=%a" (var_str v) (pr_ty false) t) ppf sb

let pr_typ_dir ppf = function
  | TCons_dir (n, ts_l, []) ->
    fprintf ppf "@[<2>%s@ (%a,@ ^)@]" (cns_str n)
      (pr_sep_list "," (pr_ty true)) ts_l
  | TCons_dir (n, ts_l, ts_r) ->
    fprintf ppf "@[<2>%s@ (%a,@ ^,@ %a)@]" (cns_str n)
      (pr_sep_list "," (pr_ty true)) ts_l
      (pr_sep_list "," (pr_ty true)) ts_r
  | Fun_left t2 ->
    fprintf ppf "@[<2>^ →@ %a@]" (pr_ty true) t2
  | Fun_right t1 ->
    fprintf ppf "@[<2>%a →@ ^@]" (pr_ty true) t1
  | Nadd_dir (ts_l, []) ->
    fprintf ppf "@[<2>%a@ + ^@]"
      (pr_sep_list " +" (pr_ty true)) ts_l
  | Nadd_dir (ts_l, ts_r) ->
    fprintf ppf "@[<2>%a@ + ^@ + %a@]"
      (pr_sep_list " +" (pr_ty true)) ts_l
      (pr_sep_list " +" (pr_ty true)) ts_r

let pr_typ_loc ppf t =
  fprintf ppf "@[<2>%a@ <-@ [%a]@]" (pr_ty false) t.typ_sub
    (pr_sep_list ";" pr_typ_dir) t.typ_ctx

let pr_opt_sig_tysch ppf = function
  | None -> ()
  | Some tysch -> fprintf ppf "@ :@ %a" pr_typscheme tysch

let pr_opt_tests ppf = function
  | [] -> ()
  | tests ->
    fprintf ppf "@\n@[<2>test@ %a@]"
      (pr_sep_list ";" (pr_expr false)) tests

let pr_struct_item ppf = function
  | TypConstr (name, [], _) ->
    fprintf ppf "@[<2>newtype@ %s@]" (cns_str name)
  | TypConstr (name, sorts, _) ->
    fprintf ppf "@[<2>newtype@ %s@ :@ %a@]" (cns_str name)
      (pr_sep_list " *" pr_sort) sorts
  | ValConstr (name, [], [], [], c_n, c_args, _) ->
    let res = TCons (c_n, List.map (fun v->TVar v) c_args) in
    fprintf ppf "@[<2>newcons@ %s@ :@ %a@]" (cns_str name)
      (pr_ty false) res
  | ValConstr (name, [], [], args, c_n, c_args, _) ->
    let res = TCons (c_n, List.map (fun v->TVar v) c_args) in
    fprintf ppf "@[<2>newcons@ %s@ :@ %a@ ⟶@ %a@]" (cns_str name)
      (pr_sep_list " *" (pr_ty true)) args (pr_ty false) res
  | ValConstr (name, vs, [], [], c_n, c_args, _) ->
    let res = TCons (c_n, List.map (fun v->TVar v) c_args) in
    fprintf ppf "@[<2>newcons@ %s@ :@ ∀%a.@ %a@]" (cns_str name)
      (pr_sep_list "," pr_tyvar) vs
      (pr_ty false) res
  | ValConstr (name, vs, phi, [], c_n, c_args, _) ->
    let res = TCons (c_n, List.map (fun v->TVar v) c_args) in
    fprintf ppf "@[<2>newcons@ %s@ :@ ∀%a[%a].@ %a@]" (cns_str name)
      (pr_sep_list "," pr_tyvar) vs
      pr_formula phi (pr_ty false) res
  | ValConstr (name, vs, [], args, c_n, c_args, _) ->
    let res = TCons (c_n, List.map (fun v->TVar v) c_args) in
    fprintf ppf "@[<2>newcons@ %s@ :@ ∀%a.%a@ ⟶@ %a@]" (cns_str name)
      (pr_sep_list "," pr_tyvar) vs
      (pr_sep_list " *" (pr_ty true)) args (pr_ty false) res
  | ValConstr (name, vs, phi, args, c_n, c_args, _) ->
    let res = TCons (c_n, List.map (fun v->TVar v) c_args) in
    fprintf ppf "@[<2>newcons@ %s@ :@ ∀%a[%a].%a@ ⟶@ %a@]" (cns_str name)
      (pr_sep_list "," pr_tyvar) vs
      pr_formula phi
      (pr_sep_list " *" (pr_ty true)) args (pr_ty false) res
  | PrimVal (name, tysch, _) ->
    fprintf ppf "@[<2>external@ %s@ :@ %a@]" name pr_typscheme tysch
  | LetRecVal (name, expr, tysch, tests, _) ->
    fprintf ppf "@[<2>let rec@ %s%a@ =@ %a@]%a" name
      pr_opt_sig_tysch tysch (pr_expr false) expr pr_opt_tests tests
  | LetVal (pat, expr, tysch, tests, _) ->
    fprintf ppf "@[<2>let@ %a@%a@ =@ %a@]%a" (pr_pat false) pat
      pr_opt_sig_tysch tysch (pr_expr false) expr pr_opt_tests tests

let pr_program ppf p =
  pr_line_list "\n" pr_struct_item ppf p

let pr_exception ppf = function
  | Report_toplevel (what, None) ->
    Format.fprintf ppf "%!\n%s\n%!" what
  | Report_toplevel (what, Some where) ->
    pr_loc_long ppf where;
    Format.fprintf ppf "%!\n%s\n%!" what
  | Contradiction (what, None, where) ->
    pr_loc_long ppf where;
    Format.fprintf ppf "%!\n%s\n%!" what
  | Contradiction (what, Some (ty1, ty2), where) ->
    pr_loc_long ppf where;
    Format.fprintf ppf "%!\n%s\ntypes involved:\n%a\n%a\n%!"
      what (pr_ty false) ty1 (pr_ty false) ty2
  | exn -> raise exn


let pr_to_str pr_f e =
  ignore (Format.flush_str_formatter ());
  pr_f Format.str_formatter e;
  Format.flush_str_formatter ()

(** {2 Unification} *)

(* If there are no parameters, the LHS variable has to be existential
   and not upstream of any RHS variable. If there are parameters, every
   universal variable must be upstream of some parameter.
   (Note that a parameter that is sufficiently downstream is a
   "savior".) *)
let quant_viol cmp_v uni_v params v t =
  let uv = uni_v v in
  let pvs, npvs = List.partition (fun v->VarSet.mem v params)
    (VarSet.elements (fvs_typ t)) in
  if pvs = [] then uv ||
    List.exists (fun v2 -> cmp_v v v2 = Upstream) npvs
  else not
    (List.for_all
       (fun uv -> List.exists (fun pv -> cmp_v uv pv = Upstream) pvs)
       (List.filter uni_v (v::npvs)))

(** Separate type sort and number sort constraints,  *)
let unify ~use_quants ?params ?(sb=[]) cmp_v uni_v cnj =
  let quant_viol = match params with
    | None -> fun _ _ -> false
    | Some params -> quant_viol cmp_v uni_v params in
  let cnj_typ, more_cnj = Aux.partition_map
    (function
    | Eqty (t1, t2, loc) when typ_sort_typ t1 && typ_sort_typ t2 ->
      Aux.Left (t1, t2, loc)
    | Eqty (t1, t2, loc) as a when num_sort_typ t1 && num_sort_typ t2 ->
      Aux.Right (Aux.Left a)
    | Leq _ as a -> Aux.Right (Aux.Left a)
    | (CFalse _ | PredVarU _ | PredVarB _) as a ->
      Aux.Right (Aux.Right a)
    | Eqty (t1, t2, loc) -> raise
      (Contradiction ("Type sort mismatch", Some (t1, t2), loc)))
    cnj in
  let cnj_num, cnj_so = Aux.partition_choice more_cnj in
  let rec aux sb num_cn = function
    | [] -> sb, num_cn
    | (t1, t2, loc)::cnj when t1 = t2 -> aux sb num_cn cnj
    | (t1, t2, loc)::cnj ->
      match subst_typ sb t1, subst_typ sb t2 with
      | t1, t2 when t1 = t2 -> aux sb num_cn cnj
      | t1, t2 when num_sort_typ t1 && num_sort_typ t2 ->
        aux sb (Eqty (t1, t2, loc)::num_cn) cnj
      | t1, t2 when num_sort_typ t1 || num_sort_typ t2 -> raise
        (Contradiction ("Type sort mismatch", Some (t1, t2), loc))
      | (TVar v as tv, t | t, (TVar v as tv))
          when VarSet.mem v (fvs_typ t) ->
        raise (Contradiction ("Occurs check fail", Some (tv, t), loc))
      | (TVar v, t | t, TVar v) when use_quants && quant_viol v t ->
        raise
          (Contradiction ("Quantifier violation", Some (TVar v, t), loc))
      | (TVar v1 as tv1, (TVar v2 as tv2)) ->
        if cmp_v v1 v2 = Upstream
        then aux ((v2, (tv1, loc))::subst_one_sb v2 tv1 sb) num_cn cnj
        else aux ((v1, (tv2, loc))::subst_one_sb v1 tv2 sb) num_cn cnj
      | (TVar v, t | t, TVar v) ->
        aux ((v, (t, loc))::subst_one_sb v t sb) num_cn cnj
      | (TCons (f, f_args) as t1,
         (TCons (g, g_args) as t2)) when f=g ->
        let more_cnj =
          try List.combine f_args g_args
          with Invalid_argument _ -> raise
            (Contradiction ("Type arity mismatch", Some (t1, t2), loc)) in
        aux sb num_cn (List.map (fun (t1,t2)->t1,t2,loc) more_cnj @ cnj)
      | Fun (f1, a1), Fun (f2, a2) ->
        let more_cnj = [f1, f2, loc; a1, a2, loc] in
        aux sb num_cn (more_cnj @ cnj)
      | t1, t2 -> raise
        (Contradiction ("Type mismatch", Some (t1, t2), loc)) in
  let cnj_typ, cnj_num = aux sb cnj_num cnj_typ in
  cnj_typ, cnj_num, cnj_so

let to_formula =
  List.map (fun (v,(t,loc)) -> Eqty (TVar v, t, loc))

let combine_sbs ~use_quants ?params cmp_v uni_v ?(more_phi=[]) sbs =
  let cnj_typ, cnj_num, cnj_so =
    unify ~use_quants ?params cmp_v uni_v
      (more_phi @ Aux.concat_map to_formula sbs) in
  assert (cnj_so = []);
  cnj_typ, cnj_num

let subst_solved ~use_quants ?params cmp_v uni_v sb ~cnj =
  let cnj = List.map
    (fun (v,(t,lc)) -> Eqty (subst_typ sb (TVar v), subst_typ sb t, lc))
    cnj in
  let cnj_typ, cnj_num, cnj_so =
    unify ~use_quants ?params cmp_v uni_v cnj in
  assert (cnj_so = []);
  cnj_typ, cnj_num

(** {2 Sort inference} *)
let newtype_env = Hashtbl.create 15

let infer_sorts_item item =
  let sorts = Hashtbl.create 15 in
  let fresh_proxy = ref 0 in
  let new_proxy () = incr fresh_proxy; Aux.Left !fresh_proxy in
  let rec find v =
    (* try *)
      match Hashtbl.find sorts v with
      | Aux.Left v' -> find (Aux.Left v')
      | Aux.Right s -> s
    (* with Not_found -> assert false *)
  in
  let rec add loc msg v s =
    try
      match Hashtbl.find sorts v with
      | Aux.Left s'l -> add loc msg (Aux.Left s'l) s
      | Aux.Right s'r as s' ->
        if s'r = Undefined_sort
        then Hashtbl.replace sorts v s
        else if s' <> s
        then match s with
        | Aux.Left sl ->
          add loc msg (Aux.Left sl) s'
        | Aux.Right sr -> raise
          (Report_toplevel ("Sort mismatch for "^
                               msg^": sorts "^sort_str sr^" and " ^
                               sort_str s'r, Some loc))
    with Not_found -> Hashtbl.add sorts v s in
  let find_v v =
    try find (Aux.Right v)
    with Not_found ->
      match v with                      (* TODO: why? *)
      | VNam (s, n) when s <> Type_sort && n.[0]='t' ->
        find (Aux.Right (VNam (Type_sort, n)))          
      | VNam (s, n) when s <> Num_sort && n.[0]='n' ->
        find (Aux.Right (VNam (Num_sort, n)))          
      | VNam (s, n) when s <> Undefined_sort ->
        find (Aux.Right (VNam (Undefined_sort, n)))
      | _ -> assert false in
  let add_v loc v s =
    if s <> Aux.Right Undefined_sort
    then add loc (var_str v) (Aux.Right v) s in
  let walk_var = function
    | VId (_,id) as tv -> VId (find_v tv, id)
    | VNam (_,v) as tv -> VNam (find_v tv, v) in
  let walk_typ =
    typ_map {typ_id_map with map_tvar =
        fun tv -> TVar (walk_var tv)} in
  let walk_atom = function
    | Eqty (t1, t2, loc) ->
      Eqty (walk_typ t1, walk_typ t2, loc)
    | Leq (t1, t2, loc) -> Leq (walk_typ t1, walk_typ t2, loc)
    | CFalse _ as a -> a
    | PredVarU (id,ty) -> PredVarU (id, walk_typ ty)
    | PredVarB (id,t1,t2) -> PredVarB (id, walk_typ t1, walk_typ t2) in
  let rec infer_typ_ cur_loc s = function
    | TVar tv -> add_v cur_loc tv s 
    | TCons (CNam "Tuple", args) ->
      List.iter (infer_typ cur_loc (Aux.Right Type_sort)) args
    | TCons (CNam _ as n, args) ->
      (try let argsorts = List.map
             (fun s -> Aux.Right s) (Hashtbl.find newtype_env n) in
           List.iter2 (infer_typ cur_loc) argsorts args
       with
       | Not_found -> raise
         (Report_toplevel ("Undefined type constructor "^cns_str n,
                           Some cur_loc))
       | Invalid_argument _ ->
         let sorts = List.map sort_str (Hashtbl.find newtype_env n) in
         let sorts = String.concat ", " sorts in
         let args = String.concat ", "
           (List.map (pr_to_str (pr_ty true)) args) in
         raise
         (Report_toplevel ("Arity mismatch for type constructor "^
                              cns_str n^": expected "^sorts^
                              "; found "^args, Some cur_loc)))
    | TCons (Extype _ as n, args) ->
      (try let argsorts = List.map
             (fun s -> Aux.Right s) (Hashtbl.find newtype_env n) in
           List.iter2 (infer_typ cur_loc) argsorts args
       with
       | Not_found ->
         List.iter (infer_typ cur_loc (Aux.Right Undefined_sort)) args
       | Invalid_argument _ -> assert false)
    | Fun (t1, t2) ->
      (match s with
      | Aux.Right s ->
        if s <> Undefined_sort && s <> Type_sort then raise
          (Report_toplevel ("Expected sort "^sort_str s^
                               " but found sort type (function)",
                            Some cur_loc));
      | Aux.Left sl ->
        add cur_loc "function type" (Aux.Left sl) (Aux.Right Type_sort));
      infer_typ cur_loc (Aux.Right Type_sort) t1;
      infer_typ cur_loc (Aux.Right Type_sort) t2
    | NCst _ ->
      (match s with
      | Aux.Right s ->
        if s <> Undefined_sort && s <> Num_sort then raise
          (Report_toplevel ("Expected sort "^sort_str s^
                               " but found sort num (constant)",
                            Some cur_loc));
      | Aux.Left sl ->
        add cur_loc "num constant" (Aux.Left sl) (Aux.Right Num_sort));
      ()
    | Nadd args ->
      (match s with
      | Aux.Right s ->
        if s <> Undefined_sort && s <> Num_sort then raise
          (Report_toplevel ("Expected sort "^sort_str s^
                               " but found sort num (addition)",
                            Some cur_loc));
      | Aux.Left sl ->
        add cur_loc "num addition" (Aux.Left sl) (Aux.Right Num_sort));
      List.iter (infer_typ cur_loc (Aux.Right Num_sort)) args
  and infer_typ cur_loc s t =
    infer_typ_ cur_loc s t
  and infer_atom = function
    | Eqty (t1, t2, loc) ->
      let s = new_proxy () in
      infer_typ loc s t1; infer_typ loc s t2
    | Leq (t1, t2, loc) ->
      infer_typ loc (Aux.Right Num_sort) t1;
      infer_typ loc (Aux.Right Num_sort) t2
    | CFalse _ -> ()
    | PredVarU (id,ty) ->
      infer_typ dummy_loc (Aux.Right Type_sort) ty
    | PredVarB (id,t1, t2) ->
      infer_typ dummy_loc (Aux.Right Type_sort) t1;
      infer_typ dummy_loc (Aux.Right Type_sort) t2 in
  match item with
  | TypConstr (CNam _ as name, sorts, _) as item ->
    Hashtbl.add newtype_env name sorts; [item]
  | TypConstr (Extype _, _, _) ->
    []                                  (* will be reintroduced *)
  | ValConstr (CNam _ as name, vs, phi, args, c_n, c_args, loc) ->
    let res = TCons (c_n, List.map (fun v->TVar v) c_args) in
    infer_typ loc (Aux.Right Type_sort) res;
    List.iter (infer_typ loc (Aux.Right Type_sort)) args;
    List.iter infer_atom phi;
    let args = List.map walk_typ args in
    let phi = List.map walk_atom phi in
    let vs = List.map walk_var vs in
    let c_args = List.map walk_var c_args in
    [ValConstr (name, vs, phi, args, c_n, c_args, loc)]
  | ValConstr (Extype _ as name, vs, phi, args,
               c_n, c_args, loc) when name = c_n ->
    let res = TCons (c_n, List.map (fun v->TVar v) c_args) in
    List.iter (infer_typ loc (Aux.Right Type_sort)) args;
    List.iter infer_atom phi;
    infer_typ loc (Aux.Right Type_sort) res;
    let sorts = List.map (fun v -> find_v v) c_args in
    let args = List.map walk_typ args in
    let phi = List.map walk_atom phi in
    let vs = List.map walk_var vs in
    let c_args = List.map walk_var c_args in
    [TypConstr (name, sorts, loc);
     ValConstr (name, vs, phi, args, c_n, c_args, loc)]
  | ValConstr (Extype _, _, _, _, _, _, _) -> assert false
  | PrimVal (n, (vs, phi, ty), loc) ->
    infer_typ loc (Aux.Right Type_sort) ty;
    List.iter infer_atom phi;
    let ty = walk_typ ty in
    let phi = List.map walk_atom phi in
    let vs = List.map walk_var vs in
    [PrimVal (n, (vs, phi, ty), loc)]
  | (LetRecVal _ | LetVal _) as item -> [item]

let infer_sorts prog =
  Aux.concat_map infer_sorts_item prog

let parser_more_items = ref []
let parser_unary_typs = Hashtbl.create 15
let parser_unary_vals = Hashtbl.create 31
let parser_last_typ = ref 0
let parser_last_num = ref 0

let reset_state () =
  extype_id := 0; predvar_id := 0;
  parser_more_items := [];
  Hashtbl.clear parser_unary_typs;
  Hashtbl.clear parser_unary_vals;
  parser_last_typ := 0;
  parser_last_num := 0
