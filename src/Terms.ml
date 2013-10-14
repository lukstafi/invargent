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

type pat =
| Zero
| One of loc
| PVar of string * loc
| PAnd of pat * pat * loc
| PCons of cns_name * pat list * loc

let pat_loc = function
  | Zero -> dummy_loc
  | One (loc) -> loc
  | PVar (_, loc) -> loc
  | PAnd (_, _, loc) -> loc
  | PCons (_, _, loc) -> loc

type expr =
| Var of string * loc
| Num of int * loc
| Cons of cns_name * expr list * loc
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

let subst_typ sb =
  typ_map {typ_id_map with map_tvar =
      fun v -> try fst (List.assoc v sb) with Not_found -> TVar v}

let subst_one v s t =
  let modif = ref false in
  let res = typ_map
    {typ_id_map with map_tvar =
        fun w -> if v = w then (modif:=true; s) else TVar w} t in
  !modif, res

let subst_sb ~sb =
  List.map (fun (w,(t,loc)) -> w, (subst_typ sb t, loc))

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

type formula = atom list

let fvs_formula phi =
  List.fold_left VarSet.union VarSet.empty (List.map fvs_atom phi)

let fvs_sb sb =
  List.fold_left VarSet.union
    (vars_of_list (List.map fst sb))
    (List.map (fun (_,(t,_))->fvs_typ t) sb)

let subst_formula sb phi =
  if sb=[] then phi else List.map (subst_atom sb) phi

let replace_loc loc phi =
  List.map (replace_loc_atom loc) phi

let formula_loc phi =
  List.fold_left loc_union dummy_loc
    (List.map atom_loc phi)

let subst_fo_formula sb phi =
  if sb=[] then phi else List.map (subst_fo_atom sb) phi

let sb_phi_unary arg = List.map (sb_atom_unary arg)

let sb_phi_binary arg1 arg2 = List.map (sb_atom_binary arg1 arg2)

type typ_scheme = var_name list * formula * typ
type answer = var_name list * formula

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

exception Contradiction of sort * string * (typ * typ) option * loc
exception NoAnswer of sort * string * (typ * typ) option * loc
exception Suspect of formula * loc

let convert = function
  | NoAnswer (sort, msg, tys, lc) ->
    Contradiction (sort, msg, tys, lc)
  | Contradiction (sort, msg, tys, lc) ->
    NoAnswer (sort, msg, tys, lc)
  | e -> e

let typ_sort_typ = function
  | TCons _ | Fun _ |
      TVar (VNam (Type_sort, _) | VId (Type_sort, _)) -> true
  | _ -> false

let num_sort_typ = function
  | NCst _ | Nadd _ |
      TVar (VNam (Num_sort, _)
                 | VId (Num_sort, _)) -> true
  | _ -> false

let typ_sort_atom = function
  | Eqty (t1, t2, _) -> typ_sort_typ t1 || typ_sort_typ t2
  | Leq _ -> false
  | CFalse _ -> false
  | PredVarU _ -> true
  | PredVarB _ -> true
  | NotEx _ -> true

let num_sort_atom = function
  | Eqty (t1, t2, _) -> num_sort_typ t1 || num_sort_typ t2
  | Leq _ -> true
  | CFalse _ -> false
  | PredVarU _ -> false
  | PredVarB _ -> false
  | NotEx _ -> false

(** {2 Global tables} *)

type sigma =
  (cns_name, var_name list * formula * typ list * cns_name * var_name list)
    Hashtbl.t

let sigma : sigma = Hashtbl.create 128
let all_ex_types = ref []
let new_ex_types = ref []

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

let rec pr_pat comma ppf = function
  | Zero -> fprintf ppf "%s" "!"
  | One _ -> fprintf ppf "%s" "_"
  | PVar (x, _) -> fprintf ppf "%s" x
  | PAnd (pat1, pat2, _) ->
      fprintf ppf "@[<2>%a@ as@ %a@]"
	(pr_pat false) pat1 (pr_more_pat false) pat2
  | PCons (CNam "Tuple", pats, _) ->
      if comma || List.length pats <= 1 then
	fprintf ppf "@[<2>(%a)@]"
	  (pr_sep_list "," ~pr_hd:(pr_pat true)
	      (pr_more_pat true)) pats
      else
	fprintf ppf "@[<2>%a@]"
	  (pr_sep_list "," ~pr_hd:(pr_pat true)
	      (pr_more_pat true)) pats
  | PCons (x, [], _) ->
      fprintf ppf "%s" (cns_str x)
  | PCons (x, [pat], _) ->
      fprintf ppf "@[<2>%s@ %a@]" (cns_str x) pr_one_pat pat
  | PCons (x, pats, _) ->
      fprintf ppf "@[<2>%s@ (%a)@]" (cns_str x)
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
      fprintf ppf "%s" (cns_str x)
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
  | Cons (CNam "Tuple", exps, _) ->
      if comma || List.length exps <= 1 then
	fprintf ppf "@[<2>(%a)@]"
	  (pr_sep_list "," (pr_expr true)) exps
      else
	fprintf ppf "@[<2>%a@]"
	  (pr_sep_list "," (pr_expr true)) exps
  | Cons (x, [], _) ->
      fprintf ppf "%s" (cns_str x)
  | Cons (x, [exp], _) ->
      fprintf ppf "@[<2>%s@ %a@]" (cns_str x) pr_one_expr exp
  | Cons (x, exps, _) ->
      fprintf ppf "@[<2>%s@ (%a)@]" (cns_str x)
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

let pr_exty = ref (fun ppf (i, rty) -> failwith "not implemented")

(* Using "script kappa" because "script chi" is not available. *)
let rec pr_atom ppf = function
  | Eqty (t1, t2, _) ->
    fprintf ppf "@[<2>%a@ =@ %a@]" pr_one_ty t1 pr_one_ty t2
  | Leq (t1, t2, _) ->
    fprintf ppf "@[<2>%a@ ≤@ %a@]" pr_one_ty t1 pr_one_ty t2
  | CFalse _ -> pp_print_string ppf "FALSE"
  | PredVarU (i,ty,lc) -> fprintf ppf "@[<2>ϰ%d(%a)@]" i (pr_ty false) ty
  | PredVarB (i,t1,t2,lc) ->
    fprintf ppf "@[<2>ϰ%d(%a,@ %a)@]" i (pr_ty true) t1 (pr_ty true) t2
  | NotEx (t,lc) ->
    fprintf ppf "@[<2>NotEx(%a)@]" (pr_ty false) t

and pr_formula ppf atoms =
  pr_sep_list " ∧" pr_atom ppf atoms

and pr_ty comma ppf = function
  | TVar v -> fprintf ppf "%s" (var_str v)
  | NCst i -> fprintf ppf "%d" i
  | TCons (CNam c, []) -> fprintf ppf "%s" c
  | TCons (CNam "Tuple", exps) ->
    if comma || List.length exps <= 1 then
      fprintf ppf "@[<2>(%a)@]"
	(pr_sep_list "," (pr_ty true)) exps
    else
      fprintf ppf "@[<2>%a@]"
	(pr_sep_list "," (pr_ty true)) exps
  | TCons (CNam c, [ty]) ->
    fprintf ppf "@[<2>%s@ %a@]" c pr_one_ty ty
  | TCons (CNam c, exps) ->
    fprintf ppf "@[<2>%s@ (%a)@]" c (pr_sep_list "," (pr_ty true)) exps
  | TCons (Extype i, args) -> !pr_exty ppf (i, args)
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
  | ValConstr (Extype _ as name, vs, phi, [arg],
               Extype j, [c_arg], _) ->
    fprintf ppf "@[<2>newcons@ %s@ :@ ∀%a[%a].%a@ ⟶@ Ex%d %s@]"
      (cns_str name)
      (pr_sep_list "," pr_tyvar) vs
      pr_formula phi (pr_ty true) arg j (var_str c_arg)
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
  | Contradiction (sort, what, None, where) ->
    pr_loc_long ppf where;
    Format.fprintf ppf "%!\nContradiction in %s: %s\n%!"
      (sort_str sort) what
  | Contradiction (sort, what, Some (ty1, ty2), where) ->
    pr_loc_long ppf where;
    Format.fprintf ppf
      "%!\nContradiction in %s: %s\ntypes involved:\n%a\n%a\n%!"
      (sort_str sort) what (pr_ty false) ty1 (pr_ty false) ty2
  | NoAnswer (sort, what, None, where) ->
    pr_loc_long ppf where;
    Format.fprintf ppf "%!\nNo answer in %s: %s\n%!"
      (sort_str sort) what
  | NoAnswer (sort, what, Some (ty1, ty2), where) ->
    pr_loc_long ppf where;
    Format.fprintf ppf
      "%!\nNo answer in %s: %s\ntypes involved:\n%a\n%a\n%!"
      (sort_str sort) what (pr_ty false) ty1 (pr_ty false) ty2
  | exn -> raise exn


let pr_to_str pr_f e =
  ignore (Format.flush_str_formatter ());
  pr_f Format.str_formatter e;
  Format.flush_str_formatter ()

(** {2 Unification} *)

let split_sorts cnj =
  let cnj_typ, cnj = List.partition
    (function
    | Eqty (_,t,_) when typ_sort_typ t -> true
    | _ -> false) cnj in
  let cnj_num, cnj = List.partition
    (function
    | Eqty (_,t,_) when num_sort_typ t -> true
    | Leq _ -> true
    | _ -> false) cnj in
  assert (cnj=[]);
  [Type_sort, cnj_typ; Num_sort, cnj_num]

let connected ?(validate=fun _ -> ()) ~directed target (vs, phi) =
  let nodes = List.map
      (function
        | Eqty (TVar _, TVar _, _) as c ->
          let cvs = fvs_atom c in c, cvs, cvs
        | (Eqty (TVar v, t, _) | Eqty (t, TVar v, _)) as c
          when directed && typ_sort_typ t ->
          c, VarSet.singleton v, fvs_typ t
        | c -> let cvs = fvs_atom c in c, cvs, cvs)
      phi in
  let rec loop acc vs nvs rem =
    let more, rem = List.partition
      (fun (c, ivs, ovs) -> List.exists (flip VarSet.mem ivs) nvs) rem in
    let mvs = List.fold_left VarSet.union VarSet.empty
      (List.map thr3 more) in
    let nvs = VarSet.elements (VarSet.diff mvs vs) in
    let acc = List.fold_left
        (fun acc (c,_,_) ->
           let acc' = c::acc in
           try validate acc'; acc'
           with Contradiction _ -> acc)
        acc more in
    if nvs = [] then acc
    else loop acc (VarSet.union mvs vs) nvs rem in
  let ans = loop [] VarSet.empty target nodes in
  (* Format.printf "connected: target=%a@ vs=%a@ phi=%a@ ans=%a@\n%!"
    pr_vars (vars_of_list target) pr_vars (vars_of_list vs) pr_formula phi
    pr_formula ans; * *)
  VarSet.elements (VarSet.inter (fvs_formula ans) (vars_of_list vs)),
  ans

(* If there are no [bvs] parameters, the LHS variable has to be
   existential and not upstream of any RHS variable.

   If [v] is a [bvs] parameter, every universal variable must be
   upstream of some [bv] parameter. (Note that a [bv] parameter that
   is sufficiently downstream is a "savior".)

   [zvs] parameters act like existential variables but are not
   located anywhere in the quantifier -- do not contribute to
   quantifier violation. *)
let quant_viol cmp_v uni_v bvs zvs v t =
  let uv = uni_v v in
  let pvs, npvs = List.partition (fun v->VarSet.mem v bvs)
    (VarSet.elements (fvs_typ t)) in
  let pvs = if VarSet.mem v bvs then v::pvs else pvs in
  let uni_vs =
    List.filter uni_v (if VarSet.mem v bvs then npvs else v::npvs) in
  let res =
  if (* pvs = [] *) not (VarSet.mem v bvs) then uv ||
    not (VarSet.mem v zvs) && List.exists
    (fun v2 -> not (VarSet.mem v2 zvs) && cmp_v v v2 = Upstream) npvs
  else
    not
      (List.for_all
         (fun uv -> List.exists (fun pv -> cmp_v uv pv = Upstream) pvs)
         uni_vs) in
  Format.printf
    "quant_viol: %b;@ v=%s;@ t=%a;@ bvs=%a;@ zvs=%a;@ pvs=%a;@ uni_vs=%a@\n%!"
    res (var_str v) (pr_ty false) t
    pr_vars bvs pr_vars zvs pr_vars (vars_of_list pvs)
    pr_vars (vars_of_list uni_vs);
  (* *)
  res  

let registered_notex_vars = Hashtbl.create 32
let register_notex v = Hashtbl.add registered_notex_vars v ()
let is_old_notex v = Hashtbl.mem registered_notex_vars v

(** Separate type sort and number sort constraints,  *)
let unify ?use_quants ?(sb=[]) cmp_v uni_v cnj =
  let new_notex = ref false in
  let use_quants, bvs, zvs =
    match use_quants with
    | None -> false, VarSet.empty, VarSet.empty
    | Some (bvs, zvs) -> true, bvs, zvs in
  let subst_one_sb v s = List.map
      (fun (w,(t,loc)) ->
         let modif, t' = subst_one v s t in
         if use_quants && modif && quant_viol cmp_v uni_v bvs zvs w t'
         then raise
             (Contradiction (Type_sort, "Quantifier violation",
                             Some (TVar w, t'), loc));
         w, (t', loc)) in
  let cnj_typ, more_cnj = partition_map
      (function
        | Eqty (t1, t2, loc) when typ_sort_typ t1 && typ_sort_typ t2 ->
          Left (t1, t2, loc)
        | Eqty (t1, t2, loc) as a when num_sort_typ t1 && num_sort_typ t2 ->
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
      | t1, t2 when num_sort_typ t1 && num_sort_typ t2 ->
        aux sb (Eqty (t1, t2, loc)::num_cn) cnj
      | t1, t2 when num_sort_typ t1 || num_sort_typ t2 ->
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
        when use_quants && quant_viol cmp_v uni_v bvs zvs v t ->
        raise
          (Contradiction (Type_sort, "Quantifier violation",
                          Some (TVar v, t), loc))
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
        Format.printf "unify: mismatch f=%s g=%s@ t1=%a@ t2=%a@\n%!"
          (cns_str f) (cns_str g) (pr_ty false) t1 (pr_ty false) t2; (* *)
        raise
          (Contradiction (Type_sort, "Type mismatch",
                          Some (t1, t2), loc))
      | t1, t2 ->
        Format.printf "unify: mismatch@ t1=%a@ t2=%a@\n%!"
          (pr_ty false) t1 (pr_ty false) t2; (* *)
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

let combine_sbs ?ignore_so ?use_quants cmp_v uni_v ?(more_phi=[]) sbs =
  let cnj_typ, cnj_num, cnj_so =
    unify ?use_quants cmp_v uni_v
      (more_phi @ concat_map to_formula sbs) in
  assert (ignore_so<>None || cnj_so = []);
  cnj_typ, cnj_num

let subst_solved ?ignore_so ?use_quants cmp_v uni_v sb ~cnj =
  let cnj = List.map
    (fun (v,(t,lc)) -> Eqty (subst_typ sb (TVar v), subst_typ sb t, lc))
    cnj in
  let cnj_typ, cnj_num, cnj_so =
    unify ?use_quants cmp_v uni_v cnj in
  assert (ignore_so<>None || cnj_so = []);
  cnj_typ, cnj_num

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
    (*Format.printf
      "@\npr_exty: i=%d ty=%a@ vs=%a@ pvs=%a@ phi=%a@\n%!"
      i (pr_ty false) ty pr_vars (vars_of_list vs) pr_vars
       (vars_of_list pvs) pr_formula phi; * *)
    let evs = VarSet.elements
        (VarSet.diff (vars_of_list vs) (vars_of_list pvs)) in
    (* TODO: "@[<2>∃%d:%a[%a].%a@]" better? *)
    fprintf ppf "∃%d:%a[%a].%a" i
      (pr_sep_list "," pr_tyvar) evs pr_formula phi (pr_ty false) ty


let parser_more_items = ref []
let parser_unary_typs = Hashtbl.create 15
let parser_unary_vals = Hashtbl.create 31
let parser_last_typ = ref 0
let parser_last_num = ref 0

let reset_state () =
  extype_id := 0; new_ex_types := []; all_ex_types := [];
  predvar_id := 0; Hashtbl.clear sigma;
  parser_more_items := [];
  Hashtbl.clear parser_unary_typs;
  Hashtbl.clear parser_unary_vals;
  Hashtbl.clear registered_notex_vars;
  parser_last_typ := 0;
  parser_last_num := 0
