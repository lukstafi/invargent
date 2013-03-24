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

and clause = pat * expr

let expr_loc = function
  | Var (_, loc)
  | Num (_, loc)
  | Cons (_, _, loc)
  | App (_, _, loc)
  | Lam (_, loc)
  | ExLam (_, _, loc)
  | Letrec (_, _, _, loc)
  | Letin (_, _, _, loc) -> loc

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
  | VId (_,i) -> string_of_int i
let cns_str = function
  | CNam c -> c
  | Extype i -> "Ex"^string_of_int i

type typ =
| TVar of var_name
| TCons of cns_name * typ list
| Fun of typ * typ
| NCst of int
| Nadd of typ list

module VarSet =
    Set.Make (struct type t = var_name let compare = Pervasives.compare end)
let vars_of_list l =
  List.fold_right VarSet.add l VarSet.empty

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

let fvs_typ =
  typ_fold {(typ_make_fold VarSet.union VarSet.empty)
            with fold_tvar = fun v -> VarSet.singleton v}

let subst_typ sb =
  typ_map {typ_id_map with map_tvar =
      fun v -> try List.assoc v sb with Not_found -> TVar v}

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


type formula = atom list

let fvs_formula phi =
  List.fold_left VarSet.union VarSet.empty (List.map fvs_atom phi)

type typ_scheme = var_name list * formula * typ

let extype_id = ref 0
let predvar_id = ref 0
let reset_processing () =
  extype_id := 0; predvar_id := 0

type struct_item =
| TypConstr of cns_name * sort list * loc
| ValConstr of cns_name * var_name list * formula * typ list * typ * loc
| PrimVal of string * typ_scheme * loc
| LetRecVal of string * expr * loc
| LetVal of string * expr * loc

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
| ValConstr (_, vs, phi, args, res, _) ->
  vs, phi, enc_funtype res args
| PrimVal (_, t, _) -> t
| LetRecVal (name, _, _) | LetVal (name, _, _) -> List.assoc name env

(** {2 Sort inference} *)
let newtype_env = Hashtbl.create 15

let infer_sorts_item item =
  let sorts = Hashtbl.create 15 in
  let walk_var = function
    | VId (_,id) as tv -> tv
    | VNam (s,v) as tv ->
      try VNam (Hashtbl.find sorts v, v) with Not_found -> tv in
  let rec walk_typ cur_loc s = function
    | TVar (VNam (_,v)) ->
      (try let s' = Hashtbl.find sorts v in
           if s <> Undefined_sort && s' <> Undefined_sort && s <> s'
           then raise
             (Report_toplevel ("Sort mismatch for type variable "^
                                  v^": sorts "^sort_str s^" and " ^
                                  sort_str s', Some cur_loc))
           else if s <> Undefined_sort then TVar (VNam (s, v))
           else TVar (VNam (s', v))
       with Not_found ->
         if s <> Undefined_sort then Hashtbl.add sorts v s;
         TVar (VNam (s,v))) 
    | TVar (VId _) -> assert false
    | TCons (CNam "Tuple" as n, args) ->
      TCons (n, List.map (walk_typ cur_loc Type_sort) args)
    | TCons (CNam _ as n, args) ->
      (try let argsorts = Hashtbl.find newtype_env n in
           TCons (n, List.map2 (walk_typ cur_loc) argsorts args)
       with
       | Not_found -> raise
         (Report_toplevel ("Undefined type constructor "^cns_str n,
                           Some cur_loc))
       | Invalid_argument _ -> raise
         (Report_toplevel ("Arity mismatch for type constructor "^
                              cns_str n, Some cur_loc)))
    | TCons (Extype _ as n, args) ->
      (try let argsorts = Hashtbl.find newtype_env n in
           TCons (n, List.map2 (walk_typ cur_loc) argsorts args)
       with
       | Not_found ->
         TCons (n, List.map (walk_typ cur_loc Undefined_sort) args)
       | Invalid_argument _ -> assert false)
    | Fun (t1, t2) ->
      if s <> Type_sort then raise
        (Report_toplevel ("Expected sort "^sort_str s^
                             " but found sort type", Some cur_loc));
        Fun (walk_typ cur_loc Type_sort t1, walk_typ cur_loc Type_sort t2)
    | NCst _ as ty ->
      if s <> Undefined_sort && s <> Num_sort then raise
        (Report_toplevel ("Expected sort "^sort_str s^
                             " but found sort num", Some cur_loc));
      ty
    | Nadd args ->
      Nadd (List.map (walk_typ cur_loc Num_sort) args)
  and walk_atom = function
    | Eqty (t1, t2, loc) ->
      Eqty (walk_typ loc Undefined_sort t1,
            walk_typ loc Undefined_sort t2, loc)
    | Leq (t1, t2, loc) ->
      Leq (walk_typ loc Num_sort t1, walk_typ loc Num_sort t2, loc)
    | CFalse _ as a -> a
    | PredVarU (id,ty) -> PredVarU (id, walk_typ dummy_loc Type_sort ty)
    | PredVarB (id,t1, t2) ->
      PredVarB (id, walk_typ dummy_loc Type_sort t1,
                walk_typ dummy_loc Type_sort t2) in
  match item with
  | TypConstr (CNam _ as name, sorts, _) as item ->
    Hashtbl.add newtype_env name sorts; [item]
  | TypConstr (Extype _, _, _) ->
    []                                  (* will be reintroduced *)
  | ValConstr (CNam _ as name, vs, phi, args, res, loc) ->
    let res = walk_typ loc Type_sort res in
    let args = List.map (walk_typ loc Type_sort) args in
    let phi = List.map walk_atom phi in
    let vs = List.map walk_var vs in
    [ValConstr (name, vs, phi, args, res, loc)]
  | ValConstr (Extype _ as name, vs, phi, args, res, loc) ->
    let args = List.map (walk_typ loc Type_sort) args in
    let phi = List.map walk_atom phi in
    let vs = List.map walk_var vs in
    let res = walk_typ loc Type_sort res in
    let sorts =
      match res with
      | TCons (tn, targs) when tn = name ->
        List.map (function TVar v -> var_sort v | _ -> assert false) targs
      | _ -> assert false in
    Hashtbl.add newtype_env name sorts;
    [TypConstr (name, sorts, loc); ValConstr (name, vs, phi, args, res, loc)]
  | PrimVal (n, (vs, phi, ty), loc) ->
    let ty = walk_typ loc Type_sort ty in
    let phi = List.map walk_atom phi in
    let vs = List.map walk_var vs in
    [PrimVal (n, (vs, phi, ty), loc)]
  | (LetRecVal _ | LetVal _) as item -> [item]

let infer_sorts prog =
  Aux.concat_map infer_sorts_item prog

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

let rec pr_sep_list sep pr_hd pr_tl ppf = function
  | [] -> ()
  | [hd] -> pr_hd ppf hd
  | hd::tl ->
      fprintf ppf "%a%s@ %a" pr_hd hd sep (pr_more_sep_list sep pr_tl) tl

and pr_more_sep_list sep pr_a ppf = function
  | [] -> ()
  | [hd] -> pr_a ppf hd
  | hd::tl ->
      fprintf ppf "%a%s@ %a" pr_a hd sep (pr_more_sep_list sep pr_a) tl

let rec pr_pre_sep_list sep pr_a ppf = function
  | [] -> ()
  | [hd] -> pr_a ppf hd
  | hd::tl ->
      fprintf ppf "%a@ %s%a" pr_a hd sep (pr_pre_sep_list sep pr_a) tl

let rec pr_line_list sep pr_hd pr_tl ppf = function
  | [] -> ()
  | [hd] -> pr_hd ppf hd
  | hd::tl ->
      fprintf ppf "%a@\n%s%a" pr_hd hd sep (pr_more_line_list sep pr_tl) tl

and pr_more_line_list sep pr_a ppf = function
  | [] -> ()
  | [hd] -> pr_a ppf hd
  | hd::tl ->
      fprintf ppf "%a@\n%s%a" pr_a hd sep (pr_more_line_list sep pr_a) tl

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
	  (pr_sep_list "," (pr_pat true)
	      (pr_more_pat true)) pats
      else
	fprintf ppf "@[<2>%a@]"
	  (pr_sep_list "," (pr_pat true)
	      (pr_more_pat true)) pats
  | PCons (x, [], _) ->
      fprintf ppf "%s" x
  | PCons (x, [pat], _) ->
      fprintf ppf "@[<2>%s@ %a@]" x pr_one_pat pat
  | PCons (x, pats, _) ->
      fprintf ppf "@[<2>%s@ (%a)@]" x
	(pr_sep_list "," (pr_pat true) (pr_more_pat true)) pats

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

let rec pr_expr comma ppf = function
  | Var (s, _) -> fprintf ppf "%s" s
  | Num (i, _) -> fprintf ppf "%d" i
  | Cons ("Tuple", exps, _) ->
      if comma then
	fprintf ppf "@[<2>(%a)@]"
	  (pr_more_sep_list "," (pr_expr true)) exps
      else
	fprintf ppf "@[<2>%a@]"
	  (pr_more_sep_list "," (pr_expr true)) exps
  | Cons (x, [], _) ->
      fprintf ppf "%s" x
  | Cons (x, [exp], _) ->
      fprintf ppf "@[<2>%s@ %a@]" x pr_one_expr exp
  | Cons (x, exps, _) ->
      fprintf ppf "@[<2>%s@ (%a)@]" x
	(pr_more_sep_list "," (pr_expr true)) exps
  | Lam ([_], _) as exp ->
      let pats, expr = collect_lambdas exp in
      fprintf ppf "@[<2>fun@ %a@ ->@ %a@]"
	(pr_more_sep_list "" pr_one_pat) pats
	(pr_expr false) expr
  | Lam (cs, _) ->
      fprintf ppf "@[<2>fun x ->@ match x with@ %a@]"
	(pr_pre_sep_list "| " pr_clause) cs
  | ExLam (_, cs, _) ->
      fprintf ppf "@[<0>function@ %a@]"
	(pr_pre_sep_list "| " pr_clause) cs
  | App (Lam ([(v,body)], _), def, _) ->
      fprintf ppf "@[<0>let@ @[<4>%a@] =@ @[<2>%a@]@ in@ @[<0>%a@]@]"
	(pr_more_pat false) v (pr_expr false) def (pr_expr false) body
  | App _ as exp ->
      let fargs = collect_apps exp in
      fprintf ppf "@[<2>%a@]"
	(pr_more_sep_list "" pr_one_expr) fargs
  | Letrec (x, exp, range, _) ->
      fprintf ppf "@[<0>let rec %s =@ @[<2>%a@] in@ @[<0>%a@]@]"
	x (pr_expr false) exp (pr_expr false) range
  | Letin (pat, exp, range, _) ->
      fprintf ppf "@[<0>let %a =@ @[<2>%a@] in@ @[<0>%a@]@]"
	(pr_pat false) pat (pr_expr false) exp (pr_expr false) range

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
  pr_more_sep_list "∧" pr_atom ppf atoms

and pr_ty comma ppf = function
  | TVar v -> fprintf ppf "%s" (var_str v)
  | NCst i -> fprintf ppf "%d" i
  | TCons (x, []) -> fprintf ppf "%s" (cns_str x)
  | TCons (CNam "Tuple", exps) ->
    if comma then
      fprintf ppf "@[<2>(%a)@]"
	(pr_more_sep_list "," (pr_ty true)) exps
    else
      fprintf ppf "@[<2>%a@]"
	(pr_more_sep_list "," (pr_ty true)) exps
  | TCons (x, [ty]) ->
    fprintf ppf "@[<2>%s@ %a@]" (cns_str x) pr_one_ty ty
  | TCons (x, exps) ->
    fprintf ppf "@[<2>%s@ (%a)@]" (cns_str x)
      (pr_more_sep_list "," (pr_ty true)) exps
  | Nadd []  -> fprintf ppf "0"
  | Nadd [ty] -> pr_ty comma ppf ty
  | Nadd (tys) ->
    fprintf ppf "@[<2>%a@]"
      (pr_more_sep_list " +" (pr_ty true)) tys
  | Fun _ as ty ->
    let tys = collect_argtys ty in
    fprintf ppf "@[<2>%a@]"
      (pr_more_sep_list " →" pr_fun_ty) tys
    
    
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
    fprintf ppf "@[<2>∀%a.@ %a@]"
      (pr_more_sep_list " *" pr_tyvar) vs (pr_ty false) ty
  | vs, phi, ty ->
    fprintf ppf "@[<2>∀%a[%a].@ %a@]"
      (pr_more_sep_list " *" pr_tyvar) vs
      pr_formula phi (pr_ty false) ty
  
let pr_struct_item ppf = function
  | TypConstr (name, [], _) ->
    fprintf ppf "@[<2>newtype@ %s@]" (cns_str name)
  | TypConstr (name, sorts, _) ->
    fprintf ppf "@[<2>newtype@ %s@ :@ %a@]" (cns_str name)
      (pr_more_sep_list " *" pr_sort) sorts
  | ValConstr (name, [], [], [], res, _) ->
    fprintf ppf "@[<2>newcons@ %s@ :@ %a@]" (cns_str name)
      (pr_ty false) res
  | ValConstr (name, [], [], args, res, _) ->
    fprintf ppf "@[<2>newcons@ %s@ :@ %a@ ⟶@ %a@]" (cns_str name)
      (pr_more_sep_list " *" (pr_ty true)) args (pr_ty false) res
  | ValConstr (name, vs, [], [], res, _) ->
    fprintf ppf "@[<2>newcons@ %s@ :@ ∀%a.@ %a@]" (cns_str name)
      (pr_more_sep_list "," pr_tyvar) vs
      (pr_ty false) res
  | ValConstr (name, vs, phi, [], res, _) ->
    fprintf ppf "@[<2>newcons@ %s@ :@ ∀%a[%a].@ %a@]" (cns_str name)
      (pr_more_sep_list "," pr_tyvar) vs
      pr_formula phi (pr_ty false) res
  | ValConstr (name, vs, [], args, res, _) ->
    fprintf ppf "@[<2>newcons@ %s@ :@ ∀%a.%a@ ⟶@ %a@]" (cns_str name)
      (pr_more_sep_list "," pr_tyvar) vs
      (pr_more_sep_list " *" (pr_ty true)) args (pr_ty false) res
  | ValConstr (name, vs, phi, args, res, _) ->
    fprintf ppf "@[<2>newcons@ %s@ :@ ∀%a[%a].%a@ ⟶@ %a@]" (cns_str name)
      (pr_more_sep_list "," pr_tyvar) vs
      pr_formula phi
      (pr_more_sep_list " *" (pr_ty true)) args (pr_ty false) res
  | PrimVal (name, tysch, _) ->
    fprintf ppf "@[<2>external@ %s@ :@ %a@]" name pr_typscheme tysch
  | LetRecVal (name, expr, _) ->
    fprintf ppf "@[<2>let rec@ %s@ =@ %a@]" name (pr_expr false) expr
  | LetVal (name, expr, _) ->
    fprintf ppf "@[<2>let@ %s@ =@ %a@]" name (pr_expr false) expr

let pr_program ppf p =
  pr_more_line_list "\n" pr_struct_item ppf p
