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
type var_name = sort * string

type typ =
| TVar of var_name
| TCons of string * typ list
| Fun of typ * typ
| NCst of int
| Nadd of typ list
| TExCons of int

type atom =
| Eqty of typ * typ * loc
| Leq of typ * typ * loc
| CFalse of loc

type formula = atom list

type typ_scheme = var_name list * formula * typ

let extype_id = ref 0
let extype_env : (int, typ_scheme) Hashtbl.t = Hashtbl.create 511
let newtype_env : (string, sort list) Hashtbl.t  = Hashtbl.create 31
let newcons_env :
    (string, var_name list * formula * typ list * typ) Hashtbl.t  =
  Hashtbl.create 31

type struct_item =
| TypConstr of string * sort list * loc
| ValConstr of string * var_name list * formula * typ list * typ * loc
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
let unary_type_constr n =
  try match Hashtbl.find newtype_env n with [_] -> true | _ -> false
  with Not_found -> false
let unary_val_constr n =
  try match Hashtbl.find newcons_env n with
  | _, _, [_], _ -> true | _ -> false
  with Not_found -> false

let infer_sorts item =
  let sorts = Hashtbl.create 15 in
  let walk_var (s,v as tv) =
    try Hashtbl.find sorts v, v with Not_found -> tv in
  let rec walk_typ cur_loc s = function
    | TVar (_,v) ->
      (try let s' = Hashtbl.find sorts v in
           if s' <> Undefined_sort && s <> s' then raise
             (Report_toplevel ("Sort mismatch for type variable "^v^
                                  ": sorts "^sort_str s^" and " ^
                                  sort_str s', Some cur_loc))
           else TVar (s,v)
       with Not_found ->
         if s <> Undefined_sort then Hashtbl.add sorts v s;
         TVar (s,v)) 
    | TCons ("Tuple" as n, args) ->
      TCons (n, List.map (walk_typ cur_loc Type_sort) args)
    | TCons (n, args) ->
      (try let argsorts = Hashtbl.find newtype_env n in
           TCons (n, List.map2 (walk_typ cur_loc) argsorts args)
       with
       | Not_found -> raise
         (Report_toplevel ("Undefined type constructor "^n,
                           Some cur_loc))
       | Invalid_argument _ -> raise
         (Report_toplevel ("Arity mismatch for type constructor "^n,
                           Some cur_loc)))
    | Fun (t1, t2) ->
      if s <> Type_sort then raise
        (Report_toplevel ("Expected sort "^sort_str s^
                             " but found sort type", Some cur_loc));
        Fun (walk_typ cur_loc Type_sort t1, walk_typ cur_loc Type_sort t2)
    | NCst _ as ty ->
      if s <> Type_sort then raise
        (Report_toplevel ("Expected sort "^sort_str s^
                             " but found sort type", Some cur_loc));
      ty
    | Nadd args ->
      Nadd (List.map (walk_typ cur_loc Num_sort) args)
    | TExCons id as item ->
      (try let vs, phi, ty = Hashtbl.find extype_env id in
           let ty = walk_typ cur_loc s ty in
           let phi = List.map walk_atom phi in
           let vs = List.map walk_var vs in
           Hashtbl.replace extype_env id (vs, phi, ty);
           item           
       with Not_found -> raise
         (Report_toplevel ("Internal error with existential type",
                           Some cur_loc)))
  and walk_atom = function
    | Eqty (t1, t2, loc) ->
      Eqty (walk_typ loc Undefined_sort t1,
            walk_typ loc Undefined_sort t2, loc)
    | Leq (t1, t2, loc) ->
      Leq (walk_typ loc Num_sort t1, walk_typ loc Num_sort t2, loc)
    | CFalse _ as a -> a in
  match item with
  | TypConstr (name, sorts, _) as item ->
    Hashtbl.add newtype_env name sorts; item
  | ValConstr (name, vs, phi, args, res, loc) ->
    let res = walk_typ loc Type_sort res in
    let args = List.map (walk_typ loc Type_sort) args in
    let phi = List.map walk_atom phi in
    let vs = List.map walk_var vs in
    Hashtbl.replace newcons_env name (vs, phi, args, res);
    ValConstr (name, vs, phi, args, res, loc)
  | PrimVal (n, (vs, phi, ty), loc) ->
    let ty = walk_typ loc Type_sort ty in
    let phi = List.map walk_atom phi in
    let vs = List.map walk_var vs in
    PrimVal (n, (vs, phi, ty), loc)
  | (LetRecVal _ | LetVal _) as item -> item

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

let pr_tyvar ppf (_,v) = pp_print_string ppf v

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

and pr_formula ppf atoms =
  pr_more_sep_list "∧" pr_atom ppf atoms

and pr_ty comma ppf = function
  | TVar (_,v) -> fprintf ppf "%s" v
  | NCst i -> fprintf ppf "%d" i
  | TCons (x, []) -> fprintf ppf "%s" x
  | TCons ("Tuple", exps) ->
    if comma then
      fprintf ppf "@[<2>(%a)@]"
	(pr_more_sep_list "," (pr_ty true)) exps
    else
      fprintf ppf "@[<2>%a@]"
	(pr_more_sep_list "," (pr_ty true)) exps
  | TCons (x, [ty]) ->
    fprintf ppf "@[<2>%s@ %a@]" x pr_one_ty ty
  | TCons (x, exps) ->
    fprintf ppf "@[<2>%s@ (%a)@]" x
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
  | TExCons k ->
    let vs, phi, ty = Hashtbl.find extype_env k in
    fprintf ppf "@[<2>∃%a[%a].@ %a@]"
      (pr_more_sep_list " *" pr_tyvar) vs
      pr_formula phi (pr_ty true) ty
    
    
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
    fprintf ppf "@[<2>newtype@ %s@]" name
  | TypConstr (name, sorts, _) ->
    fprintf ppf "@[<2>newtype@ %s@ :@ %a@]" name
      (pr_more_sep_list " *" pr_sort) sorts
  | ValConstr (name, [], [], [], res, _) ->
    fprintf ppf "@[<2>newcons@ %s@ :@ %a@]" name
      (pr_ty false) res
  | ValConstr (name, [], [], args, res, _) ->
    fprintf ppf "@[<2>newcons@ %s@ :@ %a@ ⟶@ %a@]" name
      (pr_more_sep_list " *" (pr_ty true)) args (pr_ty false) res
  | ValConstr (name, vs, [], [], res, _) ->
    fprintf ppf "@[<2>newcons@ %s@ :@ ∀%a.@ %a@]" name
      (pr_more_sep_list "," pr_tyvar) vs
      (pr_ty false) res
  | ValConstr (name, vs, phi, [], res, _) ->
    fprintf ppf "@[<2>newcons@ %s@ :@ ∀%a[%a].@ %a@]" name
      (pr_more_sep_list "," pr_tyvar) vs
      pr_formula phi (pr_ty false) res
  | ValConstr (name, vs, [], args, res, _) ->
    fprintf ppf "@[<2>newcons@ %s@ :@ ∀%a.%a@ ⟶@ %a@]" name
      (pr_more_sep_list "," pr_tyvar) vs
      (pr_more_sep_list " *" (pr_ty true)) args (pr_ty false) res
  | ValConstr (name, vs, phi, args, res, _) ->
    fprintf ppf "@[<2>newcons@ %s@ :@ ∀%a[%a].%a@ ⟶@ %a@]" name
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
