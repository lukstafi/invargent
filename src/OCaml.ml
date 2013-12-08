(** Reading and generating OCaml code/interface for InvarGenT.

    Released under the GNU General Public Licence (version 2 or
    higher), NO WARRANTY of correctness etc. (C) Lukasz Stafiniak 2013
    @author Lukasz Stafiniak lukstafi (AT) gmail.com
    @since Mar 2013
*)

open Terms
open Format
open Aux

let pr_ftyvar ppf v = fprintf ppf "'%s" (var_str v)
let pr_tycns ppf c =
  fprintf ppf "%s" (String.uncapitalize (cns_str c))

let altsyn = ref false

let rec pr_ty ppf = function
  | TVar v ->
    if !altsyn then pr_ftyvar ppf v
    else pr_tyvar ppf v
  | NCst i -> fprintf ppf "%d" i
  | TCons (c, []) -> pr_tycns ppf c
  | TCons (CNam "Tuple", exps) ->
    fprintf ppf "@[<2>(%a)@]" (pr_some_tys "* ") exps
  | TCons (c, [ty]) when typ_sort ty = Type_sort ->
    fprintf ppf "@[<2>%a@ %a@]" pr_one_ty ty pr_tycns c
  | TCons (c, [ty]) ->
    fprintf ppf "@[<2>(* %a *)@ %a@]" Terms.pr_ty ty pr_tycns c
  | TCons (c, exps)
    when List.exists (fun t->typ_sort t=Type_sort) exps ->
    fprintf ppf "@[<2>(%a)@ %a@]" (pr_some_tys ",") exps pr_tycns c
  | TCons (c, exps) ->
    fprintf ppf "@[<2>(* %a *)@ %a@]"
      (pr_sep_list "," Terms.pr_ty) exps pr_tycns c
  | Nadd _ -> assert false
  | Fun _ as ty ->
    let tys = collect_argtys ty in
    fprintf ppf "@[<2>%a@]"
      (pr_sep_list " ->" pr_fun_ty) tys    

and pr_some_tys sep ppf tys =
  let pr_one ty =
    if typ_sort ty = Type_sort then pr_ty ppf ty
    else fprintf ppf "(* %a *)" Terms.pr_ty ty in
  let rec aux = function
  | [] -> ()
  | [ty] -> pr_one ty
  | ty::tys ->
    if typ_sort ty = Type_sort
    then fprintf ppf "%a%s@ " pr_ty ty
        (if List.exists (fun t->typ_sort t = Type_sort) tys
         then sep else "")
    else fprintf ppf "(* %a%s*)@ " Terms.pr_ty ty sep;
    aux tys in
  aux tys
    
and pr_one_ty ppf ty = match ty with
  | TVar _ | NCst _ | Nadd [] | Nadd [_]
  | TCons (_, []) -> pr_ty ppf ty
  | _ -> fprintf ppf "(%a)" pr_ty ty

and pr_fun_ty ppf ty = match ty with
  | Fun _ ->
    fprintf ppf "(%a)" pr_ty ty
  | _ -> pr_ty ppf ty

let pr_typscheme ppf (vs, phi, ty) =
  let haspms = List.exists (fun v->var_sort v = Type_sort) vs in
  if phi=[] && vs=[] then pr_ty ppf ty
  else (
    if haspms then fprintf ppf "@[<0>type "
    else if vs<>[] then fprintf ppf "(*@[<0>type "
    else fprintf ppf "(*@[<0>";
    List.iter
      (fun v->
         if var_sort v=Type_sort || not haspms
         then fprintf ppf "%s " (var_str v)
         else fprintf ppf "(*%s*) " (var_str v))
      vs;
    if phi<>[]
    then
      if haspms then fprintf ppf "(*%a*). " pr_formula phi
      else fprintf ppf "[%a].*) " pr_formula phi
    else
      if haspms then fprintf ppf ". "
      else fprintf ppf ".*) ";
    fprintf ppf "%a@]" pr_ty ty)

let pr_typsig ppf (vs, phi, ty) =
  altsyn := true;
  fprintf ppf "@[<0>";
  if phi<>[] then fprintf ppf "(*%a*)@ " pr_formula phi;
  fprintf ppf "%a@]" pr_ty ty;
  altsyn := false

let pr_expr ppf =
  pr_expr (fun ppf tsch -> fprintf ppf ":@ %a@ " pr_typscheme tsch) ppf

let pr_constr c_n ppf = function
  | (name, [], [], [], c_args) ->
    let res = TCons (c_n, c_args) in
    fprintf ppf "@[<2>| %s@ :@ %a@]" (cns_str name)
      pr_ty res
  | (name, [], [], args, c_args) ->
    let res = TCons (c_n, c_args) in
    fprintf ppf "@[<2>| %s@ :@ %a@ ->@ %a@]" (cns_str name)
      (pr_sep_list " *" pr_ty) args pr_ty res
  | (name, vs, [], [], c_args) ->
    let res = TCons (c_n, c_args) in
    fprintf ppf "@[<2>| %s@ :@ (*∀%a.*)@ %a@]" (cns_str name)
      (pr_sep_list "," pr_tyvar) vs
      pr_ty res
  | (name, vs, phi, [], c_args) ->
    let res = TCons (c_n, c_args) in
    fprintf ppf "@[<2>| %s@ :@ (*∀%a[%a].*)@ %a@]" (cns_str name)
      (pr_sep_list "," pr_tyvar) vs
      pr_formula phi pr_ty res
  | (name, vs, [], args, c_args) ->
    let res = TCons (c_n, c_args) in
    fprintf ppf "@[<2>| %s@ :@ (*∀%a.*)%a@ ->@ %a@]" (cns_str name)
      (pr_sep_list "," pr_tyvar) vs
      (pr_sep_list " *" pr_ty) args pr_ty res
  | (name, vs, phi, args, c_args) ->
    let res = TCons (c_n, c_args) in
    fprintf ppf "@[<2>| %s@ :@ (*∀%a[%a].*)%a@ ->@ %a@]" (cns_str name)
      (pr_sep_list "," pr_tyvar) vs
      pr_formula phi
      (pr_sep_list " *" pr_ty) args pr_ty res

let pr_test_line ppf e =
  fprintf ppf "assert@ (%a);" pr_expr e

let pr_ty_wildcards ppf sorts =
  match List.filter ((=) Type_sort) sorts with
  | [] -> ()
  | [s] -> fprintf ppf "_ "
  | sorts ->
    fprintf ppf "(%a) "
      (pr_sep_list "," (fun ppf _ -> fprintf ppf "_")) sorts

module CNames =
    Set.Make (struct type t = cns_name let compare = Pervasives.compare end)
let cnames_of_list l =
  List.fold_right CNames.add l CNames.empty
let add_cnames l vs =
  List.fold_right CNames.add l vs

let init_types = cnames_of_list [tuple; CNam "Num"]

let cns_typ =
  typ_fold {(typ_make_fold CNames.union CNames.empty)
            with fold_tcons =
                   (fun n cns -> List.fold_left
                       CNames.union (CNames.singleton (CNam n)) cns)}

let rec pr_struct_items constrs ppf defined defining prog =
  (*[*)
  if prog<>[] then
    Format.printf "OCaml-pr_struct_items:@ item=%a@ defining=%s@\n%!"
      pr_sig_item (List.hd prog)
      (String.concat "," (List.map cns_str (CNames.elements defining)));
  (*]*)
  match prog with
  | ITypConstr (c_n, sorts, _)::prog ->
    assert (CNames.is_empty defining || CNames.mem c_n defining);
    let cns = try List.assoc c_n constrs with Not_found -> [] in
    altsyn := true;
    fprintf ppf "@[<2>%s %a%a%s@\n%a@]@\n"
      (if CNames.is_empty defining then "type" else "and")
      pr_ty_wildcards sorts pr_tycns c_n
      (if cns=[] then "" else " =")
      (pr_line_list "" (pr_constr c_n)) cns;
    altsyn := false;
    let more_defs = List.fold_left
        (fun cns ty -> CNames.union cns (cns_typ ty)) CNames.empty
        (concat_map
           (fun (name, vs, phi, args, c_args) ->
              let res = TCons (c_n, c_args) in res::args) cns) in
    let defining =
      CNames.union (CNames.diff more_defs defined) defining in
    let defining = CNames.diff (CNames.remove c_n defining) defined in
    (*[*)
    Format.printf "OCaml-pr_struct_items:@ more_defs=%s@ defining'=%s@\n%!"
      (String.concat "," (List.map cns_str (CNames.elements more_defs)))
      (String.concat "," (List.map cns_str (CNames.elements defining)));
    (*]*)
    let mutual, prog = List.partition
        (function
          | ITypConstr (c_n, _, _) when CNames.mem c_n defining -> true
          | _ -> false)
        prog in
    pr_struct_items constrs ppf (CNames.add c_n defined) defining
      (mutual @ prog)
  | IPrimVal (name, tysch, _)::prog ->
    fprintf ppf "@[<2>external@ %s@ :@ %a = \"%s\"@]@\n"
      name pr_typsig tysch name;
    assert (CNames.is_empty defining);
    pr_struct_items constrs ppf defined CNames.empty prog
  | ILetRecVal (name, expr, tysch, [], _)::prog ->
    fprintf ppf "@[<2>let rec@ %s :@ %a =@ %a@]@\n"
      name pr_typscheme tysch pr_expr expr;
    assert (CNames.is_empty defining);
    pr_struct_items constrs ppf defined CNames.empty prog
  | ILetVal (p, e, tysch, _, [], _)::prog ->
    fprintf ppf "@[<2>let@ %a :@ %a =@ %a@]@\n"
      pr_pat p pr_typscheme tysch pr_expr e;
    assert (CNames.is_empty defining);
    pr_struct_items constrs ppf defined CNames.empty prog
  | ILetRecVal (name, expr, tysch, tests, _)::prog ->
    fprintf ppf "@[<2>let rec@ %s :@ %a =@ %a@]@\n@[<2>let () =@ %a@ ()@]@\n"
      name pr_typscheme tysch pr_expr expr
      (pr_line_list "" pr_test_line) tests;
    assert (CNames.is_empty defining);
    pr_struct_items constrs ppf defined CNames.empty prog
  | ILetVal (p, e, tysch, _, tests, _)::prog ->
    fprintf ppf "@[<2>let@ %a :@ %a =@ %a@]@\n[<2>let () =@ %a@ ()@]@\n"
      pr_pat p pr_typscheme tysch pr_expr e
      (pr_line_list "" pr_test_line) tests;
    assert (CNames.is_empty defining);
    pr_struct_items constrs ppf defined CNames.empty prog
  | IValConstr _::_ -> assert false
  | [] -> ()

let pr_ml ppf prog =
  let constrs, prog = partition_map
      (function
        | IValConstr (name, vs, phi, args, c_n, c_args, _) ->
          Left (c_n, (name, vs, phi, args, c_args))
        | i -> Right i)
      prog in
  let constrs = collect constrs in
  (*[* Format.printf "pr_struct: cns key,count=@\n%a@\n%!"
    (pr_sep_list "|" (fun ppf (n,cs) -> fprintf ppf "%s(#=%d) "
                         (cns_str n) (List.length cs))) constrs; *]*)
  pr_struct_items constrs ppf init_types CNames.empty prog

let pr_mli ppf prog = failwith "not implemented yet"
