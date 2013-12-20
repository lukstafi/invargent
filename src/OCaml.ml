(** Reading and generating OCaml code/interface for InvarGenT.

    Released under the GNU General Public Licence (version 2 or
    higher), NO WARRANTY of correctness etc. (C) Lukasz Stafiniak 2013
    @author Lukasz Stafiniak lukstafi (AT) gmail.com
    @since Mar 2013
*)

let num_is = ref "int"
let num_is_mod = ref false

open Terms
open Format
open Aux

let altsyn = ref false

(* A neat hack: the [VId] variables should only be those existential
   variables that have not been, and should not be, generalized. *)
let pr_tyvar ppf v =
  match v with
  | VNam _ ->
    if !altsyn then fprintf ppf "'%s" (var_str v)
    else fprintf ppf "%s" (var_str v)
  | VId _ ->
    assert (not !altsyn);
    fprintf ppf "_"

let pr_tycns ppf c =
  fprintf ppf "%s" (String.uncapitalize (cns_str c))

let rec pr_ty ppf = function
  | TVar v -> pr_tyvar ppf v
  | NCst i -> fprintf ppf "%d" i
  | TCons (c, []) -> pr_tycns ppf c
  | TCons (CNam "Tuple", exps) ->
    fprintf ppf "@[<2>(%a)@]" (pr_some_tys " *") exps
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
    fprintf ppf "@[<2>(%a)@]"
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

let pr_typscheme ppf ((vs, phi, ty), nested_free_vars) =
  assert (not (!altsyn && nested_free_vars));
  let haspms = List.exists (fun v->var_sort v = Type_sort) vs in
  if (phi=[] && vs=[]) then pr_ty ppf ty
  else (
    if haspms && not !altsyn then fprintf ppf "@[<0>type "
    else if vs<>[] && not !altsyn then fprintf ppf "(*@[<0>type "
    else if haspms then fprintf ppf "@[<0>"
    else fprintf ppf "(*@[<0>";
    List.iter
      (fun v->
         if var_sort v=Type_sort || not haspms
         then fprintf ppf "%a " pr_tyvar v
         else fprintf ppf "(*%a*) " pr_tyvar v)
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
  fprintf ppf "@[<0>";
  if phi<>[] then fprintf ppf "(*%a*)@ " pr_formula phi;
  fprintf ppf "%a@]" pr_ty ty

let rec single_assert_false (_, e) =
  match e with
    | AssertFalse _ -> true
    | Lam (_, [cl], loc) -> single_assert_false cl
    | _ -> false

let postprocess elim_extypes e =
  let rec aux = function
    | (Var _ | Num _ | String _) as e -> e
    | Cons (k, args, loc) ->
      Cons (k, List.map aux args, loc)
    | App (e1, e2, loc) ->
      App (aux e1, aux e2, loc)
    | Lam (ann, cls, loc) ->
      let cls = List.filter (not % single_assert_false) cls in
      Lam (ann, List.map (fun (p,e)->p, aux e) cls, loc)
    | AssertFalse _ -> assert false
    | (AssertLeq _ | AssertEqty _) as e -> e
    | Letrec (docu, ann, x, e1, e2, loc) ->
      Letrec (docu, ann, x, aux e1, aux e2, loc)
    | Letin (docu, p, e1, e2, loc) ->
      (try match List.assq p elim_extypes with
         | None -> Letin (docu, p, aux e1, aux e2, loc)
         | Some i -> Letin (docu, PCons (Extype i, [p], loc),
                            aux e1, aux e2, loc)
       with Not_found -> assert false)
    | ExLam (ety_id, cls, loc) ->
      let cls = List.filter (not % single_assert_false) cls in
      ExLam (ety_id, List.map (fun (p,e)->p, aux e) cls, loc) in
  aux e

let pr_annot_rec ppf = function
  | LetRecNode tsch ->
    fprintf ppf ":@ %a@ " pr_typscheme tsch
  | _ -> ()

let pr_annot_full lettys ppf = function
  | LetRecNode tsch ->
    fprintf ppf ":@ %a@ " pr_typscheme tsch
  | LamNode (Some (arg, ret)) ->
    fprintf ppf ":@ %a -> %a)" pr_ty arg pr_ty ret    
  | MatchVal (Some (arg, ret)) ->
    fprintf ppf ":@ %a)" pr_ty arg
  | MatchRes (Some (arg, ret)) ->
    fprintf ppf ") :@ %a)" pr_ty ret
  | LamOpen (Some _)->
    fprintf ppf "("
  | MatchValOpen (Some _) ->
    fprintf ppf "("
  | MatchResOpen (Some _)->
    fprintf ppf "(("
  | LetInOpen (Some _) -> if lettys then fprintf ppf "("
  | LetInNode (Some (arg, ret)) ->
    if lettys then fprintf ppf ":@ %a)" pr_ty arg

  | LamNode None | MatchVal None | MatchRes None
  | LamOpen None | MatchValOpen None | MatchResOpen None
  | LetInOpen None | LetInNode None -> ()


let pr_expr funtys lettys ppf =
  let export_if = "if", "then", "else" in
  let export_num =
    if !num_is = "int" then None
    else if !num_is_mod
    then Some (String.capitalize !num_is ^ ".of_int")
    else Some (!num_is ^ "_of_int") in
  let export_bool = [true, "true"; false, "false"] in
  let pr_ann =
    if funtys || lettys
    then pr_annot_full lettys else pr_annot_rec in
  pr_expr ?export_num ~export_if ~export_bool pr_ann ppf

let pr_rhs_docu ppf = function
  | None -> ()
  | Some doc -> fprintf ppf "@ (**%s*)" doc

let pr_constr c_n ppf = function
  | (docu, name, [], [], [], c_args) ->
    let res = TCons (c_n, c_args) in
    fprintf ppf "@[<2>| %s@ :@ %a%a@]" (cns_str name)
      pr_ty res pr_rhs_docu docu
  | (docu, name, [], [], args, c_args) ->
    let res = TCons (c_n, c_args) in
    fprintf ppf "@[<2>| %s@ :@ %a@ ->@ %a%a@]" (cns_str name)
      (pr_sep_list " *" pr_ty) args pr_ty res pr_rhs_docu docu
  | (docu, name, vs, [], [], c_args) ->
    let res = TCons (c_n, c_args) in
    fprintf ppf "@[<2>| %s@ :@ (*∀%a.*)@ %a%a@]" (cns_str name)
      (pr_sep_list "," pr_tyvar) vs
      pr_ty res pr_rhs_docu docu
  | (docu, name, vs, phi, [], c_args) ->
    let res = TCons (c_n, c_args) in
    fprintf ppf "@[<2>| %s@ :@ (*∀%a[%a].*)@ %a%a@]" (cns_str name)
      (pr_sep_list "," pr_tyvar) vs
      pr_formula phi pr_ty res pr_rhs_docu docu
  | (docu, name, vs, [], args, c_args) ->
    let res = TCons (c_n, c_args) in
    fprintf ppf "@[<2>| %s@ :@ (*∀%a.*)%a@ ->@ %a%a@]" (cns_str name)
      (pr_sep_list "," pr_tyvar) vs
      (pr_sep_list " *" pr_ty) args pr_ty res pr_rhs_docu docu
  | (docu, name, vs, phi, args, c_args) ->
    let res = TCons (c_n, c_args) in
    fprintf ppf "@[<2>| %s@ :@ (*∀%a[%a].*)%a@ ->@ %a%a@]" (cns_str name)
      (pr_sep_list "," pr_tyvar) vs
      pr_formula phi
      (pr_sep_list " *" pr_ty) args pr_ty res pr_rhs_docu docu

let pr_test_line funtys lettys ppf e =
  fprintf ppf "assert@ (%a);" (pr_expr funtys lettys) e

let pr_ty_wildcards ppf sorts =
  match List.filter ((=) Type_sort) sorts with
  | [] -> ()
  | [s] -> fprintf ppf "_ "
  | sorts ->
    fprintf ppf "(%a) "
      (pr_sep_list "," (fun ppf _ -> fprintf ppf "_")) sorts

let cns_typ =
  typ_fold {(typ_make_fold CNames.union CNames.empty)
            with fold_tcons =
                   (fun n cns -> List.fold_left
                       CNames.union (CNames.singleton (CNam n)) cns)}

let rec pr_struct_items ~funtys ~lettys constrs ppf defined defining prog =
  (*[*
  if prog<>[] then
    Format.printf "OCaml-pr_struct_items:@ item=%a@ defining=%s@\n%!"
      pr_sig_item (List.hd prog)
      (String.concat "," (List.map cns_str (CNames.elements defining)));
  *]*)
  match prog with
  | ITypConstr (docu, c_n, sorts, _)::prog ->
    assert (CNames.is_empty defining || CNames.mem c_n defining);
    altsyn := true;
    (match docu with
     | None -> ()
     | Some doc -> fprintf ppf "(**%s*)@\n" doc);
    let cns = try List.assoc c_n constrs with Not_found -> [] in
    if cns=[]
    then
      fprintf ppf "@[<2>%s %a%a =@ %s_phantom@]@\n"
        (if CNames.is_empty defining then "type" else "and")
        pr_ty_wildcards sorts pr_tycns c_n
        (cns_str c_n)
    else
      fprintf ppf "@[<2>%s %a%a =@\n%a@]@\n"
        (if CNames.is_empty defining then "type" else "and")
        pr_ty_wildcards sorts pr_tycns c_n
        (pr_line_list "" (pr_constr c_n)) cns;
    let more_defs = List.fold_left
        (fun cns ty -> CNames.union cns (cns_typ ty)) CNames.empty
        (concat_map
           (fun (docu, name, vs, phi, args, c_args) ->
              let res = TCons (c_n, c_args) in res::args) cns) in
    let defining =
      CNames.union (CNames.diff more_defs defined) defining in
    let defining = CNames.diff (CNames.remove c_n defining) defined in
    (*[*
    Format.printf "OCaml-pr_struct_items:@ more_defs=%s@ defining'=%s@\n%!"
      (String.concat "," (List.map cns_str (CNames.elements more_defs)))
      (String.concat "," (List.map cns_str (CNames.elements defining)));
    *]*)
    let mutual, prog = List.partition
        (function
          | ITypConstr (_, c_n, _, _) when CNames.mem c_n defining -> true
          | _ -> false)
        prog in
    altsyn := false;
    pr_struct_items ~funtys ~lettys constrs ppf (CNames.add c_n defined) defining
      (mutual @ prog)
  | IPrimVal (docu, name, tysch, Left ext_def, _)::prog ->
    altsyn := true;
    (match docu with
     | None -> ()
     | Some doc -> fprintf ppf "(**%s*)@\n" doc);
    fprintf ppf "@[<2>external@ %s@ :@ %a = \"%s\"@]@\n"
      name pr_typsig tysch ext_def;
    assert (CNames.is_empty defining);
    altsyn := false;
    pr_struct_items ~funtys ~lettys constrs ppf defined CNames.empty prog
  | IPrimVal (docu, name, (_,_,ty as tysch), Right ext_def, _)::prog ->
    altsyn := true;
    (match docu with
     | None -> ()
     | Some doc -> fprintf ppf "(**%s*)@\n" doc);
    (match return_type ty with
     | TCons (Extype i, _) ->
       let args =
         String.concat " "
           (List.mapi (fun i _ -> "a"^string_of_int i) (arg_types ty)) in
       fprintf ppf "@[<2>let@ %s@ :@ %a =@ %sEx%d (%s%s%s)@]@\n"
         name pr_typsig tysch
         (if args="" then "" else "fun "^args^" -> ")
         i (if args="" then "" else "(") ext_def
         (if args="" then "" else ") "^args)
     | _ ->
       fprintf ppf "@[<2>let@ %s@ :@ %a =@ %s@]@\n"
         name pr_typsig tysch ext_def);
    assert (CNames.is_empty defining);
    altsyn := false;
    pr_struct_items ~funtys ~lettys constrs ppf defined CNames.empty prog
  | ILetRecVal (docu, name, expr, tysch, [], elim_extypes, _)::prog ->
    let expr = postprocess elim_extypes expr in
    (match docu with
     | None -> ()
     | Some doc -> fprintf ppf "(**%s*)@\n" doc);
    fprintf ppf "@[<2>let rec@ %s :@ %a =@ %a@]@\n"
      name pr_typscheme (tysch, false) (pr_expr funtys lettys) expr;
    assert (CNames.is_empty defining);
    pr_struct_items ~funtys ~lettys constrs ppf defined CNames.empty prog
  | ILetVal (docu, p, e, tysch, _, [], elim_extypes, _)::prog ->
    let vdef = match p with
      | One _ | PVar _ -> true
      | Zero | PAnd _ | PCons _ -> false in
    let e = postprocess elim_extypes e in
    (match docu with
     | None -> ()
     | Some doc -> fprintf ppf "(**%s*)@\n" doc);
    fprintf ppf "@[<2>let@ %a@ %s: %a%s =@ %a@]@\n"
      pr_pat p (if vdef then "" else "(*")
      pr_typscheme (tysch, false) (if vdef then "" else "*)")
      (pr_expr funtys lettys) e;
    assert (CNames.is_empty defining);
    pr_struct_items ~funtys ~lettys constrs ppf defined CNames.empty prog
  | ILetRecVal (docu, name, expr, tysch, tests, elim_extypes, _)::prog ->
    let expr = postprocess elim_extypes expr in
    let tests = List.map (postprocess elim_extypes) tests in
    (match docu with
     | None -> ()
     | Some doc -> fprintf ppf "(**%s*)@\n" doc);
    fprintf ppf "@[<2>let rec@ %s :@ %a =@ %a@]@\n@[<2>let () =@ %a@ ()@]@\n"
      name pr_typscheme (tysch, false) (pr_expr funtys lettys) expr
      (pr_line_list "" (pr_test_line funtys lettys)) tests;
    assert (CNames.is_empty defining);
    pr_struct_items ~funtys ~lettys constrs ppf defined CNames.empty prog
  | ILetVal (docu, p, e, tysch, _, tests, elim_extypes, _)::prog ->
    let vdef = match p with
      | One _ | PVar _ -> true
      | Zero | PAnd _ | PCons _ -> false in
    let e = postprocess elim_extypes e in
    let tests = List.map (postprocess elim_extypes) tests in
    (match docu with
     | None -> ()
     | Some doc -> fprintf ppf "(**%s*)@\n" doc);
    fprintf ppf "@[<2>let@ %a@ %s: %a%s =@ %a@]@\n[<2>let () =@ %a@ ()@]@\n"
      pr_pat p (if vdef then "" else "(*")
      pr_typscheme (tysch, false) (if vdef then "" else "*)")
      (pr_expr funtys lettys) e
      (pr_line_list "" (pr_test_line funtys lettys)) tests;
    assert (CNames.is_empty defining);
    pr_struct_items ~funtys ~lettys constrs ppf defined CNames.empty prog
  | IValConstr _::_ -> assert false
  | [] -> ()

let pr_ml ~funtys ~lettys ppf prog =
  let constrs, prog = partition_map
      (function
        | IValConstr (docu, name, vs, phi, args, c_n, c_args, _) ->
          Left (c_n, (docu, name, vs, phi, args, c_args))
        | i -> Right i)
      prog in
  let constrs = collect constrs in
  (*[* Format.printf "pr_struct: cns key,count=@\n%a@\n%!"
    (pr_sep_list "|" (fun ppf (n,cs) -> fprintf ppf "%s(#=%d) "
                         (cns_str n) (List.length cs))) constrs; *]*)
  fprintf ppf "type num = int@\n";
  pr_struct_items ~funtys ~lettys constrs ppf init_types CNames.empty prog
