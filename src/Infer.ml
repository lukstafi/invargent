(** Inferring and normalizing formulas for InvarGenT.

    Released under the GNU General Public Licence (version 2 or
    higher), NO WARRANTY of correctness etc. (C) Lukasz Stafiniak 2013
    @author Lukasz Stafiniak lukstafi (AT) gmail.com
    @since Mar 2013
*)

let annotating_fun = ref true
let annotating_letin = ref false
let inform_toplevel = ref false
let time_toplevel = ref false
let merge_rec_nonrec = ref (* false *)true

open Defs
open Terms
open Aux

type cnstrnt =
| A of formula
| And of cnstrnt list
| Impl of formula * cnstrnt
| Or of var_name *
          (VarSet.t * cnstrnt * formula * (unit -> unit)) list * cnstrnt
| All of VarSet.t * cnstrnt
| Ex of VarSet.t * cnstrnt

let rec atoms_of_cnstrnt k = function
| A cnj -> k cnj
| And [] -> k []
| And [cn] -> atoms_of_cnstrnt k cn
| And (cn::cns) ->
  atoms_of_cnstrnt
    (fun cnj0 -> atoms_of_cnstrnt
      (fun cnj1 -> k (cnj0 @ cnj1)) (And cns))
    cn
| Impl ([], cn) -> atoms_of_cnstrnt k cn
| All (vs, cn) ->
  if VarSet.is_empty vs then atoms_of_cnstrnt k cn
  else All (vs, atoms_of_cnstrnt k cn)
| Ex (vs, cn) ->
  if VarSet.is_empty vs then atoms_of_cnstrnt k cn
  else Ex (vs, atoms_of_cnstrnt k cn)
| _ -> assert false

open Format

let rec pr_cnstrnt ppf = function
  | A atoms -> pr_formula ppf atoms
  | And cns -> fprintf ppf "@[<0>";
    pr_sep_list " ∧" pr_cnstrnt ppf cns; fprintf ppf "@]"
  | Impl (prem,concl) -> fprintf ppf "@[<2>";
    pr_formula ppf prem; fprintf ppf "@ ⟹@ %a@]" pr_cnstrnt concl
  | Or (v, cns, phi) -> fprintf ppf "@[<0>[";
    pr_sep_list " ∨" (pr_disj_cnstrnt v) ppf cns;
    fprintf ppf "], Φ(%s)=@\n%a@]" (var_str v) pr_cnstrnt phi
  | All (vs, cn) ->
    fprintf ppf "@[<0>∀%a.@ %a@]"
      (pr_sep_list "," pr_tyvar) (VarSet.elements vs) pr_cnstrnt cn
  | Ex (vs, cn) ->
    fprintf ppf "@[<0>∃%a.@ %a@]"
      (pr_sep_list "," pr_tyvar) (VarSet.elements vs) pr_cnstrnt cn

and pr_disj_cnstrnt v ppf (vs, c, d, _) =
     fprintf ppf "@[<0>%a ∧@ (∀%a,%s.%a@ ⟹@ Φ)@]" pr_cnstrnt c
       pr_vars vs (var_str v) pr_formula d

let pr_brs_old ppf brs =
  pr_line_list "| " (fun ppf (prem,(sb, num, ord, so)) ->
    let concl = to_formula sb @ num @ ord @ so in
    fprintf ppf "@[<2>%a@ ⟹@ %a@]" pr_formula prem pr_formula concl) ppf brs

let pr_brs ppf brs =
  pr_line_list "| " (fun ppf (prem,concl) ->
    fprintf ppf "@[<2>%a@ ⟹@ %a@]" pr_formula prem pr_formula concl) ppf brs

let pr_rbrs ppf brs =
  pr_line_list "| " (fun ppf (prem,concl) ->
    fprintf ppf "@[<2>%a@ ⟹@ %a@]" pr_formula prem pr_formula concl) ppf brs

let pr_rbrs3 ppf brs =
  pr_line_list "| " (fun ppf (nonrec, prem,concl) ->
    fprintf ppf "@[<2>nonrec=%b;@ %a@ ⟹@ %a@]"
      nonrec pr_formula prem pr_formula concl) ppf brs

let pr_rbrs4 ppf brs =
  pr_line_list "| " (fun ppf (nonrec, chiK_pos, prem,concl) ->
    fprintf ppf "@[<2>nonrec=%b; #chiK_pos=%d;@ %a@ ⟹@ %a@]"
      nonrec (List.length chiK_pos) pr_formula prem pr_formula concl) ppf brs

let pr_rbrs5 ppf brs =
  (* TODO: print the chiK *)
  pr_line_list "| " (fun ppf (nonrec, chi_pos, chiK_pos, prem, concl) ->
    fprintf ppf "@[<2>nonrec=%b;@ chiK_pos=%a;@ %a@ ⟹@ %a@]"
      nonrec (pr_sep_list "," Format.pp_print_int)
      (List.map (fun (i,_,_,_) -> i) chiK_pos)
      pr_formula prem pr_formula concl) ppf brs


let separate_sep_subst ?(avoid=VarSet.empty) ?keep ?bvs
    ?(keep_uni=false) ~apply
    q {cnj_typ; cnj_num; cnj_ord; cnj_so} =
  let filter sb =
    if keep_uni && VarSet.is_empty avoid
    then sb
    else
      VarMap.filter
        (fun v _ -> not (VarSet.mem v avoid) &&
                    (keep_uni || not (q.uni_v v))) sb in
  let sb_ty = filter cnj_typ in
  let sb_num, _, cnj_num =
    NumS.separate_subst q ?keep ?bvs ~apply cnj_num in
  let sb_num = filter sb_num in
  let sb_ord, cnj_ord = OrderS.separate_subst q cnj_ord in
  let sb_ord = filter sb_ord in
  let more_sb = varmap_merge sb_num sb_ord in
  let sb = update_sb ~more_sb sb_ty in
  sb, {cnj_typ=VarMap.empty; cnj_num; cnj_ord;
       cnj_so=subst_formula more_sb cnj_so}

let separate_subst ?avoid ?keep ?bvs ?(keep_uni=false) ~apply q phi =
  let sb, {cnj_typ; cnj_num; cnj_ord; cnj_so} =
    separate_sep_subst ?avoid ?keep ?bvs ~keep_uni ~apply q
      (solve ~use_quants:false q phi) in
  assert (VarMap.is_empty cnj_typ);
  sb, NumS.formula_of_sort cnj_num @
        OrderS.formula_of_sort cnj_ord @ cnj_so

(** {2 Constraint inference} *)

let ex_intro_elim e =
  let rec aux = function
    | Var _ | Num _ | NumAdd _ | NumCoef _ | String _
    | Cons _ -> false
    | App (e1, _, _) -> aux e1
    | Lam _ -> false
    | ExLam _ -> true
    | Letrec (_, _, _, _, e2, _) -> aux e2
    | Letin (_, _, _, e2, _) -> true
    | AssertFalse _ -> true
    | RuntimeFailure _ -> true
    | AssertLeq (_, _, e, _)
    | AssertEqty (_, _, e, _) -> aux e in
  aux e

(* Global state for fresh variable guarantees: not re-entrant. *)
let fresh_chi_id = ref 0
let fresh_expr_var_id = ref 0

let pack_value k e =
  let lc = expr_loc e in
  Letin (None, PVar ("xcase", lc), e, Cons (Extype k, [Var ("xcase", lc)], lc), lc)

let normalize_with_target ?target e =
  (*[* Format.printf
    "normalize_expr: e=@\n%a@\n%!" pr_uexpr e; *]*)
  let new_ex_types = ref [] in
  let rec aux ?target k' e =
    match k', target, e with
    | Some k, _, e when not (ex_intro_elim e) ->
      pack_value k (aux None e)
    | _, _, ((Var _ | Num _ | String _) as x) -> x
    | _, _, Cons (k, es, lc) -> Cons (k, List.map (aux None) es, lc)
    | _, _, App (e1, e2, lc) ->
      let target = match target with
        | None -> None | Some (depth, id) -> Some (depth + 1, id) in
      App (aux ?target k' e1, aux None e2, lc)
    | _, _, NumAdd (e1, e2, lc) -> NumAdd (aux None e1, aux None e2, lc)
    | _, _, NumCoef (x, e, lc) -> NumCoef (x, aux None e, lc)
    | _, _, Lam ((), cls, lc) ->
      let target = match target with
        | Some (depth, id) when depth > 0 -> Some (depth - 1, id)
        | _ -> None in
      Lam ((), List.map (aux_cl ?target k') cls, lc)
    | None, Some (1, id), ExLam (_, cls, lc) ->
      (* Each branch must pack a witness of the written existential. *)
      Lam ((), List.map (aux_cl (Some id)) cls, lc)
    | None, _, ExLam (k, cls, lc) ->
      let chi_id = incr fresh_chi_id; !fresh_chi_id in
      let ety_cn = Extype k in
      let ex_sch =
        [delta; delta'],
        [PredVarB (chi_id, tdelta, tdelta', lc)],
        [tdelta], ety_cn, [delta'] in
      Hashtbl.add ex_type_chi k chi_id;
      Hashtbl.add sigma ety_cn ex_sch;
      (*[* Format.printf "normalize_expr: adding exty %d head pat=%a@\n%!"
        chi_id pr_pat (fst3 (List.hd cls)); *]*)
      new_ex_types := (k, lc) :: !new_ex_types;
      all_ex_types := (k, lc) :: !all_ex_types;
      ExLam (k, List.map (aux_cl (Some k)) cls, lc)
    | Some _, _, ExLam (_, cls, lc) ->
      Lam ((), List.map (aux_cl k') cls, lc)
    | _, _, Letrec (docu, ann, x, e1, e2, lc) ->
      Letrec (docu, ann, x, aux None e1, aux ?target k' e2, lc)
    | _, _, Letin (docu, p, e1, e2, lc) ->
      Letin (docu, p, aux None e1, aux ?target k' e2, lc)
    | _, _, (AssertFalse _ as e) -> e
    | _, _, RuntimeFailure (e, lc) -> RuntimeFailure (aux None e, lc)
    | _, _, AssertLeq (e1, e2, range, lc) ->
      AssertLeq (e1, e2, aux ?target k' range, lc)
    | _, _, AssertEqty (e1, e2, range, lc) ->
      AssertEqty (e1, e2, aux ?target k' range, lc)
  and aux_cl ?target k' (p, guards, e) =
    p, List.map (fun (e1,e2) -> aux None e1, aux None e2) guards,
    aux ?target k' e in
  let e = aux ?target None e in
  !new_ex_types, e

let normalize_expr e = normalize_with_target e

(* A consumed result is needed by a surrounding expression. Tail lets and
   assertions pass that demand through. A lambda starts a new result scope. *)
let rewrite_matches transform e tests =
  let rec visit consumed expr =
    let value e = visit true e and tail e = visit consumed e in
    let expr = match expr with
      | Letin (doc, p, (Lam _ as fn), b, loc) -> Letin (doc, p, visit false fn, tail b, loc)
      | Letin (doc, p, a, b, loc) -> Letin (doc, p, value a, tail b, loc)
      | Letrec (doc, (), x, a, b, loc) -> Letrec (doc, (), x, visit false a, tail b, loc)
      | Lam ((), arms, loc) -> Lam ((), List.map visit_arm arms, loc)
      | ExLam (k, arms, loc) -> ExLam (k, List.map visit_arm arms, loc)
      | App ((Lam _ as fn), arg, loc) -> App (visit false fn, value arg, loc)
      | App (a, b, loc) -> App (value a, value b, loc)
      | Cons (k, args, loc) -> Cons (k, List.map value args, loc)
      | NumAdd (a, b, loc) -> NumAdd (value a, value b, loc)
      | NumCoef (n, a, loc) -> NumCoef (n, value a, loc)
      | AssertLeq (a, b, body, loc) -> AssertLeq (value a, value b, tail body, loc)
      | AssertEqty (a, b, body, loc) -> AssertEqty (value a, value b, tail body, loc)
      | RuntimeFailure (msg, loc) -> RuntimeFailure (value msg, loc)
      | (Var _ | Num _ | String _ | AssertFalse _) as e -> e in
    transform consumed expr
  and visit_arm (p, gs, body) =
    p, List.map (fun (a, b) -> visit true a, visit true b) gs, visit false body in
  visit false e, List.map (visit false) tests

(* Move a generated package introduction into the selected match arm. The
   constructor is shared. Opening decisions are keyed by the fresh lets. *)
let branch_packages e tests =
  let changed = ref false in
  let rec pack k = function
    | App (Lam ((), arms, floc), arg, loc) ->
      changed := true;
      App (Lam ((), List.map (fun (p, gs, body) -> p, gs, pack k body) arms,
                floc), arg, loc)
    | Letin (doc, p, v, body, loc) -> Letin (doc, p, v, pack k body, loc)
    | Letrec (doc, (), x, v, body, loc) -> Letrec (doc, (), x, v, pack k body, loc)
    | AssertLeq (a, b, body, loc) -> AssertLeq (a, b, pack k body, loc)
    | AssertEqty (a, b, body, loc) -> AssertEqty (a, b, pack k body, loc)
    | (AssertFalse _ | RuntimeFailure _) as e -> e
    | value -> pack_value k value in
  let move _ = function
    | Letin (None, PVar ("xcase", _), (App (Lam _, _, _) as cases),
             Cons (Extype k, [Var ("xcase", _)], _), _) -> pack k cases
    | e -> e in
  let result = rewrite_matches move e tests in
  if !changed then Some result else None

let signature_target = function
  | None -> None
  | Some (_, _, ty) ->
    let rec result depth = function
      | Fun (_, t) -> result (depth + 1) t
      | TCons (Extype id, _) -> Some (depth, id)
      | _ -> None in
    result 0 ty

let phantom_enumeration = Hashtbl.create 5
(* Presence of a value [None] means that the datatype is excluded from
   being part of a phantom enumeration. *)
let phantom_enumeration_arg : (cns_name, cns_name list option array) Hashtbl.t
  = Hashtbl.create 15

exception Not_enum
let extract_phantom_enumerations = function
  | TypConstr _ | PrimTyp _ | LetRecVal _ | LetVal _ -> ()
  | ValConstr (_, _, vs, phi, _, name, args, loc) ->
    let sb, _ =
      separate_subst ~bvs:(vars_of_list vs) ~apply:false empty_q phi in
    let args =
      Array.map (fun v -> subst_typ sb (TVar v)) (Array.of_list args) in
    let enums =
      try Hashtbl.find phantom_enumeration_arg name
      with Not_found ->
        let enums = Array.make (Array.length args) (Some []) in
        Hashtbl.add phantom_enumeration_arg name enums;
        enums in
    Array.iteri
      (fun i ->
         function
         | None ->
           (match args.(i) with
            | TCons (c_name, []) ->
              (*[* Format.printf "not-enum: %a@\n" pr_cns c_name; *]*)
              (* Mark [c_name] as not an enum. *)
              (try
                 let bad_enum = Hashtbl.find phantom_enumeration c_name in
                 List.iter
                   (fun name -> Hashtbl.replace phantom_enumeration name [])
                   bad_enum;
                 Hashtbl.replace phantom_enumeration c_name []
               with Not_found -> Hashtbl.add phantom_enumeration c_name [])
            | _ -> ())
         | Some enum ->
           (match args.(i) with
            | TCons (c_name, []) ->
              (*[* Format.printf "is-enum: %a@\n" pr_cns c_name; *]*)
              (try
                 let old_enum =
                   try
                     let enum = Hashtbl.find phantom_enumeration c_name in
                     if enum = [] then (
                       (*[* Format.printf "but not enum %a@\n"
                         pr_cns c_name; *]*)
                       List.iter
                         (fun name ->
                            Hashtbl.replace phantom_enumeration name [])
                         enum;
                       enums.(i) <- None;
                       raise Not_enum)
                     else enum
                   with Not_found -> [] in
                 let new_enum =
                   list_remove c_name
                     (unique_sorted (List.sort compare (old_enum @ enum))) in
                 enums.(i) <- Some (c_name::new_enum);
                 if new_enum <> [] then
                   Hashtbl.replace phantom_enumeration c_name new_enum;
                 List.iter
                   (function
                     | d_name when d_name <> c_name ->
                       let d_enum =
                         try Hashtbl.find phantom_enumeration d_name
                         with Not_found -> [] in
                       Hashtbl.replace phantom_enumeration d_name
                         (list_remove d_name
                            (unique_sorted (List.sort compare 
                                              (c_name::new_enum @ d_enum))))
                     | _ -> ())
                   enum
               with Not_enum -> ())
            | t ->
              (* Mark position as not enumeration position. *)
              (*[* Format.printf "not-enum-2: %a; enum=%a@\n" pr_ty t
                (pr_sep_list "," pr_cns) enum; *]*)
              List.iter
                (fun name -> Hashtbl.replace phantom_enumeration name [])
                enum;
              enums.(i) <- None))
      enums

  | PrimVal (_, _, (_, _, ty), _, loc) ->
    match return_type ty with
    | TCons (c_name, []) ->
      (* Mark [c_name] as not an enum. *)
      (try
         let bad_enum = Hashtbl.find phantom_enumeration c_name in
         List.iter
           (fun name -> Hashtbl.replace phantom_enumeration name [])
           bad_enum;
         Hashtbl.replace phantom_enumeration c_name []
       with Not_found -> Hashtbl.add phantom_enumeration c_name [])
    | _ -> ()

let normalize_item = function
  | (TypConstr _ | PrimTyp _ | ValConstr _ | PrimVal _) as item ->
    extract_phantom_enumerations item;
    (*[* Format.printf "phantom %d enumerations after: %a@\n"
      (Hashtbl.length phantom_enumeration) pr_struct_item item;
    Hashtbl.iter
      (fun name enum -> Format.printf "phantom: name=%a enum=%a@\n"
        pr_cns name (pr_sep_list "," pr_cns) enum) phantom_enumeration; *]*)
    [], item
  | LetRecVal (docu, x, e, ty, tes, lc) ->
    let extys, e = normalize_with_target ?target:(signature_target ty) e in
    let extys, tes = fold_map
        (fun extys e ->
           let more_extys, e = normalize_expr e in
           more_extys @ extys, e)
        extys tes in
    extys, LetRecVal (docu, x, e, ty, tes, lc)
  | LetVal (docu, p, e, ty, lc) ->
    let target = match p with PVar _ -> signature_target ty | _ -> None in
    let extys, e = normalize_with_target ?target e in
    extys, LetVal (docu, p, e, ty, lc)

let normalize_program = List.map normalize_item

let rec flat_and = function
  | And cns -> concat_map flat_and cns
  | A cns -> List.map (fun cn -> A [cn]) cns
  | cn -> [cn]

let cn_and cn1 cn2 = And (flat_and cn1 @ flat_and cn2)


let freshen_cns_scheme (vs, phi, argtys, c_n, c_args) =
  let env = List.map (fun v->v, freshen_var v) vs in
  let env_sb = varmap_of_assoc env in
  let argtys = List.map (hvsubst_typ env_sb) argtys in
  let phi = hvsubst_formula env_sb phi in
  let vs = List.map snd env in
  let c_args = List.map (flip List.assoc env) c_args in
  vs, phi, argtys, c_n, c_args

let freshening vs =
  let env = List.map (fun v -> v, freshen_var v) vs in
  List.map snd env, varmap_of_assoc env

let freshen_val_scheme (vs, phi, res) =
  let vs, renaming = freshening vs in
  vs, hvsubst_formula renaming phi, hvsubst_typ renaming res

let constr_gen_pat p tau =
  let rec aux tau = function
    | Zero | One _ | PVar _ -> And []
    | PAnd (p1, p2, _) -> cn_and (aux tau p1) (aux tau p2)
    | PCons (CNam "Tuple", args, loc) ->
      let argvs = List.map (fun _ -> fresh_typ_var ()) args in
      let argtys = List.map (fun v -> TVar v) argvs in
      let cns = List.map2 aux argtys args in
      let tupt = TCons (tuple, argtys) in
      Ex (vars_of_list argvs, And (A [Eqty (tupt, tau, loc)]::cns))
    | PCons (k, args, loc) ->
      (*[* Format.printf "constructors: %!";
      Hashtbl.iter (fun k _ -> Format.printf "%s, " (cns_str k)) sigma;
      Format.printf "@\n%!";
      *]*)
      let abvs, phi, argtys, c_n, c_args =
        try freshen_cns_scheme (Hashtbl.find sigma k)
        with Not_found -> raise
          (Report_toplevel ("Undefined constructor "^cns_str k, Some loc)) in
      if List.length args <> List.length argtys
      then raise
          (Report_toplevel
             (Format.sprintf
               "Pattern arity mismatch for %s (expected %d, found %d)"
                (cns_str k) (List.length argtys) (List.length args),
              Some loc));
      let avs = vars_of_list c_args in
      let res = TCons (c_n, List.map (fun v->TVar v) c_args) in
      let bvs = VarSet.diff (vars_of_list abvs) avs in
      let argphi =
        List.fold_left cn_and (And [])
          (List.map2 aux argtys args) in
      let cn =
        if phi=[] || argphi=And [] then argphi else Impl (phi, argphi) in
      let cn = if VarSet.is_empty bvs then cn else All (bvs, cn) in
      Ex (avs, And [A [Eqty (res, tau, loc)]; cn]) in
  aux tau p
  
type envfrag = VarSet.t * formula * (string * typ) list

let envfrag_x (vs1, phi1, env1) (vs2, phi2, env2) =
  VarSet.union vs1 vs2, phi1 @ phi2, env1 @ env2
let envfrag_empty = VarSet.empty, [], []
let typ_to_sch (x, ty) = x, ([], [], ty)

let rec envfrag_gen_pat count p t =
  let rec aux t = function
    | Zero | One _ -> envfrag_empty
    | PVar (x, _) -> VarSet.empty, [], [x, t]
    | PAnd (p1, p2, _) ->
      envfrag_x (aux t p1) (aux t p2)
    | PCons (CNam "Tuple", ps, loc) ->
      let argvs = List.map (fun _ -> fresh_typ_var ()) ps in
      let argtys = List.map (fun v -> TVar v) argvs in
      let res = TCons (tuple, argtys) in
      let ef0 = vars_of_list argvs, [Eqty (res, t, loc)], [] in
      (*[* Format.printf "envfrag_gen_pat: [%d]@ bs=%a@\n%!"
        count pr_vars (fst3 ef0); *]*)
      List.fold_left envfrag_x ef0 (List.map2 aux argtys ps)
    | PCons (k, ps, loc) ->
      let vs, phi, args, c_n, c_args =
        try freshen_cns_scheme (Hashtbl.find sigma k)
        with Not_found -> raise
          (Report_toplevel ("Undefined constructor "^cns_str k, Some loc)) in
      if List.length args <> List.length ps
      then raise
          (Report_toplevel
             (Format.sprintf
               "Pattern arity mismatch for %s (expected %d, found %d)"
                (cns_str k) (List.length args) (List.length ps),
              Some loc));
      let res = TCons (c_n, List.map (fun v->TVar v) c_args) in
      let ef0 = vars_of_list vs, Eqty (res, t, loc)::phi, [] in
      (*[* Format.printf
        "envfrag_gen_pat: [%d]@ bs=%a@ phi=%a@ args=%a c_args=%a@\n%!"
        count pr_vars (fst3 ef0) pr_formula phi
        pr_ty (TCons (tuple, args)) pr_vars (vars_of_list c_args); *]*)
      List.fold_left envfrag_x ef0 (List.map2 aux args ps) in
  aux t p

let rec single_assert_false = function
    | AssertFalse _ -> true
    | Letin (_, _, AssertFalse _, _, _) -> true
    | Lam (_, [_, _, e], loc) -> single_assert_false e
    | _ -> false

let impl prem concl =
  if prem=[] || concl = A [] || concl = And []
  then concl else Impl (prem, concl)

let letin_count = ref 0

let uses_pos_assertions = ref false

(* Leading lambdas give a lower bound on the number of arguments needed
   before a package can be returned. An efunction contributes one arrow. *)
let rec lambda_depth = function
  | Lam (_, [_, [], body], _) -> 1 + lambda_depth body
  | Lam _ | ExLam _ -> 1
  | _ -> 0

(* Compare actual values from this pattern. An expression computed using
   native arithmetic, including a call to an inferred successor function,
   can overflow even when its inferred index is an affine term. *)
let guard_operand env = function
  | Var (x, _) -> (try Some (List.assoc x env) with Not_found -> None)
  | Num (n, _) -> Some (TCons (numtype, [num (NumDefs.Cst (n,1))]))
  | _ -> None

let impossible_guard prem env guards =
  let operand = guard_operand env in
  let tests = map_some (fun (left, right) ->
      match operand left, operand right with
      | Some a, Some b -> Some (a, b, expr_loc left)
      | _ -> None) guards in
  tests <> [] &&
    try
      let solved = unify ~use_quants:false empty_q prem in
      let used = ref (VarSet.union (fvs_formula prem) (fvs_typs (List.map snd env))) in
      let indices = Hashtbl.create 2 in
      let index loc ty = match subst_typ solved.cnj_typ ty with
        | TCons (name, [t]) when name = numtype -> num_unbox ~t2:ty loc t
        | TVar v ->
          if not (Hashtbl.mem indices v) then (
            let i = next_var !used Num_sort in
            used := VarSet.add i !used;
            Hashtbl.add indices v i);
          NumDefs.Lin (1,1,Hashtbl.find indices v)
        | _ -> raise Not_found in
      let comparisons = List.map (fun (a,b,loc) ->
          NumDefs.Leq (index loc a, index loc b, loc)) tests in
      match NumS.satisfiable (comparisons @ solved.cnj_num) with
      | Left _ -> true | Right _ -> false
    with Contradiction _ | Not_found -> false
       | Failure msg when msg = "int_of_big_int" -> false

let guard_atom = function Eqty _ | Terms.A (Num_atom _) -> true | _ -> false

let rec refined_pattern = function
  | PCons (k, args, _) ->
    let constrains_index = match k with
      | Extype _ | CNam "Tuple" -> false
      | CNam _ -> let _, phi, _, _, _ = Hashtbl.find sigma k in List.exists guard_atom phi in
    constrains_index || List.exists refined_pattern args
  | PAnd (a, b, _) -> refined_pattern a || refined_pattern b
  | Zero | One _ | PVar _ -> false

(* Give a consumed GADT match its own unary arrow predicate. The ordinary
   local-definition rule checks every admitted instance in the original
   lexical environment. The old use instantiates the inferred scheme. *)
let name_consumed_matches e tests =
  let used = ref Strings.empty and serial = ref 0 in
  let rec fresh () =
    incr serial;
    let name = "_match_result" ^ string_of_int !serial in
    if Strings.mem name !used then fresh () else name in
  let refined = function
    | Lam ((), arms, _) -> List.exists (fun (p, _, _) -> refined_pattern p) arms
    | _ -> false in
  let bind fn loc use =
    (* Descendants have already been visited, including references that will
       lie in the scope of the new binder. *)
    let x = fresh () in
    Letrec (None, (), x, fn, use (Var (x, expr_loc fn)), loc) in
  let name consumed = function
    | Var (x, _) as e -> used := Strings.add x !used; e
    | App (fn, arg, loc) when consumed && refined fn ->
      bind fn loc (fun f -> App (f, arg, loc))
    | Letin (doc, p, fn, body, loc) when refined fn ->
      (* Keep the original binding monomorphic even if its RHS can now be
         given a polymorphic contract. *)
      bind fn loc (fun f -> Letin (doc, p, f, body, loc))
    | fn when consumed && refined fn -> bind fn (expr_loc fn) (fun f -> f)
    | e -> e in
  let result = rewrite_matches name e tests in
  if !serial = 0 then None else Some result

(* A local recursive definition checks every member of its input predicate.
   Project its mandatory equations onto the arrow. A constructor-only premise
   may be used once the accumulated equations already entail it. The summary
   does not depend on any recursive predicate or guarded RHS. *)
let necessary_contract gamma anchor body =
  let captured = List.fold_left (fun free (_, (bound, phi, t)) ->
      let used = VarSet.union (fvs_typ t) (fvs_formula phi) in
      VarSet.union free (VarSet.diff used (vars_of_list bound))) VarSet.empty gamma in
  let rec collect (facts, pending as acc) = function
    | A atoms -> List.rev_append (List.filter guard_atom atoms) facts, pending
    | And parts -> List.fold_left collect acc parts
    | Ex (_, part) | Impl ([], part) -> collect acc part
    | Impl (prem, part) when List.for_all (function Eqty _ -> true | _ -> false) prem ->
      facts, (prem, part) :: pending
    | All _ | Or _ | Impl _ -> acc in
  let rec close (facts, pending) =
    let solved = unify ~use_quants:false empty_q facts in
    let apply = subst_typ solved.cnj_typ in
    let implied = function Eqty (a,b,_) -> apply a = apply b | _ -> false in
    let ready, rest = List.partition (fun (prem, _) -> List.for_all implied prem) pending in
    if ready <> [] then close (List.fold_left
        (fun acc (_, part) -> collect acc part) (facts, rest) ready) else
    let shared = VarMap.filter (fun v _ -> VarSet.mem v captured) solved.cnj_typ in
    let arrow = apply anchor and phi = to_formula shared @ NumS.formula_of_sort solved.cnj_num in
    let vs = VarSet.diff (VarSet.union (fvs_typ arrow) (fvs_formula phi)) captured in
    Some (VarSet.elements vs, phi, arrow) in
  try close (collect ([], []) body)
  with Contradiction _ -> None
     | Failure msg when msg = "int_of_big_int" -> None

type guard_observation =
  | Evaluated of cnstrnt
  | Entered_let of cnstrnt * typ * atom * (cns_name * formula) list

(* Keep necessary first-order observations. Existential names are fresh per
   occurrence. A plain let binds the RHS itself. A package supplies its local
   witness only after entry into that let's body. *)
let guard_context contracts observations =
  let boundaries = ref [] in
  let add_atom facts = function
    | PredVarU (i, t, loc) when Hashtbl.mem contracts i ->
      (match Lazy.force (Hashtbl.find contracts i) with
       | None -> facts
       | Some scheme ->
         let _, phi, arrow = freshen_val_scheme scheme in
         Eqty (t, arrow, loc) :: List.rev_append phi facts)
    | atom -> if guard_atom atom then atom :: facts else facts in
  let rec collect (facts, openings as acc) = function
    | A atoms -> List.fold_left add_atom facts atoms, openings
    | And parts -> List.fold_left collect acc parts
    | Ex (_, part) | Impl ([], part) -> collect acc part
    | Or (v, (_, A [NotEx (rhs, _)], [Eqty (TVar x, t, _) as link], _) :: _, sub)
      when x = v && t = rhs -> facts, (rhs, link, [], sub) :: openings
    | All _ | Or _ | Impl _ -> acc in
  let observe acc = function
    | Evaluated cn -> collect acc cn
    | Entered_let (cn, rhs, plain, packages) ->
      let facts, openings = collect acc cn in
      facts, (rhs, plain, packages, A []) :: openings in
  let rec close (facts, openings) =
    let solved = unify ~use_quants:false empty_q facts in
    let open_one ((added, waiting) as acc) ((rhs, plain, packages, sub) as opening) =
      match subst_typ solved.cnj_typ rhs with
      | TCons (CNam _, _) | Fun _ -> collect (plain :: added, waiting) sub
      | TCons ((Extype _ as tag), _) when List.mem_assoc tag packages ->
        let entered = List.assoc tag packages in
        List.iter (function
            | Terms.A (Num_atom (NumDefs.Leq (a, b, loc))) ->
              boundaries := NumDefs.Eq (a, b, loc) :: !boundaries
            | _ -> ()) entered;
        collect acc (A entered)
      | _ -> added, opening :: waiting in
    let added, waiting = List.fold_left open_one ([], []) openings in
    if added <> [] then close (List.rev_append added facts, waiting) else
    match NumS.satisfiable solved.cnj_num with
    | Left _ -> None
    | Right state -> Some (state, !boundaries) in
  try close (List.fold_left observe ([], []) observations)
  with Contradiction _ -> None
     | Failure msg when msg = "int_of_big_int" -> None

let excludes_comparisons state comparisons =
  try match NumS.satisfiable ~state comparisons with Left _ -> true | Right _ -> false
  with Failure msg when msg = "int_of_big_int" -> false

let integer_complement = function
  | Terms.A (Num_atom (NumDefs.Leq (a, b, loc))) ->
    Some (NumDefs.Leq (NumDefs.add b (NumDefs.Cst (1,1)), a, loc))
  | _ -> None

type band_endpoint = Literal of int | Bound_value of string * loc

type 'a guard_band = At_least of 'a | At_most of 'a | Between of 'a * 'a
type observed_bands = band_endpoint guard_band list ref

let map_band f = function
  | At_least x -> At_least (f x) | At_most x -> At_most (f x)
  | Between (a,b) -> Between (f a,f b)
type guard_bounds =
  | Observe_comparisons of bool ref
  | Prove_complements of bool ref * observed_bands
  | Probe_boundaries of observed_bands

(* A comparison forced on even one package boundary is a poor choice to
   falsify throughout an opening. Use the remaining position to propose a
   goal. Only the check on the full package can certify an erased arm. *)
let remaining_comparison mode context conditions =
  match conditions, context with
  | [_], _ -> Some 0
  | _, Some (state, boundaries) ->
    let candidates = mapi_some (fun i atom -> match integer_complement atom with
        | Some neg when not (excludes_comparisons state [neg]) -> Some (i, neg)
        | _ -> None) conditions in
    (match candidates, mode with
     | [(i, _)], _ -> Some i
     | _ :: _ :: _, Prove_complements (seen,_) ->
       if boundaries <> [] then seen := true;
       None
     | _ :: _ :: _, Probe_boundaries _ ->
       let probes = map_some (fun eq ->
           try match NumS.satisfiable ~state [eq] with
             | Left _ -> None | Right boundary -> Some boundary
           with Failure msg when msg = "int_of_big_int" -> None) boundaries in
       (match List.filter (fun (_, neg) ->
            not (List.exists (fun probe -> excludes_comparisons probe [neg]) probes)) candidates with
        | [(i, _)] -> Some i | _ -> None)
     | _ -> None)
  | _ -> None

type source_arm = (unit, unit) clause
type arm_check = Already_excluded | Check_with_postconditions of int option | Keep_arm
type guard_erasure =
  | Keep_bodies | Direct_guards
  | Collect_guards of (source_arm * (unit -> arm_check)) list ref * guard_bounds
  | Certified_guards of source_arm list * source_arm list * (source_arm * int) list

type numeric_band = NumDefs.term guard_band
type key_use =
  | Endpoints of NumDefs.term * NumDefs.term
  | Result_keys of NumDefs.term * var_name * NumS.key_probe list

type key_query = {
  key : var_name;
  bounds : NumDefs.formula;
  use : key_use
}

type call_policy = Restrict_calls of formula | Open_at_keys of key_query
                 | Exclude_bands of numeric_band list
type admission = Admitted | Unavailable | Retry_keys of key_query

type replay =
  | Fixed of typ
  | Outside_bands of cns_name * numeric_band list
  | After_result of cns_name * (typ -> (typ * VarSet.t * formula * cnstrnt) list)

(* Each graph is total and single valued. Only fresh variable renamings are
   applied to the input and payload expressions. *)
let selected_key sb payload probe observed =
  let open NumDefs in
  let k = fresh_num_var () and r = fresh_num_var () and mid = fresh_num_var () in
  let v x = Lin (1,1,x) in
  let sub a b = add a (scale_term (-1) 1 b) in
  let target = hvsubst_term (VarMap.add payload r sb) probe.NumS.target_value in
  let low = hvsubst_term sb probe.NumS.clip_lower and high = hvsubst_term sb probe.NumS.clip_upper in
  k, vars_of_list [r;mid;k],
  [Eq (v r,observed,dummy_loc);
   Opti (sub low (v mid),sub target (v mid),dummy_loc);
   Opti (sub (v k) high,sub (v k) (v mid),dummy_loc)]

(* At an integer opening, failure of lo <= r <= hi has unit slack on
   at least one side. Fresh names avoid negating an input coefficient. *)
let outside_bands loc value bands =
  let open NumDefs in
  let alias term =
    let x = fresh_num_var () in x, Lin (1,1,x), Eq (Lin (1,1,x),term,loc) in
  let x,r,link = alias value in
  let side a b = Add [a; Cst (1,1); scale_term (-1) 1 b] in
  let outside (vs,phi) = function
    | At_least lo -> vs,Leq (Add [r;Cst (1,1)],lo,loc)::phi
    | At_most hi -> vs,Leq (Add [hi;Cst (1,1)],r,loc)::phi
    | Between (lo,hi) ->
      let i,l,left = alias lo and j,h,right = alias hi in
      add_vars [i;j] vs, Subopti (side r l,side h r,loc)::left::right::phi in
  let vars,atoms = List.fold_left outside (VarSet.singleton x,[link]) bands in
  vars,NumS.formula_of_sort atoms

(* None denotes zero, Some i the numeric index at parameter position i.
   A bound enters a round only after every constructor justifies it from
   the preceding round's facts about immediate value fields. *)
let index_bound args loc (left,right) =
  let term = function
    | None -> NumDefs.Cst (0,1)
    | Some i -> NumS.num_of (List.nth args i) in
  NumDefs.Leq (term left,term right,loc)

let constructor_value_bounds prog =
  let families = map_some (function
      | _, TypConstr (_,(CNam _ as name),sorts,_) when List.mem Num_sort sorts ->
        let rules = map_some (function
            | _, ValConstr (_,_,_,phi,fields,parent,params,loc) when parent=name ->
              Some ((sep_formulas phi).cnj_num, fields, List.map (fun v -> TVar v) params,loc)
            | _ -> None) prog in
        if rules=[] then None else
        let positions = None :: map_some (fun (i,s) ->
            if s=Num_sort then Some (Some i) else None) (List.mapi (fun i s -> i,s) sorts) in
        let pool = concat_map (fun i -> map_some (fun j ->
            if i=j then None else Some (i,j)) positions) positions in
        Some (name,sorts,rules,pool)
      | _ -> None) prog in
  let rec close previous =
    let child loc = function
      | TCons (name,args) when List.mem_assoc name previous ->
        List.map (index_bound args loc) (List.assoc name previous)
      | _ -> [] in
    let next = List.map (fun (name,_,rules,pool) ->
        let checks = List.map (fun (guard,fields,args,loc) ->
            let state = NumS.satisfiable (guard @ concat_map (child loc) fields) in
            fun bound -> match state with Left _ -> true | Right state ->
              NumS.implies_cnj state [index_bound args loc bound]) rules in
        let prior = List.assoc name previous in
        name, List.filter (fun bound -> List.mem bound prior ||
            List.for_all (fun check -> check bound) checks) pool)
        families in
    if next=previous then next else close next in
  let proved = close (List.map (fun (name,_,_,_) -> name,[]) families) in
  map_some (fun (name,sorts,_,_) -> match List.assoc name proved with
      | [] -> None | bounds -> Some (name,(sorts,bounds))) families

let value_patterns families relevant e arrow =
  let rec collect args e = match args,e with
    | TCons (name,params)::rest,Lam (_,arms,_) ->
      concat_map (fun (pat,_,body) ->
          let nested = collect rest body in
          match pat with
          | PVar (_,loc) when List.mem_assoc name families ->
            let sorts,bounds = List.assoc name families in
            if VarSet.is_empty (VarSet.inter relevant
                (NumDefs.fvs_formula (List.map (index_bound params loc) bounds)))
            then nested else (pat,(name,sorts,bounds))::nested
          | _ -> nested) arms
    | _::rest,Lam (_,arms,_) -> concat_map (fun (_,_,body) -> collect rest body) arms
    | _ -> [] in
  collect (arg_types arrow) e

let constr_gen_expr_with_arities ?paired ?(value_patterns=[]) ~erase_bodies arities gamma e t =
  let erased_packages = ref None in
  let contracts = Hashtbl.create 2 in
  let alias_arities = Hashtbl.create 2 in
  let rec known_arrows gamma = function
    | App (f, _, _) -> max 0 (known_arrows gamma f - 1)
    | Var (x, _) when List.mem_assoc x gamma ->
      let _, phi, typ = List.assoc x gamma in
      let depth = match typ with
        | TVar v when Hashtbl.mem alias_arities v -> Hashtbl.find alias_arities v
        | _ -> List.length (arg_types typ) in
      List.fold_left (fun n -> function
          | PredVarU (i, arg, _) when arg = typ && Hashtbl.mem arities i ->
            max n (Hashtbl.find arities i)
          | _ -> n) depth phi
    | e -> lambda_depth e in
  let elim_extype = ref [] and preserve = ref [] in
  let collecting = match erase_bodies with Collect_guards _ -> true | _ -> false in
  (* Only a saturated reference to this recursive binding gets a paired
     opening. A local binding with the same spelling has its own scheme. *)
  let rec paired_call gamma depth = function
    | App (fn,_,_) -> paired_call gamma (depth+1) fn
    | Var (name,_) ->
      (match paired with
       | Some (binding,(vs,phi,arrow),other) when depth = List.length (arg_types arrow) &&
           (try List.assoc name gamma == binding with Not_found -> false) ->
         let vs,renaming = freshening vs in
         Some (vs, hvsubst_formula renaming phi, hvsubst_typ renaming arrow,
               other renaming)
       | _ -> None)
    | _ -> None in
  let rec aux_in scope ?scrutinee ?operator gamma t e : cnstrnt * iexpr =
    let aux = aux_in scope in
    (*[* Format.printf "constr_gen: t=%a e=@\n%a@\n%!"
      pr_ty t pr_uexpr e;
    *]*)
    match e with
    | Var (x, loc) when not (List.mem_assoc x gamma) ->
      raise (Report_toplevel ("Undefined variable "^x, Some loc))
    | Var (x, loc) as e ->
      let vs, phi, res = match operator with
        | None -> freshen_val_scheme (List.assoc x gamma)
        | Some (phi,res) -> [],phi,res in
      Ex (vars_of_list vs, cn_and (A [Eqty (res, t, loc)]) (A phi)),
      e
    | Num (i, loc) as e ->
      A [Eqty (TCons (numtype, [num (NumDefs.Cst (i,1))]), t, loc)],
      e
    | NumAdd (e1, e2, loc) ->
      let a1 = fresh_var Num_sort in
      let a2 = fresh_var Num_sort in
      let t1 = TCons (numtype, [TVar a1]) in
      let t2 = TCons (numtype, [TVar a2]) in
      (*[* Format.printf "constr_gen_expr: NumAdd=%a + %a@\n%!"
        pr_uexpr e1 pr_uexpr e2; *]*)
      let cn1, e1 = aux gamma t1 e1 in
      let cn2, e2 = aux gamma t2 e2 in
      let rt = TCons (numtype, [Alien (Num_term NumDefs.(
          Add [Lin (1,1,a1); Lin (1,1,a2)]))]) in
      Ex (vars_of_list [a1; a2],
          cn_and cn1 (cn_and cn2 (A [Eqty (t, rt, loc)]))),
      NumAdd (e1, e2, loc)
    | NumCoef (x, e, loc) ->
      let a1 = fresh_var Num_sort in
      let t1 = TCons (numtype, [TVar a1]) in
      (*[* Format.printf "constr_gen_expr: NumCoef=%d * %a@\n%!"
        x pr_uexpr e; *]*)
      let cn, e = aux gamma t1 e in
      let rt = TCons (numtype, [Alien (Num_term NumDefs.(
          Lin (x, 1, a1)))]) in
      Ex (VarSet.singleton a1,
          cn_and cn (A [Eqty (t, rt, loc)])),
      NumCoef (x, e, loc)
    | String (_, loc) as e ->
      A [Eqty (ty_string, t, loc)],
      e
    | Cons (CNam "Tuple", args, loc) ->
      let argvs =
        List.map (fun _ -> fresh_typ_var ()) args in
      let argtys = List.map (fun v -> TVar v) argvs in
      let cns, args = List.split
          (List.map2 (aux gamma) argtys args) in
      let tupt = TCons (tuple, argtys) in
      Ex (vars_of_list argvs, And (A [Eqty (t, tupt, loc)]::cns)),
      Cons (CNam "Tuple", args, loc)
    | Cons (k, args, loc) when not (Hashtbl.mem sigma k)->
      raise (Report_toplevel ("Undefined constructor "^cns_str k, Some loc))
    | Cons (k, args, loc) ->
      let vs, phi, argtys, c_n, c_args =
        freshen_cns_scheme (Hashtbl.find sigma k) in
      if List.length args <> List.length argtys
      then raise
          (Report_toplevel
             (Format.asprintf
                "Arity mismatch for %s (expected %d, found %d): (%a)"
                (cns_str k) (List.length argtys) (List.length args)
                (pr_sep_list " | " pr_uexpr) args,
              Some loc));
      let res = TCons (c_n, List.map (fun v->TVar v) c_args) in
      let cns, args = List.split
          (List.map2 (aux gamma) argtys args) in
      let cn = List.fold_left
          cn_and (A (Eqty (res, t, loc)::phi)) cns in
      (*[* Format.printf "constr_gen_expr: Cons=%a@\nphi=%a@\ncn=%a@\n%!"
        pr_uexpr e pr_formula phi pr_cnstrnt cn; *]*)
      Ex (vars_of_list vs, cn),
      Cons (k, args, loc)      
    | App (e1, e2, loc) (*[* as e *]*) ->
      let a = fresh_typ_var () in
      let ta = TVar a in
      (*[* Format.printf "constr_gen_expr: App=@\n%a@\n%!"
        pr_uexpr e; *]*)
      let (cn1, e1), (cn2, e2) = match e1 with
        | Lam _ when collecting ->
          (* A literal lambda enters its body after the argument returns.
             Generate the function first to retain the normal variable order. *)
          let argument = ref (And []) in
          let fn = aux_in scope ~scrutinee:(ta, lazy !argument)
              gamma (Fun (ta, t)) e1 in
          let value = aux gamma ta e2 in
          argument := fst value;
          fn, value
        | _ ->
          let fn = aux_in scope ?operator gamma (Fun (ta, t)) e1 in
          fn, aux gamma ta e2 in
      Ex (VarSet.singleton a,
          cn_and cn1 (cn_and cn2 (A [NotEx (ta, loc)]))),
      App (e1, e2, loc)
    | Lam ((), cls, loc) ->
      let a1 = fresh_typ_var () in
      let t1 = TVar a1 in
      let a2 = fresh_typ_var () in
      let t2 = TVar a2 in
      let scope = match scrutinee with
        | None -> scope
        | Some (actual, facts) -> lazy (Evaluated (And [A [Eqty (t1, actual, loc)]; Lazy.force facts])) :: scope in
      let _, checked = fold_map (fun shadowed cl ->
          let checked = aux_cl_in scope ~shadowed 0 gamma t1 t2 cl in
          shadowed || catches_all cl, checked) false cls in
      let cns, cls = List.split checked in
      let cn = List.fold_left cn_and
          (A [Eqty (Fun (t1, t2), t, loc)]) cns in
      if match cls with [_] -> !annotating_letin | _ -> !annotating_fun
      then preserve := a1::a2:: !preserve;
      Ex (vars_of_list [a1; a2], cn),
      Lam ([a1, a2], cls, loc)
    | AssertFalse loc as e -> A [CFalse loc], e
    | RuntimeFailure (e, loc) ->
      let cn, e = aux gamma ty_string e in
      cn, RuntimeFailure (e, loc)
    | Letin (_, _, AssertFalse _, _, loc) ->
      A [CFalse loc], AssertFalse loc
    | Letin (_, _, (RuntimeFailure _ as e1), _, _) ->
      aux gamma t e1
    | AssertLeq (e1, e2, e3, loc) ->
      uses_pos_assertions := true;
      let a1 = fresh_var Num_sort in
      let t1 = TVar a1 in
      let a2 = fresh_var Num_sort in
      let t2 = TVar a2 in
      let nt1 = TCons (numtype, [t1]) in
      let nt2 = TCons (numtype, [t2]) in
      let cn1, e1 = aux gamma nt1 e1 in
      let cn2, e2 = aux gamma nt2 e2 in
      let cn3, e3 = aux gamma t e3 in
      let cn =
        cn_and (A [Terms.A NumDefs.(Num_atom (
            Leq (Lin (1,1,a1), Lin (1,1,a2), loc)))])
          (cn_and cn1 (cn_and cn2 cn3)) in
      Ex (vars_of_list [a1; a2], cn),
      AssertLeq (e1, e2, e3, loc)
    | AssertEqty (e1, e2, e3, loc) ->
      uses_pos_assertions := true;
      let a1 = fresh_typ_var () in
      let t1 = TVar a1 in
      let a2 = fresh_typ_var () in
      let t2 = TVar a2 in
      let cn1, e1 = aux gamma t1 e1 in
      let cn2, e2 = aux gamma t2 e2 in
      let cn3, e3 = aux gamma t e3 in
      (*[* Format.printf
        "constr_gen-AssertEqty:@ %a == %a@\n%!" pr_ty t1 pr_ty t2; *]*)
      let cn =
        cn_and (A [Eqty (t1, t2, loc)])
          (cn_and cn1 (cn_and cn2 cn3)) in
      Ex (vars_of_list [a1; a2], cn),
      AssertEqty (e1, e2, e3, loc)
    | Letrec (docu, (), x, e1, e2, loc) ->
      let a = fresh_typ_var () in
      let b = fresh_typ_var () in
      let chi_id = incr fresh_chi_id; !fresh_chi_id in
      let tb = TVar b in
      let chi_b = PredVarU (chi_id, tb, expr_loc e1) in
      let chi_a = PredVarU (chi_id, TVar a, expr_loc e1) in
      Hashtbl.replace arities chi_id (lambda_depth e1);
      let gamma = (x, ([b], [chi_b], tb))::gamma in
      let cn1, e1 = aux gamma tb e1 in
      if collecting then Hashtbl.add contracts chi_id (lazy (necessary_contract gamma tb cn1));
      let cn2, e2 = aux gamma t e2 in
      let def_cn = 
        All (vars_of_list [b],
             Impl ([chi_b], cn1)) in
      cn_and def_cn (cn_and (Ex (vars_of_list [a], A [chi_a])) cn2),
      Letrec (docu, [chi_id], x, e1, e2, loc)
    | Letin (docu, (PVar (name, _) as p), rhs, body, loc)
      when !all_ex_types <> [] && known_arrows gamma rhs > 0 ->
      let a = fresh_typ_var () in
      let ta = TVar a in
      Hashtbl.add alias_arities a (known_arrows gamma rhs);
      (* A variable pattern binds this ordinary value at the same monotype.
         Keep the binding in scope for every use of the alias. *)
      let value_cn, rhs = aux gamma ta rhs in
      let body_scope = if collecting then lazy (Evaluated value_cn) :: scope else scope in
      let body_cn, body = aux_in body_scope ((name, ([], [], ta)) :: gamma) t body in
      elim_extype := (p, None) :: !elim_extype;
      Ex (VarSet.singleton a, cn_and value_cn body_cn),
      Letin (docu, p, rhs, body, loc)
    | Letin (docu, p, e1, e2, loc) (* as e *) ->
      let count = incr letin_count; !letin_count in
      (*[* Format.printf "constr_gen-Letin: [%d] starting...@\n%!" count; *]*)
      let a0 = fresh_typ_var () in
      let ta0 = TVar a0 in
      let extra_vars, other, (cn1,e1) = match paired with
        | None -> [],None,aux gamma ta0 e1
        | Some _ ->
          (match paired_call gamma 0 e1 with
           | None -> [],None,aux gamma ta0 e1
           | Some (vs,phi,arrow,other) ->
             vs,Some other,aux_in scope ~operator:(phi,arrow) gamma ta0 e1) in
      (*[* Format.printf
        "constr_gen-Letin: [%d] generated ta0=%a@ cn1=%a@\ne1=%a@\n%!"
        count pr_ty ta0 pr_cnstrnt cn1 pr_iexpr e1; *]*)
      let b0 = fresh_typ_var () in
      let tb0 = TVar b0 in
      let open_package tag package lc =
        let vs,phi,env = envfrag_gen_pat count (PCons (tag,[PVar ("x",lc)],lc)) package in
        match env with [_,value] -> vs,phi,value | _ -> assert false in
      (* A single target can also guide abduction from the initial opening.
         In a family, later admissions can require an earlier postcondition.
         The exported predicate must certify the whole family before use. *)
      let admission = match other with
        | Some (After_result (tag,choose)) ->
          let witnesses,prem,value = open_package tag ta0 loc in
          (match choose value with
           | [_,_,_,positive] -> All (witnesses,Impl (prem,positive))
           | _ -> And [])
        | _ -> And [] in
      let packages = ref [] in
      let plain = Eqty (tb0, ta0, loc) in
      let body_scope = if collecting then
          lazy (Entered_let (cn1, ta0, plain, !packages)) :: scope else scope in
      let cn2, (p, _, e2) = aux_cl_in body_scope count gamma tb0 t (p, [], e2) in
      (*[* Format.printf
        "constr_gen-Letin: [%d] generated tb0=%a@ cn2=%a@\np2=%a@ e2=%a@\n%!"
        count pr_ty tb0 pr_cnstrnt cn2 pr_pat p pr_iexpr e2; *]*)
      (* Aiming at: Or of var_name *
          (VarSet.t * cnstrnt * formula * (unit -> unit)) list * cnstrnt *)
      let disjs = List.map
          (fun (i, loc) ->
             let trigger () = elim_extype := (p, Some i) :: !elim_extype in
             let k = Extype i in
             let bs,d_prem,value = open_package k ta0 loc in
             let pcn = constr_gen_pat (PCons (k, [p], loc)) ta0 in
             let entered = Eqty (tb0,value,loc) :: d_prem in
             let again (bs,entered) package keys graph =
               let fresh,post,second = open_package k package loc in
               VarSet.union bs (VarSet.union keys fresh),
               Eqty (tb0,second,loc) :: graph @ post @ entered in
             let bs,entered = match other with
               | Some (Fixed (TCons (tag,_) as second)) when tag=k ->
                 again (bs,entered) second VarSet.empty []
               | Some (Outside_bands (tag,bands)) when tag=k ->
                 (match value with
                  | TCons (n,[r]) when n=numtype ->
                    let vars,phi = outside_bands loc (NumS.num_of r) bands in
                    VarSet.union bs vars, phi @ entered
                  | _ -> bs,entered)
               | Some (After_result (tag,choose)) when tag=k ->
                 List.fold_left (fun context (second,keys,graph,_) ->
                     again context second keys graph) (bs,entered) (choose value)
               | _ -> bs,entered in
             if collecting then packages := (k, entered) :: !packages;
             bs, pcn, entered, trigger)
          !all_ex_types in
      let altcn = A [NotEx (ta0, loc)] in
      let alttr () = elim_extype := (p, None) :: !elim_extype in
      let disjs =
        (VarSet.empty, altcn, [plain], alttr)::disjs in
      (* FIXME: explain in the doc. Change [iexpr] from [int expr]
         to [int list expr]. Exactly one [chi_id] in the list will be
         present in the solution. *)
      (*[* Format.printf
        "constr_gen-Letin: [%d] t=%a@\ndisjs=@ %a@\n%!%!"
        count pr_ty t (pr_sep_list " ∨" (pr_disj_cnstrnt b0)) disjs;
      *]*)
      Ex (vars_of_list (a0::extra_vars), cn_and cn1 (cn_and admission (Or (b0, disjs, cn2)))),
      Letin (docu, p, e1, e2, loc)
    | ExLam (ety_id, cls, loc) ->
      (match !erased_packages with
       | Some ids -> ids := ety_id :: !ids
       | None -> ());
      let a0 = fresh_typ_var () in
      let t0 = TVar a0 in
      let chi_id =
        try Hashtbl.find ex_type_chi ety_id
        with Not_found -> assert false in
      let cn, e = aux gamma t (Lam ((), cls, loc)) in
      let a1 = fresh_typ_var () in
      let t1 = TVar a1 in
      let cn_ex =
        Ex (vars_of_list [a1],
            (A [RetType (t, t0, loc);
                Eqty (t0, TCons (Extype ety_id, [t1]), loc);
                PredVarU (chi_id, t1, loc)])) in
      Ex (vars_of_list [a0], cn_and cn_ex cn),
      e

  and aux_cl_in scope ?(shadowed=false) count gamma t1 t2 ((p, guards, e) as arm) =
    let is_neg = single_assert_false e in
    let t3 = if is_neg then TVar (fresh_typ_var ()) else t1 in
    let guarded_neg = is_neg && guards <> [] in
    let scrutinee = if guarded_neg then t1 else t3 in
    let returns_function = match e with Lam _ -> not shadowed | _ -> false in
    let pcns = constr_gen_pat p (if returns_function then t1 else scrutinee) in
    let bs, prem, env = envfrag_gen_pat count p scrutinee in
    let pcns,bs,prem = match (try Some (List.assq p value_patterns) with Not_found -> None) with
      | None -> pcns,bs,prem
      | Some (name,sorts,bounds) ->
        (* Enforce the datatype head in the ordinary pattern constraint.
           Its indices in the implication are universally quantified exactly
           as for a constructor pattern. The source binds the original value. *)
        let instance () =
          let vs = List.map fresh_var sorts in
          let args = List.map (fun v -> TVar v) vs in
          vars_of_list vs, args, Eqty (TCons (name,args),scrutinee,pat_loc p) in
        let shape,_,required = instance () and vars,args,matched = instance () in
        let facts = NumS.formula_of_sort (List.map (index_bound args (pat_loc p)) bounds) in
        cn_and pcns (Ex (shape,A [required])), VarSet.union bs vars, matched :: facts @ prem in
    (*[* Format.printf "constr_gen-aux_cl: [%d] t1=%a@ t2=%a@ t3=%a@ bs=%a@ prem=%a@\n%!"
      count pr_ty t1 pr_ty t2 pr_ty t3 pr_vars bs pr_formula prem; *]*)
    let gamma' = List.map typ_to_sch env @ gamma in
    let returned = ref (And [], []) in
    let pattern_scope = if collecting then lazy (Evaluated (A prem)) :: scope else scope in
    let body_scope = if not collecting || guards = [] then pattern_scope else
        lazy (let evaluation, tests = !returned in Evaluated (And [evaluation; A tests])) :: pattern_scope in
    let body () = aux_in body_scope gamma' t2 e in
    let eligible = not is_neg && not !force_nodeadcode && !erased_packages = None &&
      erase_bodies <> Keep_bodies && (guards <> [] || count = 0 && refined_pattern p) in
    (* A source assertion keeps its original body and negative obligation.
       It can use the same comparison goals as a proposed exclusion. *)
    let asserted_guard = match e with
      | AssertFalse _ -> guards <> [] && !erased_packages = None
      | _ -> false in
    let proved, require_false = match erase_bodies with
      | Certified_guards (proved, checked, _) -> List.memq arm proved, List.memq arm checked
      | _ -> false, false in
    let erase = eligible && (proved || require_false || impossible_guard prem env guards) in
    let concl, e =
      if not erase then body () else (
        (* Still diagnose unbound names and malformed constructors in the
           body. Its local annotations and assertions do not reach the solver. *)
        let old_preserve = !preserve and old_elims = !elim_extype
        and old_assertions = !uses_pos_assertions in
        let ids = ref [] in
        erased_packages := Some ids;
        ignore (body ());
        erased_packages := None;
        if List.exists (fun id -> List.mem_assoc id !all_ex_types) !ids then
          all_ex_types := List.filter (fun (id, _) -> not (List.mem id !ids)) !all_ex_types;
        preserve := old_preserve;
        elim_extype := old_elims;
        uses_pos_assertions := old_assertions;
        let obligation = if require_false then [CFalse (expr_loc e)] else [] in
        A obligation, AssertFalse (expr_loc e)) in
    let neg_prem =
      if is_neg && not guarded_neg
      then [Eqty (t1, t3, dummy_loc)]
      else [] in
    let (g_as, g_concl, g_cond), checked_guards = fold_map
        (fun (g_as, g_concl, g_cond) (e1,e2) ->
           let a1 = fresh_var Num_sort and a2 = fresh_var Num_sort in
           let cn1,e1 = aux_in pattern_scope gamma' (TCons (numtype, [TVar a1])) e1
           and cn2,e2 = aux_in pattern_scope gamma' (TCons (numtype, [TVar a2])) e2 in
           (add_vars [a1; a2] g_as,
            cn_and (cn_and cn1 cn2) g_concl,
            Terms.A (Num_atom (NumDefs.Leq
                                 (NumDefs.Lin (1,1,a1),
                                  NumDefs.Lin (1,1,a2),
                                  dummy_loc))) :: g_cond),
           (e1,e2))
        (VarSet.empty, And [], []) guards in
    returned := g_concl, g_cond;
    (match erase_bodies with
     | Collect_guards (pending, bounds) when (eligible && not erase) || asserted_guard ->
       let check () =
         let observations = Evaluated g_concl :: List.map Lazy.force pattern_scope in
         let context = lazy (guard_context contracts observations) in
         if not asserted_guard && guards <> [] && (match Lazy.force context with
             | Some (state, _) -> excludes_comparisons state (sep_formulas g_cond).cnj_num
             | None -> false)
         then Already_excluded
         else if List.exists (function Entered_let (_, _, _, _ :: _) -> true | _ -> false) observations
         then (match bounds with
           | Observe_comparisons seen | Prove_complements (seen,_) when asserted_guard ->
             (* Leave source assertions in the ordinary searches. A later
                replay may use a check-only negative at their original site. *)
             seen := true; Keep_arm
           | Observe_comparisons seen ->
             if g_cond <> [] then seen := true;
             Check_with_postconditions None
           | Prove_complements _ | Probe_boundaries _ ->
             Check_with_postconditions (remaining_comparison bounds (Lazy.force context) g_cond))
         else Keep_arm in
       pending := (arm, check) :: !pending
     | _ -> ());
    let checked = impl (neg_prem @ g_cond) concl in
    let checked = match erase_bodies with
      | Certified_guards (_, _, bounds) when List.mem_assq arm bounds ->
        (* Make the failed comparison a conclusion at this opening. All uses
           share its call instance. The original negative remains checked. *)
        (match integer_complement (List.nth g_cond (List.assq arm bounds)) with
         | Some neg -> cn_and (A [Terms.A (Num_atom neg)]) checked
         | None -> checked)
      | _ -> checked in
    let cn = impl prem (cn_and g_concl checked) in
    let cn = if VarSet.is_empty g_as then cn else Ex (g_as, cn) in
    let cn = if VarSet.is_empty bs then cn else All (bs, cn) in
    (*[* Format.printf "constr_gen-aux_cl: [%d]@\ncn=%a@\n%!"
      count pr_cnstrnt cn; *]*)
    let exvs = 
      if is_neg then fvs_typ t3 else VarSet.empty in
    let cn = cn_and pcns cn in
    (if VarSet.is_empty exvs then cn else Ex (exvs, cn)),
    (p, checked_guards, e) in

  let cn = aux_in [] gamma t e in
  cn, elim_extype, !preserve

(* Once a package introduction disappears, regenerate the item's let
   choices so that none can open a package declared only in erased code. *)
let rec with_live_packages mode generate =
  let saved = match mode with Collect_guards (pending, _) -> !pending | _ -> [] in
  let before = !all_ex_types in
  let result = generate () in
  if before == !all_ex_types then result else (
    (match mode with Collect_guards (pending, _) -> pending := saved | _ -> ());
    with_live_packages mode generate)

let live_packages packages = List.filter (fun (i, _) -> List.mem_assoc i !all_ex_types) packages

let gen_expr ~erase_bodies gamma e t =
  with_live_packages erase_bodies (fun () ->
      constr_gen_expr_with_arities ~erase_bodies (Hashtbl.create 2) gamma e t)

let constr_gen_expr gamma e t = gen_expr ~erase_bodies:Keep_bodies gamma e t

let constr_gen_tests ~erase_bodies ~arities gamma tests =
  let elim_cells = ref [] in
  let cns, tests, preserve = split3
      (List.map
         (fun e ->
            let (cn, e), elim_ex, preserve = constr_gen_expr_with_arities ~erase_bodies arities gamma e
                (TCons (booltype, [])) in
            elim_cells := elim_ex :: !elim_cells;
            cn, e, preserve)
         tests) in
  List.fold_left cn_and (And []) cns,
  tests, !elim_cells, List.concat preserve

(* A failed guard can suggest a forbidden interval for an opened result.
   The source operands only guide search. Every exclusion is checked again
   with the original operands and the complete package. *)
let guard_band = function
  | PVar (r,_), guards, _ ->
    let endpoint = function
      | Num (n,_) -> Literal n | Var (x,lc) when x<>r -> Bound_value (x,lc)
      | _ -> raise Not_found in
    let bound = function
      | Var (x,_),u when x=r -> At_most (endpoint u)
      | l,Var (x,_) when x=r -> At_least (endpoint l)
      | _ -> raise Not_found in
    (try match List.map bound guards with
       | [b] -> Some b
       | [At_least l;At_most u] | [At_most u;At_least l] ->
         (match l,u with Literal a,Literal b when a>b -> None | _ -> Some (Between (l,u)))
       | _ -> None
     with Not_found -> None)
  | _ -> None

(* Resolve a guard operand at its lexical occurrence. A numeric argument
   and a local alias of it carry the same observation. An unrelated binder
   hides the outer value, even when the source uses the same spelling. *)
let observed_bands arrow body bands =
  let bindings = Hashtbl.create 8 in
  let rec bind env p ty = match p with
    | PVar (x,_) ->
      let env = List.remove_assoc x env in
      (match ty with None -> env | Some t -> (x,t)::env)
    | PAnd (a,b,_) -> bind (bind env a ty) b ty
    | PCons (tag,ps,_) ->
      (match ty with
       | Some (TCons (n,ts)) when n=tuple && tag=tuple && List.length ps=List.length ts ->
         List.fold_left2 (fun env p t -> bind env p (Some t)) env ps ts
       | _ -> List.fold_left (fun env p -> bind env p None) env ps)
    | One _ | Zero -> env in
  let rec visit env args expr =
    let child = visit env [] in
    match expr with
    | Var (x,lc) -> (match guard_operand env expr with
        | Some (TCons (n,[t])) when n=numtype -> Hashtbl.replace bindings (x,lc) (NumS.num_of t)
        | _ -> ())
    | Lam (_,arms,_) | ExLam (_,arms,_) ->
      let input,tail = match args with a::rest -> a,rest | [] -> None,[] in
      List.iter (fun (p,guards,rhs) ->
          let env = bind env p input in
          List.iter (fun (a,b) -> visit env [] a; visit env [] b) guards;
          visit env tail rhs) arms
    | Letin (_,p,a,b,_) -> child a; visit (bind env p (guard_operand env a)) args b
    | Letrec (_,_,x,a,b,_) -> let env = List.remove_assoc x env in visit env [] a; visit env args b
    | App ((Lam _ as fn),a,_) -> visit env (guard_operand env a :: args) fn; child a
    | App (a,b,_) | NumAdd (a,b,_) -> child a; child b
    | NumCoef (_,a,_) | RuntimeFailure (a,_) -> child a
    | Cons (_,xs,_) -> List.iter child xs
    | AssertLeq (a,b,c,_) | AssertEqty (a,b,c,_) -> child a; child b; visit env args c
    | Num _ | String _ | AssertFalse _ -> () in
  if List.exists (function Between (Literal _,Literal _) | At_least (Literal _) | At_most (Literal _) -> false | _ -> true) bands then
    visit [] (List.map (fun t -> Some t) (arg_types arrow)) body;
  let resolve = function Literal n -> NumDefs.Cst (n,1)
    | Bound_value (x,lc) -> Hashtbl.find bindings (x,lc) in
  map_some (fun band -> try Some (map_band resolve band) with Not_found -> None) bands

let interval_call_key samples signature arrow body bands loc =
  let variable = function
    | TVar v | Alien (Num_term (NumDefs.Lin (1,1,v))) when var_sort v = Num_sort -> Some v
    | _ -> None in
  let numeric phi = (unify ~use_quants:false empty_q phi).cnj_num in
  match List.rev (collect_argtys arrow) with
  | TCons ((Extype _ as tag), actuals) :: args when bands <> [] ->
    let scheme = Hashtbl.find sigma tag in
    let indices = concat_map (function
        | TCons (name,args) -> map_some (fun arg -> match variable arg with
              | Some index -> Some (name,index) | None -> None) args
        | _ -> []) args in
    let inputs = vars_of_list (List.map snd indices) in
    let literals = map_some (function Between (Literal l,Literal u) -> Some (l,u) | _ -> None) bands in
    let before = match actuals, scheme with
      | [actual], (_,post,[TCons (n,[out])],_,[formal]) when n = numtype && literals <> [] ->
        (match variable actual, variable out with
         | Some key, Some result ->
           let package = formal,result,numeric post and pre = numeric signature in
           let sampled () = concat_map (fun (name,index) ->
               if index = key then [] else
               let states = unique_sorted (assoc_all name samples) in
               NumS.fit_interval_calls ~index ~key ~samples:states ~bands:literals ~package pre loc) indices in
           let symbolic () = NumS.symbolic_interval_calls ~inputs:(VarSet.remove key inputs)
               ~key ~bands:literals ~package pre loc in
           [sampled; symbolic]
         | _ -> [])
      | _ -> [] in
    let observed = lazy (observed_bands arrow body bands) in
    let fixed = vars_of_map fvs_typ args in
    let keys = List.filter (fun k -> not (VarSet.mem k fixed))
        (unique_sorted (map_some variable actuals)) in
    let package = lazy (
      let _,post,returns,_,formals = freshen_cns_scheme scheme in
      match returns with
      | [TCons (n,[out])] when n=numtype && List.length formals=List.length actuals &&
          List.for_all (fun t -> typ_sort t=Num_sort) actuals ->
        (match variable out with
         | None -> None
         | Some result when not (List.mem result formals) ->
           let sb = varmap_of_assoc (List.map2 (fun v t -> v,(NumS.num_of t,loc)) formals actuals) in
           Some (result,NumS.subst_num_formula sb (numeric post))
         | Some _ -> None)
      | _ -> None) in
    let guarded band_sets () = match Lazy.force package with
      | None -> []
      | Some (result,post) ->
        let checks = map_some (function Between (lo,hi) -> Some (lo,hi) | _ -> None) (Lazy.force observed) in
        concat_map (fun key -> concat_map (fun bands ->
            NumS.guarded_interval_call ~inputs ~key ~result ~bands ~checks
              ~post (numeric signature) loc) (band_sets checks)) keys in
    (* Try fixed endpoints before choosing a key from the payload of the
       first package. Only a saturated call can use either retry. *)
    let singles = function _::_::_ as bs -> List.map (fun b -> [b]) bs | _ -> [] in
    let paired strategy () = match scheme with
      | _,_,[TCons (n,[_])],_,_ when n=numtype ->
        let pre = numeric signature in
        concat_map (fun key ->
            let endpoints = NumS.interval_endpoints ~inputs ~key pre loc in
            let propose bounds use = Open_at_keys {key;bounds;use} in
            match strategy,endpoints with
            | `Endpoints,Some (lo,hi,defs) -> [propose defs (Endpoints (lo,hi))]
            | (`Hull | `Components),Some (lower,upper,bounds) ->
              (match Lazy.force package with
               | None -> []
               | Some (r,post) ->
                 let probes,graph = if strategy=`Components then
                     NumS.component_keys ~inputs ~key ~result:r ~post pre loc
                   else List.map (fun target_value ->
                       {NumS.target_value;clip_lower=lower;clip_upper=upper})
                       (NumS.refuting_keys ~inputs ~key ~result:r post),[] in
                 let query probes = propose (bounds @ graph) (Result_keys (lower,r,probes)) in
                 List.map (fun p -> query [p]) probes @
                 (match probes with _::_::_ -> [query probes] | _ -> []))
            | _,None -> []) keys
      | _ -> [] in
    let conditional = lazy (NumS.has_conditional_key_bound ~keys (numeric signature)) in
    let on_guard early () = match scheme with
      | _,_,[TCons (n,[_])],_,_ when n=numtype &&
          List.for_all (fun t -> typ_sort t=Num_sort) actuals ->
        if early <> Lazy.force conditional then [] else
        (match unique_sorted (Lazy.force observed) with
         | [] -> [] | bs -> List.map (fun bands -> Exclude_bands bands) (bs :: singles bs))
      | _ -> [] in
    on_guard true ::
    List.map (fun generate () -> List.map (fun phi -> Restrict_calls (NumS.formula_of_sort phi)) (generate ()))
      (before @ [guarded singles; guarded (fun bs -> [bs])]) @
    [paired `Endpoints; paired `Hull; paired `Components; on_guard false]
  | _ -> []

let gen_letrec ~value_patterns ~call_constraints ~erase_bodies ~nonrec gamma x e sig_cn tb tests =
  (* χ is a predicate on one type variable. A written scheme constrains
     the instances χ can admit, and each recursive use instantiates both. *)
  let anchor = match tb, sig_cn with
    | TVar _, [] -> tb
    | _ -> TVar (fresh_typ_var ()) in
  let signature =
    if anchor = tb then [] else Eqty (anchor, tb, expr_loc e) :: sig_cn in
  let a = fresh_typ_var () in
  let chi_id = incr fresh_chi_id; !fresh_chi_id in
  let chi_b = PredVarU (chi_id, anchor, expr_loc e) in
  let chi_a = PredVarU (chi_id, TVar a, expr_loc e) in
  let bvs = VarSet.union (fvs_typ tb) (fvs_formula sig_cn) in
  let anchor_vars = fvs_typ anchor in
  let def_typ =
    VarSet.elements (VarSet.union bvs anchor_vars), chi_b :: signature, tb in
  let gamma =
    if nonrec then gamma else (x, def_typ)::gamma in
  let arities = Hashtbl.create 2 in
  Hashtbl.add arities chi_id (lambda_depth e);
  (* Each recursive occurrence freshens this restriction along with its own
     instance of the written scheme. The declaration and the clients keep
     the full parameter range. *)
  let body_gamma,paired = match call_constraints with
    | Restrict_calls [] -> gamma,None
    | Restrict_calls extra ->
      let vs, phi, t = def_typ in
      let local = VarSet.diff (fvs_formula extra) (vars_of_list vs) in
      (x, (VarSet.elements local @ vs, extra @ phi, t)) :: gamma,None
    | Exclude_bands bands ->
      let tag = match return_type tb with TCons (tag,_) -> tag | _ -> assert false in
      let other sb = Outside_bands (tag,List.map (map_band (NumDefs.hvsubst_term sb)) bands) in
      gamma,Some (def_typ,def_typ,other)
    | Open_at_keys query ->
      let lc = expr_loc e in
      let instance sb k =
        let rename = VarMap.add query.key k sb in
        let arrow = hvsubst_typ rename tb and id = fresh_typ_var () in
        let required = PredVarU (chi_id,TVar id,lc) :: Eqty (TVar id,arrow,lc) ::
            hvsubst_formula rename sig_cn in
        arrow,id,required in
      let graph = NumS.formula_of_sort query.bounds in
      let tag = match return_type tb with TCons (tag,_) -> tag | _ -> assert false in
      (match query.use with
       | Endpoints (lower,upper) ->
         let endpoint term =
           let k = fresh_num_var () in
           let arrow,_,phi = instance VarMap.empty k in
           arrow, Eqty (TVar k,num term,lc)::phi in
         let first,p = endpoint lower and second,q = endpoint upper in
         let phi = graph @ p @ q in
         let vs = VarSet.elements (fvs_formula phi) in
         gamma,Some (def_typ,(vs,phi,first),fun sb -> Fixed (hvsubst_typ sb (return_type second)))
       | Result_keys (lower,r,targets) ->
         let terms = concat_map (fun p -> [p.NumS.target_value;p.NumS.clip_lower;p.NumS.clip_upper]) targets in
         let other sb =
           let choose = function
             | TCons (n,[observed]) when n=numtype ->
               List.map (fun target ->
                   let k,keys,graph = selected_key sb r target (NumS.num_of observed) in
                   let arrow,id,positive = instance sb k in
                   let graph = NumS.formula_of_sort graph in
                   return_type arrow, keys, graph, Ex (VarSet.add id keys,A (graph @ positive))) targets
             | _ -> assert false in
           After_result (tag,choose) in
         let primary = Eqty (TVar query.key,num lower,lc) :: chi_b :: signature @ graph in
         let vs = VarSet.union (fvs_formula primary) (VarSet.remove r (vars_of_map NumDefs.fvs_term terms)) in
         gamma,Some (def_typ,(VarSet.elements vs,primary,tb),other)) in
  let (expr_cn, e), elim_cell, preserve =
    constr_gen_expr_with_arities ?paired ~value_patterns ~erase_bodies arities body_gamma e anchor in
  let def_cn =
    let body = if signature = [] then expr_cn
      else cn_and (Ex (bvs, A signature)) expr_cn in
    All (anchor_vars, Impl ([chi_b], body)) in
  let test_cn, tests, elim_cells, more_preserve =
    constr_gen_tests ~erase_bodies ~arities gamma tests in
  chi_id, def_typ,
  cn_and def_cn (cn_and (Ex (vars_of_list [a], A [chi_a])) test_cn),
  e, tests, elim_cell::elim_cells, more_preserve @ preserve

let constr_gen_letrec ?(value_patterns=[]) ?(call_constraints=Restrict_calls []) ~erase_bodies ?(nonrec=false) gamma x e sig_cn tb tests =
  with_live_packages erase_bodies (fun () -> gen_letrec ~value_patterns ~call_constraints ~erase_bodies ~nonrec gamma x e sig_cn tb tests)

let constr_gen_let ~erase_bodies gamma p e ta =
  let pcns = constr_gen_pat p ta in
  let bs, exphi, env = envfrag_gen_pat 0 p ta in
  let (cn, e), elim_cell, preserve = gen_expr ~erase_bodies gamma e ta in
  bs, exphi, env, cn_and pcns cn,
  (p, e), elim_cell, preserve

type solution =
  quant_ops * Terms.formula *
    (int * (Defs.var_name list * Terms.formula)) list

type solver = uses_pos_assertions:bool -> new_ex_types:(int * loc) list ->
  preserve:VarSet.t -> cnstrnt -> solution

type program = ((int * Defs.loc) list * Terms.struct_item) list

(* Native overflow can invalidate the index of a value before it reaches a
   constructor, including through a call in a later item. Float conversion
   and custom numeral representations can also change comparisons. *)
let can_erase_guarded_bodies prog =
  let rec exact = function
    | NumAdd _ | NumCoef _ -> false
    | Var _ | Num _ | String _ | AssertFalse _ -> true
    | App (a,b,_) | Letrec (_,_,_,a,b,_) | Letin (_,_,a,b,_) -> exact a && exact b
    | Cons (_,args,_) -> List.for_all exact args
    | Lam (_,arms,_) | ExLam (_,arms,_) -> List.for_all (fun (_,guards,body) ->
        exact body && List.for_all (fun (a,b) -> exact a && exact b) guards) arms
    | RuntimeFailure (e,_) -> exact e
    | AssertLeq (a,b,e,_) | AssertEqty (a,b,e,_) -> exact a && exact b && exact e in
  List.for_all (function
    | _, LetRecVal (_,_,body,_,tests,_) -> exact body && List.for_all exact tests
    | _, LetVal (_,_,body,_,_) -> exact body
    | _ -> true) prog

let infer_prog_mockup (prog : program) =
  let erase_bodies = if can_erase_guarded_bodies prog then Direct_guards else Keep_bodies in
  let gamma = ref [] in
  let cns = List.map (function
    | _, TypConstr _ -> [], VarSet.empty, And []
    | _, PrimTyp _ -> [], VarSet.empty, And []
    | _, ValConstr _ ->
      [], VarSet.empty, And []
    | _, PrimVal (docu, x, tsch, ext_def, loc) ->
      gamma := (x, tsch) :: !gamma;
      [], VarSet.empty, And []
    | new_ex_types,
      (LetRecVal (docu, x, e, defsig, tests, loc) as it) ->
      let bvs, sig_cn, t = match defsig with
        | None ->
          let b = fresh_typ_var () in
          let tb = TVar b in
          [b], [], tb
        | Some (vs, phi, t) -> vs, phi, t in
      let preserve = VarSet.union (fvs_typ t) (fvs_formula sig_cn) in
      let nonrec = match it with LetVal _ -> true | _ -> false in
      let chi_id, typ_sch, cn, e, tests, elim_cells, more_preserve =
        constr_gen_letrec ~erase_bodies ~nonrec !gamma x e sig_cn t tests in
      gamma := (x, typ_sch) :: !gamma;
      new_ex_types, add_vars more_preserve preserve, cn
    | new_ex_types,
      (LetVal (docu, PVar (x, _), e, defsig, loc) as it) ->
      let bvs, sig_cn, t = match defsig with
        | None ->
          let b = fresh_typ_var () in
          let tb = TVar b in
          [b], [], tb
        | Some (vs, phi, t) -> vs, phi, t in
      let preserve = VarSet.union (fvs_typ t) (fvs_formula sig_cn) in
      let nonrec = match it with LetVal _ -> true | _ -> false in
      let chi_id, typ_sch, cn, e, tests, elim_cells, more_preserve =
        constr_gen_letrec ~erase_bodies ~nonrec !gamma x e sig_cn t [] in
      gamma := (x, typ_sch) :: !gamma;
      (*[* Format.printf "LetRecVal: mock x=%s@\ncn=%a@\n%!" x
        pr_cnstrnt cn; *]*)
      new_ex_types, add_vars more_preserve preserve, cn
    | new_ex_types, LetVal (docu, p, e, defsig, loc) ->
      let avs, sig_vs, sig_cn, t = match defsig with
        | None ->
          let a = fresh_typ_var () in
          let ta = TVar a in
          VarSet.singleton a, [], [], ta
        | Some (vs, phi, t) -> VarSet.empty, vs, phi, t in
      let bs, exphi, env, cn, cl, elim_cell, preserve =
        constr_gen_let ~erase_bodies !gamma p e t in
      let preserve = add_vars preserve
        (VarSet.union (fvs_typ t)
           (VarSet.union (fvs_formula sig_cn) (fvs_formula exphi))) in
      let cn = impl sig_cn cn in
      let cn =
        if sig_vs <> [] then All (vars_of_list sig_vs, cn) else cn in
      (*[* Format.printf "LetVal: mock p=%a@\ninit_cn=%a@\n%!" pr_pat p
        pr_cnstrnt cn; *]*)
      (* WARNING: dropping constraints on introduced variables *)
      (* FIXME: Why is everything a postcondition? *)
      let typ_sch_ex =
        if VarSet.is_empty bs && exphi = []
        then fun (x, res) -> x, ([], [], res)
        else fun (x, res) ->
          let vs = VarSet.union (fvs_formula exphi) (fvs_typ res) in
          let resvs = VarSet.elements (VarSet.diff vs bs) in
          let targs = List.map (fun v -> TVar v) resvs in
          let ety_id = incr extype_id; !extype_id in
          let ety_cn = Extype ety_id in
          let ety = TCons (ety_cn, targs) in
          let ex_sch = VarSet.elements vs, exphi, [res], ety_cn, resvs in
          Hashtbl.add sigma ety_cn ex_sch;
          all_ex_types := (ety_id, loc) :: !all_ex_types;
          (*[* Format.printf
            "infer_mockup-LetVal-ex_types: id=%d@ exphi=%a@ ty=%a@\n%!"
            ety_id pr_formula exphi pr_ty res;
          *]*)
          x, ([], [], ety) in
      gamma := map_append typ_sch_ex env !gamma;
      new_ex_types, preserve, cn
  ) prog in
  List.fold_right
    (fun (extys, pres, cn) (extys_acc, pres_acc, cn_acc) ->
      live_packages extys @ extys_acc, VarSet.union pres pres_acc, cn_and cn cn_acc)
    cns ([], VarSet.empty, And [])

let annotate_expr q res_sb chi_sb nice_sb e : texpr =
  let typ_sch nice_sb ns =
    let _, ans =
      try List.find (fun (k,_) -> List.mem k ns) chi_sb
      with Not_found -> assert false in
    (*[* Format.printf
      "annotate_expr-typ_sch: ans=@ %a@\n%!" pr_ans ans; *]*)
    let nice_sb, (vs, phi) = nice_ans ~sb:nice_sb ans in
    (*[* Format.printf
      "annotate_expr-typ_sch: phi=@ %a@\n%!" pr_formula phi; *]*)
    let sb, phi =
      separate_subst ~bvs:(vars_of_list vs) ~apply:true q phi in
    (*[* Format.printf
      "annotate_expr-typ_sch: sb=@ %a@\n%!" pr_subst sb; *]*)
    let res, _ = VarMap.find delta sb in
    let vs = VarSet.inter
        (VarSet.union (fvs_formula phi) (fvs_typ res))
        (vars_of_list vs) in
    vs, nice_sb, (VarSet.elements vs, phi, res) in
  let rec aux nice_sb : iexpr -> (VarSet.t * texpr) = function
    | (Var _ | Num _ | String _) as e -> VarSet.empty, e
    | Cons (n, args, lc) ->
      let evs, args = List.split (List.map (aux nice_sb) args) in
      List.fold_left VarSet.union VarSet.empty evs,
      Cons (n, args, lc)
    | NumAdd (e1, e2, lc) ->
      let evs1, e1 = aux nice_sb e1
      and evs2, e2 = aux nice_sb e2 in
      VarSet.union evs1 evs2,
      NumAdd (e1, e2, lc)
    | NumCoef (x, e, lc) ->
      let evs, e = aux nice_sb e in
      evs, NumCoef (x, e, lc)
    | App (e1, e2, lc) ->
      let evs1, e1 = aux nice_sb e1
      and evs2, e2 = aux nice_sb e2 in
      VarSet.union evs1 evs2,
      App (e1, e2, lc)
    | Lam (ann, cls, lc) ->
      let evs, cls = List.split (List.map (aux_cl nice_sb) cls) in
      let evs = List.fold_left VarSet.union VarSet.empty evs in
      let ann =
        if match cls with
          | [p,_,e] -> !annotating_letin && not (single_assert_false e)
          | _ -> !annotating_fun
        then
          let a1, a2 = match ann with
            | [pair] -> pair
            | _ -> List.find
                (fun (a, b) -> VarMap.mem a res_sb && VarMap.mem b res_sb) ann in
          (* An unconstrained representative (e.g. the argument of a packed
             identity function) is absent from the solved substitution. *)
          let ann_type a = hvsubst_typ nice_sb (subst_typ res_sb (TVar a)) in
          Some (ann_type a1, ann_type a2)
        else None in
      evs, Lam (ann, cls, lc)
    | ExLam (k, cls, lc) ->
      let evs, cls = List.split (List.map (aux_cl nice_sb) cls) in
      List.fold_left VarSet.union VarSet.empty evs,
      ExLam (k, cls, lc)
    | Letrec (docu, ns, x, e1, e2, lc) ->
      let vs, nice_sb, tysch = typ_sch nice_sb ns in
      let evs1, e1 = aux nice_sb e1
      and evs2, e2 = aux nice_sb e2 in
      let evs = VarSet.union evs1 evs2 in
      VarSet.diff evs vs,
      Letrec (docu, (tysch, not (VarSet.is_empty evs)), x, e1, e2, lc)
    | Letin (docu, p, e1, e2, lc) ->
      let evs1, e1 = aux nice_sb e1
      and evs2, e2 = aux nice_sb e2 in
      VarSet.union evs1 evs2,
      Letin (docu, p, e1, e2, lc)
    | AssertFalse lc -> VarSet.empty, AssertFalse lc
    | RuntimeFailure (e, lc) ->
      let evs, e = aux nice_sb e in
      evs, RuntimeFailure (e, lc)
    | AssertLeq (e1, e2, e3, lc) ->
      let evs1, e1 = aux nice_sb e1
      and evs2, e2 = aux nice_sb e2
      and evs3, e3 = aux nice_sb e3 in
      VarSet.union evs1 (VarSet.union evs2 evs3),
      AssertLeq (e1, e2, e3, lc)
    | AssertEqty (e1, e2, e3, lc) ->
      let evs1, e1 = aux nice_sb e1
      and evs2, e2 = aux nice_sb e2
      and evs3, e3 = aux nice_sb e3 in
      VarSet.union evs1 (VarSet.union evs2 evs3),
      AssertEqty (e1, e2, e3, lc)
  and aux_cl nice_sb (p, guards, e) =
    let evs, e = aux nice_sb e in
    let evs, guards = fold_map
        (fun evs (e1,e2) ->
           let evs1, e1 = aux nice_sb e1
           and evs2, e2 = aux nice_sb e2 in
           VarSet.union evs (VarSet.union evs1 evs2),
           (e1, e2))
        evs guards in
    evs, (p, guards, e) in
  snd (aux nice_sb e)
    
let prepare_scheme phi res =
  let rvs = fvs_typ res in
  let phi = List.filter
      (fun a -> not (VarSet.is_empty (VarSet.inter rvs (fvs_atom a))))
      phi in
  let vs = fvs_formula phi in
  VarSet.union vs rvs, phi

let recursive_answer bvs loc chi_id (q,residual,predicates) =
  let nice_sb,(vs,phi) = nice_ans (List.assoc chi_id predicates) in
  let bound = vars_of_list (vs @ bvs) in
  let sb_res,_ = separate_subst ~bvs:bound ~apply:true q residual in
  let more_sb,phi = separate_subst ~bvs:bound ~apply:true q phi in
  let sb = update_sb ~more_sb sb_res in
  let res,_ = VarMap.find delta sb in
  let free = VarSet.elements (VarSet.union (fvs_formula phi) (fvs_typ res)) in
  let escaping,gvs = List.partition (fun v -> not (List.mem v vs) && q.uni_v v) free in
  if escaping <> [] then raise (Report_toplevel
      ("Escaping local variables "^String.concat ", " (List.map var_str escaping),Some loc));
  nice_sb,sb_res,sb,(gvs,phi,res)

let numeric_admission phi = List.map (function
    | Terms.A (Num_atom a) -> a
    | Eqty (a,b,lc) when typ_sort a=Num_sort && typ_sort b=Num_sort ->
      NumDefs.Eq (NumS.num_of a,NumS.num_of b,lc)
    | _ -> raise Not_found) phi

(* A direct recursive constructor allocates one node. Each recursive field
   opens that same node at its own indices. Hidden witnesses or other fields
   require a separate construction. *)
let recursive_value_signature self = function
  | Cons (tag,(_::_ as args),loc) when Hashtbl.mem sigma tag && List.for_all (function
        Var (x,_) -> x=self | _ -> false) args ->
    let _,phi,fields,name,params = freshen_cns_scheme (Hashtbl.find sigma tag) in
    let interface = vars_of_list params in
    if VarSet.cardinal interface<>List.length params || List.length fields<>List.length args ||
       not (List.for_all (fun v -> var_sort v=Num_sort) params) then None else
    (try
       let guard = numeric_admission phi in
       let fields = List.map (function
           | TCons (child,ts) when child=name && List.length ts=List.length params &&
               List.for_all (fun t -> typ_sort t=Num_sort && VarSet.subset (fvs_typ t) interface) ts ->
             List.map NumS.num_of ts
           | _ -> raise Not_found) fields in
       if not (VarSet.subset (NumDefs.fvs_formula guard) interface) then None else
       match NumS.affine_cycle_guard ~params ~guard ~fields loc with
       | NumS.Outside_directions -> None
       | NumS.Empty_cycle -> raise (NoAnswer (Num_sort,
           "No index satisfies every unfolding of this recursive constructor value",None,loc))
       | NumS.Cycle_guard domain ->
         Some (NumS.formula_of_sort domain, TCons (name,List.map (fun v->TVar v) params))
     with Not_found -> None)
  | _ -> None

(* The returned value must be instantiable at every index of the proposed
   cycle domain. A fresh copy of the inferred variables supplies its witnesses. *)
let covers_cycle (guard,ty) inferred loc =
  let vs,actual,result = freshen_val_scheme inferred in
  match ty,result with
  | TCons (name,params), TCons (other,terms) when name=other &&
      List.length params=List.length terms && List.for_all (fun t -> typ_sort t=Num_sort) terms ->
    (try
       let equalities = List.map2 (fun p t -> NumDefs.Eq (NumS.num_of p,NumS.num_of t,loc))
           params terms in
       NumS.common_result_possible ~keys:(fvs_typ ty) ~witnesses:(vars_of_list vs)
         ~admissions:[numeric_admission guard] ~post:(equalities @ numeric_admission actual) []
     with Not_found | Contradiction _ -> false
        | Failure msg when msg = "int_of_big_int" -> false)
  | _ -> false

(* A first-order input with constructor heads and bare index variables
   determines a ground substitution for every hole it exposes. Align those
   holes bijectively before comparing the two complete public contracts. *)
let strictly_broader_guard (vs,old_guard,old_ty) (ws,new_guard,new_ty) =
  let variable = function
    | TVar v | Alien (Num_term (NumDefs.Lin (1,1,v))) -> Some v
    | _ -> None in
  let rec align (forward,backward as maps) a b =
    match variable a, variable b, a, b with
    | Some v, Some w, _, _ when var_sort v = var_sort w ->
      if (VarMap.mem w forward && VarMap.find w forward <> v) ||
         (VarMap.mem v backward && VarMap.find v backward <> w) then raise Not_found;
      VarMap.add w v forward, VarMap.add v w backward
    | _,_,TCons (CNam c,args),TCons (CNam d,other)
      when c=d && List.length args=List.length other ->
      List.fold_left2 align maps args other
    | _,_,Alien (Num_term (NumDefs.Cst _)),_ when a=b -> maps
    | _ -> raise Not_found in
  try
    let a = arg_types old_ty and b = arg_types new_ty in
    if a=[] || List.length a<>List.length b then false else
    let forward,backward = List.fold_left2 align (VarMap.empty,VarMap.empty) a b in
    VarSet.equal (vars_of_list vs) (varmap_domain backward) &&
    VarSet.equal (vars_of_list ws) (varmap_domain forward) &&
    VarSet.subset (fvs_formula old_guard) (vars_of_list vs) &&
    VarSet.subset (fvs_formula new_guard) (vars_of_list ws) &&
    hvsubst_typ forward (return_type new_ty) = return_type old_ty &&
    let old = numeric_admission old_guard
    and fresh = numeric_admission (hvsubst_formula forward new_guard) in
    match NumS.satisfiable old, NumS.satisfiable fresh with
    | Right old_state, Right new_state ->
      NumS.implies_cnj old_state fresh && not (NumS.implies_cnj new_state old)
    | _ -> false
  with Not_found | Contradiction _ -> false

(* A recursive occurrence instantiates the quantified variables of the written
   scheme. When their projection fits in a scheme predicate, give that domain
   directly to the abducer. Replay still checks the original signature. *)
let project_call_signature bound signature arrow =
  let vars = VarSet.diff (VarSet.inter (vars_of_list bound) (fvs_formula signature))
      (fvs_typ arrow) in
  if VarSet.is_empty vars then signature else
  try match NumS.project_exists ~vars (numeric_admission signature) with
    | [phi] -> NumS.formula_of_sort phi
    | _ -> signature
  with Not_found -> signature
     | Failure msg when msg = "int_of_big_int" -> signature

(* A fresh typing must match every numeric position of the arrow. Each scheme
   may choose its own quantified witnesses for that tuple. *)
let check_key_admission ~integer_target policy bound signature written inferred loc =
  let open NumDefs in
  let eq a b = Eq (a,b,loc) and v x = Lin (1,1,x) in
  let rec align left right = match left,right with
    | _ when typ_sort left=Num_sort && typ_sort right=Num_sort ->
      [NumS.num_of left,NumS.num_of right]
    | Fun (a,b),Fun (c,d) -> align a c @ align b d
    | TCons (a,xs),TCons (b,ys) when a=b && List.length xs=List.length ys ->
      List.concat (List.map2 align xs ys)
    | TVar a,TVar b when var_sort a=var_sort b -> []
    | _ -> raise Not_found in
  try
    let inferred_bound,actual,arrow = freshen_val_scheme inferred in
    let decl = numeric_admission signature and actual = numeric_admission actual in
    let args t = TCons (tuple,arg_types t) in
    let package = return_type written in
    let inputs = align (args arrow) (args written) and outputs = align (return_type arrow) package in
    let positions = inputs @ outputs in
    let original = List.map (fun (a,b) -> eq a b) positions @ actual @ decl in
    let input_slots = List.map (fun _ -> fresh_num_var ()) inputs
    and output_slots = List.map (fun _ -> fresh_num_var ()) outputs in
    let slots = input_slots @ output_slots in
    let domain bound terms phi =
      let bound = vars_of_list bound in
      let aliases = List.fold_left2 (fun sb term slot -> match term with
          | Lin (1,1,x) when VarSet.mem x bound && not (VarMap.mem x sb) ->
            VarMap.add x slot sb
          | _ -> sb) VarMap.empty terms slots in
      let matches = List.fold_left2 (fun phi term slot ->
          let term = hvsubst_term aliases term in
          if term=v slot then phi else eq term (v slot) :: phi) [] terms slots in
      NumS.project_exists ~vars:(VarSet.diff bound (varmap_domain aliases))
        (matches @ List.map (hvsubst_atom aliases) phi) in
    let inferred_terms,written_terms = List.split positions in
    let actual_cells = domain inferred_bound inferred_terms actual in
    let written_cells = domain bound written_terms decl in
    let cells = concat_map (fun a -> List.map (fun b -> a @ b) written_cells) actual_cells in
    let tag = match package with TCons (tag,_) -> tag | _ -> raise Not_found in
    let open_package at =
      let vars,prem,env = envfrag_gen_pat 0 (PCons (tag,[PVar ("x",loc)],loc)) at in
      match env with
      | [_,TCons (n,[t])] when n=numtype ->
        vars,NumS.num_of t,(unify ~use_quants:false empty_q prem).cnj_num
      | _ -> raise Not_found in
    match policy with
    | Restrict_calls _ -> assert false
    | Exclude_bands bands ->
      ignore (NumS.satisfiable_exn original);
      let _,observed,opened = open_package package in
      let candidate = TCons (tag,List.map (fun slot -> TVar slot) output_slots) in
      let witnesses,value,post = open_package candidate in
      let post = eq observed value :: post and keys = vars_of_list output_slots in
      let same_inputs = List.map2 (fun slot (_,term) -> eq (v slot) term) input_slots inputs in
      let facts = original @ opened @ same_inputs in
      let integer_result = if integer_target then Some observed else None in
      (* A paired opening follows a fully applied call. Only an actual Num
         argument, or a Num component of an actual tuple, supplies a native
         value here. Numeric parameters inside an abstract type can be phantom. *)
      let rec native_values = function
        | TCons (n,[t]) when n=numtype -> [NumS.num_of t]
        | TCons (n,ts) when n=tuple -> concat_map native_values ts
        | _ -> [] in
      let integer_inputs = if integer_target then concat_map native_values (arg_types written)
        else [] in
      let refuted band =
        let inside = match band with
          | At_least lo -> [Leq (lo,observed,loc)]
          | At_most hi -> [Leq (observed,hi,loc)]
          | Between (lo,hi) -> [Leq (lo,observed,loc); Leq (observed,hi,loc)] in
        not (NumS.common_result_possible ?integer_result ~integer_inputs ~keys ~witnesses
               ~admissions:cells ~post (inside @ facts)) in
      if List.for_all refuted bands then Admitted else Unavailable
    | Open_at_keys query ->
      let original = original @ query.bounds in
      let admission k =
        let replace = hvsubst_term (VarMap.singleton query.key k) in
        let sb,bindings = List.fold_left2 (fun (sb,phi) slot term -> match replace term with
            | Lin (1,1,x) -> VarMap.add slot x sb,phi
            | term -> let x = fresh_num_var () in VarMap.add slot x sb,eq (v x) term :: phi)
            (VarMap.empty,[]) slots written_terms in
        bindings,List.map (List.map (hvsubst_atom sb)) cells in
      let check ?(vacuous=false) k extra =
        let bindings,goals = admission k in
        let pre = original @ extra @ bindings in
        match NumS.satisfiable pre,goals with
        | Left _,_ -> vacuous
        | Right state,[goal] -> NumS.implies_cnj state goal
        | Right _,alternatives ->
          let impossible = [eq (Cst (0,1)) (Cst (1,1))] in
          not (NumS.conditional_satisfiable pre
                 (List.map (fun goal -> goal,impossible) alternatives)) in
      let lower = match query.use with Endpoints (lo,_) | Result_keys (lo,_,_) -> lo in
      let first = fresh_num_var () in
      let initial = [eq (v first) lower] in
      if not (check first initial) then Unavailable else
      let opening key =
        let _,value,post = open_package (hvsubst_typ (VarMap.singleton query.key key) package) in
        value,post in
      (match query.use with
       | Endpoints (_,upper) ->
         let high = fresh_num_var () in
         if check high [eq (v high) upper] then Admitted else Unavailable
       | Result_keys (lower,r,targets) ->
         let observed,opened = opening first in
         let queries = List.map (fun target ->
             let k,_,graph = selected_key VarMap.empty r target observed in
             target,k,graph) targets in
         let extend facts (_,k,graph) =
           let value,post = opening k in
           eq observed value :: graph @ post @ facts in
         (* Only already admitted typings may supply facts for a later round.
            Fresh openings share their result and retain their private witnesses. *)
         let rec certify facts keep pending =
           let ready,rest = List.partition (fun (_,k,graph) ->
               check ~vacuous:true k (graph @ facts)) pending in
           if rest=[] then Admitted else if ready=[] then
             (match keep with _::_::_ -> Retry_keys {query with use=Result_keys (lower,r,keep)}
              | _ -> Unavailable)
           else
             let keep = List.rev_append (List.map (fun (t,_,_) -> t) ready) keep in
             certify (List.fold_left extend facts ready) keep rest in
         certify (initial @ opened) [] queries)
  with Not_found | Terms.Contradiction _ -> Unavailable
     | Failure msg when msg = "int_of_big_int" -> Unavailable

let infer_prog ?(integer_target=false) ?check_excluded solver prog =
  let value_families = lazy (try constructor_value_bounds prog with
      Failure msg when msg = "int_of_big_int" -> []) in
  let check_guards = integer_target && not !force_nodeadcode && can_erase_guarded_bodies prog in
  let search_item bounds packages generate =
    let run mode =
      uses_pos_assertions := false;
      let cn, preserve, data = generate mode in
      let packages = live_packages packages in
      let solver = match mode, check_excluded with
        | Certified_guards (_, (_ :: _ as checked), _), Some check ->
          check (List.map (fun (_, _, body) -> expr_loc body) checked)
        | _ -> solver in
      let solution = solver ~uses_pos_assertions:!uses_pos_assertions
          ~new_ex_types:packages ~preserve cn in
      data, packages, solution in
    if not check_guards then run Keep_bodies else
    let pending = ref [] in
    try run (Collect_guards (pending, bounds)) with
    | (NoAnswer (_, msg, _, _) | Contradiction (_, msg, _, _)) as original
      when msg <> "Answers do not converge" ->
      let proved, proposals = List.fold_right (fun (arm, check) (proved, rest) ->
          match check () with
          | Already_excluded -> arm :: proved, rest
          | Check_with_postconditions i -> proved, (arm, i) :: rest
          | Keep_arm -> proved, rest) !pending ([], []) in
      (* Check the package postcondition at each proposed exclusion, with
         the original guard operands and opening witnesses in scope. *)
      let unresolved = List.map fst proposals in
      (match bounds with
       | Prove_complements (_,bands) | Probe_boundaries bands -> bands := unique_sorted (map_some guard_band unresolved @ !bands)
       | _ -> ());
      let choices = (if proved = [] then [] else [[]]) @
          (match unresolved with
           | [] -> []
           | [_] -> [unresolved]
           | _ -> unresolved :: List.map (fun guard -> [guard]) unresolved) in
      let rec retry = function
        | [] -> raise original
        | checked :: rest ->
          let before = !all_ex_types in
          let comparisons = map_some (fun arm -> match List.assq arm proposals with
              | Some i -> Some (arm, i) | None -> None) checked in
          let repeated = match bounds with
            | Observe_comparisons _ -> false
            | Prove_complements _ -> comparisons = []
            | Probe_boundaries _ -> comparisons = [] &&
              not (List.exists (function _, _, AssertFalse _ -> true | _ -> false) checked) in
          if repeated then retry rest else
          try run (Certified_guards (proved, checked, comparisons)) with exn ->
            all_ex_types := before;
            match exn with
            | NoAnswer (_, _, _, loc) | Contradiction (_, _, _, loc) ->
              (* When the solver identifies one of our negative goals, put
                 its original body back and keep checking the other goals. *)
              let keep = List.filter (fun (_, _, e) -> expr_loc e <> loc) checked in
              if List.length keep > 1 && List.length keep < List.length checked
              then retry (keep :: rest) else retry rest
            | _ -> raise exn in
      retry choices in
  let solve_item ?(propose_call=(fun _ -> [])) ?(admitted=(fun _ _ -> Admitted)) packages e tests generate =
    let initial_packages = !all_ex_types in
    let search ?(call_constraints=Restrict_calls []) bounds =
      let run (e, tests) = search_item bounds packages (generate e tests call_constraints) in
      let initial = e, tests in
      NumS.with_affine_retry (fun () ->
        all_ex_types := initial_packages;
        try run initial with
        | (NoAnswer (_, msg, _, _) | Contradiction (_, msg, _, _)) as original ->
          let rec retry input = function
            | [] -> raise original
            | rewrite :: rest ->
              match rewrite (fst input) (snd input) with
              | None -> retry input rest
              | Some candidate ->
                (* A failed search may have erased a local declaration. *)
                all_ex_types := initial_packages;
                try run candidate with exn ->
                  all_ex_types := initial_packages;
                  match exn with
                  | NoAnswer _ | Contradiction _ -> retry candidate rest
                  | _ -> raise exn in
          let placements = if msg = "Answers do not converge" then [] else [branch_packages] in
          retry initial (placements @ [name_consumed_matches])) in
    NumS.with_joint_retry (fun () ->
      let seen = ref false in
      try search (Observe_comparisons seen) with
      | (NoAnswer _ | Contradiction _) as original when !seen ->
        let ambiguous = ref false and bands = ref [] in
        let try_proposals failed =
          let saved = List.map (fun (i,_) -> Extype i, Hashtbl.find sigma (Extype i)) packages in
          let rec try_keys candidates groups = match candidates, groups with
            | [], [] -> raise failed
            | [], next::rest -> try_keys (next ()) rest
            | call_constraints::rest, _ ->
              let candidate = try Some (search ~call_constraints (Observe_comparisons (ref false)))
                with NoAnswer _ | Contradiction _ -> None in
              (match candidate with
               | None -> try_keys rest groups
               | Some answer ->
                 match admitted call_constraints answer with
                 | Admitted -> answer
                 | retry ->
                   (* Restore the schemes installed for this tentative answer.
                      Every reduced family gets a new solve and admission check. *)
                   List.iter (fun (tag,scheme) -> Hashtbl.replace sigma tag scheme) saved;
                   all_ex_types := initial_packages;
                   let next = match retry with Retry_keys q -> Open_at_keys q :: rest | _ -> rest in
                   try_keys next groups) in
          try_keys [] (propose_call !bands) in
        (try
           try search (Prove_complements (ambiguous,bands)) with
           | (NoAnswer _ | Contradiction _) as failed ->
             (* A failed one-sided comparison can also need a different call
                typing. Boundary probes resolve ambiguity between comparisons. *)
             if not !ambiguous then try_proposals failed else
             (try search (Probe_boundaries bands) with
              | (NoAnswer _ | Contradiction _) as probed -> try_proposals probed)
         with exn ->
           all_ex_types := initial_packages;
           match exn with
           | NoAnswer _ | Contradiction _ -> raise original
           | Failure msg when msg = "int_of_big_int" -> raise original
           | _ -> raise exn)) in
  let ntime = ref (Sys.time ()) in
  let start_time = !ntime in
  let gamma = ref builtin_gamma in
  (*[* Format.printf "infer_prog: start time=%.2f@\n%!" start_time; *]*)
  let update_new_ex_types q new_ex_types sb sb_chi =
    let more_items = ref [] in
    (* FIXME: possibly duplicate with code at the end of [solve].  Clean up
       handling of ex. type parameters. *)
    List.iter
      (fun (ety_id, loc) ->
         let vs, phi, ty, ety_n, pvs =
           Hashtbl.find sigma (Extype ety_id) in
         let nice_sb, (vs, phi) =
           nice_ans ~fvs:(fvs_typ (TCons (tuple,ty))) (vs, phi) in
         let pvs = List.map
             (fun v -> try VarMap.find v nice_sb with Not_found -> v)
             pvs in
         let ty = List.map (hvsubst_typ nice_sb) ty in
         (*[* Format.printf
           "infer-update-ex_types: from id=%d@ phi=%a@ ty=%a@\n%!"
           ety_id pr_formula phi pr_ty (List.hd ty);
         *]*)
         let extydec =
           ITypConstr (None, ety_n, List.map var_sort pvs, loc) in
         let sb, phi =
           separate_subst ~bvs:(vars_of_list vs) ~apply:true q phi in
         let ty = List.map (subst_typ sb) ty in
         let pvs = List.map
             (fun v -> try fst (VarMap.find v sb) with Not_found -> TVar v)
             pvs in
         let vs = VarSet.inter
             (VarSet.union (fvs_formula phi) (fvs_typ (TCons (tuple, ty))))
             (vars_of_list vs) in
         let extydef = IValConstr
             (None, ety_n, VarSet.elements vs, phi, ty, ety_n, pvs, loc) in
         more_items := extydec :: extydef :: !more_items)
      new_ex_types;
    !more_items in
  let constructor_samples = ref [] in
  let items : annot_item list = concat_map
      (function
        | _, TypConstr (docu, n, sorts, lc) ->
          [ITypConstr (docu, n, sorts, lc)]
        | _, PrimTyp (docu, n, sorts, expansion, lc) ->
          [IPrimTyp (docu, n, sorts, expansion, lc)]
        | _, ValConstr (docu, name, vs, phi, args, c_n, c_args, lc) ->
          let sb, phi =
            separate_subst ~bvs:(vars_of_list vs) ~apply:true empty_q phi in
          (*[* Format.printf "ValConstr: n=%s@ sb=%a@ phi=%a@\n%!"
            (cns_str name) pr_subst sb pr_formula phi; *]*)
          let args = List.map (subst_typ sb) args in
          let c_args = List.map
            (fun v -> try fst (VarMap.find v sb) with Not_found -> TVar v)
            c_args in
          let vs = VarSet.inter (vars_of_list vs)
              (fvs_formula
                 (Eqty (TCons (tuple, args),
                        TCons (tuple, c_args), dummy_loc)::phi)) in
          (match c_args with
           | [Alien (Num_term (NumDefs.Cst (x,1)))] ->
             constructor_samples := (c_n,x) :: !constructor_samples
           | _ -> ());
          [IValConstr (docu, name, VarSet.elements vs, phi,
                       args, c_n, c_args, lc)]
        | _, PrimVal (docu, x, tsch, ext_def, lc) ->
          gamma := (x, tsch) :: !gamma;
          [IPrimVal (docu, x, tsch, ext_def, lc)]
        | new_ex_types,
          (LetRecVal (docu, x, e, defsig, _, loc) as it)
        | new_ex_types,
          (LetVal (docu, PVar (x, _), e, defsig, loc) as it) ->
          let tests = match it with
            | LetRecVal (_, _, _, _, tests, _) -> tests
            | LetVal _ -> []
            | _ -> assert false in
          let bvs, sig_cn, t = match defsig with
            | None ->
              let b = fresh_typ_var () in
              let tb = TVar b in
              [b], [], tb
            | Some (vs, phi, t) -> vs, phi, t in
          let pat_loc = match it with
            | LetVal (_, PVar (_, lc), _, _, _) -> Some lc
            | _ -> None in
          let (chi_id, e, tests, elim_cells), new_ex_types, (q, phi_res, sb_chi) =
            let call_signature = lazy (project_call_signature bvs sig_cn t) in
            let propose_call bands = match pat_loc, defsig with
              | None, Some _ -> interval_call_key !constructor_samples (Lazy.force call_signature) t e bands loc
              | _ -> [] in
            let admitted policy ((id,_,_,_),_,solution) = match policy with
              | Restrict_calls _ -> Admitted
              | Open_at_keys _ | Exclude_bands _ ->
                (try
                   let _,_,_,scheme = recursive_answer bvs loc id solution in
                   check_key_admission ~integer_target policy bvs sig_cn t scheme loc
                 with Report_toplevel _ | NoAnswer _ | Contradiction _ -> Unavailable) in
            let search ?(value_patterns=[]) ?(contract=(sig_cn,t)) () =
              let sig_cn,t = contract in
              solve_item ~propose_call ~admitted new_ex_types e tests (fun e tests call_constraints erase_bodies ->
                let retry_signature = match call_constraints with
                  | Open_at_keys _ | Exclude_bands _ -> Lazy.force call_signature | Restrict_calls _ -> sig_cn in
                let chi_id, _, cn, e, tests, elim_cells, preserve =
                  constr_gen_letrec ~value_patterns ~call_constraints ~erase_bodies ~nonrec:(pat_loc<>None)
                    !gamma x e retry_signature t tests in
                let preserve = add_vars preserve
                    (VarSet.union (fvs_typ t) (fvs_formula sig_cn)) in
                cn, preserve, (chi_id, e, tests, elim_cells)) in
            if new_ex_types<>[] || signature_target defsig<>None then search () else
            if lambda_depth e=0 then (
              let contract = if pat_loc=None && defsig=None then recursive_value_signature x e else None in
              match contract with
              | None -> search ()
              | Some contract ->
                let saved = !all_ex_types in
                let proposal =
                  try
                    let (id,_,_,_),packages,solution as answer = search ~contract () in
                    let _,_,_,scheme = recursive_answer bvs loc id solution in
                    if packages=[] && covers_cycle contract scheme loc then Some answer else None
                  with NoAnswer _ | Contradiction _ | Report_toplevel _ -> None
                     | Failure msg when msg = "int_of_big_int" -> None in
                match proposal with Some ans -> ans | None -> all_ex_types := saved; search ())
            else
            let initial = !all_ex_types in
            let hints vars ty = value_patterns (Lazy.force value_families) vars e ty in
            let original,seen =
              try
                if pat_loc=None || defsig<>None then search (),false
                else NumS.observe_guard_choices (fun () -> search ())
              with (NoAnswer _ | Contradiction _) as failed ->
                (match defsig with
                 | None -> raise failed
                 | Some (_,_,ty) ->
                   let patterns = hints (fvs_typ ty) ty in
                   if patterns=[] then raise failed;
                   all_ex_types := initial;
                   try search ~value_patterns:patterns (),false
                   with NoAnswer _ | Contradiction _ -> raise failed) in
            let scheme ((id,_,_,_),_,solution) =
              let _,_,_,sch = recursive_answer bvs loc id solution in sch in
            let improve current old_scheme trial =
              let saved = !all_ex_types in
              let keep () = all_ex_types := saved; current in
              all_ex_types := initial;
              try
                let _,packages,_ as proposal = trial () in
                if packages=[] && strictly_broader_guard old_scheme (scheme proposal)
                then proposal else keep ()
              with
              | NoAnswer _ | Contradiction _ | Report_toplevel _ -> keep ()
              | Failure msg when msg = "int_of_big_int" -> keep ()
              | exn -> all_ex_types := saved; raise exn in
            let _,packages,_ = original in
            if packages<>[] then original else
            let _,guard,_ as old_scheme = scheme original in
            if guard=[] then original else
            let best = if seen then improve original old_scheme
                (fun () -> NumS.with_combined_guards (fun () -> search ())) else original in
            let _,guard,ty as best_scheme = if best==original then old_scheme else scheme best in
            if guard=[] then best else
            let patterns = hints (fvs_formula guard) ty in
            if patterns=[] then best else
            let trial () = search ~value_patterns:patterns () in
            improve best best_scheme (if best==original then trial
                else fun () -> NumS.with_combined_guards trial) in
          let elim_extypes = concat_map (!) elim_cells in
          let nice_sb,sb_res,sb,typ_sch = recursive_answer bvs loc chi_id (q,phi_res,sb_chi) in
          let e = annotate_expr q sb sb_chi nice_sb e in
          let tests = List.map (annotate_expr q sb sb_chi nice_sb) tests in
          gamma := (x, typ_sch) :: !gamma;
          let ex_items =
            update_new_ex_types q new_ex_types sb_res sb_chi in
          if !inform_toplevel
          then Format.printf
              "@[<2>val@ %s :@ %a@]@\n%!" x pr_typscheme typ_sch;
          if !inform_toplevel && !time_toplevel
          then (
            let time = Sys.time () in
            Format.printf "(t=%.3fs)@\n" (time -. !ntime);
            ntime := time);
          (match pat_loc with
           | Some lc ->
             ex_items @
               [ILetVal (docu, PVar (x, lc), e, typ_sch, [x, typ_sch],
                         elim_extypes, loc)]
           | None ->
             ex_items @
               [ILetRecVal (docu, x, e, typ_sch,
                            tests, elim_extypes, loc)])
        | new_ex_types, LetVal (docu, p, e, defsig, loc) ->
          let avs, sig_vs, sig_cn, t = match defsig with
            | None ->
              let a = fresh_typ_var () in
              let ta = TVar a in
              VarSet.singleton a, [], [], ta
            | Some (vs, phi, t) -> VarSet.empty, vs, phi, t in
          let (bs, exphi, env, p, e, elim_cell, preserve), new_ex_types, (q, phi, sb_chi) =
            solve_item new_ex_types e [] (fun e _ _ erase_bodies ->
                let bs, exphi, env, cn, (p, e), elim_cell, preserve =
                  constr_gen_let ~erase_bodies !gamma p e t in
                let preserve = add_vars preserve
                    (VarSet.union (fvs_typ t)
                       (VarSet.union (fvs_formula sig_cn) (fvs_formula exphi))) in
                let cn = impl sig_cn cn in
                let cn = if sig_vs <> [] then All (vars_of_list sig_vs, cn) else cn in
                let cn = if VarSet.is_empty avs then cn else Ex (avs, cn) in
                cn, preserve, (bs, exphi, env, p, e, elim_cell, preserve)) in
          let elim_extypes = !elim_cell in
          (*[* Format.printf "Infer: solved.@\n%!"; *]*)
          (*[* Format.printf
            "Infer: [6] phi=%a@\n%!"
            pr_formula phi; *]*)
          let sb, phi =
            separate_subst ~bvs:preserve ~apply:true q phi in
          (*[* Format.printf
            "Infer: [7] sb=%a@\n%!" pr_subst sb; *]*)
          let res = subst_typ sb t in
          let gvs = VarSet.union (fvs_formula phi) (fvs_typ res) in
          (*[* Format.printf "LetVal: res=%a@ gvs=%a@ phi=%a@\n%!"
            pr_ty res pr_vars gvs pr_formula phi; *]*)
          let gvs = VarSet.elements gvs in
          let nice_sb, (gvs, phi) =
            nice_ans ~fvs:(fvs_typ res) (gvs, phi) in
          (*[* Format.printf
            "Infer: [8] nice_sb=%a@\n%!" pr_hvsubst nice_sb; *]*)
          let sb = hvsubst_sb nice_sb sb in
          let res = hvsubst_typ nice_sb res in
          (*[* Format.printf
            "LetVal: nice@ res=%a@ gvs=%a@\nphi=%a@\nsb=%a@\nexphi=%a@\n%!"
            pr_ty res pr_vars (vars_of_list gvs)
            pr_formula phi pr_subst sb pr_formula exphi; *]*)
          let top_sch = gvs, phi, res in
          let e = annotate_expr q sb sb_chi nice_sb e in
          let exphi = subst_formula sb exphi in
          (*[* Format.printf
            "Infer: [9] exphi=%a@\n%!"
            pr_formula exphi; *]*)
          let exsb, exphi =
            separate_subst ~bvs:(add_vars gvs preserve) ~apply:true q exphi in
          (*[* Format.printf
            "Infer: [10] exsb=%a@\n%!" pr_subst sb; *]*)
          let exsb = update_sb ~more_sb:exsb sb in
          let ex_items =
            update_new_ex_types q new_ex_types sb sb_chi in
          let more_items = ref [] in
          let all_exvs = fvs_formula exphi in
          (*[* Format.printf
            "LetVal: exphi=%a@\nexsb=%a@\n%!" pr_formula exphi
            pr_subst exsb; *]*)
          let typ_sch_ex =
            if VarSet.is_empty (VarSet.inter bs all_exvs) && exphi = []
            then fun (x, res) ->
              let res' = subst_typ exsb res in
              let gvs, phi = prepare_scheme phi res' in
              (*[* Format.printf
                "LetVal: x=%s@ res=%a@ nice res=%a@ gvs=%a@ phi=%a@\n%!"
                x pr_ty res pr_ty res'
                pr_vars gvs pr_formula phi; *]*)
              let typ_sch = VarSet.elements gvs, phi, res' in
              if !inform_toplevel
              then Format.printf
                  "@[<2>val@ %s :@ %a@]@\n%!" x pr_typscheme typ_sch;
              if !inform_toplevel && !time_toplevel
              then (
                let time = Sys.time () in
                Format.printf "(t=%.3fs)@\n" (time -. !ntime);
                ntime := time);
              x, typ_sch
            else fun (x, res) ->
              let res = subst_typ exsb res in
              let gvs, phi = prepare_scheme phi res in
              let exvs, exphi = prepare_scheme exphi res in
              (*[* Format.printf
                "Infer: [11] exphi=%a@\n%!"
                pr_formula exphi; *]*)
              let more_sb, exphi =
                separate_subst
                  ~bvs:(VarSet.union exvs gvs) ~apply:true q exphi in
              (*[* Format.printf
                "Infer: [12] more_sb=%a@\n%!" pr_subst sb; *]*)
              let sb = update_sb ~more_sb sb in
              let exvs = VarSet.diff exvs (vars_of_list [delta; delta']) in
              let gvs = VarSet.diff gvs (vars_of_list [delta; delta']) in
              let pvs = VarSet.diff exvs bs in
              let pvs = VarSet.filter (not % q.uni_v) pvs in
              let gvs = VarSet.elements
                  (VarSet.diff gvs (VarSet.diff exvs pvs)) in
              let exvs = VarSet.elements exvs in
              let pvs = VarSet.elements pvs in
              let ety_id = incr extype_id; !extype_id in
              let ety_n = Extype ety_id in
              let extydec =
                ITypConstr (None, ety_n, List.map var_sort pvs, loc) in
              let pts = List.map
                  (fun v ->
                     try fst (VarMap.find v sb) with Not_found -> TVar v)
                  pvs in
              let extydef = IValConstr
                  (None, ety_n, exvs, phi, [res], ety_n, pts, loc) in
              more_items := extydef :: extydec :: !more_items;
              let ex_sch = exvs, exphi, [res], ety_n, pvs in
              Hashtbl.add sigma (ety_n) ex_sch;
              all_ex_types := (ety_id, loc) :: !all_ex_types;
              (*[* Format.printf "infer-LetVal-ex_types: id=%d@ phi=%a@ ty=%a@\n%!"
                ety_id pr_formula exphi pr_ty res;
              *]*)
              (* Here in [ety] the variables are free, unlike the
                 occurrences in [exphi]. *)
              let typ_sch =
                gvs, phi, TCons (ety_n, List.map (fun v->TVar v) pvs) in
              if !inform_toplevel
              then Format.printf
                  "@[<2>val@ %s :@ %a@]@\n%!" x pr_typscheme typ_sch;  
              if !inform_toplevel && !time_toplevel
              then (
                let time = Sys.time () in
                Format.printf "(t=%.3fs)@\n" (time -. !ntime);
                ntime := time);
              x, typ_sch in
          let typ_schs = List.map typ_sch_ex env in
          gamma := typ_schs @ !gamma;
          ex_items @ List.rev !more_items
          @ [ILetVal (docu, p, e, top_sch, typ_schs, elim_extypes, loc)]
      ) prog in
  if !time_toplevel
  then Format.printf "@\nTotal time %.3fs@\n" (Sys.time () -. start_time);
  List.rev !gamma, items


(** {2 Normalization} *)

type branch = Terms.formula * Terms.formula

let rec remove_qns = function
  | All (_, cn) | Ex (_, cn) -> remove_qns cn
  | A _ as cn -> cn
  | And cns -> And (List.map remove_qns cns)
  | Or (b0, disjs, cn) ->
    Or (b0, List.map
          (fun (bs, c_cn, d, tr) -> bs, remove_qns c_cn, d, tr) disjs,
        remove_qns cn)
  | Impl (prem, concl) -> Impl (prem, remove_qns concl)

let prenexize cn =
  let quant = Hashtbl.create 64 in
  let upward = Hashtbl.create 64 in
  let univars = Hashtbl.create 32 in
  let allvars = Hashtbl.create 64 in
  let parent_param = Hashtbl.create 32 in
  let same_as v1 v2 =
    if Hashtbl.mem quant v1
    then (
      Hashtbl.replace parent_param v2 v1;
      let q_id = Hashtbl.find quant v1 in
      Hashtbl.replace quant v2 q_id;
      if Hashtbl.mem univars v1
      then Hashtbl.replace univars v2 (Hashtbl.find univars v1)
      else Hashtbl.remove univars v2)
    else if Hashtbl.mem quant v2
    then (
      Hashtbl.replace parent_param v1 v2;
      let q_id = Hashtbl.find quant v2 in
      Hashtbl.replace quant v1 q_id;
      if Hashtbl.mem univars v2
      then Hashtbl.replace univars v1 (Hashtbl.find univars v2)
      else Hashtbl.remove univars v1)
    else (
      (*[* Format.printf "same_as: unknown vars %s, %s@\n%!"
        (var_str v1) (var_str v2); *]*)
      assert false) in
  let cmp_v v1 v2 =
    let par1 = try Hashtbl.find parent_param v1 with Not_found -> v1
    and par2 = try Hashtbl.find parent_param v2 with Not_found -> v2 in
    if par1 = par2 then Same_params
    else
      try
        let id1 = Hashtbl.find quant v1
        and id2 = Hashtbl.find quant v2 in
        if id1 < id2 then Left_of
        else if id1 = id2 then Same_quant
        else Right_of
      with Not_found ->
        let c1 = not (Hashtbl.mem allvars v1)
        and c2 = not (Hashtbl.mem allvars v2) in
        if c1 && c2 then Same_quant
        else if c1 then Right_of
        else if c2 then Left_of
        else (
          (*[* Format.printf "cmp_v: unknown vars %s, %s@\n%!"
            (var_str v1) (var_str v2); *]*)
          assert false) in
  let uni_v v =
    try Hashtbl.find univars v with Not_found -> false in
  let upward_of v1 v2 =
    try Hashtbl.find upward (v1, v2) with Not_found -> false in
  let current_id = ref 0
  (*[* and current_vars = ref VarSet.empty *]*)
  and change = ref true and at_uni = ref true in
  let q_add_vars upvs vs =
    if !at_uni then VarSet.iter (fun v -> Hashtbl.add univars v true) vs;
    let v_id = !current_id in
    VarSet.iter (fun v ->
        Hashtbl.add quant v v_id; Hashtbl.add allvars v ();
        VarSet.iter (fun up -> Hashtbl.add upward (up, v) true)
          upvs)
      vs;
    (*[* current_vars := VarSet.union !current_vars vs; *]*)
    change := true in
  let alternate () =
    (*[* Format.printf "alternate: %s.%a@\n%!" (if !at_uni then "∀" else "∃")
      pr_vars !current_vars;
    current_vars := VarSet.empty;
    *]*)
    incr current_id;
    change := false; at_uni := not !at_uni in
  let rec aux upvs = function
    | (All (vs, cn) | Ex (vs, cn))
      when VarSet.is_empty vs ->
      aux upvs cn
    | (All (vs, cn) | Ex (vs, cn))
      when Hashtbl.mem allvars (VarSet.choose vs) ->
      aux (VarSet.union vs upvs) cn
    | All (vs, cn) when !at_uni ->
      q_add_vars upvs vs; aux upvs cn
    | Ex (vs, cn) when not !at_uni -> q_add_vars upvs vs; aux upvs cn
    | (All _ | Ex _ | A _) -> ()
    | And cns -> List.iter (aux upvs) cns
    | Or (v, disjs, subcn) ->
      let skip = Hashtbl.mem allvars v in
      if not skip && !at_uni then q_add_vars upvs (VarSet.singleton v);
      let upvs = List.fold_left
          (fun acc (bs, cn, prem, tr) ->
             aux upvs cn;
             if not skip && !at_uni then q_add_vars upvs bs;
          VarSet.union bs acc)
          (VarSet.add v upvs) disjs in
      if skip || !at_uni then aux upvs subcn
    | Impl (prem, concl) -> aux upvs concl in
  let rec loop () =
    alternate (); aux VarSet.empty cn; if !change then loop () in
  (* Start the prefix from existential quantifiers. *)
  loop ();
  (*[* Format.printf "prenexize: done@\n%!"; *]*)
  {cmp_v; uni_v; same_as; upward_of}, remove_qns cn

type 'a guarded_br = {
  guard_cnj : formula;
  prem : formula;
  concl : 'a
}

(* FIXME: needs a rewrite or better description. *)
let normalize q cn =
  let unify ?sb cnj = solve ~use_quants:false ?sb q cnj in
  (* Predicate variables for invariants of recursive definitions (some
     positive occs of unary pred vars are for postconditions). *)
  let chi_rec = Hashtbl.create 2 in
  let collect_chi_rec prem = List.iter
      (function PredVarU (i, _, _) -> Hashtbl.replace chi_rec i ()
              | _ -> ()) prem in
  (* From unary predicate variable to the existential type of its
     result (if any). *)
  let chi_exty = Hashtbl.create 2 in
  (* Inverse of [chi_exty]. *)
  let exty_res_chi = Hashtbl.create 2 in
  (* Existential type compatible with the variable. *)
  let v_exty = Hashtbl.create 8 in
  (* A function returning a package can itself be passed to a function.
     NotEx tests the outer constructor of its argument. *)
  let head_exty = Hashtbl.create 8 in
  let record_package v i =
    Hashtbl.replace v_exty v i;
    Hashtbl.replace head_exty v i in
  let v_chi = Hashtbl.create 8 in
  (* Raises [Contradiction] *)
  let simplify_brs = List.map
      (fun {guard_cnj; prem; concl} ->
         (*[* Format.printf
           "simplify_brs:@\nguard_cnj=%a@\nprem=%a@\nconcl=%a@\n%!"
           pr_formula guard_cnj pr_formula prem pr_formula concl; *]*)
         if concl=[] ||
            List.exists (function CFalse _ -> true | _ -> false) concl
         then prem, concl
         else
           (* 1 *)
           let sb =
             try (unify (guard_cnj @ prem @ concl)).cnj_typ
             with Contradiction _ as e ->
               if !nodeadcode then (deadcode_flag := true; raise e)
               else VarMap.empty in
           let {cnj_typ=concl_typ; cnj_num=concl_num; cnj_so=concl_so} =
             unify concl in
           (*[* Format.printf "simplify_brs: passed unify@\n%!"; *]*)
           (* FIXME: only filter out if known to hold *)
           let concl_so = List.filter
               (function NotEx _ -> false
                       | _ -> true) concl_so in
           (* 2 *)
           VarMap.iter (fun v (t, _) ->
               (match t with
                | TCons (Extype i, _) -> Hashtbl.replace head_exty v i
                | _ -> ());
               match return_type t with
               | TCons (Extype i, _) when not (Hashtbl.mem v_exty v) ->
                 (*[* Format.printf
                   "dsj-chi-exty: [2] v=%s i=%d@\n%!"
                   (var_str v) i; *]*)
                 Hashtbl.add v_exty v i
               | _ -> ())
             sb;
           (* 3 *)
           List.iter
             (function
               | RetType (t, TVar a, _) ->
                 let i =
                   try Hashtbl.find v_exty a
                   with Not_found -> assert false in
                 (*[* Format.printf
                   "dsj-chi-exty: [3] t=%a a=%s i=%d@\n%!"
                   pr_ty t (var_str a) i; *]*)
                 (match return_type t with
                  | TVar v -> record_package v i
                  | _ -> assert false);
                 (match return_type (subst_typ sb t) with
                  | TVar v -> record_package v i
                  | _ -> assert false)
               | _ -> ()) concl;
           (* 4 *)
           List.iter
             (function
               | PredVarU (i, TVar b, _)
                 when Hashtbl.mem chi_rec i && not (Hashtbl.mem v_chi b) ->
                 (*[* Format.printf
                   "dsj-chi-exty: [4] b=%s i=%d@\n%!"
                   (var_str b) i; *]*)
                 Hashtbl.add v_chi b i
               (* | NotEx _ -> assert false *)
               | _ -> ()) (prem @ concl);
           (* 5 *)
           VarMap.iter (fun v (t, _) ->
               match return_type t with
               | TVar w when Hashtbl.mem v_chi v &&
                             not (Hashtbl.mem v_chi w)->
                 (*[* Format.printf
                   "dsj-chi-exty: [5] v=%s w=%s i=%d@\n%!"
                   (var_str v) (var_str w) (Hashtbl.find v_chi v); *]*)
                 Hashtbl.add v_chi w (Hashtbl.find v_chi v)
               | _ -> ())
             sb;
           (* 6 *)
           Hashtbl.iter
             (fun b i ->
                if Hashtbl.mem v_exty b &&
                   not (Hashtbl.mem chi_exty i)
                then (
                  (*[* Format.printf
                    "dsj-chi-exty: [6] b=%s i=%d->j=%d@\n%!"
                    (var_str b) i (Hashtbl.find v_exty b); *]*)
                  let exty = Hashtbl.find v_exty b in
                  Hashtbl.add exty_res_chi exty i;
                  Hashtbl.add chi_exty i exty))
             v_chi;
           (* 7 *)
           Hashtbl.iter
             (fun b i ->
                if Hashtbl.mem chi_exty i &&
                   not (Hashtbl.mem v_exty b)
                then (
                  (*[* Format.printf
                    "dsj-chi-exty: [7] b=%s i=%d->j=%d@\n%!"
                    (var_str b) i (Hashtbl.find chi_exty i); *]*)
                  record_package b (Hashtbl.find chi_exty i)))
             v_chi;
           prem,
           (* TODO: keep [sep_formula] *)
           to_formula concl_typ @
             NumS.formula_of_sort concl_num @ concl_so) in
  (* Produces: a formula, formula-constraint pairs,
     disjuncts list list. *)
  let rec flat_and = function
    | A cns -> cns, [], []
    | And cns ->
      let cnj, impls, dsjs = split3 (List.map flat_and cns) in
      let cnj = List.concat cnj
      and impls = List.concat impls
      and dsjs = List.concat dsjs in
      cnj, impls, dsjs
    | Impl ([], concl) -> flat_and concl
    | Impl (prem, concl) ->
      collect_chi_rec prem; [], [prem, concl], []
    | Or (_, disjs, cn) ->
      [], [], [disjs, cn]      
    | All _ | Ex _ -> assert false in
  (* Produces: normal branches and disjunction branches.
     Normal branch: guard formula (conclusions sharing the premise),
     premise formula, local conclusion formula.
     Disjunction branch: premise formula, guard formula,
     constraint-trigger pairs. *)
  let rec flat_cn prem guard_cnj cn =
    let cnj, impls, dsjs = flat_and cn in
    let guard_cnj = cnj @ guard_cnj in
    let br0 = {guard_cnj; prem; concl=cnj} in
    let dsj_brs1 = List.map
        (fun dsjs ->
           {prem; guard_cnj; concl=dsjs}) dsjs in
    let brs, dsj_brs2 = List.split
        (List.map
           (fun (more_prem, concl) ->
              let more_prem = List.filter
                  (function
                    | Eqty (t1, t2, _) when t1=t2 -> false
                    | a -> not (List.exists (eq_atom a) cnj
                                || List.exists (eq_atom a) guard_cnj))
                  more_prem in
              flat_cn
                (more_prem @ prem) guard_cnj concl)
           impls) in
    br0 :: List.concat brs, List.concat (dsj_brs1 :: dsj_brs2) in
  (* Produces: guard formula, and a list of: a disjunct constraint,
     flat_cn result of the constraint (the [sol] part), a trigger. *)
  let flat_dsj {prem=more_prem; guard_cnj; concl=(disjs, e_dsj)} =
    let e_impls, e_disjs = flat_cn more_prem guard_cnj e_dsj in
    guard_cnj, List.map
      (fun (bs, cn, prem, trigger) ->
         let c_impls, c_disj = flat_cn more_prem guard_cnj cn in
         assert (c_disj = []);
         cn, c_impls, prem, trigger)
      disjs,
    e_impls, e_disjs in
  let check_chi_exty =
    VarMap.for_all
      (fun v -> function
        | (TCons (cn, _), _) when Hashtbl.mem v_exty v ->
          (*[* Format.printf "dsj-test: ex case =%s v=%s v_chi=%d@\n%!"
            (cns_str cn) (var_str v) (Hashtbl.find v_exty v); *]*)
          cn = Extype (Hashtbl.find v_exty v)
        | _ -> true) in
  (* Takes the result of [flat_dsj], returns the [sol] part of one
     of the disjuncts as Left (calls trigger first), or the filtered
     disjuncts as Right. *)
  let solve_dsj forced (guard_cnj, dsjs, e_impls, e_disjs) =
    let sb =
      (* TODO: optimize by precomputing unifiers for guard_cnj and
         e_cnj separately, before calling [solve_dsj]. *)
      try (unify guard_cnj).cnj_typ
      with Contradiction _ as e ->
        if !nodeadcode then (deadcode_flag := true; raise e)
        else VarMap.empty in
    (*[* Format.printf "dsj-checking: init #dsjs=%d@ sb=%a@\n%!"
      (List.length dsjs) pr_subst sb; *]*)
    let first_exn = ref None in
    let check_dsj (cn, c_impls, prem, trigger) =
      (*[* Format.printf "dsj-test: starting case.@\n%!"; *]*)
      try
        let sb = (unify ~sb prem).cnj_typ in
        List.for_all
          (fun {guard_cnj; prem; concl} ->
             List.exists (function CFalse _ -> true | _ -> false) concl
             || (
               (*[* Format.printf "dsj-test: br@ prem=%a@ concl=%a@\n%!"
                 pr_formula prem pr_formula concl; *]*)
               try
                 let {cnj_typ=sb'; cnj_so=so; _} =
                   unify ~sb (guard_cnj @ prem @ concl) in
                 (*[* Format.printf "dsj-test: br@ sb'=%a@\n%!"
                   pr_subst sb'; *]*)
                 List.iter
                   (function
                     | NotEx (TCons (Extype _, _) as t, loc) ->
                       raise (Contradiction
                                (Type_sort, "Should not be existential",
                                 Some (t, t), loc))        
                     | NotEx (TVar v as t, loc) when Hashtbl.mem head_exty v ->
                       let st =
                         TCons (Extype (Hashtbl.find head_exty v), []) in
                       raise (Contradiction
                                (Type_sort, "Should not be existential",
                                 Some (t, st), loc))
                     | _ -> ())
                   so;
                 (*[* let res = *]*) check_chi_exty sb' (*[* in
                  Format.printf
                   "tested disjunct! branch above, res=%b@\n%!"
                   res; res *]*)
               with Contradiction _ as e ->
                 (*[* Format.printf
                   "test rejected a disjunct! branch above@\nexn=%a@\n%!"
                   pr_exception e; *]*)
                 if !nodeadcode then (deadcode_flag := true; raise e)
                 else false)
          ) c_impls
      with Contradiction _ as e ->
        (*[* Format.printf "test rejected a disjunct!@\nr-cn=%a@\nexn=%a@\n%!"
          pr_cnstrnt cn pr_exception e; *]*)
        if !first_exn = None then first_exn := Some e;
        false in
    let dsjs = List.filter check_dsj dsjs in
    (*[* Format.printf "checking: result #dsjs=%d; #e_disjs=%d@\n%!"
      (List.length dsjs) (List.length e_disjs); *]*)
    match dsjs with
    | [] ->
      (*[* Format.printf "checking-Or: none passes@\n%!"; *]*)
      (match !first_exn with
       | Some e -> raise e
       | None ->
         raise
           (Report_toplevel
              ("No valid disjunct, check existential type use",
               Some (formula_loc guard_cnj))))
    | [cn, c_impls, prem, trigger] ->
      (*[* Format.printf "dsj-test: selected\n%a@\n%!"
        pr_cnstrnt cn; *]*)
      forced := false; trigger ();
      Left (guard_cnj, c_impls, prem, e_impls, e_disjs)
    | (cn, c_impls, prem, trigger)::_ when !forced ->
      (*[* Format.printf "dsj-test: forced selected\n%a@\n%!"
        pr_cnstrnt cn; *]*)
      forced := false; trigger ();
      Left (guard_cnj, c_impls, prem, e_impls, e_disjs)
    | _ ->
      Right (guard_cnj, dsjs, e_impls, e_disjs) in
  let concat_brs more_brs =
    List.fold_left
      (fun (brs, dsj_brs) (guard_cnj, c_impls, more_prem, e_impls, e_disjs) ->
         let more_brs =
           c_impls @ List.map
               (fun {guard_cnj; prem; concl} ->
                  {guard_cnj; prem = more_prem @ prem; concl}) e_impls in
         more_brs @ brs,
         List.map (fun ({prem; guard_cnj; concl}) ->
             {prem = more_prem @ prem; guard_cnj; concl})
           e_disjs @ dsj_brs)
      ([], []) more_brs in
  let prepare_brs (brs, dsjs) =
    let dsjs = List.map flat_dsj dsjs in
    let brs = simplify_brs brs in
    brs, dsjs in
  let rec loop (brs, dsj_brs) =
    (*[* Format.printf
      "normalize-loop: init #brs=%d #dsj_brs=%d@\n%!"
      (List.length brs) (List.length dsj_brs);
    *]*)
    let more_brs, dsj_brs = partition_map (solve_dsj (ref false)) dsj_brs in
    (*[* if more_brs = [] then Format.printf
      "normalize-loop: forcing #dsj_brs'=%d@\n%!" (List.length dsj_brs);
    *]*)
    let more_brs, dsj_brs =
      if more_brs = [] then partition_map (solve_dsj (ref true)) dsj_brs
      else more_brs, dsj_brs in
    let more_brs, more_dsj = prepare_brs (concat_brs more_brs) in
    let dsj_brs =
      more_dsj @ dsj_brs in
    (*[* Format.printf
      "normalize-loop: completed #brs=%d #dsj_brs=%d \
       brs=@\n%a@\nmore_brs=@\n%a@\n%!"
      (List.length brs) (List.length dsj_brs) pr_brs brs pr_brs more_brs;
    *]*)
    if more_brs = [] || dsj_brs = [] then more_brs @ brs, dsj_brs
    else loop (more_brs @ brs, dsj_brs) in
  let sol0 = flat_cn [] [] cn in
  let brs, dsj_brs = loop (prepare_brs sol0) in
  assert (dsj_brs = []);
  (*[* Format.printf "normalize: done@\n%!"; *]*)
  exty_res_chi, brs

let vs_hist_alien_term increase = function
  | Num_term t -> NumDefs.iter_term_vars increase t
  | Order_term t -> OrderDefs.iter_term_vars increase t

let vs_hist_typ increase =
  typ_fold {(typ_make_fold (fun _ _ -> ()) ())
            with fold_tvar = (fun v -> increase v);
                 fold_alien = vs_hist_alien_term increase}

let vs_hist_alien_atom increase = function
    | Num_atom a -> NumDefs.iter_terms
                      (NumDefs.iter_term_vars increase) a
    | Order_atom a -> OrderDefs.iter_terms
                      (OrderDefs.iter_term_vars increase) a

let vs_hist_atom increase = function
  | Eqty (t1, t2, _) ->
    vs_hist_typ increase t1; vs_hist_typ increase t2
  | CFalse _ -> ()
  | PredVarU (_, t, _) -> vs_hist_typ increase t
  | PredVarB (_, t1, t2, _) ->
    vs_hist_typ increase t1; vs_hist_typ increase t2
  | NotEx (t, _) -> vs_hist_typ increase t
  | RetType (t1, t2, _) ->
    vs_hist_typ increase t1; vs_hist_typ increase t2
  | Terms.A a -> vs_hist_alien_atom increase a

let vs_hist_sb increase sb =
  List.iter (fun (v,(t,_)) -> increase v; vs_hist_typ increase t) sb

let simplify preserve q brs =
  (* Prune "implies true" branches. *)
  let brs = List.filter
      (function _, [] -> false | _ -> true) brs in
  (* Predicate variables for invariants of recursive definitions (some
     positive occs of unary pred vars are for postconditions). *)
  let chi_rec = Hashtbl.create 2 in
  let collect_chi_rec (prem, _) = List.iter
      (function PredVarU (i, _, _) -> Hashtbl.replace chi_rec i ()
              | _ -> ()) prem in
  List.iter collect_chi_rec brs;
  (* Prune uninformative variables. *)
  let ht = Hashtbl.create 255 in
  let increase v =
    try
      let n = Hashtbl.find ht v in
      Hashtbl.replace ht v (n+1)
    with Not_found -> Hashtbl.add ht v 1 in
  let count v =
    try Hashtbl.find ht v with Not_found -> 0 in
  List.iter
    (fun (prem,concl) ->
       List.iter (vs_hist_atom increase) prem;
       List.iter (vs_hist_atom increase) concl)
    brs;
  let redundant_atom in_prem = function
    | Eqty (TVar v, _, _)
    | Eqty (_, TVar v, _) ->
      not (VarSet.mem v preserve) && count v = 1
      && (in_prem || not (q.uni_v v))       (* FIXME: use cmp_v? *)
    | _ -> false in                         (* FIXME: check other sorts? *)
  let nonred_pr_atom a = not (redundant_atom true a) in
  let nonred_atom a = not (redundant_atom false a) in
  (* FIXME: should we identify the same nonrec branches as
     Invariants.solve? *)
  let is_nonrec prem concl =
    not (List.exists (function
        | PredVarU (i, _, _) -> Hashtbl.mem chi_rec i
        | _ -> false) concl) &&
    not (List.exists (function
        | PredVarB (i, _, _, _) -> true(* Hashtbl.mem chiK_res i *)
        | _ -> false) prem) in
  let brs = List.map
      (fun (prem,concl) ->
         List.filter nonred_pr_atom prem,
         List.filter nonred_atom concl)
      brs in
  (* Merge branches with the same premise. Optionally,
     do not merge branches when
     one is non-recursive and the other is recursive. *)
  (* Roughly like [map_reduce (@) [] brs] *)
  let equiv cnj1 cnj2 =
    try
      let {cnj_typ=c1_ty; cnj_num=c1_num; cnj_so=c1_so} =
        unify ~use_quants:false q cnj1 in
      let {cnj_typ=c2_ty; cnj_num=c2_num; cnj_so=c2_so} =
        unify ~use_quants:false q cnj2 in
      (* TODO: use [Terms.subformula], [NumS.equivalent] etc. instead? *)
      let c1_ty = List.map
          (fun (v,(t,_)) -> v,t) (varmap_to_assoc c1_ty)
      and c2_ty = List.map
          (fun (v,(t,_)) -> v,t) (varmap_to_assoc c2_ty)
      and c1_num = NumDefs.replace_loc dummy_loc c1_num
      and c2_num = NumDefs.replace_loc dummy_loc c2_num
      and c1_so = replace_loc dummy_loc c1_so
      and c2_so = replace_loc dummy_loc c2_so in
      let res =
        List.sort compare c1_ty = List.sort compare c2_ty &&
        (* NumS.equivalent q c1_num c2_num && *)
        List.sort compare c1_num = List.sort compare c2_num &&
        List.sort compare c1_so = List.sort compare c2_so in
      (*[* Format.printf
        "simplify: equiv? res=%b ty=%b num=%b so=%b@\nc1=%a@\nc2=%a@\n%!"
        res (List.sort compare c1_ty = List.sort compare c2_ty)
        (* (NumS.equivalent q c1_num c2_num)  *)
        (List.sort compare c1_num = List.sort compare c2_num)
        (List.sort compare c1_so = List.sort compare c2_so)
        pr_formula cnj1 pr_formula cnj2; *]*)
      res
    with Contradiction _ -> false in
  let rec meet nonrec prem concl = function
    | [] -> raise Not_found
    | (prem2, concl2 as br) :: brs ->
      let nonrec2 = is_nonrec prem2 concl2 in
      if (nonrec=nonrec2 || !merge_rec_nonrec) && equiv prem prem2
      then (prem, concl @ concl2) :: brs
      else br :: meet nonrec prem concl brs in
  let rec merge acc = function
    | [] -> List.rev acc
    | (prem, concl as br) :: brs ->
      try merge acc (meet (is_nonrec prem concl) prem concl brs)
      with Not_found -> merge (br::acc) brs in
  let brs = merge [] brs in
  (*[* Format.printf
    "simplify: ended phase 1; start solving RetType. brs=@\n%a@\n%!"
    pr_brs brs; *]*)
  let retypes, brs = fold_map
      (fun retypes (prem, concl) ->
         let concl = solve ~use_quants:false q concl in
         let more, cnj_so = partition_map
           (function
             | RetType (TVar v1, t2, lc) -> Left (v1, t2, lc)
             | RetType _ -> assert false
             | a -> Right a)
           concl.cnj_so in
         more @ retypes, (prem, {concl with cnj_so}))
      [] brs in
  let brs = List.map
      (fun (prem, concl) ->
         let more = map_some
           (fun (v1, t2, lc2) ->
             try
               let t1, lc1 = VarMap.find v1 concl.cnj_typ in
               let t1 = return_type t1 in
               Some (Eqty (t1, t2, loc_union lc1 lc2))
             with Not_found -> None)
           retypes in
         prem, more @ unsep_formulas concl)
      brs in
  List.stable_sort
    (fun (prem1,_) (prem2,_) -> List.length prem1 - List.length prem2)
    brs

(** {2 Postprocessing and printing} *)

let reset_state () =
  Hashtbl.clear phantom_enumeration;
  Hashtbl.clear phantom_enumeration_arg;
  fresh_expr_var_id := 0; fresh_chi_id := 0
