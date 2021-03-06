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

let normalize_expr e =
  (*[* Format.printf
    "normalize_expr: e=@\n%a@\n%!" pr_uexpr e; *]*)
  let new_ex_types = ref [] in
  let rec aux k' e =
    match k', e with
    | Some k, e when not (ex_intro_elim e) ->
      let lc = expr_loc e in
      Letin (None, PVar ("xcase", lc), aux None e,
             Cons (Extype k, [Var ("xcase", lc)], lc), lc)
    | _, ((Var _ | Num _ | String _) as x) -> x
    | _, Cons (k, es, lc) -> Cons (k, List.map (aux None) es, lc)
    | _, App (e1, e2, lc) -> App (aux k' e1, aux None e2, lc)
    | _, NumAdd (e1, e2, lc) -> NumAdd (aux None e1, aux None e2, lc)
    | _, NumCoef (x, e, lc) -> NumCoef (x, aux None e, lc)
    | _, Lam ((), cls, lc) -> Lam ((), List.map (aux_cl k') cls, lc)
    | None, ExLam (k, cls, lc) ->
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
    | Some _, ExLam (_, cls, lc) ->
      Lam ((), List.map (aux_cl k') cls, lc)
    | _, Letrec (docu, ann, x, e1, e2, lc) ->
      Letrec (docu, ann, x, aux None e1, aux k' e2, lc)
    | _, Letin (docu, p, e1, e2, lc) ->
      Letin (docu, p, aux None e1, aux k' e2, lc)
    | _, (AssertFalse _ as e) -> e
    | _, RuntimeFailure (e, lc) -> RuntimeFailure (aux None e, lc)
    | _, AssertLeq (e1, e2, range, lc) ->
      AssertLeq (e1, e2, aux k' range, lc)
    | _, AssertEqty (e1, e2, range, lc) ->
      AssertEqty (e1, e2, aux k' range, lc)
  and aux_cl k' (p, guards, e) =
    p, List.map (fun (e1,e2) -> aux None e1, aux None e2) guards,
    aux k' e in
  !new_ex_types, aux None e

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
    let extys, e = normalize_expr e in
    let extys, tes = fold_map
        (fun extys e ->
           let more_extys, e = normalize_expr e in
           more_extys @ extys, e)
        extys tes in
    extys, LetRecVal (docu, x, e, ty, tes, lc)
  | LetVal (docu, p, e, ty, lc) ->
    let extys, e = normalize_expr e in
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

let freshen_val_scheme (vs, phi, res) =
  let env = List.map (fun v->v, freshen_var v) vs in
  let env_sb = varmap_of_assoc env in
  let res = hvsubst_typ env_sb res in
  let phi = hvsubst_formula env_sb phi in
  let vs = List.map snd env in
  vs, phi, res

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

let constr_gen_expr gamma e t =
  let elim_extype = ref [] and preserve = ref [] in
  let rec aux gamma t e : cnstrnt * iexpr =
    (*[* Format.printf "constr_gen: t=%a e=@\n%a@\n%!"
      pr_ty t pr_uexpr e;
    *]*)
    match e with
    | Var (x, loc) when not (List.mem_assoc x gamma) ->
      raise (Report_toplevel ("Undefined variable "^x, Some loc))
    | Var (x, loc) as e ->
      let vs, phi, res = freshen_val_scheme (List.assoc x gamma) in
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
      let cn1, e1 = aux gamma (Fun (ta, t)) e1 in
      let cn2, e2 = aux gamma ta e2 in
      Ex (VarSet.singleton a,
          cn_and cn1 (cn_and cn2 (A [NotEx (ta, loc)]))),
      App (e1, e2, loc)
    | Lam ((), cls, loc) ->
      let a1 = fresh_typ_var () in
      let t1 = TVar a1 in
      let a2 = fresh_typ_var () in
      let t2 = TVar a2 in
      let cns, cls = List.split
          (List.map (aux_cl 0 gamma t1 t2) cls) in
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
      let gamma = (x, ([b], [chi_b], tb))::gamma in
      let cn1, e1 = aux gamma tb e1 in
      let cn2, e2 = aux gamma t e2 in
      let def_cn = 
        All (vars_of_list [b],
             Impl ([chi_b], cn1)) in
      cn_and def_cn (cn_and (Ex (vars_of_list [a], A [chi_a])) cn2),
      Letrec (docu, [chi_id], x, e1, e2, loc)
    | Letin (docu, p, e1, e2, loc) (* as e *) ->
      let count = incr letin_count; !letin_count in
      (*[* Format.printf "constr_gen-Letin: [%d] starting...@\n%!" count; *]*)
      let a0 = fresh_typ_var () in
      let ta0 = TVar a0 in
      let cn1, e1 = aux gamma ta0 e1 in
      (*[* Format.printf
        "constr_gen-Letin: [%d] generated ta0=%a@ cn1=%a@\ne1=%a@\n%!"
        count pr_ty ta0 pr_cnstrnt cn1 pr_iexpr e1; *]*)
      let b0 = fresh_typ_var () in
      let tb0 = TVar b0 in
      let cn2, (p, _, e2) = aux_cl count gamma tb0 t (p, [], e2) in
      (*[* Format.printf
        "constr_gen-Letin: [%d] generated tb0=%a@ cn2=%a@\np2=%a@ e2=%a@\n%!"
        count pr_ty tb0 pr_cnstrnt cn2 pr_pat p pr_iexpr e2; *]*)
      (* Aiming at: Or of var_name *
          (VarSet.t * cnstrnt * formula * (unit -> unit)) list * cnstrnt *)
      let disjs = List.map
          (fun (i, loc) ->
             let trigger () = elim_extype := (p, Some i) :: !elim_extype in
             let k = Extype i in
             let bs, d_prem, env =
               envfrag_gen_pat count
                 (PCons (k, [PVar ("x", loc)], loc)) ta0 in
             let t' = match env with [_, t'] -> t' | _ -> assert false in
             let pcn = constr_gen_pat (PCons (k, [p], loc)) ta0 in
             bs, pcn, Eqty (tb0, t', loc)::d_prem, trigger)
          !all_ex_types in
      let altcn = A [NotEx (ta0, loc)] in
      let alttr () = elim_extype := (p, None) :: !elim_extype in
      let disjs =
        (VarSet.empty, altcn, [Eqty (tb0, ta0, loc)], alttr)::disjs in
      (* FIXME: explain in the doc. Change [iexpr] from [int expr]
         to [int list expr]. Exactly one [chi_id] in the list will be
         present in the solution. *)
      (*[* Format.printf
        "constr_gen-Letin: [%d] t=%a@\ndisjs=@ %a@\n%!%!"
        count pr_ty t (pr_sep_list " ∨" (pr_disj_cnstrnt b0)) disjs;
      *]*)
      Ex (vars_of_list [a0], cn_and cn1 (Or (b0, disjs, cn2))),
      Letin (docu, p, e1, e2, loc)
    | ExLam (ety_id, cls, loc) ->
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

  and aux_cl count gamma t1 t2 (p, guards, e) =
    let is_neg = single_assert_false e in
    let t3 = if is_neg then TVar (fresh_typ_var ()) else t1 in
    let pcns = constr_gen_pat p t3 in
    let bs, prem, env = envfrag_gen_pat count p t3 in
    (*[* Format.printf "constr_gen-aux_cl: [%d] t1=%a@ t2=%a@ t3=%a@ bs=%a@ prem=%a@\n%!"
      count pr_ty t1 pr_ty t2 pr_ty t3 pr_vars bs pr_formula prem; *]*)
    let gamma' = List.map typ_to_sch env @ gamma in
    let concl, e = aux gamma' t2 e in
    let neg_prem =
      if is_neg
      then [Eqty (t1, t3, dummy_loc)]
      else [] in
    let (g_as, g_concl, g_cond), guards = fold_map
        (fun (g_as, g_concl, g_cond) (e1,e2) ->
           let a1 = fresh_var Num_sort and a2 = fresh_var Num_sort in
           let cn1,e1 = aux gamma' (TCons (numtype, [TVar a1])) e1
           and cn2,e2 = aux gamma' (TCons (numtype, [TVar a2])) e2 in
           (add_vars [a1; a2] g_as,
            cn_and (cn_and cn1 cn2) g_concl,
            Terms.A (Num_atom (NumDefs.Leq
                                 (NumDefs.Lin (1,1,a1),
                                  NumDefs.Lin (1,1,a2),
                                  dummy_loc))) :: g_cond),
           (e1,e2))
        (VarSet.empty, And [], []) guards in
    let cn = impl prem
        (cn_and g_concl (impl (neg_prem @ g_cond) concl)) in
    let cn = if VarSet.is_empty g_as then cn else Ex (g_as, cn) in
    let cn = if VarSet.is_empty bs then cn else All (bs, cn) in
    (*[* Format.printf "constr_gen-aux_cl: [%d]@\ncn=%a@\n%!"
      count pr_cnstrnt cn; *]*)
    let exvs = 
      if is_neg then fvs_typ t3 else VarSet.empty in
    let cn = cn_and pcns cn in
    (if VarSet.is_empty exvs then cn else Ex (exvs, cn)),
    (p, guards, e) in

  let cn = aux gamma t e in
  cn, elim_extype, !preserve

let constr_gen_tests gamma tests =
  let elim_cells = ref [] in
  let cns, tests, preserve = split3
      (List.map
         (fun e ->
            let (cn, e), elim_ex, preserve = constr_gen_expr gamma e
                (TCons (booltype, [])) in
            elim_cells := elim_ex :: !elim_cells;
            cn, e, preserve)
         tests) in
  List.fold_left cn_and (And []) cns,
  tests, !elim_cells, List.concat preserve

let constr_gen_letrec ?(nonrec=false) gamma x e sig_cn tb tests =
  let a = fresh_typ_var () in
  let chi_id = incr fresh_chi_id; !fresh_chi_id in
  let chi_b = PredVarU (chi_id, tb, expr_loc e) in
  let chi_a = PredVarU (chi_id, TVar a, expr_loc e) in
  let bvs = VarSet.union (fvs_typ tb) (fvs_formula sig_cn) in
  let def_typ = VarSet.elements bvs, [chi_b], tb in
  let gamma =
    if nonrec then gamma else (x, def_typ)::gamma in
  let (expr_cn, e), elim_cell, preserve = constr_gen_expr gamma e tb in
  let def_cn =
    All (bvs, Impl (chi_b::sig_cn, expr_cn)) in
  let test_cn, tests, elim_cells, more_preserve =
    constr_gen_tests gamma tests in
  chi_id, def_typ,
  cn_and def_cn (cn_and (Ex (vars_of_list [a], A [chi_a])) test_cn),
  e, tests, elim_cell::elim_cells, more_preserve @ preserve

let constr_gen_let gamma p e ta =
  let pcns = constr_gen_pat p ta in
  let bs, exphi, env = envfrag_gen_pat 0 p ta in
  let (cn, e), elim_cell, preserve = constr_gen_expr gamma e ta in
  bs, exphi, env, cn_and pcns cn,
  (p, e), elim_cell, preserve

type solution =
  quant_ops * Terms.formula *
    (int * (Defs.var_name list * Terms.formula)) list

type program = ((int * Defs.loc) list * Terms.struct_item) list

let infer_prog_mockup (prog : program) =
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
        constr_gen_letrec ~nonrec !gamma x e sig_cn t tests in
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
        constr_gen_letrec ~nonrec !gamma x e sig_cn t [] in
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
        constr_gen_let !gamma p e t in
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
      extys @ extys_acc, VarSet.union pres pres_acc, cn_and cn cn_acc)
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
          let a1, a2 =
            try List.find
                  (fun (a1,a2) -> VarMap.mem a1 res_sb &&
                                  VarMap.mem a2 res_sb)
                  ann
            with Not_found ->
              (*[* Format.printf "a1s,a2s=%s@\nres_sb=%a@\nnice_sb=%a@\n%!"
                (String.concat "; "
                   (List.map (fun (a1,a2)->var_str a1^","^var_str a2)
                      ann))
                pr_subst res_sb pr_hvsubst nice_sb; *]*)
              assert false in
          let t1 = hvsubst_typ nice_sb (fst (VarMap.find a1 res_sb))
          and t2 = hvsubst_typ nice_sb (fst (VarMap.find a2 res_sb)) in
          Some (t1, t2)
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

let infer_prog solver prog =
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
          uses_pos_assertions := false;
          let chi_id, _, cn, e, tests, elim_cells, preserve =
            constr_gen_letrec ~nonrec:(pat_loc<>None)
              !gamma x e sig_cn t tests in
          (*[* Format.printf "LetRecVal: x=%s@\ncn=%a@\n%!" x
             pr_cnstrnt cn; *]*)
          let preserve = add_vars preserve
              (VarSet.union (fvs_typ t) (fvs_formula sig_cn)) in
          let q, phi_res, sb_chi =
            solver ~uses_pos_assertions:!uses_pos_assertions
              ~new_ex_types ~preserve cn in
          let elim_extypes = concat_map (!) elim_cells in
          let nice_sb, (vs, phi) =
            try nice_ans (List.assoc chi_id sb_chi)
            with Not_found -> assert false in
          (*[* Format.printf
            "Infer: nice_sb=%a@\n%!" pr_hvsubst nice_sb; *]*)
          (*[* Format.printf
            "Infer: [1] phi_res=%a@\n%!"
            pr_formula phi_res; *]*)
          let sb_res, phi_res =
            separate_subst ~bvs:(vars_of_list (vs @ bvs))
              ~apply:true q phi_res in
          (*[* Format.printf
            "Infer: [2] sb_res=%a@ phi_res=%a@\n%!"
            pr_subst sb_res pr_formula phi_res; *]*)
          (*[* Format.printf
            "Infer: [3] phi=%a@\n%!"
            pr_formula phi; *]*)
          let more_sb, phi =
            separate_subst ~bvs:(vars_of_list (vs @ bvs))
              ~apply:true q phi in
          (*[* Format.printf
            "Infer: [4] more_sb=%a@ phi=%a@\n%!"
            pr_subst more_sb pr_formula phi; *]*)
          let sb = update_sb ~more_sb sb_res in
          (*[* Format.printf
            "Infer: [5] sb=%a@\n%!" pr_subst sb; *]*)
          let e = annotate_expr q sb sb_chi nice_sb e in
          let tests = List.map (annotate_expr q sb sb_chi nice_sb) tests in
          let res, _ = VarMap.find delta sb in
          let gvs = VarSet.elements
              (VarSet.union (fvs_formula phi) (fvs_typ res)) in
          let escaping, gvs = List.partition
              (fun v -> not (List.mem v vs) && q.uni_v v) gvs in
          (*[* Format.printf
            "gvs=%a;@ vs=%a;@ res=%a;@ phi=%a;@ phi_res=%a@\n%!"
            pr_vars (vars_of_list gvs) pr_vars (vars_of_list vs)
            pr_ty res
            pr_formula phi pr_formula phi_res; *]*)
          if escaping <> []
          then raise (Report_toplevel
                        ("Escaping local variables "^
                           String.concat ", " (List.map var_str escaping),
                         Some loc));
          (* There is no need to include parts of [phi_res] in invariant. *)
          let typ_sch = gvs, phi, res in
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
          uses_pos_assertions := false;
          let bs, exphi, env, cn, (p, e), elim_cell, preserve =
            constr_gen_let !gamma p e t in
          (*[* Format.printf "LetVal: p=%a@\ninit_cn=%a@\n%!" pr_pat p
             pr_cnstrnt cn; *]*)
          let preserve = add_vars preserve
              (VarSet.union (fvs_typ t)
                 (VarSet.union (fvs_formula sig_cn) (fvs_formula exphi))) in
          let cn = impl sig_cn cn in
          let cn =
            if sig_vs <> [] then All (vars_of_list sig_vs, cn) else cn in
          let cn =
            if VarSet.is_empty avs then cn else Ex (avs, cn) in
          (*[* Format.printf "LetVal: p=%a@\ncn=%a@\n%!" pr_pat p
             pr_cnstrnt cn; *]*)
          let q, phi, sb_chi = solver
              ~uses_pos_assertions:!uses_pos_assertions
              ~new_ex_types ~preserve cn in
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
                  | TVar v -> Hashtbl.replace v_exty v i
                  | _ -> assert false);
                 (match return_type (subst_typ sb t) with
                  | TVar v -> Hashtbl.replace v_exty v i
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
                  Hashtbl.replace v_exty b (Hashtbl.find chi_exty i)))
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
                     | NotEx (TVar v as t, loc) when Hashtbl.mem v_exty v ->
                       let st =
                         TCons (Extype (Hashtbl.find v_exty v), []) in
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
