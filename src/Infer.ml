(** Inferring and normalizing formulas for InvarGenT.

    Released under the GNU General Public Licence (version 2 or
    higher), NO WARRANTY of correctness etc. (C) Lukasz Stafiniak 2013
    @author Lukasz Stafiniak lukstafi (AT) gmail.com
    @since Mar 2013
*)
open Terms
open Aux

type cnstrnt =
| A of formula
| And of cnstrnt list
| Impl of formula * cnstrnt
| Or of cnstrnt list
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
  | Or cns -> fprintf ppf "@[<2>[";
    pr_sep_list " ∨" pr_cnstrnt ppf cns;
    fprintf ppf "]@]"
  | All (vs, cn) ->
    fprintf ppf "@[<0>∀%a.@ %a@]"
      (pr_sep_list "," pr_tyvar) (VarSet.elements vs) pr_cnstrnt cn
  | Ex (vs, cn) ->
    fprintf ppf "@[<0>∃%a.@ %a@]"
      (pr_sep_list "," pr_tyvar) (VarSet.elements vs) pr_cnstrnt cn

let pr_brs_old ppf brs =
  pr_line_list "| " (fun ppf (prem,(sb, num, so)) ->
    let concl = to_formula sb @ num @ so in
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
  pr_line_list "| " (fun ppf (nonrec, _, prem,concl) ->
    fprintf ppf "@[<2>nonrec=%b;@ %a@ ⟹@ %a@]"
      nonrec pr_formula prem pr_formula concl) ppf brs

let pr_rbrs5 ppf brs =
  (* TODO: print the chiK *)
  pr_line_list "| " (fun ppf (nonrec,_,_,prem,concl) ->
    fprintf ppf "@[<2>nonrec=%b;@ %a@ ⟹@ %a@]"
      nonrec pr_formula prem pr_formula concl) ppf brs


let separate_subst q phi =
  let sb_ty, phi_num, phi_so = unify q phi in
  let sb_num, phi_num = NumS.separate_subst q phi_num in
  let sb = update_sb ~more_sb:sb_num sb_ty in
  sb, phi_num @ subst_formula sb_num phi_so

(** {2 Constraint inference} *)

let ex_intro_elim e =
  let rec aux = function
    | Var _ | Num _
    | Cons _ -> false
    | App (e1, _, _) -> aux e1
    | Lam _ -> false
    | ExLam _ -> true
    | Letrec (_, _, e2, _) -> aux e2
    | Letin (_, _, e2, _) -> true
    | AssertFalse _
    | AssertLeq _
    | AssertEqty _ -> false in
  aux e

(* Global state for fresh variable guarantees: not re-entrant. *)
let fresh_var_id = ref 0
let fresh_chi_id = ref 0
let fresh_expr_var_id = ref 0

let normalize_expr e =
  let rec aux k' e =
    match k', e with
    | Some k, e when not (ex_intro_elim e) ->
      let lc = expr_loc e in
      Letin (PVar ("xcase", lc), aux None e,
             Cons (Extype k, [Var ("xcase", lc)], lc), lc)
    | _, ((Var _ | Num _) as x) -> x
    | _, Cons (k, es, lc) -> Cons (k, List.map (aux None) es, lc)
    | _, App (e1, e2, lc) -> App (aux k' e1, aux None e2, lc)
    | _, Lam (cls, lc) -> Lam (List.map (aux_cl k') cls, lc)
    | None, ExLam (k, cls, lc) ->
      let chi_id = incr fresh_chi_id; !fresh_chi_id in
      let ety_cn = Extype k in
      let ex_sch =
        [delta; delta'],
        [PredVarB (chi_id, tdelta, tdelta', lc)],
        [tdelta], ety_cn, [delta'] in
      (* FIXME: go to [sigma] altogether *)
      Hashtbl.add sigma ety_cn ex_sch;
      new_ex_types := (k, lc) :: !new_ex_types;
      all_ex_types := (k, lc) :: !all_ex_types;
      Lam (List.map (aux_cl (Some k)) cls, lc)
    | Some _, ExLam (_, cls, lc) ->
      Lam (List.map (aux_cl k') cls, lc)
    | _, Letrec (x, e1, e2, lc) ->
      Letrec (x, aux None e1, aux k' e2, lc)
    | _, Letin (p, e1, e2, lc) -> Letin (p, aux None e1, aux k' e2, lc)
    | _, (AssertFalse _ as e) -> e
    | _, AssertLeq (e1, e2, range, lc) ->
      AssertLeq (e1, e2, aux k' range, lc)
    | _, AssertEqty (e1, e2, range, lc) ->
      AssertEqty (e1, e2, aux k' range, lc)
  and aux_cl k' (p, e) = p, aux k' e in
  aux None e

let normalize_item = function
  | (TypConstr _ | ValConstr _ | PrimVal _) as item -> item
  | LetRecVal (x, e, ty, tes, lc) ->
    LetRecVal (x, normalize_expr e, ty, List.map normalize_expr tes, lc)
  | LetVal (p, e, ty, tes, lc) ->
    LetVal (p, normalize_expr e, ty, List.map normalize_expr tes, lc)

let normalize_program = List.map normalize_item

let rec flat_and = function
  | And cns -> concat_map flat_and cns
  | A cns -> List.map (fun cn -> A [cn]) cns
  | cn -> [cn]

let cn_and cn1 cn2 = And (flat_and cn1 @ flat_and cn2)


let fresh_typ_var () =
  incr fresh_var_id; VId (Type_sort, !fresh_var_id)  

let fresh_num_var () =
  incr fresh_var_id; VId (Num_sort, !fresh_var_id)  

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
  | PredVarU (i, t, lc) -> PredVarU (i, freshen_typ env t, lc)
  | PredVarB (i, t1, t2, lc) ->
    PredVarB (i, freshen_typ env t1, freshen_typ env t2, lc)
  | NotEx (t, lc) -> NotEx (freshen_typ env t, lc)

let freshen_cns_scheme (vs, phi, argtys, c_n, c_args) =
  let env = List.map (fun v->v, freshen_var v) vs in
  let argtys = List.map (freshen_typ env) argtys in
  let phi = List.map (freshen_atom env) phi in
  let vs = List.map snd env in
  let c_args = List.map (flip List.assoc env) c_args in
  vs, phi, argtys, c_n, c_args

let freshen_val_scheme (vs, phi, res) =
  let env = List.map (fun v->v, freshen_var v) vs in
  let res = freshen_typ env res in
  let phi = List.map (freshen_atom env) phi in
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
      Format.printf "constructors: %!";
      Hashtbl.iter (fun k _ -> Format.printf "%s, " (cns_str k)) sigma;
      Format.printf "@\n%!";
      (* *)
      let abvs, phi, argtys, c_n, c_args =
        try freshen_cns_scheme (Hashtbl.find sigma k)
        with Not_found -> raise
          (Report_toplevel ("Undefined constructor "^cns_str k, Some loc)) in
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
      Format.printf "envfrag_gen_pat: [%d]@ bs=%a@\n%!"
        count pr_vars (fst3 ef0); (* *)
      List.fold_left envfrag_x ef0 (List.map2 aux argtys ps)
    | PCons (k, ps, loc) ->
      let vs, phi, args, c_n, c_args =
        try freshen_cns_scheme (Hashtbl.find sigma k)
        with Not_found -> raise
          (Report_toplevel ("Undefined constructor "^cns_str k, Some loc)) in
      let res = TCons (c_n, List.map (fun v->TVar v) c_args) in
      let ef0 = vars_of_list vs, Eqty (res, t, loc)::phi, [] in
      Format.printf
        "envfrag_gen_pat: [%d]@ bs=%a@ phi=%a@ args=%a c_args=%a@\n%!"
        count pr_vars (fst3 ef0) pr_formula phi
        (pr_ty false) (TCons (tuple, args)) pr_vars (vars_of_list c_args); (* *)
      List.fold_left envfrag_x ef0 (List.map2 aux args ps) in
  aux t p

let rec single_assert_false (_, e) =
  match e with
    | AssertFalse _ -> true
    | Lam ([cl], loc) -> single_assert_false cl
    | _ -> false

let impl prem concl =
  if prem=[] || concl = A [] || concl = And []
  then concl else Impl (prem, concl)

let letin_count = ref 0

let constr_gen_expr gamma e t =
  let rec aux gamma t e =
    Format.printf "constr_gen: t=%a e=@\n%a@\n%!"
      (pr_ty false) t (pr_expr false) e;
    (* *)
    match e with
    (* function *)
    | Var (x, loc) when not (List.mem_assoc x gamma) ->
      raise (Report_toplevel ("Undefined variable "^x, Some loc))
    | Var (x, loc) ->
      let vs, phi, res = freshen_val_scheme (List.assoc x gamma) in
      Ex (vars_of_list vs, cn_and (A [Eqty (res, t, loc)]) (A phi))
    | Num (i, loc) -> A [Eqty (TCons (CNam "Num", [NCst i]), t, loc)]
    | Cons (CNam "Tuple", args, loc)->
      let argvs = List.map (fun _ -> fresh_typ_var ()) args in
      let argtys = List.map (fun v -> TVar v) argvs in
      let cns = List.map2 (aux gamma) argtys args in
      let tupt = TCons (tuple, argtys) in
      Ex (vars_of_list argvs, And (A [Eqty (t, tupt, loc)]::cns))
    | Cons (k, args, loc) when not (Hashtbl.mem sigma k)->
      raise (Report_toplevel ("Undefined constructor "^cns_str k, Some loc))
    | Cons (k, args, loc)->
      let vs, phi, argtys, c_n, c_args =
        freshen_cns_scheme (Hashtbl.find sigma k) in
      let res = TCons (c_n, List.map (fun v->TVar v) c_args) in
      let cn = List.fold_left cn_and (A (Eqty (res, t, loc)::phi))
        (List.map2 (aux gamma) argtys args) in
      Ex (vars_of_list vs, cn)
    | App (e1, e2, loc) as e ->
      let a = fresh_typ_var () in
      let ta = TVar a in
      Format.printf "constr_gen_expr: App=@\n%a@\n%!"
        (pr_expr false) e; (* *)
      Ex (VarSet.singleton a,
          cn_and (aux gamma (Fun (ta, t)) e1)
            (cn_and (aux gamma (ta) e2) (A [NotEx (ta, loc)])))
    | Lam ([cl], loc) when single_assert_false cl ->
      let a1 = fresh_typ_var () in
      let t1 = TVar a1 in
      let a2 = fresh_typ_var () in
      let t2 = TVar a2 in
      let cn =
        aux_cl_negcn gamma t1 t2
          (Eqty (Fun (t1, t2), t, loc)) cl in
      Ex (vars_of_list [a1; a2], cn)
    | Lam (cls, loc) ->
      let a1 = fresh_typ_var () in
      let t1 = TVar a1 in
      let a2 = fresh_typ_var () in
      let t2 = TVar a2 in
      let cn = List.fold_left cn_and
        (A [Eqty (Fun (t1, t2), t, loc)])
        (List.map (aux_cl 0 gamma t1 t2) cls) in
      Ex (vars_of_list [a1; a2], cn)
    | AssertFalse loc -> A [CFalse loc]
    | AssertLeq (e1, e2, e3, loc) ->
      let a1 = fresh_typ_var () in
      let t1 = TVar a1 in
      let a2 = fresh_typ_var () in
      let t2 = TVar a2 in
      let a3 = fresh_typ_var () in
      let t3 = TVar a3 in
      let nt1 = TCons (CNam "Num", [t1]) in
      let nt2 = TCons (CNam "Num", [t2]) in
      let cn =
        cn_and (A [Leq (t1, t2, loc)])
          (cn_and (aux gamma nt1 e1)
             (cn_and (aux gamma nt2 e2)
                (aux gamma t3 e3))) in
      Ex (vars_of_list [a1; a2; a3], cn)
    | AssertEqty (e1, e2, e3, loc) ->
      let a1 = fresh_typ_var () in
      let t1 = TVar a1 in
      let a2 = fresh_typ_var () in
      let t2 = TVar a2 in
      let a3 = fresh_typ_var () in
      let t3 = TVar a3 in
      let cn =
        cn_and (A [Eqty (t1, t2, loc)])
          (cn_and (aux gamma t1 e1)
             (cn_and (aux gamma t2 e2)
                (aux gamma t3 e3))) in
      Ex (vars_of_list [a1; a2; a3], cn)
    | Letrec (x, e1, e2, loc) ->
      let a = fresh_typ_var () in
      let b = fresh_typ_var () in
      incr fresh_chi_id;
      let tb = TVar b in
      let chi_b = PredVarU (!fresh_chi_id, tb, expr_loc e1) in
      let chi_a = PredVarU (!fresh_chi_id, TVar a, expr_loc e1) in
      let gamma = (x, ([b], [chi_b], tb))::gamma in
      let def_cn =
        All (vars_of_list [b],
             Impl ([chi_b], aux gamma tb e1)) in
      cn_and def_cn (cn_and (Ex (vars_of_list [a], A [chi_a]))
                       (aux gamma t e2))
    | Letin (p, e1, e2, loc) as e ->
      let count = incr letin_count; !letin_count in
      Format.printf "constr_gen-Letin: [%d] starting...@\n%!" count; (* *)
      let a0 = fresh_typ_var () in
      let t0 = TVar a0 in
      let cn0 = aux gamma t0 e1 in
      Format.printf
        "constr_gen-Letin: [%d] generated t0=%a@ cn0=%a@\ne1=%a@\n%!"
        count (pr_ty false) t0 pr_cnstrnt cn0 (pr_expr false) e1; (* *)
      let disjs = List.map
        (fun (i, loc) ->
          aux_cl count gamma t0 t (PCons (Extype i, [p], loc), e2))
        !all_ex_types in
      let altcn =
        cn_and (aux_cl count gamma t0 t (p,e2)) (A [NotEx (t0, loc)]) in
      Format.printf
        "constr_gen-Letin: [%d] t0=%s@ t=%a@ cn0=%a@\naltcn=%a@\ne=%a@\n%!"
        count (var_str a0) (pr_ty false) t pr_cnstrnt cn0 pr_cnstrnt altcn
        (pr_expr false) e;
      (* *)
      Ex (vars_of_list [a0], cn_and cn0 (Or (altcn::disjs)))
    | ExLam (ety_id, cls, loc) -> assert false

  and aux_cl_negcn gamma t1 t2 tcn (p, e) =
    (* Format.printf "aux_cl_negcn: p=@ %a ->@ e= %a@\n%!" (pr_pat false) p
       (pr_expr false) e; * *)
    let pcns = constr_gen_pat p t1 in
    let bs, prem, env = envfrag_gen_pat 0 p t1 in
    let concl = aux (List.map typ_to_sch env @ gamma) t2 e in
    let cn = atoms_of_cnstrnt
      (fun pcns -> Impl (tcn::pcns @ prem, concl)) pcns in
    let res = if VarSet.is_empty bs then cn else All (bs, cn) in
    (* Format.printf "aux_cl_negcn: res=@ %a@\n%!" pr_cnstrnt res; * *)
    res
      
  and aux_cl count gamma t1 t2 (p, e) =
    let pcns = constr_gen_pat p t1 in
    let bs, prem, env = envfrag_gen_pat count p t1 in
    Format.printf "constr_gen-aux_cl: [%d] t1=%a@ t2=%a@ bs=%a@ prem=%a@\n%!"
      count (pr_ty false) t1 (pr_ty false) t2 pr_vars bs pr_formula prem; (* *)
    let concl = aux (List.map typ_to_sch env @ gamma) t2 e in
    let cn = impl prem concl in
    let cn = if VarSet.is_empty bs then cn else All (bs, cn) in
    Format.printf "constr_gen-aux_cl: [%d]@ cn=%a@\n%!"
      count pr_cnstrnt cn; (* *)
    cn_and pcns cn in
  
  aux gamma t e

let constr_gen_tests gamma tests =
  let cns = List.map
    (fun e -> constr_gen_expr gamma e
      (TCons (CNam "Bool", [])))
    tests in
  List.fold_left cn_and (And []) cns

let constr_gen_letrec gamma x e sig_cn tb tests =
  let a = fresh_typ_var () in
  let chi_id = incr fresh_chi_id; !fresh_chi_id in
  let chi_b = PredVarU (chi_id, tb, expr_loc e) in
  let chi_a = PredVarU (chi_id, TVar a, expr_loc e) in
  let bvs = VarSet.union (fvs_typ tb) (fvs_formula sig_cn) in
  let def_typ = VarSet.elements bvs, [chi_b], tb in
  let gamma = (x, def_typ)::gamma in
  let def_cn =
    All (bvs, Impl (chi_b::sig_cn,
                    constr_gen_expr gamma e tb)) in
  let test_cn =
    constr_gen_tests gamma tests in
  chi_id, def_typ,
  cn_and def_cn (cn_and (Ex (vars_of_list [a], A [chi_a])) test_cn)

let constr_gen_let gamma p e ta =
  let pcns = constr_gen_pat p ta in
  let bs, exphi, env = envfrag_gen_pat 0 p ta in
  let cn = constr_gen_expr gamma e ta in
  bs, exphi, env, cn_and pcns cn

type solution =
  quant_ops * Terms.formula *
    (int * (Terms.var_name list * Terms.formula)) list

let infer_prog_mockup prog =
  let gamma = ref [] in
  let cns = List.map (function
    | TypConstr _ -> VarSet.empty, And []
    | ValConstr _ ->
      VarSet.empty, And []
    | PrimVal (x, tsch, loc) ->
      gamma := (x, tsch) :: !gamma;
      VarSet.empty, And []
    | LetRecVal (x, e, defsig, tests, loc) ->
      let bvs, sig_cn, t = match defsig with
        | None ->
          let b = fresh_typ_var () in
          let tb = TVar b in
          [b], [], tb
        | Some (vs, phi, t) -> vs, phi, t in
      let preserve = VarSet.union (fvs_typ t) (fvs_formula sig_cn) in
      let chi_id, typ_sch, cn =
        constr_gen_letrec !gamma x e sig_cn t tests in
      gamma := (x, typ_sch) :: !gamma;
      preserve, cn
    | LetVal (p, e, defsig, tests, loc) ->
      let avs, sig_vs, sig_cn, t = match defsig with
        | None ->
          let a = fresh_typ_var () in
          let ta = TVar a in
          VarSet.singleton a, [], [], ta
        | Some (vs, phi, t) -> VarSet.empty, vs, phi, t in
      let bs, exphi, env, cn =
        constr_gen_let !gamma p e t in
      let preserve = VarSet.union (fvs_typ t)
        (VarSet.union (fvs_formula sig_cn) (fvs_formula exphi)) in
      let cn = impl sig_cn cn in
      let cn =
        if sig_vs <> [] then All (vars_of_list sig_vs, cn) else cn in
      let test_cn = constr_gen_tests !gamma tests in
      let test_cn = impl exphi test_cn in
      let test_cn =
        if not (VarSet.is_empty bs) && test_cn <> And []
        then All (bs, test_cn) else test_cn in
      let cn = cn_and cn test_cn in
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
          Format.printf
            "infer_mockup-LetVal-ex_types: id=%d@ exphi=%a@ ty=%a@\n%!"
            ety_id pr_formula exphi (pr_ty false) res;
          (* *)
          x, ([], [], ety) in
      gamma := map_append typ_sch_ex env !gamma;
      preserve, cn
  ) prog in
  List.fold_right
    (fun (pres, cn) (pres_acc, cn_acc) ->
      VarSet.union pres pres_acc, cn_and cn cn_acc)
    cns (VarSet.empty, And [])

let infer_prog solver prog =
  let gamma = ref [] in
  let update_new_ex_types q sb sb_chi =
    let more_items = ref [] in
    (* FIXME: duplicate with code at the end of [solve].  Clean up
       handling of ex. type parameters. *)
    List.iter
      (fun (ety_id, loc) ->
         let vs, phi, ty, ety_n, pvs =
           Hashtbl.find sigma (Extype ety_id) in
         Format.printf "infer-update-ex_types: from id=%d@ phi=%a@ ty=%a@\n%!"
           ety_id pr_formula phi (pr_ty false) (List.hd ty);
         (* *)
         let extydec = TypConstr (ety_n, List.map var_sort pvs, loc) in
         let extydef = ValConstr
             (ety_n, vs, phi, ty, ety_n, pvs, loc) in
         more_items := extydec :: extydef :: !more_items)
      !new_ex_types;
    new_ex_types := [];
    !more_items in
  let items = concat_map
      (function
        | (TypConstr _ | ValConstr _) as item -> [item]
        | PrimVal (x, tsch, loc) as item ->
          gamma := (x, tsch) :: !gamma;
          [item]
        | LetRecVal (x, e, defsig, tests, loc) ->
          let bvs, sig_cn, t = match defsig with
            | None ->
              let b = fresh_typ_var () in
              let tb = TVar b in
              [b], [], tb
            | Some (vs, phi, t) -> vs, phi, t in
          let chi_id, _, cn =
            constr_gen_letrec !gamma x e sig_cn t tests in
          let preserve = VarSet.union (fvs_typ t) (fvs_formula sig_cn) in
          let q, phi_res, sb_chi = solver ~preserve cn in
          let sb_res, phi_res = separate_subst q phi_res in
          let vs, phi =
            try List.assoc chi_id sb_chi
            with Not_found -> assert false in
          let more_sb, phi = separate_subst q phi in
          let sb = update_sb ~more_sb sb_res in
          let res = subst_typ sb t in
          let gvs = VarSet.elements
              (VarSet.union (fvs_formula phi) (fvs_typ res)) in
          let escaping, gvs = List.partition
              (fun v -> not (List.mem v vs) && q.uni_v v) gvs in
          if escaping <> []
          then raise (Report_toplevel
                        ("Escaping local variables "^
                           String.concat ", " (List.map var_str escaping),
                         Some loc));
          (* There is no need to include parts of [phi_res] in invariant. *)
          let typ_sch = gvs, phi, res in
          gamma := (x, typ_sch) :: !gamma;
          let ex_items =
            update_new_ex_types q sb_res sb_chi in
          ex_items @ [LetRecVal (x, e, Some typ_sch, tests, loc)]
        | LetVal (p, e, defsig, tests, loc) ->
          let avs, sig_vs, sig_cn, t = match defsig with
            | None ->
              let a = fresh_typ_var () in
              let ta = TVar a in
              VarSet.singleton a, [], [], ta
            | Some (vs, phi, t) -> VarSet.empty, vs, phi, t in
          let bs, exphi, env, cn =
            constr_gen_let !gamma p e t in
          let preserve = VarSet.union (fvs_typ t)
              (VarSet.union (fvs_formula sig_cn) (fvs_formula exphi)) in
          let cn = impl sig_cn cn in
          let cn =
            if sig_vs <> [] then All (vars_of_list sig_vs, cn) else cn in
          let test_cn = constr_gen_tests !gamma tests in
          let test_cn = impl exphi test_cn in
          let test_cn =
            if not (VarSet.is_empty bs) && test_cn <> And []
            then All (bs, test_cn) else test_cn in
          let cn = cn_and cn test_cn in
          let q, phi, sb_chi = solver ~preserve cn in
          let sb, phi = separate_subst q phi in
          let ex_items =
            update_new_ex_types q sb sb_chi in
          let res = subst_typ sb t in
          let gvs = VarSet.union (fvs_formula phi) (fvs_typ res) in
          let gvs = VarSet.elements gvs in
          let typ_sch = gvs, phi, res in
          let more_items = ref [] in
          let typ_sch_ex =
            if VarSet.is_empty bs && exphi = []
            then fun (x, res) -> x, (gvs, phi, res)
            else fun (x, res) ->
              let allvs = VarSet.union (fvs_formula exphi) (fvs_typ res) in
              let allvs = VarSet.diff allvs (vars_of_list [delta; delta']) in
              let pvs = VarSet.elements (VarSet.diff allvs bs) in
              let allvs = VarSet.elements allvs in
              let ety_id = incr extype_id; !extype_id in
              let ety_n = Extype ety_id in
              let extydec = TypConstr (ety_n, List.map var_sort pvs, loc) in
              let extydef = ValConstr
                  (ety_n, allvs, phi, [res], ety_n, pvs, loc) in
              more_items := extydef :: extydec :: !more_items;
              let ex_sch = allvs, exphi, [res], ety_n, pvs in
              Hashtbl.add sigma (ety_n) ex_sch;
              all_ex_types := (ety_id, loc) :: !all_ex_types;
              Format.printf "infer-LetVal-ex_types: id=%d@ phi=%a@ ty=%a@\n%!"
                ety_id pr_formula exphi (pr_ty false) res;
              (* *)
              (* Here in [ety] the variables are free, unlike the
                 occurrences in [exphi]. *)
              x, (gvs, phi, TCons (ety_n, List.map (fun v->TVar v) pvs)) in
          gamma := map_append typ_sch_ex env !gamma;
          ex_items @ List.rev !more_items
          @ [LetVal (p, e, Some typ_sch, tests, loc)]
      ) prog in
  List.rev !gamma, items


(** {2 Normalization} *)

type branch = Terms.formula * Terms.formula

let prenexize cn =
  let quants = Hashtbl.create 2048 in
  let univars = Hashtbl.create 32 in
  let allvars = Hashtbl.create 64 in
  let same_tbl = Hashtbl.create 32 in
  let same_as v1 v2 = Hashtbl.replace same_tbl v1 v2 in
  let cmp_v v1 v2 =
    let v1 = try Hashtbl.find same_tbl v1 with Not_found -> v1
    and v2 = try Hashtbl.find same_tbl v2 with Not_found -> v2 in
    try Hashtbl.find quants (v1, v2) with Not_found ->
      let c1 = not (Hashtbl.mem allvars v1)
      and c2 = not (Hashtbl.mem allvars v2) in
      if c1 && c2 then Same_quant
      else if c1 then Right_of
      else if c2 then Left_of
      else (
        Format.printf "cmp_v: unknown vars %s, %s@\n%!"
          (var_str v1) (var_str v2); (* *)
        assert false) in
  let uni_v v =
    let v = try Hashtbl.find same_tbl v with Not_found -> v in
    try Hashtbl.find univars v with Not_found -> false in
  let up_vars = ref VarSet.empty and same_vars = ref VarSet.empty
  and change = ref true and at_uni = ref true in
  let add_var_rels vs =
    VarSet.iter (fun v -> Hashtbl.add allvars v ()) vs;
    VarSet.iter (fun uv ->
        VarSet.iter (fun dv ->
            Hashtbl.add quants (uv,dv) Left_of;
            Hashtbl.add quants (dv,uv) Right_of
          ) vs) !up_vars;
    VarSet.iter (fun av ->
        VarSet.iter (fun bv ->
            Hashtbl.add quants (av,bv) Same_quant;
            Hashtbl.add quants (bv,av) Same_quant) vs) !same_vars;
    VarSet.iter (fun av ->
        VarSet.iter (fun bv ->
            Hashtbl.add quants (av,bv) Same_quant) vs) vs;
    change := true; same_vars := VarSet.union vs !same_vars in
  let alternate () =
    Format.printf "alternate: %s.%a@\n%!" (if !at_uni then "∀" else "∃")
      pr_vars !same_vars;
    up_vars := VarSet.union !same_vars !up_vars;
    same_vars := VarSet.empty;
    change := false; at_uni := not !at_uni in
  let rec aux = function
    | All (vs, cn) when !at_uni ->
      VarSet.iter (fun v -> Hashtbl.add univars v true) vs;
      add_var_rels vs; aux cn
    | Ex (vs, cn) when not !at_uni -> add_var_rels vs; aux cn
    | (All _ | Ex _ | A _) as cn -> cn
    | And cns -> And (List.map aux cns)
    | Or cns -> Or (List.map aux cns)
    | Impl (prem, concl) -> Impl (prem, aux concl) in
  let rec loop cn =
    if !change then (alternate (); loop (aux cn))
    else cn in
  (* Start the prefix from existential quantifiers. *)
  {cmp_v; uni_v; same_as}, loop cn

let normalize q cn =
  let unify ?sb cnj = unify ?sb q cnj in
  (* From unary predicate variable to the existential type of its result. *)
  let chi_exty = Hashtbl.create 2 in
  (* Existential type compatible with the variable. *)
  let v_exchi = Hashtbl.create 8 in
  let v_chi = Hashtbl.create 8 in
  (* Raises [Contradiction] *)
  let simplify_brs = List.map
      (fun (guard_cnj, prem, concl) ->
         (* Past this point, the branches are definitely part of the
              constraint, try not raising contradiction. *)
         if List.exists (function CFalse _ -> true | _ -> false) concl
         then prem, concl
         else
           (* 1 *)
           let sb, _, _ = unify (guard_cnj @ prem @ concl) in
           let concl_typ, concl_num, concl_so = unify concl in
           let concl_so = List.filter
               (function NotEx (_, _) -> false | _ -> true) concl_so in
           (* 2 *)
           List.iter (fun (v, (t, _)) ->
               match return_type t with
               | TCons (Extype i, _) when not (Hashtbl.mem v_exchi v) ->
                 Format.printf
                   "dsj-chi-exty: [2] v=%s i=%d@\n%!"
                   (var_str v) i; (* *)
                 Hashtbl.add v_exchi v i
               | _ -> ())
             sb;
           (* 3 *)
           List.iter
             (function
               | PredVarU (i, TVar b, _) when not (Hashtbl.mem v_chi b) ->
                 Format.printf
                   "dsj-chi-exty: [3] b=%s i=%d@\n%!"
                   (var_str b) i; (* *)
                 Hashtbl.add v_chi b i
               (* | NotEx _ -> assert false *)
               | _ -> ()) (prem @ concl);
           (* 4 *)
           List.iter (fun (v, (t, _)) ->
               match return_type t with
               | TVar w when Hashtbl.mem v_chi v &&
                             not (Hashtbl.mem v_chi w)->
                 Format.printf
                   "dsj-chi-exty: [4] v=%s w=%s i=%d@\n%!"
                   (var_str v) (var_str w) (Hashtbl.find v_chi v); (* *)
                 Hashtbl.add v_chi w (Hashtbl.find v_chi v)
               | _ -> ())
             sb;
           (* 5 *)
           Hashtbl.iter
             (fun b i ->
                if Hashtbl.mem v_exchi b &&
                   not (Hashtbl.mem chi_exty i)
                then (
                  Format.printf
                    "dsj-chi-exty: [5] b=%s i=%d->j=%d@\n%!"
                    (var_str b) i (Hashtbl.find v_exchi b); (* *)
                  Hashtbl.add chi_exty i (Hashtbl.find v_exchi b)))
             v_chi;
           (* 6 *)
           Hashtbl.iter
               (fun b i ->
                  if Hashtbl.mem chi_exty i &&
                     not (Hashtbl.mem v_exchi b)
                  then (
                    Format.printf
                      "dsj-chi-exty: [6] b=%s i=%d->j=%d@\n%!"
                      (var_str b) i (Hashtbl.find chi_exty i); (* *)
                    Hashtbl.replace v_exchi b (Hashtbl.find chi_exty i)))
               v_chi;
           prem,
           to_formula concl_typ @ concl_num @ concl_so) in
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
      [], [prem, concl], []
    | Or cns ->
      [], [], [cns]      
    | All _ | Ex _ -> assert false in
  let rec flat_cn prem guard_cnj cn =
    let cnj, impls, dsjs =
      flat_and cn in
    let guard_cnj = cnj @ guard_cnj in
    let impls = List.map
        (fun (prem, concl) ->
           let prem = List.filter
               (function
                 | Eqty (t1, t2, _) when t1=t2 -> false
                 | a -> not (List.exists (eq_atom a) cnj
                             || List.exists (eq_atom a) guard_cnj)) prem in
           prem, concl)
        impls in
    let br0 = guard_cnj, prem, cnj in
    let dsj_brs1 = List.map
        (fun dsj -> prem, cnj @ guard_cnj, dsj) dsjs in
    let brs, dsj_brs2 = List.split
        (List.map
           (fun (more_prem, concl) ->
              flat_cn
                (more_prem @ prem) guard_cnj concl)
           impls) in
    br0 :: List.concat brs, List.concat (dsj_brs1 :: dsj_brs2) in
  let flat_dsj (more_prem, guard_cnj, cns) =
    guard_cnj, List.map
      (fun cn ->
         cn, flat_cn more_prem guard_cnj cn)
      cns in
  let check_chi_exty =
    List.for_all
      (function
        | v, (TCons (cn, _), _) when Hashtbl.mem v_exchi v ->
          Format.printf "dsj-test: ex case =%s v=%s v_chi=%d@\n%!"
            (cns_str cn) (var_str v) (Hashtbl.find v_exchi v); (* *)
          cn = Extype (Hashtbl.find v_exchi v)
        | _ -> true) in
  let solve_dsj step (guard_cnj, dsjs) =
    let sb, _, _ = unify guard_cnj in
    Format.printf "dsj-checking: init #dsjs=%d@ sb=%a@\n%!"
      (List.length dsjs) pr_subst sb; (* *)
    let first_exn = ref None in
    let check_dsj (_, (brs, dsjs)) =
      Format.printf "dsj-test: starting case.@\n%!"; (* *)
      try
        List.for_all
          (fun (guard_cnj, prem, concl) ->
             List.exists (function CFalse _ -> true | _ -> false) concl
             || (
               Format.printf "dsj-test: br@ prem=%a@ concl=%a@\n%!"
                 pr_formula prem pr_formula concl; (* *)
               let sb', _, so = unify ~sb (guard_cnj @ prem @ concl) in
               Format.printf "dsj-test: br@ sb'=%a@\n%!"
                 pr_subst sb'; (* *)
               List.iter
                 (function
                   | NotEx (TCons (Extype _, _) as t, loc) ->
                     raise (Contradiction
                              (Type_sort, "Should not be existential",
                               Some (t, t), loc))        
                   | NotEx (TVar v as t, loc) when Hashtbl.mem v_exchi v ->
                     let st =
                       TCons (Extype (Hashtbl.find v_exchi v), []) in
                     raise (Contradiction
                              (Type_sort, "Should not be existential",
                               Some (t, st), loc))
                   | _ -> ())
                 so;
               check_chi_exty sb')
          ) brs
      with Contradiction _ as e ->
        Format.printf "test rejected a disjunct!@\nexn=%a@\n%!"
          pr_exception e; (* *)
        if !first_exn = None then first_exn := Some e;
        false in
    let dsjs = List.filter check_dsj dsjs in
    Format.printf "checking: result #dsjs=%d@\n%!"
      (List.length dsjs); (* *)
    match dsjs with
    | [] ->
      Format.printf "checking-Or: none passes@\n%!"; (* *)
      raise (unsome !first_exn)
    | [cn, sol] ->
      (* selected_disj := cn:: !selected_disj; *)
      Left sol
    | (cn, sol)::_ when step > 0 ->
      (* selected_disj := cn:: !selected_disj; *)
      Left sol
    | _ -> Right (guard_cnj, dsjs) in
  let concat_brs more_brs =
    let brs, dsjs = List.split more_brs in
    List.concat brs, List.concat dsjs in
  let prepare_brs (brs, dsjs) =
    let dsjs = List.map flat_dsj dsjs in
    let brs = simplify_brs brs in
    brs, dsjs in
  let rec loop step (brs, dsj_brs) =
    Format.printf
      "normalize-loop: init step=%d #dsj_brs=%d@\n%!"
      step (List.length dsj_brs);
    (* *)
    let more_brs, dsj_brs = partition_map (solve_dsj step) dsj_brs in
    let more_brs, more_dsj = prepare_brs (concat_brs more_brs) in
    let dsj_brs = more_dsj @ dsj_brs in
    Format.printf
      "normalize-loop: step=%d #dsj_brs=%d brs=@\n%a@\nmore_brs=@\n%a@\n%!"
      step (List.length dsj_brs) pr_brs brs pr_brs more_brs;
    (* *)
    if more_brs = [] then brs, dsj_brs
    else loop step (more_brs @ brs, dsj_brs) in
  let sol0 = flat_cn [] [] cn in
  let brs_dsj_brs = ref (prepare_brs sol0) in
  for i=0 to 1 do brs_dsj_brs := loop i !brs_dsj_brs done;
  let brs, dsj_brs = !brs_dsj_brs in
  assert (dsj_brs = []);
  brs

let vs_hist_typ increase =
  typ_fold {(typ_make_fold (fun _ _ -> ()) ())
            with fold_tvar = (fun v -> increase v)}

let vs_hist_atom increase = function
  | Eqty (t1, t2, _) | Leq (t1, t2, _) ->
    vs_hist_typ increase t1; vs_hist_typ increase t2
  | CFalse _ -> ()
  | PredVarU (_, t, _) -> vs_hist_typ increase t
  | PredVarB (_, t1, t2, _) ->
    vs_hist_typ increase t1; vs_hist_typ increase t2
  | NotEx (t, _) -> vs_hist_typ increase t

let vs_hist_sb increase sb =
  List.iter (fun (v,(t,_)) -> increase v; vs_hist_typ increase t) sb

let simplify preserve q brs =
  (* Prune "implies true" branches. *)
  let brs = List.filter
    (function _, [] -> false | _ -> true) brs in
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
    | Eqty (TVar v, _, _) | Leq (TVar v, _, _)
    | Eqty (_, TVar v, _) | Leq (_, TVar v, _) ->
      not (VarSet.mem v preserve) && count v = 1
      && (in_prem || not (q.uni_v v))       (* FIXME: use cmp_v? *)
    | _ -> false in
  let nonred_pr_atom a = not (redundant_atom true a) in
  let nonred_atom a = not (redundant_atom false a) in
  let brs = List.map
    (fun (prem,concl) ->
      List.filter nonred_pr_atom prem,
      List.filter nonred_atom concl)
    brs in
  (* Merge branches with the same premise. *)
  (* Roughly like [map_reduce (@) [] brs] *)
  let equiv cnj1 cnj2 =
    let c1_ty, c1_num, c1_so = unify q cnj1 in
    let c2_ty, c2_num, c2_so = unify q cnj2 in
    let c1_ty = List.map (fun (v,(t,_)) -> v,t) c1_ty
    and c2_ty = List.map (fun (v,(t,_)) -> v,t) c2_ty
    and c1_num = replace_loc dummy_loc c1_num
    and c2_num = replace_loc dummy_loc c2_num
    and c1_so = replace_loc dummy_loc c1_so
    and c2_so = replace_loc dummy_loc c2_so in
    let res =
      List.sort compare c1_ty = List.sort compare c2_ty &&
      (* NumS.equivalent q c1_num c2_num && *)
      List.sort compare c1_num = List.sort compare c2_num &&
      List.sort compare c1_so = List.sort compare c2_so in
    Format.printf
      "simplify: equiv? res=%b ty=%b num=%b so=%b@\nc1=%a@\nc2=%a@\n%!"
      res (List.sort compare c1_ty = List.sort compare c2_ty)
      (* (NumS.equivalent q c1_num c2_num)  *)
      (List.sort compare c1_num = List.sort compare c2_num)
      (List.sort compare c1_so = List.sort compare c2_so)
      pr_formula cnj1 pr_formula cnj2; (* *)
    res in
  let rec meet prem concl = function
    | [] -> raise Not_found
    | (prem2, concl2 as br) :: brs ->
      if equiv prem prem2 then (prem, concl @ concl2) :: brs
      else br :: meet prem concl brs in
  let rec merge acc = function
    | [] -> List.rev acc
    | (prem, concl as br) :: brs ->
      try merge acc (meet prem concl brs)
      with Not_found -> merge (br::acc) brs in
  let short_brs, long_brs = List.partition
    (function [],_  | [_],_ (* | [_;_],_ *) -> true | _ -> false)
    (merge [] brs) in
  short_brs @ long_brs

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
  (* FIXME: conflicts with named variables? *)
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

let nicevars_v env = function
  | VNam _ as v -> v
  | VId (s, id) as v ->
    try VNam (s, List.assoc id env.nvs_env)
    with Not_found -> v

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
  | PredVarU (i, t, lc) -> PredVarU (i, nicevars_typ env t, lc)
  | PredVarB (i, t1, t2, lc) ->
    PredVarB (i, nicevars_typ env t1, nicevars_typ env t2, lc)
  | NotEx (t, lc) -> NotEx (nicevars_typ env t, lc)

let nicevars_vs vs =
  let vs' = map_some
    (function VNam _ -> None | VId (s,id) -> Some (s,id)) vs in
  let env = List.fold_left (fun env ->
    function Num_sort,id -> next_num env id
    | Type_sort,id -> next_typ env id)
    nicevars_empty vs' in
  let vs = List.map
    (function VNam _ as v -> v
    | VId (s, id) -> VNam (s, List.assoc id env.nvs_env)) vs in
  env, vs

let nicevars_struct_item = function
  | TypConstr _ as i -> i
  | ValConstr (n, vs, phi, tys, c_n, c_args, loc) ->
    let env, vs = nicevars_vs vs in
    let phi = List.map (nicevars_atom env) phi in
    let tys = List.map (nicevars_typ env) tys in
    let c_args = List.map (nicevars_v env) c_args in
    ValConstr (n, vs, phi, tys, c_n, c_args, loc)
  | PrimVal (x, (vs, phi, ty), loc) ->
    let env, vs = nicevars_vs vs in
    let phi = List.map (nicevars_atom env) phi in
    let ty = nicevars_typ env ty in
    PrimVal (x, (vs, phi, ty), loc)    
  | LetRecVal (_, _, None, _, _) as i -> i
  | LetRecVal (x, e, Some (vs, phi, ty), tests, loc) ->
    let env, vs = nicevars_vs vs in
    let phi = List.map (nicevars_atom env) phi in
    let ty = nicevars_typ env ty in
    LetRecVal (x, e, Some (vs, phi, ty), tests, loc)
  | LetVal (_, _, None, _, _) as i -> i
  | LetVal (p, e, Some (vs, phi, ty), tests, loc) ->
    let env, vs = nicevars_vs vs in
    let phi = List.map (nicevars_atom env) phi in
    let ty = nicevars_typ env ty in
    LetVal (p, e, Some (vs, phi, ty), tests, loc)  

let reset_state () =
  fresh_expr_var_id := 0; fresh_var_id := 0; fresh_chi_id := 0
