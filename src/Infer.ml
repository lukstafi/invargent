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
| Or of (formula * answer) list * (answer option -> cnstrnt)
(** If the first formula holds, pass the second formula to get the
    constraint. The constructor name is the existential type which
    gives [SameExistential]. *)
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
  | Or (cases, cns) -> fprintf ppf "@[<2>[";
    let disjs = List.map
      (fun (cond,arg) -> And [A cond; cns (Some arg)]) cases in
    pr_sep_list " ∨" pr_cnstrnt ppf disjs;
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


let separate_subst cmp_v uni_v phi =
  let sb_ty, phi_num, phi_so = unify cmp_v uni_v phi in
  let sb_num, phi_num = NumS.separate_subst cmp_v uni_v phi_num in
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
    | ExCase _ -> true
    | Letrec (_, _, e2, _) -> aux e2
    | Letin (_, _, e2, _) -> true
    | AssertFalse _
    | AssertLeq _
    | AssertEqty _ -> false in
  aux e

let fresh_expr_var_id = ref 0

let normalize_expr e =
  let rec aux k' = function
    | e when k' <> None && not (ex_intro_elim e) ->
      let lc = expr_loc e in
      Letin (PVar ("xcase", lc), aux None e,
             ExCase (unsome k', Var ("xcase", lc), lc), lc)
    | (Var _ | Num _) as x -> x
    | Cons (k, es, lc) -> Cons (k, List.map (aux None) es, lc)
    | App (e1, e2, lc) -> App (aux k' e1, aux None e2, lc)
    | Lam (cls, lc) -> Lam (List.map (aux_cl k') cls, lc)
    | ExLam (k, cls, lc) when k' = None ->
      ExLam (k, List.map (aux_cl (Some k)) cls, lc)
    | ExLam (k, cls, lc) ->
      ExLam (unsome k', List.map (aux_cl k') cls, lc)
    | ExCase (k, e, lc) -> assert false
    | Letrec (x, e1, e2, lc) ->
      Letrec (x, aux None e1, aux k' e2, lc)
    | Letin (p, e1, e2, lc) -> Letin (p, aux None e1, aux k' e2, lc)
    | AssertFalse _ as e -> e
    | AssertLeq (e1, e2, range, lc) ->
      AssertLeq (e1, e2, aux k' range, lc)
    | AssertEqty (e1, e2, range, lc) ->
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

(* Global state for fresh variable guarantees: not re-entrant. *)
let fresh_var_id = ref 0
let fresh_chi_id = ref 0


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
    | PCons ("Tuple", args, loc) ->
      let argvs = List.map (fun _ -> fresh_typ_var ()) args in
      let argtys = List.map (fun v -> TVar v) argvs in
      let cns = List.map2 aux argtys args in
      let tupt = TCons (CNam "Tuple", argtys) in
      Ex (vars_of_list argvs, And (A [Eqty (tupt, tau, loc)]::cns))
    | PCons (k, args, loc) ->
      Format.printf "constructors: %!";
      Hashtbl.iter (fun k _ -> Format.printf "%s, " k) sigma;
      Format.printf "@\n%!";
      (* *)
      let abvs, phi, argtys, c_n, c_args =
        try freshen_cns_scheme (Hashtbl.find sigma k)
        with Not_found -> raise
          (Report_toplevel ("Undefined constructor "^k, Some loc)) in
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

let rec envfrag_gen_pat p t =
  let rec aux t = function
    | Zero | One _ -> envfrag_empty
    | PVar (x, _) -> VarSet.empty, [], [x, t]
    | PAnd (p1, p2, _) ->
      envfrag_x (aux t p1) (aux t p2)
    | PCons ("Tuple", ps, loc) ->
      let argvs = List.map (fun _ -> fresh_typ_var ()) ps in
      let argtys = List.map (fun v -> TVar v) argvs in
      let res = TCons (CNam "Tuple", argtys) in
      let ef0 = vars_of_list argvs, [Eqty (res, t, loc)], [] in
      List.fold_left envfrag_x ef0 (List.map2 aux argtys ps)
    | PCons (k, ps, loc) ->
      let vs, phi, args, c_n, c_args =
        try freshen_cns_scheme (Hashtbl.find sigma k)
        with Not_found -> raise
          (Report_toplevel ("Undefined constructor "^k, Some loc)) in
      let res = TCons (c_n, List.map (fun v->TVar v) c_args) in
      let ef0 = vars_of_list vs, Eqty (res, t, loc)::phi, [] in
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

let constr_gen_expr gamma e t =
  let chiK_t2 = ref [] in
  let rec aux gamma excase_env t e =
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
    | Cons ("Tuple", args, loc)->
      let argvs = List.map (fun _ -> fresh_typ_var ()) args in
      let argtys = List.map (fun v -> TVar v) argvs in
      let cns = List.map2 (aux gamma excase_env) argtys args in
      let tupt = TCons (CNam "Tuple", argtys) in
      Ex (vars_of_list argvs, And (A [Eqty (t, tupt, loc)]::cns))
    | Cons (k, args, loc) when not (Hashtbl.mem sigma k)->
      raise (Report_toplevel ("Undefined constructor "^k, Some loc))
    | Cons (k, args, loc)->
      let vs, phi, argtys, c_n, c_args =
        freshen_cns_scheme (Hashtbl.find sigma k) in
      let res = TCons (c_n, List.map (fun v->TVar v) c_args) in
      let cn = List.fold_left cn_and (A (Eqty (res, t, loc)::phi))
        (List.map2 (aux gamma excase_env) argtys args) in
      Ex (vars_of_list vs, cn)
    | App (e1, e2, loc) ->
      let a = fresh_typ_var () in
      Ex (VarSet.singleton a,
          cn_and (aux gamma excase_env (Fun (TVar a, t)) e1)
            (aux gamma excase_env (TVar a) e2))
    | Lam ([cl], loc) when single_assert_false cl ->
      let a1 = fresh_typ_var () in
      let t1 = TVar a1 in
      let a2 = fresh_typ_var () in
      let t2 = TVar a2 in
      let cn =
        aux_cl_negcn gamma excase_env t1 t2
          (Eqty (Fun (t1, t2), t, loc)) cl in
      Ex (vars_of_list [a1; a2], cn)
    | Lam (cls, loc) ->
      let a1 = fresh_typ_var () in
      let t1 = TVar a1 in
      let a2 = fresh_typ_var () in
      let t2 = TVar a2 in
      let cn = List.fold_left cn_and
        (A [Eqty (Fun (t1, t2), t, loc)])
        (List.map (aux_cl gamma excase_env t1 t2) cls) in
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
          (cn_and (aux gamma excase_env nt1 e1)
             (cn_and (aux gamma excase_env nt2 e2)
                (aux gamma excase_env t3 e3))) in
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
          (cn_and (aux gamma excase_env t1 e1)
             (cn_and (aux gamma excase_env t2 e2)
                (aux gamma excase_env t3 e3))) in
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
             Impl ([chi_b], aux gamma excase_env tb e1)) in
      cn_and def_cn (cn_and (Ex (vars_of_list [a], A [chi_a]))
                       (aux gamma excase_env t e2))
    | Letin (p, e1, e2, loc) ->
      let a0 = fresh_typ_var () in
      let t0 = TVar a0 in
      let cn0 = aux gamma excase_env t0 e1 in
      let a3 = fresh_typ_var () in
      let t3 = TVar a3 in
      let disjs =
        Hashtbl.fold
          (fun i sch disjs ->
             let vs, phi, ty, c_n, pvs = freshen_cns_scheme sch in
             let ty = match ty with [ty] -> ty | _ -> assert false in
             let phi = Eqty (t3, ty, loc)::phi in
             let evs = list_diff vs pvs in
             (pvs,
              ([Eqty (TCons (c_n, List.map (fun v->TVar v) pvs), t0, loc)],
               (evs, phi)))
             ::disjs)
          ex_types [] in
      let allpvs, disjs = List.split disjs in
      let concl = aux_cl gamma excase_env t3 t (p, e2) in
      let altcn = aux gamma excase_env t (App (Lam ([p,e2],loc),e1,loc)) in
      Format.printf
        "constr_gen-Letin: t3=%s t0=%s@ t=%a@ concl=%a@ disj_prem=@\n| %a@\n%!"
        (var_str a3) (var_str a0) (pr_ty false) t
        pr_cnstrnt concl
        (pr_sep_list "| " pr_formula) (List.map fst disjs);
      (* *)
      let impls = function
        | Some (evs, phi) ->
          Format.printf "letin-impls: Existential a0=%s a3=%s@\n%!"
            (var_str a0) (var_str a3); (* *)
          All (vars_of_list (a3::evs), impl phi concl)
        | None ->
          Format.printf "letin-impls: not ex. a0=%s@\n%!"
            (var_str a0); (* *)
          altcn  in
      (* We need to quantify [allpvs] outside rather than each [pvs]
         inside disjunction because the variables need already be in
         [q] when the guards are checked. *)
      Ex (vars_of_list (a0::List.concat allpvs),
          cn_and cn0 (Or (disjs, impls)))
    | ExLam (ety_id, cls, loc) ->
      let a1 = fresh_typ_var () in
      let t1 = TVar a1 in
      let (a2, t2), nu_a2 =
        try List.assoc ety_id !chiK_t2, false
        with Not_found ->
          let a2 = fresh_typ_var () in
          let t2 = TVar a2 in
          (* push on top *)
          chiK_t2 := (ety_id, (a2, t2)) :: !chiK_t2;
          (a2, t2), true in
      let ety_cn = Extype ety_id in
      let ety = TCons (ety_cn, [t2]) in
      let chi_id =
        try
          let _, ex_phi, _, _, _ = Hashtbl.find ex_types ety_id in
          match ex_phi with
          | PredVarB (id, _, _, _)::_ -> id
          | _ -> assert false
        with Not_found ->
          let chi_id = incr fresh_chi_id; !fresh_chi_id in
          let ex_sch =
            [delta; delta'],
            [PredVarB (chi_id, tdelta, tdelta', loc)],
            [tdelta], ety_cn, [delta'] in
          Hashtbl.add ex_types ety_id ex_sch;
          new_ex_types := (ety_id, loc) :: !new_ex_types;
          chi_id in
      Format.printf
        "infer-ExLam-ex_types: id=%d chi_id=%d a1=%s a2=%s@ nu_a2=%b@\n%!"
        ety_id chi_id (var_str a1) (var_str a2) nu_a2;
      (* *)
      let cn = List.fold_left cn_and
        (A [Eqty (Fun (t1, ety), t, loc)])
        (List.map (aux_ex_cl gamma excase_env ety_id chi_id t1 t2) cls) in
      (* pop when done *)
      if nu_a2 then (
        match !chiK_t2 with
        | (ety_id', (a2', _)) :: tl when ety_id' = ety_id && a2' = a2 ->
          chiK_t2 := tl
        | _ -> assert false);
      Ex (vars_of_list (if nu_a2 then [a1; a2] else [a1]), cn)         
    | ExCase (ety_id, e, lc) ->
      let cn = aux gamma excase_env t e in
      let chi_id, t1, t2 = List.assoc ety_id excase_env in
      cn_and cn (A [PredVarB (chi_id, t1, t2, lc)])

  and aux_cl_negcn gamma excase_env t1 t2 tcn (p, e) =
    (* Format.printf "aux_cl_negcn: p=@ %a ->@ e= %a@\n%!" (pr_pat false) p
       (pr_expr false) e; * *)
    let pcns = constr_gen_pat p t1 in
    let bs, prem, env = envfrag_gen_pat p t1 in
    let concl = aux (List.map typ_to_sch env @ gamma) excase_env t2 e in
    let cn = atoms_of_cnstrnt
      (fun pcns -> Impl (tcn::pcns @ prem, concl)) pcns in
    let res = if VarSet.is_empty bs then cn else All (bs, cn) in
    (* Format.printf "aux_cl_negcn: res=@ %a@\n%!" pr_cnstrnt res; * *)
    res
      

  and aux_cl gamma excase_env t1 t2 (p, e) =
    let pcns = constr_gen_pat p t1 in
    let bs, prem, env = envfrag_gen_pat p t1 in
    let concl = aux (List.map typ_to_sch env @ gamma) excase_env t2 e in
    let cn = impl prem concl in
    let cn = if VarSet.is_empty bs then cn else All (bs, cn) in
    Format.printf "constr_gen-aux_cl: t1=%a@ t2=%a@ cn=%a@\n%!"
      (pr_ty false) t1 (pr_ty false) t2 pr_cnstrnt cn; (* *)
    cn_and pcns cn

  and aux_ex_cl gamma excase_env ety_id chi_id t1 t2 (p, e) =
    let pcns = constr_gen_pat p t1 in
    let bs, prem, env = envfrag_gen_pat p t1 in
    let a3 = fresh_typ_var () in
    let t3 = TVar a3 in
    let concl =
      aux (List.map typ_to_sch env @ gamma)
        ((ety_id,(chi_id,t3,t2))::excase_env) t3 e in
    let cn = impl prem (Ex (VarSet.singleton a3, concl)) in
    let cn = if VarSet.is_empty bs then cn else All (bs, cn) in
    Format.printf
      "constr_gen-aux_ex_cl: ety=%d chi=%d t1=%a@ t2=%a @ t3=%a@ cn=%a@\n%!"
      ety_id chi_id (pr_ty false) t1 (pr_ty false) t2 (pr_ty false) t3
      pr_cnstrnt cn; (* *)
    cn_and pcns cn in
  
  aux gamma [] t e

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
  let bs, exphi, env = envfrag_gen_pat p ta in
  let cn = constr_gen_expr gamma e ta in
  bs, exphi, env, cn_and pcns cn

type solution =
  (Terms.var_name -> Terms.var_name -> Terms.var_scope) *
    (Terms.var_name -> bool) * Terms.formula *
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
          Hashtbl.add ex_types ety_id ex_sch;
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
  let update_new_ex_types cmp_v uni_v sb sb_chi =
    let more_items = ref [] in
    (* FIXME: duplicate with code at the end of [solve].  Clean up
       handling of ex. type parameters. *)
    List.iter
      (fun (ety_id, loc) ->
         let vs, phi, ty, ety_n, pvs = Hashtbl.find ex_types ety_id in
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
          let cmp_v, uni_v, phi_res, sb_chi = solver ~preserve cn in
          let sb_res, phi_res = separate_subst cmp_v uni_v phi_res in
          let vs, phi =
            try List.assoc chi_id sb_chi
            with Not_found -> assert false in
          let more_sb, phi = separate_subst cmp_v uni_v phi in
          let sb = update_sb ~more_sb sb_res in
          let res = subst_typ sb t in
          let gvs = VarSet.elements
              (VarSet.union (fvs_formula phi) (fvs_typ res)) in
          let escaping, gvs = List.partition
              (fun v -> not (List.mem v vs) && uni_v v) gvs in
          if escaping <> []
          then raise (Report_toplevel
                        ("Escaping local variables "^
                           String.concat ", " (List.map var_str escaping),
                         Some loc));
          (* There is no need to include parts of [phi_res] in invariant. *)
          let typ_sch = gvs, phi, res in
          gamma := (x, typ_sch) :: !gamma;
          let ex_items =
            update_new_ex_types cmp_v uni_v sb_res sb_chi in
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
          let cmp_v, uni_v, phi, sb_chi = solver ~preserve cn in
          let sb, phi = separate_subst cmp_v uni_v phi in
          let ex_items =
            update_new_ex_types cmp_v uni_v sb sb_chi in
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
              Hashtbl.add ex_types ety_id ex_sch;
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


let normalize cn =
  let quants = Hashtbl.create 2048 in
  let univars = Hashtbl.create 128 in
  let cmp_v v1 v2 =
    try Hashtbl.find quants (v1, v2) with Not_found -> Not_in_scope in
  let uni_v  v =
    try Hashtbl.find univars v with Not_found -> false in
  let unify ?sb cnj = unify ?sb cmp_v uni_v cnj in
  (* From unary predicate variable to the existential type of its result. *)
  let chi_exchi = Hashtbl.create 2 in
  (* Existential type compatible with the variable. *)
  let v_exchi = Hashtbl.create 4 in
  let simplify_brs = List.map
    (fun (prem,concl as br) ->
      try
        let concl_typ, concl_num, concl_so = unify concl in
        List.iter
          (function
          | PredVarU (i, TVar b, _) ->
            (if List.mem_assoc b concl_typ
             then match return_type (fst (List.assoc b concl_typ)) with
             | TCons (Extype j, _) ->
               Format.printf
                 "chi-exchi: add chi_exchi b=%s i=%d->j=%d@ ty=%a@\n%!"
                 (var_str b) i j
                 (pr_ty false) (fst (List.assoc b concl_typ)); (* *)
               Hashtbl.add chi_exchi i j
             | _ -> ())
          | _ -> ()) prem;
        List.iter
          (function
          | PredVarU (i, TVar b, _) when Hashtbl.mem chi_exchi i ->
            (if List.mem_assoc b concl_typ
             then match return_type (fst (List.assoc b concl_typ)) with
             | TVar v ->
               Format.printf
                 "chi-exchi: add v_exchi i=%d b=%s v=%s->j=%d@ ty=%a@\n%!"
                 i (var_str b) (var_str v) (Hashtbl.find chi_exchi i)
                 (pr_ty false) (fst (List.assoc b concl_typ)); (* *)
               Hashtbl.add v_exchi v (Hashtbl.find chi_exchi i)
             | _ -> ())
          | _ -> ()) concl_so;
        prem,
        to_formula concl_typ @ concl_num @ concl_so
      with Contradiction _ ->
        (* We could replace the conclusion with [CFalse] if it weren't
           reserved to represent [assert false] -- i.e. expected
           falsehood, negated constraint. *)
        br) in
  let add_var_rels up_vars same_vars vs =
    VarSet.iter (fun uv ->
      VarSet.iter (fun dv ->
        Hashtbl.add quants (uv,dv) Upstream;
        Hashtbl.add quants (dv,uv) Downstream
      ) vs) up_vars;
    VarSet.iter (fun av ->
      VarSet.iter (fun bv ->
        Hashtbl.add quants (av,bv) Same_quant;
        Hashtbl.add quants (bv,av) Same_quant) vs) same_vars;
    VarSet.iter (fun av ->
      VarSet.iter (fun bv ->
        Hashtbl.add quants (av,bv) Same_quant) vs) vs in
  let rec flat_and up_vars same_vars at_uni = function
    | A cns -> cns, [], []
    | And cns ->
      let cnj, impls, dsjs =
        split3 (List.map (flat_and up_vars same_vars at_uni) cns) in
      let cnj = List.concat cnj
      and impls = List.concat impls
      and dsjs = List.concat dsjs in
      cnj, impls, dsjs
    | Impl ([], concl) -> flat_and up_vars same_vars at_uni concl
    | Impl (prem, concl) ->
      [], [up_vars, same_vars, at_uni, prem, concl], []
    | Or (cases, cns) ->
      [], [], [up_vars, same_vars, at_uni, cases, cns]      
    | All (vs, cn) ->
      if at_uni
      then add_var_rels up_vars same_vars vs
      else add_var_rels (VarSet.union up_vars same_vars) VarSet.empty vs;
      VarSet.iter (fun v->Hashtbl.add univars v true) vs;
      if at_uni
      then flat_and up_vars (VarSet.union vs same_vars) true cn
      else flat_and (VarSet.union up_vars same_vars) vs true cn
    | Ex (vs, cn) ->
      if not at_uni
      then add_var_rels up_vars same_vars vs
      else add_var_rels (VarSet.union up_vars same_vars) VarSet.empty vs;
      VarSet.iter (fun v->Hashtbl.add univars v false) vs;
      if not at_uni
      then flat_and up_vars (VarSet.union vs same_vars) false cn
      else flat_and (VarSet.union up_vars same_vars) vs false cn in
  let rec flat_cn up_vars same_vars at_uni prem guard_cnj cn =
    let cnj, impls, dsjs =
      flat_and up_vars same_vars at_uni cn in
    let impls = List.map
      (fun (up_vars, same_vars, at_uni, prem, concl) ->
        let prem = List.filter
          (function
          | Eqty (t1, t2, _) when t1=t2 -> false
          | a -> not (List.exists (eq_atom a) cnj
                         || List.exists (eq_atom a) guard_cnj)) prem in
        up_vars, same_vars, at_uni, prem, concl)
      impls in
    let br0 = prem, cnj in
    let dsj_brs1 = List.map
      (fun dsj -> prem, cnj @ guard_cnj, dsj) dsjs in
    let brs, dsj_brs2 = List.split
      (List.map
         (fun (up_vars, same_vars, at_uni, more_prem, concl) ->
           flat_cn up_vars same_vars at_uni
             (more_prem @ prem) (cnj @ guard_cnj) concl)
         impls) in
    br0 :: List.concat brs, List.concat (dsj_brs1 :: dsj_brs2) in
  let rec loop step (brs, dsj_brs) =
    Format.printf
      "normalize-loop: init step=%d #dsj_brs=%d@\n%!"
      step (List.length dsj_brs);
    (* *)
    let check_dsj (more_prem, guard_cnj,
                   (up_vars, same_vars, at_uni, cases, cns)) =
      Format.printf "checking: init #cases=%d cns(NotEx)=%a@\n%!"
        (List.length cases) pr_cnstrnt (cns None); (* *)
      let cases = List.filter
        (function
        | (Eqty (TCons (Extype i, _), TVar v, _) :: _, _
              | Eqty (TVar v, TCons (Extype i, _), _) :: _, _)
            when Hashtbl.mem v_exchi v ->
          Format.printf "test: ex case i=%d v=%s v_chi=%d@\n%!"
            i (var_str v) (Hashtbl.find v_exchi v); (* *)
          Hashtbl.find v_exchi v = i
        | case, (_, phi) ->
          try
            let sb, _, _ = unify case in
            Format.printf "test: case=%a@\nsb=%a@\n%!"
              pr_formula (case @ more_prem) pr_subst sb; (* *)
            Format.printf "cn_arg=Ex: phi=%a@\n%!" pr_formula phi;
            List.iter (fun (prem,concl) ->
              Format.printf "test: br@ prem=%a@ concl=%a@\n%!"
                pr_formula prem pr_formula concl; (* *)
              let sb', _, _ = unify ~sb (prem @ concl) in
              Format.printf "test: br@ sb'=%a@\n%!"
                pr_subst sb'; (* *)
            ) brs;
            true
          with Contradiction _ as e ->
            Format.printf "test rejected a disjunct!@\nexn=%a@\n%!"
              pr_exception e; (* *)
            false)
        cases in
      Format.printf "checking: result #cases=%d@\n%!"
        (List.length cases); (* *)
      match cases with
      | [] ->
        Format.printf "checking-Or: not ex.@\n%!"; (* *)
        Left (flat_cn up_vars same_vars at_uni more_prem guard_cnj
                (cns None))
      | [case, cn_arg] when step > 0 ->
        let brs, dsj_brs = flat_cn
          up_vars same_vars at_uni more_prem guard_cnj
          (cn_and (A case) (cns (Some cn_arg))) in
        Left (brs, dsj_brs)
      | _ -> Right (more_prem, guard_cnj,
                    (up_vars, same_vars, at_uni, cases, cns)) in
    let more_brs, dsj_brs = partition_map check_dsj dsj_brs in
    let more_brs, more_dsj = List.split more_brs in
    let more_brs = simplify_brs (List.concat more_brs)
    and dsj_brs = List.concat (more_dsj @ [dsj_brs]) in
    Format.printf
      "normalize-loop: step=%d #dsj_brs=%d brs=@\n%a@\nmore_brs=@\n%a@\n%!"
      step (List.length dsj_brs) pr_brs brs pr_brs more_brs;
    (* *)
    if more_brs = [] then brs, dsj_brs
    else loop step (more_brs @ brs, dsj_brs) in
  let brs, dsj_brs =
    flat_cn VarSet.empty VarSet.empty false [] [] cn in
  let brs_dsj_brs = ref (simplify_brs brs, dsj_brs) in
  for i=0 to 1 do brs_dsj_brs := loop i !brs_dsj_brs done;
  let brs, dsj_brs = !brs_dsj_brs in
  assert (dsj_brs = []);
  cmp_v, univars, brs

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

let vs_hist_sb increase sb =
  List.iter (fun (v,(t,_)) -> increase v; vs_hist_typ increase t) sb

let simplify preserve cmp_v uni_v brs =
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
      && (in_prem || not (uni_v v))       (* FIXME: use cmp_v? *)
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
    let c1_ty, c1_num, c1_so = unify cmp_v uni_v cnj1 in
    let c2_ty, c2_num, c2_so = unify cmp_v uni_v cnj2 in
    let c1_ty = List.map (fun (v,(t,_)) -> v,t) c1_ty
    and c2_ty = List.map (fun (v,(t,_)) -> v,t) c2_ty
    and c1_num = replace_loc dummy_loc c1_num
    and c2_num = replace_loc dummy_loc c2_num
    and c1_so = replace_loc dummy_loc c1_so
    and c2_so = replace_loc dummy_loc c2_so in
    let res =
      List.sort compare c1_ty = List.sort compare c2_ty &&
      (* NumS.equivalent cmp_v uni_v c1_num c2_num && *)
      List.sort compare c1_num = List.sort compare c2_num &&
      List.sort compare c1_so = List.sort compare c2_so in
    Format.printf
      "simplify: equiv? res=%b ty=%b num=%b so=%b@\nc1=%a@\nc2=%a@\n%!"
      res (List.sort compare c1_ty = List.sort compare c2_ty)
      (* (NumS.equivalent cmp_v uni_v c1_num c2_num)  *)
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
    (function [],_ | [_],_ | [_;_],_ -> true | _ -> false)
    (merge [] brs) in
  short_brs @ long_brs

let prune_cn cmp_v uni_v brs cn =
  let brs = List.map
      (fun (prem, _) ->
         prem,
         concat_map
           (fun (prem2,concl) ->
              if subformula prem2 prem then concl else [])
           brs)
      brs in
  let test_brs = List.filter
      (fun (prem,concl) ->
         try ignore (unify cmp_v uni_v (prem@concl)); true
         with Contradiction _ as e ->
           Format.printf
             "prune_cn: discarded branch@\n%a@ ⟹@ %a@\nreason: %a@\n%!"
             pr_formula prem pr_formula concl pr_exception e; (* *)
           false)
      brs in
  let rec aux = function
    | A _ as a -> a
    | And cns -> And (List.map aux cns)
    | Impl (prem, concl) -> Impl (prem, aux concl)
    | Or (conds, cn) ->
      (* of cns_name * (formula * answer) list * (answer option -> cnstrnt) *)
      let conds = List.filter
          (fun (c,_) ->
             Format.printf "prune_cn: trying=@ %a...@\n%!"
               pr_formula c; (* *)
             try
               List.iter (fun (prem,concl) ->
                   Format.printf "prune_cn: at@ %a@\n%!"
                     pr_formula (c@prem@concl); (* *)
                   ignore (unify cmp_v uni_v (c@prem@concl)))
                 test_brs;
               Format.printf "prune_cn: passed@\n%!"; (* *)
               true
             with Contradiction _ ->
               Format.printf "prune_cn: rejected@\n%!"; (* *)
               false)
          conds in
      (match conds with
       | [] ->
         Format.printf "prune_cn: as not ex., result=@\n%a@\n%!"
           pr_cnstrnt (cn None); (* *)
         aux (cn None)
       | [guard, ans] ->
         Format.printf "prune_cn: as guard=@ %a@\n%!"
           pr_formula guard; (* *)
         aux (cn_and (A guard) (cn (Some ans)))
       | _ ->
         Format.printf "prune_cn: ambiguous disjunction, cases=@\n%a@\n%!"
           (pr_line_list "| " pr_formula) (List.map fst conds); (* *)
         assert false)
    | All (vs, cn) -> All (vs, aux cn)
    | Ex (vs, cn) -> Ex (vs, aux cn) in
  aux cn

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
