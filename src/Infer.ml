(** Inferring and normalizing formulas for InvarGenT.

    Released under the GNU General Public Licence (version 2 or
    higher), NO WARRANTY of correctness etc. (C) Lukasz Stafiniak 2013
    @author Lukasz Stafiniak lukstafi (AT) gmail.com
    @since Mar 2013
*)
open Terms

exception Contradiction of string * (typ * typ) option * loc

type cnstrnt =
| A of atom list
| And of cnstrnt list
| Or1 of atom list
| Impl of atom list * cnstrnt
| ImplOr2 of atom list list * cnstrnt * cnstrnt
| All of VarSet.t * cnstrnt
| Ex of VarSet.t * cnstrnt

(** {2 Constraint inference} *)

let rec flat_and = function
  | And cns -> Aux.concat_map flat_and cns
  | A cns -> List.map (fun cn -> A [cn]) cns
  | cn -> [cn]

let cn_and cn1 cn2 = And (flat_and cn1 @ flat_and cn2)

(* Global state for fresh variable guarantees: not re-entrant. *)
let fresh_var_id = ref 0
let fresh_chi_id = ref 0


let fresh_typ_var () =
  incr fresh_var_id; VId (Type_sort, !fresh_var_id)  

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
  | PredVarU (i, t) -> PredVarU (i, freshen_typ env t)
  | PredVarB (i, t1, t2) ->
    PredVarB (i, freshen_typ env t1, freshen_typ env t2)

let freshen_cns_scheme (vs, phi, argtys, res) =
  let env = List.map (fun v->v, freshen_var v) vs in
  let res = freshen_typ env res in
  let argtys = List.map (freshen_typ env) argtys in
  let phi = List.map (freshen_atom env) phi in
  let vs = List.map snd env in
  vs, phi, argtys, res

let freshen_val_scheme (vs, phi, res) =
  let vs, phi, _, res = freshen_cns_scheme (vs, phi, [], res) in
  vs, phi, res

type sigma =
  (string,
   Terms.var_name list * Terms.atom list * Terms.typ list * Terms.typ)
    Hashtbl.t

let constr_gen_pat sigma p tau =
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
      let abvs, phi, argtys, res =
        try freshen_cns_scheme (Hashtbl.find sigma k)
        with Not_found -> failwith ("constr_gen_pat: not found "^k) in
      let avs = fvs_typ res in
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

let rec envfrag_gen_pat sigma p t =
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
      let vs, phi, args, res =
        try freshen_cns_scheme (Hashtbl.find sigma k)
        with Not_found -> failwith ("envfrag_gen_pat: not found "^k) in
      let ef0 = vars_of_list vs, Eqty (res, t, loc)::phi, [] in
      List.fold_left envfrag_x ef0 (List.map2 aux args ps) in
  aux t p

let constr_gen_expr gamma sigma ex_types e t =
  let rec aux gamma t = function
    | Var (x, loc) when not (List.mem_assoc x gamma) ->
      raise (Report_toplevel ("Undefined variable "^x, Some loc))
    | Var (x, loc) ->
      let vs, phi, res = freshen_val_scheme (List.assoc x gamma) in
      Ex (vars_of_list vs, cn_and (A [Eqty (res, t, loc)]) (A phi))
    | Num (i, loc) -> A [Eqty (TCons (CNam "Num", [NCst i]), t, loc)]
    | Cons ("Tuple", args, loc)->
      let argvs = List.map (fun _ -> fresh_typ_var ()) args in
      let argtys = List.map (fun v -> TVar v) argvs in
      let cns = List.map2 (aux gamma) argtys args in
      let tupt = TCons (CNam "Tuple", argtys) in
      Ex (vars_of_list argvs, And (A [Eqty (t, tupt, loc)]::cns))
    | Cons (k, args, loc) when not (Hashtbl.mem sigma k)->
      raise (Report_toplevel ("Undefined constructor "^k, Some loc))
    | Cons (k, args, loc)->
      let vs, phi, argtys, res =
        try freshen_cns_scheme (Hashtbl.find sigma k)
        with Not_found -> failwith ("constr_gen_expr: not found "^k)
      in
      let cn = List.fold_left cn_and (A (Eqty (res, t, loc)::phi))
        (List.map2 (aux gamma) argtys args) in
      Ex (vars_of_list vs, cn)
    | App (e1, e2, loc) ->
      let a = fresh_typ_var () in
      Ex (VarSet.singleton a,
          cn_and (aux gamma (Fun (TVar a, t)) e1) (aux gamma (TVar a) e2))
    | Lam (cls, loc) ->
      let a1 = fresh_typ_var () in
      let t1 = TVar a1 in
      let a2 = fresh_typ_var () in
      let t2 = TVar a2 in
      let cn = List.fold_left cn_and
        (A [Eqty (Fun (t1, t2), t, loc)])
        (List.map (aux_cl gamma t1 t2) cls) in
      Ex (vars_of_list [a1; a2], cn)
    | ExLam (ety_id, cls, loc) ->
      let a1 = fresh_typ_var () in
      let t1 = TVar a1 in
      let a2 = fresh_typ_var () in
      let t2 = TVar a2 in
      let ety_cn = Extype ety_id in
      let ety = TCons (ety_cn, [t2]) in
      incr fresh_chi_id;
      let ex_phi t2 t3 = [PredVarB (!fresh_chi_id, t2, t3)] in
      ex_types := (ety_cn, ex_phi, loc) :: !ex_types;
      let cn = List.fold_left cn_and
        (A [Eqty (Fun (t1, ety), t, loc)])
        (List.map (aux_ex_cl gamma !fresh_chi_id t1 t2) cls) in
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
             (cn_and (aux gamma nt2 e2) (aux gamma t3 e3))) in
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
             (cn_and (aux gamma t2 e2) (aux gamma t3 e3))) in
      Ex (vars_of_list [a1; a2; a3], cn)
    | Letrec (x, e1, e2, loc) ->
      let a = fresh_typ_var () in
      let b = fresh_typ_var () in
      incr fresh_chi_id;
      let tb = TVar b in
      let chi_b = PredVarU (!fresh_chi_id, tb) in
      let chi_a = PredVarU (!fresh_chi_id, TVar a) in
      let gamma = (x, ([b], [chi_b], tb))::gamma in
      let def_cn =
        All (vars_of_list [b],
             Impl ([chi_b], aux gamma tb e1)) in
      cn_and def_cn (cn_and (Ex (vars_of_list [a], A [chi_a]))
                       (aux gamma t e2))
    | Letin (p, e1, e2, loc) ->
      let a0 = fresh_typ_var () in
      let t0 = TVar a0 in
      let a2 = fresh_typ_var () in
      let t2 = TVar a2 in
      let disj = List.map
        (fun (ety_cn, phi, loc) -> Eqty (TCons (ety_cn, [t2]), t0, loc))
        !ex_types in
      let cn0 = aux gamma t0 e1 in
      let a3 = fresh_typ_var () in
      let t3 = TVar a3 in
      let disj_prem = List.map
        (fun (ety_cn, phi, loc) ->
          Eqty (TCons (ety_cn, [t2]), t0, loc) :: phi t2 t3)
        !ex_types in
      let concl = aux_cl gamma t3 t (p, e2) in
      let altcn = aux gamma t (App (Lam ([p,e2],loc),e1,loc)) in
      Ex (vars_of_list [a0; a2],
          cn_and (cn_and (A disj) cn0)
            (All (vars_of_list [a3], ImplOr2 (disj_prem, concl, altcn))))

  and aux_cl gamma t1 t2 (p, e) =
    let pcns = constr_gen_pat sigma p t1 in
    let bs, prem, env = envfrag_gen_pat sigma p t1 in
    let concl = aux (List.map typ_to_sch env @ gamma) t2 e in
    let cn =
      if prem=[] || concl=And [] then concl else Impl (prem, concl) in
    let cn = if VarSet.is_empty bs then cn else All (bs, cn) in
    cn_and pcns cn

  and aux_ex_cl gamma chi_id t1 t2 (p, e) =
    let pcns = constr_gen_pat sigma p t1 in
    let bs, prem, env = envfrag_gen_pat sigma p t1 in
    let a3 = fresh_typ_var () in
    let t3 = TVar a3 in
    let concl = aux (List.map typ_to_sch env @ gamma) t3 e in
    let cn = cn_and (A [PredVarB (chi_id, t2, t3)]) concl in
    let cn =
      if prem=[] || concl=And [] then cn else Impl (prem, cn) in
    let cn = if VarSet.is_empty bs then cn else All (bs, cn) in
    cn_and pcns cn in
  
  aux gamma t e

let constr_gen_tests gamma sigma ex_types tests =
  let cns = List.map
    (fun e -> constr_gen_expr gamma sigma ex_types e
      (TCons (CNam "Bool", [])))
    tests in
  List.fold_left cn_and (And []) cns

let constr_gen_letrec gamma sigma ex_types x e sig_cn tb tests =
  let a = fresh_typ_var () in
  let chi_id = incr fresh_chi_id; !fresh_chi_id in
  let chi_b = PredVarU (chi_id, tb) in
  let chi_a = PredVarU (chi_id, TVar a) in
  let bvs = VarSet.union (fvs_typ tb) (fvs_formula sig_cn) in
  let def_typ = VarSet.elements bvs, [chi_b], tb in
  let gamma = (x, def_typ)::gamma in
  let def_cn =
    All (bvs, Impl (chi_b::sig_cn,
                    constr_gen_expr gamma sigma ex_types e tb)) in
  let test_cn =
    constr_gen_tests gamma sigma ex_types tests in
  chi_id, def_typ,
  cn_and def_cn (cn_and (Ex (vars_of_list [a], A [chi_a])) test_cn)

let constr_gen_let gamma sigma ex_types p e ta =
  let pcns = constr_gen_pat sigma p ta in
  let bs, exphi, env = envfrag_gen_pat sigma p ta in
  let cn = constr_gen_expr gamma sigma ex_types e ta in
  bs, exphi, env, cn_and pcns cn

type solution =
  (Terms.subst * Terms.formula) *
    (int * (Terms.typ -> Terms.subst * Terms.atom list)) list *
    (int * (Terms.var_name -> Terms.var_name -> Terms.subst * Terms.formula))
    list

let infer_prog_mockup prog =
  let gamma = ref [] in
  let sigma = Hashtbl.create 127 in
  let ex_types = ref [] in
  let cns = List.map (function
    | TypConstr _ -> And []
    | ValConstr (CNam x, vs, phi, args, res, loc) ->
      Hashtbl.add sigma x (vs, phi, args, res);
      And []
    | ValConstr (Extype _ as n, vs, phi, [arg],
                 TCons (Extype _, targs), loc) ->
      let ex_phi t2 t3 =
        Eqty (t3, arg, loc) ::
          Eqty (t2, TCons (CNam "Tuple", targs), loc) :: phi in
      ex_types := (n, ex_phi, loc) :: !ex_types;
      And []
    | ValConstr (Extype _, _, _, _, _, _) -> assert false
    | PrimVal (x, tsch, loc) ->
      gamma := (x, tsch) :: !gamma;
      And []
    | LetRecVal (x, e, defsig, tests, loc) ->
      let bvs, sig_cn, t = match defsig with
        | None ->
          let b = fresh_typ_var () in
          let tb = TVar b in
          [b], [], tb
        | Some (vs, phi, t) -> vs, phi, t in
      let chi_id, typ_sch, cn =
        constr_gen_letrec !gamma sigma ex_types x e sig_cn t tests in
      gamma := (x, typ_sch) :: !gamma;
      cn
    | LetVal (p, e, defsig, tests, loc) ->
      let avs, sig_vs, sig_cn, t = match defsig with
        | None ->
          let a = fresh_typ_var () in
          let ta = TVar a in
          VarSet.singleton a, [], [], ta
        | Some (vs, phi, t) -> VarSet.empty, vs, phi, t in
      let bs, exphi, env, cn =
        constr_gen_let !gamma sigma ex_types p e t in
      let cn =
        if sig_cn=[] || cn=And [] then cn else Impl (sig_cn, cn) in
      let cn =
        if sig_vs <> [] then All (vars_of_list sig_vs, cn) else cn in
      let test_cn = constr_gen_tests !gamma sigma ex_types tests in
      let test_cn =
        if exphi=[] || test_cn=And [] then test_cn
        else Impl (exphi, test_cn) in
      let test_cn =
        if not (VarSet.is_empty bs) && test_cn <> And []
        then All (bs, test_cn) else test_cn in
      let cn = cn_and cn test_cn in
      (* WARNING: dropping constraints on introduced variables *)
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
          let ex_phi t2 t3 =
            Eqty (t3, res, loc) :: Eqty (t2, ety, loc) :: exphi in
          ex_types := (ety_cn, ex_phi, loc) :: !ex_types;
          x, ([], [], ety) in
      gamma := Aux.map_append typ_sch_ex env !gamma;
      cn
  ) prog in
  List.fold_right cn_and cns (And [])

let infer_prog solver prog =
  let gamma = ref [] in
  let sigma = Hashtbl.create 127 in
  let ex_types = ref [] in
  let update_new_ex_types old_ex_types sb sb_chi =
    let more_items = ref [] in
    ex_types := Aux.map_upto old_ex_types
      (fun (ety_cn, phi, loc) ->
        let a2 = fresh_typ_var () in
        let t2 = TVar a2 in
        let a3 = fresh_typ_var () in
        let t3 = TVar a3 in
        match phi t2 t3 with
        | [PredVarB (chi_id, vt2, vt3)] when vt2=t2 && vt3=t3 ->
          let more_sb, cond = List.assoc chi_id sb_chi a2 a3 in
          let sb = update_sb ~more_sb sb in
          let res = try List.assoc a2 sb with Not_found -> t2 in
          let arg = try List.assoc a3 sb with Not_found -> t3 in
          let resvs = fvs_typ res in
          let vs = VarSet.elements
            (VarSet.union resvs
               (VarSet.union (fvs_formula cond) (fvs_typ arg))) in
          let resvs = VarSet.elements resvs in
          let targs = List.map (fun v -> TVar v) resvs in
          let ety = TCons (ety_cn, targs) in
          let sorts = List.map var_sort resvs in
          let extydec =
            TypConstr (ety_cn, sorts, loc) in
          let extydef =
            ValConstr (ety_cn, vs, cond, [arg], ety, loc) in
          more_items := extydec :: extydef :: !more_items;
          let ex_phi t2 t3 =
            Eqty (t3, arg, loc) :: Eqty (t2, ety, loc) :: cond in
          ety_cn, ex_phi, loc
        | _ -> assert false
      )
      !ex_types;
    !more_items in
  Aux.concat_map (function
  | TypConstr _ as item -> [item]
  | ValConstr (CNam x, vs, phi, args, res, loc) as item ->
    Hashtbl.add sigma x (vs, phi, args, res);
    [item]
  | ValConstr (Extype _ as n, vs, phi, [arg],
               TCons (Extype _, targs), loc) as item ->
    let ex_phi t2 t3 =
      Eqty (t3, arg, loc) ::
        Eqty (t2, TCons (CNam "Tuple", targs), loc) :: phi in
    ex_types := (n, ex_phi, loc) :: !ex_types;
    [item]
  | ValConstr (Extype _, _, _, _, _, _) -> assert false
  | PrimVal (x, tsch, loc) as item ->
    gamma := (x, tsch) :: !gamma;
    [item]
  | LetRecVal (x, e, defsig, tests, loc) ->
    let old_ex_types = !ex_types in
    let bvs, sig_cn, t = match defsig with
      | None ->
        let b = fresh_typ_var () in
        let tb = TVar b in
        [b], [], tb
      | Some (vs, phi, t) -> vs, phi, t in
    let chi_id, _, cn =
      constr_gen_letrec !gamma sigma ex_types x e sig_cn t tests in
    let (sb_res, phi_res), sb_chiU, sb_chiB = solver cn in
    let more_sb, phi = List.assoc chi_id sb_chiU t in
    let sb = update_sb ~more_sb sb_res in
    let phi = subst_formula sb (phi_res @ phi) in
    let res = subst_typ sb t in
    let gvs = VarSet.union (fvs_formula phi) (fvs_typ res) in
    let typ_sch = VarSet.elements gvs, phi, res in
    gamma := (x, typ_sch) :: !gamma;
    let ex_items = update_new_ex_types old_ex_types sb sb_chiB in
    ex_items @ [LetRecVal (x, e, Some typ_sch, tests, loc)]
  | LetVal (p, e, defsig, tests, loc) ->
    let old_ex_types = !ex_types in
    let avs, sig_vs, sig_cn, t = match defsig with
      | None ->
        let a = fresh_typ_var () in
        let ta = TVar a in
        VarSet.singleton a, [], [], ta
      | Some (vs, phi, t) -> VarSet.empty, vs, phi, t in
    let bs, exphi, env, cn =
      constr_gen_let !gamma sigma ex_types p e t in
    let cn =
      if sig_cn=[] || cn=And [] then cn else Impl (sig_cn, cn) in
    let cn =
      if sig_vs <> [] then All (vars_of_list sig_vs, cn) else cn in
    let test_cn = constr_gen_tests !gamma sigma ex_types tests in
    let test_cn =
      if exphi=[] || test_cn=And [] then test_cn
      else Impl (exphi, test_cn) in
    let test_cn =
      if not (VarSet.is_empty bs) && test_cn <> And []
      then All (bs, test_cn) else test_cn in
    let cn = cn_and cn test_cn in
    let (sb, phi), sb_chiU, sb_chiB = solver cn in
    let ex_items = update_new_ex_types old_ex_types sb sb_chiB in
    let res = subst_typ sb t in
    let gvs = VarSet.union (fvs_formula phi) (fvs_typ res) in
    let gvs = VarSet.elements gvs in
    let typ_sch = gvs, phi, res in
    let more_items = ref [] in
    let typ_sch_ex =
      if VarSet.is_empty bs && exphi = []
      then fun (x, res) -> x, (gvs, phi, res)
      else fun (x, res) ->
        let vs = VarSet.union (fvs_formula exphi) (fvs_typ res) in
        let resvs = VarSet.elements (VarSet.diff vs bs) in
        let vs = VarSet.elements vs in
        let targs = List.map (fun v -> TVar v) resvs in
        let ety_id = incr extype_id; !extype_id in
        let ety_cn = Extype ety_id in
        let ety = TCons (ety_cn, targs) in
        let sorts = List.map var_sort resvs in
        let extydec =
          TypConstr (ety_cn, sorts, loc) in
        let extydef =
          ValConstr (ety_cn, vs, exphi, [res], ety, loc) in
        more_items := extydec :: extydef :: !more_items;
        let ex_phi t2 t3 =
          Eqty (t3, res, loc) :: Eqty (t2, ety, loc) :: exphi in
        ex_types := (ety_cn, ex_phi, loc) :: !ex_types;
        x, (gvs, phi, ety) in
    gamma := Aux.map_append typ_sch_ex env !gamma;
    ex_items @ !more_items @ [LetVal (p, e, Some typ_sch, tests, loc)]
  ) prog

(** {2 Normalization} *)

type var_scope =
| Upstream | Downstream | Not_in_scope

let normalize cn =
  let quants = Hashtbl.create 2047 in
  let cmp_vars v1 v2 =
    try Hashtbl.find quants (v1, v2) with Not_found -> Not_in_scope in
  cmp_vars, []
  

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
  | PredVarU (i, t) -> PredVarU (i, nicevars_typ env t)
  | PredVarB (i, t1, t2) ->
    PredVarB (i, nicevars_typ env t1, nicevars_typ env t2)

let nicevars_cnstrnt c =
  let rec aux env = function
    | A atoms -> A (List.map (nicevars_atom env) atoms)
    | And cns -> And (List.map (aux env) cns)
    | Or1 disjs -> Or1 (List.map (nicevars_atom env) disjs)
    | ImplOr2 (disjs, concl, altcn) -> ImplOr2
      (List.map (List.map (nicevars_atom env)) disjs,
       aux env concl, aux env altcn)
    | Impl (prem, concl) ->
      Impl (List.map (nicevars_atom env) prem, aux env concl)
    | All (vs, cn) ->
      let vs' = Aux.map_some
        (function VNam _ -> None | VId (s,id) -> Some (s,id))
        (VarSet.elements vs) in
      let env = List.fold_left (fun env ->
        function Num_sort,id -> next_num env id
        | Type_sort,id -> next_typ env id
        | Undefined_sort,_ -> assert false) nicevars_empty vs' in
      let vs = List.map
        (function VNam _ as v -> v
        | VId (s, id) -> VNam (s, List.assoc id env.nvs_env))
        (VarSet.elements vs) in
      All (vars_of_list vs, aux env cn)
    | Ex (vs, cn) ->
      let vs' = Aux.map_some
        (function VNam _ -> None | VId (s,id) -> Some (s,id))
        (VarSet.elements vs) in
      let env = List.fold_left (fun env ->
        function Num_sort,id -> next_num env id
        | Type_sort,id -> next_typ env id
        | Undefined_sort,_ -> assert false) env vs' in
      let vs = List.map
        (function VNam _ as v -> v
        | VId (s, id) -> VNam (s, List.assoc id env.nvs_env))
        (VarSet.elements vs) in
      Ex (vars_of_list vs, aux env cn) in
  aux {nvs_env = []; last_typ = 0; last_num = 0} c

let nicevars_vs vs =
  let vs' = Aux.map_some
    (function VNam _ -> None | VId (s,id) -> Some (s,id)) vs in
  let env = List.fold_left (fun env ->
    function Num_sort,id -> next_num env id
    | Type_sort,id -> next_typ env id
    | Undefined_sort,_ -> assert false) nicevars_empty vs' in
  let vs = List.map
    (function VNam _ as v -> v
    | VId (s, id) -> VNam (s, List.assoc id env.nvs_env)) vs in
  env, vs

let nicevars_struct_item = function
  | TypConstr _ as i -> i
  | ValConstr (n, vs, phi, tys, ty, loc) ->
    let env, vs = nicevars_vs vs in
    let phi = List.map (nicevars_atom env) phi in
    let tys = List.map (nicevars_typ env) tys in
    let ty = nicevars_typ env ty in
    ValConstr (n, vs, phi, tys, ty, loc)
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

open Format

let rec pr_cnstrnt ppf = function
  | A atoms -> pr_formula ppf atoms
  | And cns -> fprintf ppf "@[<0>";
    pr_sep_list " ∧" pr_cnstrnt ppf cns; fprintf ppf "@]"
  | Or1 disjs -> fprintf ppf "@[<0>[";
    pr_sep_list " ∨" pr_atom ppf disjs; fprintf ppf "]@]"
  | Impl (prem,concl) -> fprintf ppf "@[<2>";
    pr_formula ppf prem; fprintf ppf "@ ⟹@ %a@]" pr_cnstrnt concl
  | ImplOr2 (disjs, concl, altcn) -> fprintf ppf "@[<2>[";
    pr_sep_list " ∨" pr_formula ppf disjs;
    fprintf ppf "]@ ⟹@ %a@]@[<2>[or@ %a]@]"
      pr_cnstrnt concl pr_cnstrnt altcn
  | All (vs, cn) ->
    fprintf ppf "@[<0>∀%a.@ %a@]"
      (pr_sep_list "," pr_tyvar) (VarSet.elements vs) pr_cnstrnt cn
  | Ex (vs, cn) ->
    fprintf ppf "@[<0>∃%a.@ %a@]"
      (pr_sep_list "," pr_tyvar) (VarSet.elements vs) pr_cnstrnt cn
