(** Solving second-order i.e. formula variables for InvarGenT.

    Released under the GNU General Public Licence (version 2 or
    higher), NO WARRANTY of correctness etc. (C) Lukasz Stafiniak 2013
    @author Lukasz Stafiniak lukstafi (AT) gmail.com
    @since Mar 2013
*)
open Terms
open Aux

type chi_subst = (int * (var_name list * formula)) list

let sb_typ_unary arg =
  typ_map {typ_id_map with map_tvar = fun v ->
    if v = delta then arg else TVar v}  

let sb_typ_binary arg1 arg2 =
  typ_map {typ_id_map with map_tvar = fun v ->
    if v = delta then arg1 else if v = delta' then arg2 else TVar v}  

let sb_atom_unary arg = function
  | Eqty (t1, t2, lc) ->
    Eqty (sb_typ_unary arg t1, sb_typ_unary arg t2, lc)
  | Leq (t1, t2, lc) ->
    Leq (sb_typ_unary arg t1, sb_typ_unary arg t2, lc)
  | CFalse _ as a -> a
  | PredVarU (_, t) -> assert false
  | PredVarB (_, t1, t2) -> assert false

let sb_atom_binary arg1 arg2 = function
  | Eqty (t1, t2, lc) ->
    Eqty (sb_typ_binary arg1 arg2 t1, sb_typ_binary arg1 arg2 t2, lc)
  | Leq (t1, t2, lc) ->
    Leq (sb_typ_binary arg1 arg2 t1, sb_typ_binary arg1 arg2 t2, lc)
  | CFalse _ as a -> a
  | PredVarU (_, t) -> assert false
  | PredVarB (_, t1, t2) -> assert false

let sb_phi_unary arg = List.map (sb_atom_unary arg)

let sb_phi_binary arg1 arg2 = List.map (sb_atom_binary arg1 arg2)

type q_with_bvs = {
  cmp_v : var_name -> var_name -> var_scope;
  uni_v : var_name -> bool;
  positive_b : var_name -> bool;
  add_b_vs : var_name -> var_name list -> unit;
  set_b_uni : bool -> unit;
  b_vs : (var_name, VarSet.t) Hashtbl.t;
  b_qvs : (var_name, var_name list) Hashtbl.t;
  add_bchi : var_name -> int -> bool -> unit;
  find_b : int -> var_name list;
  find_chi : var_name -> int;
  mutable allbvs : VarSet.t;
  mutable allchi : Ints.t;
  mutable negbs : var_name list;
}
  
let new_q cmp_v uni_v =
  let same_q = Hashtbl.create 32 in
  let posi_b = Hashtbl.create 16 in
  let cmp_v v1 v2 =
    let v1 = try Hashtbl.find same_q v1 with Not_found -> v1 in
    let v2 = try Hashtbl.find same_q v1 with Not_found -> v2 in
    cmp_v v1 v2 in
  let b_is_uni = ref true in
  let uni_v v =
    if Hashtbl.mem same_q v then
      let bv = Hashtbl.find same_q v in
      not (Hashtbl.mem posi_b bv) && !b_is_uni
    else uni_v v in
  let positive_b v = Hashtbl.mem posi_b v in
  let b_vs = Hashtbl.create 16 in
  let b_qvs = Hashtbl.create 16 in
  let chi_b = Hashtbl.create 16 in
  let b_chi = Hashtbl.create 16 in
  let find_b i = Hashtbl.find_all chi_b i in
  let find_chi b = Hashtbl.find b_chi b in
  let rec add_bchi b i posi =
    if Hashtbl.mem b_chi b
    then assert (Hashtbl.find b_chi b = i)
    else (
      if posi then Hashtbl.add posi_b b ()
      else q.negbs <- b::q.negbs;
      q.allchi <- Ints.add i q.allchi;
      Hashtbl.add chi_b i b;
      Hashtbl.add b_chi b i;
      q.add_b_vs b [b])
  and add_b_vs b vs =
    assert (Hashtbl.mem b_chi b);
    List.iter (fun v -> Hashtbl.add same_q v b) vs;
    q.allbvs <- VarSet.union q.allbvs (vars_of_list vs);
    try
      let ovs = Hashtbl.find b_vs b in
      Hashtbl.replace b_vs b (VarSet.union ovs (vars_of_list vs));
      let qvs = try Hashtbl.find b_qvs b with Not_found -> [] in
      let vs = List.filter (fun v -> not (List.mem v qvs)) vs in
      Hashtbl.replace b_qvs b (vs @ qvs);
    with Not_found -> Hashtbl.add b_vs b (vars_of_list vs)
  and q = {
    cmp_v; uni_v; add_b_vs;
    set_b_uni = (fun b -> b_is_uni := b); allchi = Ints.empty;
    b_vs; b_qvs; allbvs = VarSet.empty; add_bchi; find_b; find_chi;
    positive_b; negbs = [];
  } in q

(* Return renaming of [nvs] into [ovs], creating fresh [ovs] when
   needed and adding them as locals of [b] in [q]. *)
let matchup_vars q b nvs =
  let rec loop acc = function
    | [], [] -> acc
    | [], _ -> assert false
    | nv::nvs, ov::ovs -> loop ((nv, (TVar ov, dummy_loc))::acc) (nvs, ovs)
    | nvs, [] ->
      let ovs = List.map Infer.freshen_var nvs in
      q.add_b_vs b ovs; loop acc (nvs, ovs) in
  let locals = Hashtbl.find q.b_qvs b in
  loop [] (List.rev nvs, List.rev locals)

let sb_atom_pred q posi psb = function
  | PredVarU (i, (TVar b as t)) as a ->
    (try
       let vs, phi = List.assoc i psb in
       if not posi
       then sb_phi_unary t phi
       else
         let renaming = matchup_vars q b vs in
         sb_phi_unary t (subst_formula renaming phi)
     with Not_found -> [a])  
  | PredVarB (i, (TVar b as t1), t2) as a ->
    (try
       let vs, phi = List.assoc i psb in
       let renaming = matchup_vars q b vs in
       sb_phi_binary t1 t2 (subst_formula renaming phi)
     with Not_found -> [a])
  | a -> [a]

let sb_formula_pred q posi psb phi =
  concat_map (sb_atom_pred q posi psb) phi

let sb_brs_pred q psb brs = List.map
  (fun (prem,concl) ->
    sb_formula_pred q false psb prem, sb_formula_pred q true psb concl)
  brs

type state = subst * NumS.state

let empty_state : state = [], NumS.empty_state

let holds q ?params (ty_st, num_st) cnj =
  let ty_st, num_cnj, _ =
    unify ~use_quants:true ?params ~sb:ty_st q.cmp_v q.uni_v cnj in
  let num_st = NumS.holds q.cmp_v q.uni_v num_st num_cnj in
  ty_st, num_st

(* 5 *)
let select check_max_b q ans ans_min ans_max =
  let allmax = concat_map snd ans_max
  and allmin = concat_map snd ans_min in
  let init_res = list_diff ans allmax in
  let cands = list_diff allmax allmin in
  (* Raises [Contradiction] here if solution impossible. *)
  let init_state = holds q empty_state init_res in
  let rec loop state ans_res ans_p = function
    | [] -> ans_res, ans_p
    | c::cands ->
      try
        let state = holds q state [c] in
        loop state (c::ans_res) ans_p cands
      with Contradiction _ ->
        let vs = fvs_atom c in
        let ans_p = List.map
          (fun (b,ans as b_ans) ->
            let bs = Hashtbl.find q.b_vs b in
            if check_max_b vs bs then b, c::ans else b_ans)
          ans_p in
        loop state ans_res ans_p cands in
  loop init_state init_res ans_min cands

(* 6 *)
let strat q b ans =
  let strat = List.map
    (fun c ->
      let vs = VarSet.elements (fvs_atom c) in
      let vs = List.filter
        (fun v -> q.cmp_v b v = Upstream) vs in
      let loc = atom_loc c in
      if List.exists q.uni_v vs then
        raise (Contradiction
                 ("Escaping universal variable",
                  Some (TVar b, TVar (List.find q.uni_v vs)), loc));
      let avs = List.map Infer.freshen_var vs in
      let ans_r = List.map2 (fun a b -> a, (TVar b, loc)) avs vs in
      avs, subst_atom ans_r c, ans_r)
    ans in
  let avs, ans_l, ans_r = split3 strat in
  List.concat avs, ans_l, List.concat ans_r
  

let rec split avs ans q =
  (* 1 FIXME: do we really need this? *)
  let cmp_v v1 v2 =
    let a = q.cmp_v v1 v2 in
    if a <> Same_quant then a
    else
      let c1 = VarSet.mem v1 q.allbvs
      and c2 = VarSet.mem v2 q.allbvs in
      if c1 && c2 then Same_quant
      else if c1 then Downstream
      else if c2 then Upstream
      else Same_quant in
  let greater_v v1 v2 = cmp_v v1 v2 = Upstream in
  let rec loop avs ans sol =
    (* 2 *)
    let ans0 = List.filter
      (function
      | Eqty (TVar a, TVar b, _)
          when not (q.uni_v a) && VarSet.mem b q.allbvs &&
            cmp_v a b = Downstream -> false
      | Eqty (TVar b, TVar a, _)
          when not (q.uni_v a) && VarSet.mem b q.allbvs &&
            cmp_v a b = Downstream -> false
      | _ -> true) ans in
    let ans0 = List.map (fun c -> c, fvs_atom c) ans0 in
    (* 3 *)
    let ans_min = List.map
      (fun b ->
        let bs = Hashtbl.find q.b_vs b in
        b, map_some
          (fun (c, vs) ->
            let vmax =
              minimal ~less:greater_v (VarSet.elements vs) in
            if List.for_all (fun v -> VarSet.mem v bs) vmax
            then Some c else None)
          ans0)
      q.negbs in
    (* 4 *)
    let check_max_b vs bs =
      let vmax = minimal ~less:greater_v
        (VarSet.elements (VarSet.inter vs q.allbvs)) in
      List.exists (fun v -> VarSet.mem v bs) vmax in
    let ans_max = List.map
      (fun b ->
        let bs = Hashtbl.find q.b_vs b in
        b, map_some
          (fun (c, vs) ->
            if check_max_b vs bs then Some c else None)
          ans0)
      q.negbs in
    (* 5, 10a *)
    let ans_res, ans_ps = select check_max_b q ans ans_min ans_max in
    (* 6 *)
    let ans_strat = List.map
      (fun (b, ans_p) ->
        let (avs_p, ans_l, ans_r) = strat q b ans_p in
        q.add_b_vs b avs_p;
        (* 7 *)
        let ans0 = List.assoc b sol in
        let ans = ans0 @ ans_l in
        (* 8 *)
        let avs0 = VarSet.inter avs (fvs_formula ans) in
        (* 9.a *)
        let avs = VarSet.union avs0 (vars_of_list avs_p) in
        (b, avs), (b, ans), (avs_p, ans_r))
      ans_ps in
    let avss, sol', more = split3 ans_strat in
    let avs_ps, ans_rs = List.split more in
    (* 9.b *)
    let avss = List.map
      (fun (b, avs) ->
        let lbs = List.filter
          (fun b' -> q.cmp_v b b' = Downstream) q.negbs in
        let uvs = List.fold_left VarSet.union VarSet.empty
          (List.map (flip List.assoc avss) lbs) in
        VarSet.diff avs uvs)
      avss in
    (* 10b *)
    let ans_p = List.concat ans_rs in
    let ans_res = to_formula ans_p @ subst_formula ans_p ans_res in
    let avs_p = List.concat avs_ps in
    let avsl = List.map VarSet.elements avss in
    (* 11 *)
    if avs_p <> []
    then
      (* 12 *)
      let avs' = VarSet.diff avs
        (List.fold_left VarSet.union VarSet.empty avss) in
      let ans_res', sol' = loop avs' ans_res sol' in
      (* 13 *)
      ans_res', List.map2
        (fun avs (b, (avs', ans')) -> b, (avs@avs', ans')) avsl sol'
    else
      (* 14 *)
      ans_res, List.map2 (fun avs (b, ans) -> b, (avs, ans)) avsl sol' in
  let solT = List.map (fun b->b, []) q.negbs in
  loop (vars_of_list avs) ans solT  

let connected v (vs, phi) =
  let nodes = List.map (fun c -> c, fvs_atom c) phi in
  let rec loop acc vs nvs rem =
    let more, rem = List.partition
      (fun (c, cvs) -> List.exists (flip VarSet.mem cvs) nvs) rem in
    let mvs = List.fold_left VarSet.union VarSet.empty
      (List.map snd more) in
    let nvs = VarSet.elements (VarSet.diff mvs vs) in
    let acc = List.map fst more @ acc in
    if nvs = [] then acc
    else loop acc (VarSet.union mvs vs) nvs rem in
  let ans = loop [] VarSet.empty [v] nodes in
  VarSet.elements (VarSet.inter (fvs_formula ans) (vars_of_list vs)),
  ans

(** Perform quantifier elimination on provided variables and generally
    simplify the formula. *)
let simplify cmp_v uni_v vs cnj =
  let ty_ans, num_ans, _ =
    unify ~use_quants:false ~params:vs cmp_v uni_v cnj in
  let ty_sb, ty_ans = List.partition
    (fun (v,_) -> List.mem v vs) ty_ans in
  let ty_ans = subst_formula ty_sb (to_formula ty_ans) in
  let vs = vars_of_list vs in
  let ty_vs = VarSet.inter vs (fvs_formula ty_ans)
  and num_vs = VarSet.inter vs (fvs_formula num_ans) in
  let num_vs, num_ans =
    NumS.simplify cmp_v (VarSet.elements num_vs) num_ans in
  VarSet.elements (VarSet.union ty_vs (vars_of_list num_vs)),
  ty_ans @ num_ans

let converge sol0 sol1 sol2 =
  (* TODO *)
  sol2

let neg_constrns = ref false

let solve cmp_v uni_v brs =
  let q = new_q cmp_v uni_v in
  let cmp_v = q.cmp_v and uni_v = q.uni_v in
  let neg_brs, brs = List.partition
    (fun (_,concl) -> List.exists
      (function CFalse _ -> true | _ -> false) concl) brs in
  let neg_cns = List.map
    (fun (prem, concl) ->
      let loc =
        match List.find (function CFalse _ -> true | _ -> false) concl
        with CFalse loc -> loc | _ -> assert false in
      concl, loc)
    neg_brs in
  List.iter
    (fun (prem,concl) ->
      List.iter
        (function
        | PredVarU (i, TVar b) | PredVarB (i, TVar b, _) ->
          q.add_bchi b i false
        | _ -> ()) prem;
      List.iter
        (function
        | PredVarU (i, TVar b) | PredVarB (i, TVar b, _) ->
          q.add_bchi b i true
        | _ -> ()) concl;
    ) brs;
  let solT = List.map
    (fun i -> i, ([], []))
    (Ints.elements q.allchi) in
  (* 1 *)
  let chiK = collect
    (concat_map
       (fun (prem,concl) -> Aux.map_some
         (function PredVarB (i,t1,t2) ->
           Some ((i,t2), Eqty (TVar delta, t1, dummy_loc) :: prem @ concl)
         | _ -> None) concl) brs) in
  let chiK = List.map (fun ((i,t2),cnjs) -> i, (t2, cnjs)) chiK in
  let rec loop sol0 (sol1 : (int * (var_name list * formula)) list) =
    let gK = List.map
      (fun (i,(t2,cnjs)) ->
        i, connected delta (DisjElim.disjelim cmp_v uni_v cnjs)) chiK in
    let gK = map_some
      (fun (i,(gvs, g_ans)) ->
        (* 2 *)
        let vs, ans = List.assoc i sol1 in
        (* Adding to quantifier for [abd_s] and [simplify]. *)
        let cmp_v' gvs v1 v2 =
          let c1 = List.mem v1 gvs and c2 = List.mem v2 gvs in
          if c1 && c2 then Same_quant
          else if c1 then Downstream
          else if c2 then Upstream
          else cmp_v v1 v2 in
        (* FIXME:     q.set_b_uni false; ? *)
        match Abduction.abd_s (cmp_v' gvs) uni_v ans g_ans with
        | None -> None
        | Some (gvs', g_ans') ->
          (* 3 *)
          let gvs', g_ans' =
            simplify (cmp_v' (gvs' @ gvs)) uni_v gvs' g_ans' in
          if g_ans' = [] then None
          else
            let gvs = VarSet.elements
              (VarSet.inter (vars_of_list (gvs @ gvs')) (fvs_formula g_ans)) in
            (* freshened [gvs] will be added to [q] by substitution *)
            Some (i, (gvs @ vs, g_ans' @ ans))
      ) gK in
    (* 4 *)
    let sol1 = replace_assocs ~repl:gK sol1 in
    let brs = sb_brs_pred q sol1 brs in
    let fincheck (params, sb) = List.for_all
      (fun (cnj, loc) ->
        try
          ignore (unify ~use_quants:true ~params ~sb cmp_v uni_v cnj);
          false
        with Contradiction _ -> true)
      neg_cns in
    let fincheck =
      if not !neg_constrns then None else Some fincheck in
    (* 5 *)
    q.set_b_uni false;
    let vs, ans =
      try Abduction.abd cmp_v uni_v ?fincheck brs
      with Suspect (vs, concl) ->
        q.set_b_uni false; ignore (holds q ~params:vs empty_state concl);
        q.set_b_uni true; ignore (holds q ~params:vs empty_state concl);
        assert false in
    q.set_b_uni true;
    let ans_res, sol2 = split vs ans q in
    (* 6 *)
    let lift_ex_types t2 (vs, ans) =
      let fvs = fvs_formula ans in
      let dvs = VarSet.elements (VarSet.diff fvs (vars_of_list vs)) in
      let targs = List.map (fun v -> TVar v) dvs in
      let a2 = match t2 with TVar a2 -> a2 | _ -> assert false in
      vs @ dvs, Eqty (TVar delta', TCons (CNam "Tuple", targs), dummy_loc) ::
        subst_formula [a2, (TVar delta', dummy_loc)] ans in
    (* 7 *)
    if List.for_all (fun (_,(_,ans)) -> ans=[]) sol2
    then
      let sol = List.map
        (fun ((i,sol) as isol) ->
          try let t2, _ = List.assoc i chiK in
              i, lift_ex_types t2 sol
          with Not_found -> isol)
        sol1 in
      fold_map
        (fun ans_res (i,(vs,ans)) ->
          let vs, ans = simplify cmp_v uni_v vs ans in
          let allbs = (* VarSet.union q.allbvs *)
            (vars_of_list (delta::vs)) in
          let more, ans = List.partition
            (fun c-> VarSet.is_empty (VarSet.inter allbs (fvs_atom c)))
            ans in
          more @ ans_res, (i, (vs, ans)))
        ans_res sol
    else
      (* 8 *)
      let sol2 = List.map
        (fun (i, (vs, ans)) ->
          (* [sol2] is currently organized by [b], and [sol1] by [i]
             also, subsitute [delta] by [Delta true] *)
          let bs = List.filter (not % q.positive_b) (q.find_b i) in
          let ds = List.map (fun b-> b, List.assoc b sol2) bs in
          let dans = concat_map
            (fun (b, (dvs, dans)) ->
              let renaming = matchup_vars q b vs in
              subst_formula ((b, (TVar delta, dummy_loc))::renaming) dans
            ) ds in
          let dvs = concat_map (fun (_,(dvs,_))->dvs) ds in
          (* [dvs] must come before [vs] bc. of [matchup_vars] and [q] *)
          i, (dvs @ vs, dans @ ans))
        sol1 in    
      (* 9 *)
      let sol2 = converge sol0 sol1 sol2 in
      loop sol1 sol2 in
  let sol = loop solT solT in
  List.iter (fun (cnj, loc) ->
    try
      let cnj = sb_formula_pred q false (snd sol) cnj in
      ignore (holds q empty_state cnj);
      raise (Contradiction ("A branch with \"assert false\" is possible",
                            None, loc))
    with Contradiction _ -> ()
  ) neg_cns;
  q.set_b_uni true;
  cmp_v, uni_v, sol
