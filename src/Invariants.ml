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
  typ_map {typ_id_map with map_delta = fun _ -> arg}  

let sb_typ_binary arg1 arg2 =
  typ_map {typ_id_map with map_delta = fun b -> if b then arg1 else arg2}  

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

let sb_atom_pred psb = function
  | PredVarU (i, t) as a ->
    (try
       let phi = List.assoc i psb in
       sb_phi_unary t phi
     with Not_found -> [a])  
  | PredVarB (i, t1, t2) as a ->
    (try
       let phi = List.assoc i psb in
       sb_phi_binary t1 t2 phi
     with Not_found -> [a])
  | a -> [a]

let sb_formula_pred psb phi =
  concat_map (sb_atom_pred psb) phi

let sb_brs_pred psb brs = (*List.map
  (fun (prem,concl) -> sb_formula_pred psb prem, sb_formula_pred psb concl)*)
  (* FIXME: freshen variables and put them in the quantifier *)
  brs

type q_with_bvs = {
  cmp_v : var_name -> var_name -> var_scope;
  uni_v : var_name -> bool;
  add_b_vs : var_name -> var_name list -> unit;
  set_b_uni : bool -> unit;
  b_vs : (var_name, VarSet.t) Hashtbl.t;
  add_bchi : var_name -> int -> unit;
  find_b : int -> var_name;
  find_chi : var_name -> int;
  mutable allbvs : VarSet.t;
  mutable allchi : Ints.t;
}
  
let new_q cmp_v uni_v =
  let same_q = Hashtbl.create 32 in
  let cmp_v v1 v2 =
    let v1 = try Hashtbl.find same_q v1 with Not_found -> v1 in
    let v2 = try Hashtbl.find same_q v1 with Not_found -> v2 in
    cmp_v v1 v2 in
  let b_is_uni = ref true in
  let uni_v v =
    if Hashtbl.mem same_q v then !b_is_uni
    else uni_v v in
  let b_vs = Hashtbl.create 32 in
  let chi_b = Hashtbl.create 16 in
  let b_chi = Hashtbl.create 16 in
  let find_b i = Hashtbl.find chi_b i in
  let find_chi b = Hashtbl.find b_chi b in
  let rec add_bchi b i =
    q.allchi <- Ints.add i q.allchi;
    Hashtbl.add chi_b i b;
    Hashtbl.add b_chi b i
  and add_b_vs b vs =
    assert (Hashtbl.mem b_chi b);
    List.iter (fun v -> Hashtbl.add same_q v b) vs;
    q.allbvs <- VarSet.union q.allbvs (vars_of_list vs);
    try
      let ovs = Hashtbl.find b_vs b in
      Hashtbl.replace b_vs b (VarSet.union ovs (vars_of_list vs))
    with Not_found -> Hashtbl.add b_vs b (vars_of_list vs)
  and q = {
    cmp_v; uni_v; add_b_vs;
    set_b_uni = (fun b -> b_is_uni := b); allchi = Ints.empty;
    b_vs; allbvs = VarSet.empty; add_bchi; find_b; find_chi;
  } in q

let rec split avs ans q =
  failwith "FIXME: not implemented yet"

let connected v phi =
  (* FIXME: TODO *)
  phi

(** Perform quantifier elimination on provided variables and generally
    simplify the formula. *)
let simplify cmp_v vs cnj =
  let ty_ans, num_ans, _ = unify ~use_quants:false ~params:vs cmp_v
    (fun _ -> false) cnj in
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

let implies sol1 sol2 =
  failwith "FIXME: not implemented yet"

let solve cmp_v uni_v brs =
  let q = new_q cmp_v uni_v in
  let cmp_v = q.cmp_v and uni_v = q.uni_v in
  List.iter
    (fun (prem,_) -> List.iter
      (function
      | PredVarU (i, TVar b) | PredVarB (i, TVar b, _) ->
        q.add_bchi b i; q.add_b_vs b [b]
      | _ -> ()) prem) brs;
  let solT = List.map
    (fun i -> i, ([], []))
    (Ints.elements q.allchi) in
  let delta = Infer.fresh_typ_var () in
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
        match Abduction.abd_s (cmp_v' gvs) uni_v ans g_ans with
        | None -> None
        | Some (gvs', g_ans') ->
          (* 3 *)
          let gvs', g_ans' =
            simplify (cmp_v' (gvs' @ gvs)) gvs' g_ans' in
          if g_ans' = [] then None
          else
            let gvs = VarSet.elements
              (VarSet.inter (vars_of_list (gvs @ gvs')) (fvs_formula g_ans)) in
            let b = q.find_b i in
            q.add_b_vs b gvs;
            Some (i, (gvs @ vs, g_ans' @ ans))
      ) gK in
    (* 4 *)
    let sol1 = replace_assocs ~repl:gK sol1 in
    let brs = sb_brs_pred sol1 brs in
    (* 5 -- could be relocated *)
    let lift_ex_types t2 (vs, ans) =
      let fvs = fvs_formula ans in
      let dvs = VarSet.elements (VarSet.diff fvs (vars_of_list vs)) in
      let targs = List.map (fun v -> TVar v) dvs in
      let a2 = match t2 with TVar a2 -> a2 | _ -> assert false in
      vs @ dvs, Eqty (Delta false, TCons (CNam "Tuple", targs), dummy_loc) ::
        subst_formula [a2, (Delta false, dummy_loc)] ans in
    (* 6 *)
    let vs, ans =
      match Abduction.abd cmp_v uni_v brs with Some (vs,ans) -> vs,ans
      | None -> failwith "FIXME-TODO: propagate contradiction"
        (* raise (Contradiction) *) in
    let ans_res, sol2 = split vs ans q in
    (* 7 *)
    let sol2 = List.map2
      (fun (i,(vs, ans)) (j,(dvs, dans)) -> assert (i=j);
        let b = q.find_b i in
        q.add_b_vs b dvs;
        i, (vs@dvs, ans@dans))
      sol1 (order_key sol2) in    
    (* 8 *)
    let sol2 = converge sol0 sol1 sol2 in
    if implies sol1 sol2
    then
      let sol = List.map
        (fun ((i,sol) as isol) ->
          try let t2, _ = List.assoc i chiK in
              i, lift_ex_types t2 sol
          with Not_found -> isol)
        sol2 in
      ans_res, sol
    else loop sol1 sol2 in
  loop solT solT
