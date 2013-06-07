(** Solving second-order i.e. formula variables for InvarGenT.

    Released under the GNU General Public Licence (version 2 or
    higher), NO WARRANTY of correctness etc. (C) Lukasz Stafiniak 2013
    @author Lukasz Stafiniak lukstafi (AT) gmail.com
    @since Mar 2013
*)
open Terms
open Aux

type chi_subst = (int * formula) list

let sb_typ_unary arg =
  typ_map {typ_id_map with map_delta = fun _ -> arg}  

let sb_typ_binary arg1 arg2 =
  typ_map {typ_id_map with map_delta = fun b -> if b then arg1 else arg2}  

let sb_atom_unary arg = function
  | Eqty (t1, t2, lc) ->
    Eqty (subst_typ_unary arg t1, subst_typ_unary arg t2, lc)
  | Leq (t1, t2, lc) ->
    Leq (subst_typ_unary arg t1, subst_typ_unary arg t2, lc)
  | CFalse _ as a -> a
  | PredVarU (_, t) -> assert false
  | PredVarB (_, t1, t2) -> assert false

let sb_atom_binary arg1 arg2 = function
  | Eqty (t1, t2, lc) ->
    Eqty (subst_typ_binary arg1 arg2 t1, subst_typ_binary arg1 arg2 t2, lc)
  | Leq (t1, t2, lc) ->
    Leq (subst_typ_binary arg1 arg2 t1, subst_typ_binary arg1 arg2 t2, lc)
  | CFalse _ as a -> a
  | PredVarU (_, t) -> assert false
  | PredVarB (_, t1, t2) -> assert false

let sb_phi_unary arg = List.map (sb_atom_unary arg)

let sb_phi_binary arg1 arg2 = List.map (sb_atom_binary arg1 arg2)

let sb_atom_pred psb = function
  | PredVarU (i, t) as a ->
    (try
       let phi = List.find i psb in
       sb_phi_unary t phi
     with Not_found -> a)  
  | PredVarB (_, t1, t2) -> assert false
    (try
       let phi = List.find i psb in
       sb_phi_binary t1 t2 phi
     with Not_found -> a)

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
  let add_bchi b i =
    Hashtbl.add chi_b i b;
    Hashtbl.add b_chi b i in
  let find_b i = Hashtbl.find chi_b i in
  let find_chi b = Hashtbl.find b_chi b in
  let rec add_b_vs b vs =
    assert (Hashtbl.mem b_chi b);
    List.iter (fun v -> Hashtbl.add same_q v b) vs;
    q.allbvs <- VarSet.union q.allbvs (vars_of_list vs);
    try
      let ovs = Hashtbl.find b_vs b in
      Hashtbl.replace b_vs b (VarSet.union ovs (vars_of_list vs))
    with Not_found -> Hashtbl.add b_vs b (vars_of_list vs)
  and q = {
    cmp_v; uni_v; add_b_vs;
    set_b_uni = (fun b -> b_is_uni := b);
    b_vs; allbvs = VarSet.empty; add_bchi; find_b; find_chi;
  } in q

let rec split avs ans q =
  ()  

let solve cmp_v uni_v brs =
  (*let chi p phi = map_some
    (function
    | PredVarU (i,t) -> Some (i, (p, Left t))
    | PredVarB (i,t1,t2) -> Some (i, (p, Right (t1, t2)))
    | _ -> None) phi in
  let chis = collect
    (concat_map
       (fun (prem,concl) -> chi true prem @ chi false concl) brs) in*)
  let q = new_q cmp_v uni_v in
  let cmp_v = q.cmp_v and uni_v = q.uni_v in
  let bchis = List.iter
    (fun (prem,_) -> List.iter
      (function
      | PredVarU (i, TVar v) | PredVarB (i, TVar v, _) ->
        q.add_bchi v i; q.add_b_vs b [b]
      | _ -> ()) prem) brs in
  let delta = Infer.fresh_typ_var ()
  and delta' = Infer.fresh_typ_var () in
  (* 1 *)
  let chiK = collect
    (concat_map
       (fun (prem,concl) -> Aux.map_some
         (function PredVarB (i,t1,t2) ->
           Some ((i,t2), Eqty (delta, t1, dummy_loc) :: prem @ concl)
         | _ -> None) concl) brs) in
  let chiK = List.map (fun ((i,t2),cnjs) -> i, (t2, cnjs)) chiK in
  let rec loop sol0 sol1 =
    let gK = List.map
      (fun (i,(t2,cnjs)) ->
        i, connected delta (DisjElim.disjelim cmp_v uni_v cnjs)) chiK in
    let gK = map_some
      (fun (i,(gvs, g_ans)) ->
        (* 2 *)
        let vs, ans = List.assoc i sol1 in
        match Abduction.abd_s cmp_v uni_v ans g_ans with
        | None -> None
        | Some gv_ans' ->
          (* 3 *)
          let (gvs', g_ans') = simplify gv_ans' in
          if g_ans' = [] then None
          else
            let gvs = list_inter (gvs @ gvs') (fvs_formula g_ans) in
            let b = q.find_b i in
            q.add_b_vs b gvs;
            Some (gvs @ vs, g_ans' @ ans)
      ) gK in
    (* 4 *)
    let sol1 = replace_assocs ~repl:gK sol1 in
    let brs = subst_brs_pred sol1 in
    (* 5 -- could be relocated *)
    let lift_ex_types t2 (vs, ans) =
      let fvs = fvs_formula ans in
      let dvs = VarSet.elements (VarSet.diff fvs (vars_of_list vs)) in
      let targs = List.map (fun v -> TVar v) dvs in
      let a2 = match t2 with TVar a2 -> a2 | _ -> assert false in
      vs @ dvs, Eqty (Delta false, TCons ("Tuple", targs)) ::
        subst_formula [a2, Delta false] ans in
    (* 6 *)
    let vs, ans = Abduction.abd cmp_v uni_v brs in
    let ans_res, sol2 = split vs ans q in
    (* 7 *)
    let sol2 = List.map2
      (fun (i,(vs, ans)) (j,(dvs, dans)) -> assert (i=j);
        let b = q.find_b i in
        q.add_vs b dvs;
        i, (vs@dvs, ans@dans))
      sol1 (order_key sol2) in    
    (* 8 *)
    let sol2 = converge sol0 sol1 sol2 in
    if implies sol1 sol2
    then
      let sol = List.map
        (fun (i,sol) ->
          try let t2, _ = List.assoc i chiK in
              list_ex_types t2 sol
          with Not_found -> sol)
        sol2 in
      ans_res, sol
    else loop sol1 sol2 in
  loop solT solT
