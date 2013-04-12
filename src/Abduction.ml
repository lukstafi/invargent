(** Abduction for InvarGenT.

    Released under the GNU General Public Licence (version 2 or
    higher), NO WARRANTY of correctness etc. (C) Lukasz Stafiniak 2013
    @author Lukasz Stafiniak lukstafi (AT) gmail.com
    @since Mar 2013
*)
open Terms

let residuum cmp_v uni_v prem concl =
  let concl = to_formula concl in
  let res_ty, res_num, res_so =
    unify ~use_quants:false cmp_v uni_v
      (subst_formula prem concl) in
  assert (res_so = []);
  res_ty, res_num


let abd_simple cmp_v uni_v (prem, concl) =
  let prem_and ans =
    combine_sbs ~use_quants:false cmp_v uni_v [prem; ans] in
  let implies_concl vs ans =
    let cmp' v1 v2 =
      if List.mem v1 vs then
        if List.mem v2 vs then Same_quant else Downstream
      else if List.mem v2 vs then Upstream
      else cmp_v v1 v2 in
    let cnj_typ, cnj_num = prem_and ans in
    let res_ty, res_num = residuum cmp' uni_v cnj_typ concl in
    if List.for_all (fun (v,_) -> List.mem v vs) res_ty
    then Some (res_num @ cnj_num)
    else None in
  let rec abstract repls vs ans num = function
    | [] -> [vs, ans, num]
    | (x, (t, lc))::cand ->
      step x lc {typ_sub=t; typ_ctx=[]} repls vs ans num cand
  and step x lc loc repls vs ans (num : atom list) cand =
    let advance () =
      match typ_next loc with
      | None -> abstract repls vs ((x, (typ_out loc,lc))::ans) num cand
      | Some loc -> step x lc loc repls vs ans num cand in
    if num_sort_typ loc.typ_sub
    then advance ()
    else
      let a = Infer.fresh_typ_var () in
      let repls' = (loc.typ_sub, a)::repls in
      let vs' = a::vs in
      let loc' = {loc with typ_sub = TVar a} in
      let ans' = (x, (typ_out loc', lc))::ans in
      match implies_concl vs' ans' with
      | Some more_num ->
        (match typ_next loc' with
      | None -> abstract repls' vs' ans' num cand
      | Some loc' ->
        step x lc loc' repls' vs' ans (more_num @ num) cand
        (* x ^ bound when leaving step *) )
      | None ->
        let repl = Aux.assoc_all loc.typ_sub repls in
        List.rev_append
          (match typ_up loc with
          | None -> advance ()        
          | Some loc -> step x lc loc repls vs ans num cand)
          (Aux.concat_map
             (fun b ->
               let loc' = {loc with typ_sub = TVar b} in
               let ans' = (x, (typ_out loc', lc))::ans in
               match implies_concl vs ans' with
               | Some more_num ->
                 (match typ_next loc' with
                 | None -> abstract repls vs ans' (more_num @ num) cand
                 | Some loc' ->
                   step x lc loc' repls vs ans (more_num @ num) cand)
               | None -> [])
             repl) in
  let cnj_typ, cnj_num = prem_and concl in
  (* abstract repls vs ans num (prem/\concl) *)
  abstract [] [] [] cnj_num cnj_typ

let abd_typ cmp_v uni_v brs =
  let sols = List.map (abd_simple cmp_v uni_v) brs in
  let sols = Aux.product sols in
  Aux.map_some (fun anss ->
    let vs, cn_typ, cns_num = List.fold_left
      (fun (vs, cn_typ, cns_num) (avs, ans_typ, ans_num) ->
        avs @ vs, ans_typ @ cn_typ, ans_num :: cns_num)
      ([], [], []) anss in
    let cn_typ = to_formula cn_typ in
    let cns_num = List.rev cns_num in
    let cmp' v1 v2 =
      if List.mem v1 vs then
        if List.mem v2 vs then Same_quant else Downstream
      else if List.mem v2 vs then Upstream
      else cmp_v v1 v2 in
    let uni' v = if List.mem v vs then false else uni_v v in
    try
      let ans_typ, more_num, more_so =
        unify ~use_quants:true cmp' uni' cn_typ in
      assert (more_so = []);
      let tvs = VarSet.inter (fvs_sb ans_typ) (vars_of_list vs) in
      let ans_typ = to_formula ans_typ in
      (* FIXME: adding num to typ answer? *)
      Some (tvs, ans_typ @ more_num, cns_num)
    with Contradiction _ -> None
  ) sols

let satisfiable_num cnj =
  true

let abd_num cmp_v uni_v brs =
  [[],[]]

let abd cmp_v uni_v brs =
  (* Do not change the order and no. of branches afterwards. *)
  let brs_typ, brs_num, brs_so = Aux.split3
      (Aux.map_some (fun (prem, concl) ->
        let prems_opt =
          try Some (unify ~use_quants:false cmp_v uni_v prem)
          with Contradiction _ -> None in
        match prems_opt with
        | Some (prem_typ, prem_num, prem_so) ->
          if List.exists
            (function CFalse _ -> true | _ -> false) prem_so
          then None
          else                          (* can raise Contradiction *)
            let concl_typ, concl_num, concl_so =
              unify ~use_quants:false cmp_v uni_v concl in
            List.iter (function
            | CFalse loc ->
              raise (Contradiction ("assert false is possible", None, loc))
            | _ -> ()) concl_so;
            if not (satisfiable_num concl_num) then None
            else Some ((prem_typ, concl_typ), (prem_num, concl_num),
                       (prem_so, concl_so))
        | None -> None)
         brs) in
  let sols_typ = abd_typ cmp_v uni_v brs_typ in
  Aux.concat_map
    (fun (tvs, ans_typ, more_num) ->
      let tvs = VarSet.elements tvs in
      let brs_num = List.map2
        (fun (prem,concl) more -> prem, more @ concl)
        brs_num more_num in
      let sols_num = abd_num cmp_v uni_v brs_num in
      List.map
        (fun (nvs, ans_num) -> nvs @ tvs,
          (* Aux.map_append (fun (v,t,loc) -> Eqty (TVar v,t,loc)) *)
            ans_typ @ ans_num)
        sols_num)
    sols_typ
