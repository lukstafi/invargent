(** Abduction for InvarGenT.

    Released under the GNU General Public Licence (version 2 or
    higher), NO WARRANTY of correctness etc. (C) Lukasz Stafiniak 2013
    @author Lukasz Stafiniak lukstafi (AT) gmail.com
    @since Mar 2013
*)

let abd_simple cmp_v uni_v (prem, concl) =
  let rec next a =
    if
    then Aux.LCons (a, lazy (next))
    else Aux.LNil in
  lazy (next )

let abd_typ cmp_v uni_v brs =
  let sols = List.map (abd_simple cmp_v uni_v) brs in
  let sols = Aux.lproduct brs in
  Aux.lmap_some (fun anss ->
    let vs, cn_typ, cns_num = Aux.fold_left
      (fun (vs, cn_typ, cns_num) (avs, ans_typ, ans_num) ->
        avs @ vs, ans_typ @ cn_typ, ans_num :: cns_num)
      ([], [], []) anss in
    let cns_num = List.rev cns_num in
    let cmp' v1 v2 =
      if List.mem v1 vs then
        if List.mem v2 vs then Same_quant else Upstream
      else if List.mem v2 vs then Downstream
      else cmp_v v1 v2 in
    let uni' v = if List.mem v vs then false else uni_v v in
    try
      let ans_typ, more_num, more_so =
        unify ~use_quants:true cmp' uni' cns in
      assert (more_so = []);
      let tvs = VarSet.inter (fvs_formula ans_typ) vs in
      let ans_typ = List.map
        (fun (v,(t,loc)) -> Eqty (TVar v, t, loc)) ans_typ in
      (* FIXME: adding num to typ answer? *)
      Some (tvs, ans_typ @ more_num, cns_num)
    with Contradiction _ -> None
  ) sols

let satisfiable_num cnj =
  true

let abd_num cmp_v uni_v brs =
  ()

let abd cmp_v uni_v brs =
  (* Do not change the order and no. of branches afterwards. *)
  let brs_typ, brs_num, brs_so = Aux.split3
      (Aux.map_some (fun (prem, concl) ->
        let prems_opt =
          try Some (unify ~use_quants:false cmp_v uni_v prem)
          with Contradiction _ -> None in
        match prems_opt with
        | prem_typ, prem_num, prem_so ->
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
                       (prem_so, concl_so)))
         brs in
  let sols_typ = abd_typ cmp_v uni_v brs_typ in
  Aux.lconcat_map
    (fun (tvs, ans_typ, more_num) ->
      let brs_num = List.map2
        (fun (prem,concl) more -> prem, more @ concl)
        brs_num more_num in
      let sols_num = abd_num cmp_v uni_v brs_num in
      Aux.lmap
        (fun (nvs, ans_num) -> nvs @ tvs,
          (* Aux.map_append (fun (v,t,loc) -> Eqty (TVar v,t,loc)) *)
            ans_typ @ ans_num)
        sols_typ)
    sols_typ
