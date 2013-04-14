(** Abduction for InvarGenT.

    Released under the GNU General Public Licence (version 2 or
    higher), NO WARRANTY of correctness etc. (C) Lukasz Stafiniak 2013
    @author Lukasz Stafiniak lukstafi (AT) gmail.com
    @since Mar 2013
*)
open Terms

let residuum cmp_v uni_v params prem concl =
  let concl = to_formula concl in
  let res_ty, res_num, res_so =
    unify ~use_quants:false ~params cmp_v uni_v
      (subst_formula prem concl) in
  assert (res_so = []);
  res_ty, res_num

exception Result of var_name list * subst * formula

let abd_simple cmp_v uni_v skip (vs, ans) (prem, concl) =
  Format.printf "abd_simple:@\nans=%a@\n@[<2>%a@ ⟹@ %a@]@\n"
    pr_subst ans pr_subst prem pr_subst concl;
  let skip = ref skip in
  let prem_and vs ans =
    combine_sbs ~use_quants:false ~params:vs cmp_v uni_v [prem; ans] in
  let implies_concl vs ans =
    let cnj_typ, cnj_num = prem_and vs ans in
    let res_ty, res_num = residuum cmp_v uni_v vs cnj_typ concl in
    Format.printf "@[<2>[%a@ ?⟹@ %a@ |@ %a]@]@\n" pr_subst cnj_typ
      pr_subst concl pr_subst res_ty;
    let num = res_num @ cnj_num in
    if res_ty = [] && NumS.satisfiable num
    then Some num else None in
  let rec abstract repls vs ans = function
    | [] ->
      (match implies_concl vs ans with
      | None -> ()
      | Some num ->
        if !skip > 0 then decr skip
        else raise (Result (vs, ans, num)))
    | (x, (t, lc))::cand ->
      Format.printf "abstract:@ x=%s;@ t=%a@\n"
        (var_str x) (pr_ty false) t;
      step x lc {typ_sub=t; typ_ctx=[]} repls vs ans cand
  and step x lc loc repls vs ans cand =
    Format.printf "step:@ x=%s;@ loc=%a@\n"
      (var_str x) pr_typ_loc loc;
    let advance () =
      match typ_next loc with
      | None ->
        let ans =
          try
            let ans, _, so =
              unify ~use_quants:true ~prems:vs ~sb:ans
                cmp_v uni_v [Eqty (x, typ_out loc, lc)] in
            assert (so = []); Some ans
          with Contradiction _ -> None in
        (match ans with None -> ()
        | Some ans -> abstract repls vs ans cand)
      | Some loc -> step x lc loc repls vs ans cand in
    if num_sort_typ loc.typ_sub
    then advance ()
    else
      let a = Infer.fresh_typ_var () in
      let repls' = (loc.typ_sub, a)::repls in
      let vs' = a::vs in
      let loc' = {loc with typ_sub = TVar a} in
      let ans' =
        try
          let ans, _, so =
            unify ~use_quants:true ~prems:vs ~sb:ans
              cmp_v uni_v [Eqty (x, typ_out loc', lc)] in
          assert (so = []); Some ans
        with Contradiction _ -> None in
      let advance' () =
        match typ_next loc' with (* x bound when leaving step *)
        | None ->
          (match ans' with
          | None -> ()                  (* cannot fix answer *)
          | Some ans' -> abstract repls' vs' ans' cand)
        | Some loc' -> step x lc loc' repls' vs' ans cand in
      Format.printf "trying location:@ a=%s@\n" (var_str a);
      match implies_concl vs' (ans' @ cand) with
      | Some _ -> Format.printf "impl holds@\n"; advance' ()
      | None ->
        let repl = Aux.assoc_all loc.typ_sub repls in
        Format.printf "older:@ repl=%s@\n"
          (String.concat ", " (List.map var_str repl));
        List.iter
          (fun b ->
            let loc' = {loc with typ_sub = TVar b} in
            let ans' = (x, (typ_out loc', lc))::ans in
            match typ_next loc' with
            | None -> abstract repls vs ans' cand
            | Some loc' ->
              step x lc loc' repls vs ans cand)
          repl;
          advance' ();
        (match typ_up loc with
        | None -> advance ()        
        | Some loc -> step x lc loc repls vs ans cand);
  in
  let cleanup (vs, ans) =
    let ans = List.filter (fun (x,_) -> not (List.mem x vs)) ans in
    vs, List.sort compare ans in
  let cnj_typ, _ = prem_and vs concl in
  let res = List.map cleanup (abstract [] vs ans cnj_typ) in
  let leq (vs1, ans1) (vs2, ans2) =
    Aux.sorted_diff ans1 ans2 = [] in
  Aux.minimal leq res

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
            if not (NumS.satisfiable concl_num) then None
            else Some ((prem_typ, concl_typ), (prem_num, concl_num),
                       (prem_so, concl_so))
        | None -> None)
         brs) in
  let sols_typ = abd_typ cmp_v uni_v brs_typ in
  Aux.concat_map
    (fun (tvs, ans_typ, more_num) ->
      (* let tvs = VarSet.elements tvs in *)
      let brs_num = List.map2
        (fun (prem,concl) more -> prem, more @ concl)
        brs_num more_num in
      let sols_num = NumS.abd cmp_v uni_v brs_num in
      List.map
        (fun (nvs, ans_num) -> VarSet.union nvs tvs,
          (* Aux.map_append (fun (v,t,loc) -> Eqty (TVar v,t,loc)) *)
            ans_typ @ ans_num)
        sols_num)
    sols_typ
