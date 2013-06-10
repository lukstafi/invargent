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

exception Result of var_name list * subst

let abd_simple cmp_v uni_v validate skip (vs, ans) (prem, concl) =
  let skip = ref skip in
  let skipped = ref [] in
  let allvs = ref VarSet.empty in
  try
    let prem, _ =
      subst_solved ~use_quants:false ~params:vs cmp_v uni_v ans
        ~cnj:prem in
    let concl, _ =
      subst_solved ~use_quants:false ~params:vs cmp_v uni_v ans
        ~cnj:concl in
    let prem_and vs ans =
      (* TODO: optimize, don't redo work *)
      combine_sbs ~use_quants:false ~params:vs cmp_v uni_v [prem; ans] in
    let implies_concl vs ans =
      let cnj_typ, cnj_num = prem_and vs ans in
      let res_ty, res_num = residuum cmp_v uni_v vs cnj_typ concl in
      let num = res_num @ cnj_num in
      res_ty = [] && NumS.satisfiable num in
    let rec abstract repls vs ans cur_ans = function
      | [] ->
        if implies_concl vs ans then
          let ans = List.sort compare ans in
          allvs := List.fold_right VarSet.add vs !allvs;
          if List.exists (fun xs ->
            List.for_all (fun (y,_) -> VarSet.mem y !allvs)
              (Aux.sorted_diff xs ans)) !skipped
          then ()
          else if !skip > 0 then (
            skipped := ans :: !skipped;
            decr skip)
          else raise (Result (vs, ans))
      | (x, (t, lc))::cand ->
        if implies_concl vs (ans @ cand) then (
          (* Choice 1: drop premise/conclusion atom from answer *)
          abstract repls vs ans cur_ans cand);
        step x lc {typ_sub=t; typ_ctx=[]} repls vs ans cur_ans cand
    and step x lc loc repls vs ans cur_ans cand =
      (* Choice 2: preserve current premise/conclusion subterm for answer *)
      (match typ_next loc with
        | None ->
          let ans =
            try
              let ans, _, so =
                unify ~use_quants:true ~params:vs ~sb:ans
                  cmp_v uni_v [Eqty (TVar x, typ_out loc, lc)] in
              validate vs ans;
              assert (so = []); Some ans
            with Contradiction _ -> None in
          (match ans with None -> ()
          | Some ans ->
            abstract repls vs ans cur_ans cand)
        | Some loc ->
          step x lc loc repls vs ans cur_ans cand);
      if not (num_sort_typ loc.typ_sub)
      then
        (* Choice 3: remove subterm from answer *)
        let a = Infer.fresh_typ_var () in
        let repls' = (loc.typ_sub, a)::repls in
        let vs' = a::vs in
        let loc' = {loc with typ_sub = TVar a} in
        let t' = typ_out loc' in
        let cur_ans' = (x, (t', lc))::cur_ans in
        (match typ_next loc' with (* x bound when leaving step *)
        | None ->
          (try
             let ans', _, so =
               unify ~use_quants:true ~params:vs' ~sb:ans
                 cmp_v uni_v [Eqty (TVar x, t', lc)] in
             validate vs' ans';
             assert (so = []);
             abstract repls' vs' ans' cur_ans' cand
           with Contradiction _ ->
             ())
        | Some loc' ->
          step x lc loc' repls' vs' ans cur_ans cand);
        (* Choice 4: match subterm with an earlier occurrence *)
        if not (implies_concl vs' (cur_ans' @ cand))
        then (
          let repl = Aux.assoc_all loc.typ_sub repls in
          List.iter
            (fun b ->
              let loc' = {loc with typ_sub = TVar b} in
              let t' = typ_out loc' in
              let cur_ans' = (x, (t', lc))::cur_ans in
              match typ_next loc' with
              | None ->
                (try
                   let ans', _, so =
                     unify ~use_quants:true ~params:vs' ~sb:ans
                       cmp_v uni_v [Eqty (TVar x, t', lc)] in
                   validate vs ans';
                   assert (so = []);
                   abstract repls vs ans' cur_ans' cand
                 with Contradiction _ ->
                   ())
              | Some loc' ->
                step x lc loc' repls vs ans cur_ans cand)
            repl;
          (* Choice 5: try subterms of the subterm *)
          (match typ_up loc with
          | None ->
            ()        
          | Some loc ->
            step x lc loc repls vs ans cur_ans cand);
        )
    in
    let cleanup vs ans =
      let ans = List.filter (fun (x,_) -> not (List.mem x vs)) ans in
      let ansvs = fvs_sb ans in
      List.filter (Aux.flip VarSet.mem ansvs) vs, ans in
    if implies_concl vs ans then Some (vs, ans)
    else
      let cnj_typ, _ = prem_and vs concl in
      try abstract [] vs ans [] cnj_typ; None
      with Result (vs, ans) -> Some (cleanup vs ans)
  with Contradiction _ -> None          (* subst_solved or implies_concl *)

let abd_typ cmp_v uni_v brs =
  let br0 = 0, List.hd brs in
  let more_brs = List.map (fun br -> -1, br) (List.tl brs) in
  let validate vs ans = List.iter
    (fun (prem, _) ->
      ignore (combine_sbs ~use_quants:false ~params:vs cmp_v uni_v
                [prem; ans]))
    brs in
  (* let time = ref (Sys.time ()) in *)
  let rec loop first acc done_brs = function
    | [] -> Some acc
    | (skip, br as obr)::more_brs ->
      (*Format.printf "abd_typ-loop:@ @[<2>%a@ ⟹@ %a@]@\n"
        pr_subst (fst br) pr_subst (snd br);*)
      match abd_simple cmp_v uni_v validate skip acc br with
      | Some acc ->
        (*let ntime = Sys.time () in
        Format.printf "ans: (%.2fs)@ @[<2>%a@]@\n" (ntime -. !time)
          pr_subst (snd acc); time := ntime;*)
        loop false acc (obr::done_brs) more_brs
      | None ->
        (* Format.printf "reset@\n"; *)
        if first then None
        else loop true ([], []) []
          ((skip+1, br)::List.rev_append done_brs more_brs) in
  Aux.bind_opt (loop true ([], []) [] (br0::more_brs))
    (fun (vs, ans) ->
      let num = List.map
        (fun (prem, concl) ->
          try
            let cnj_ty, cnj_num =
              combine_sbs ~use_quants:false ~params:vs cmp_v uni_v
                [prem; ans] in
            let res_ty, res_num =
              residuum cmp_v uni_v vs cnj_ty concl in
            assert (res_ty = []);
            cnj_num @ res_num
          with Contradiction _ -> assert false)
        brs in
      Some (vs, ans, num))
  

let abd_mockup_num cmp_v uni_v brs =
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
  Aux.map_opt (abd_typ cmp_v uni_v brs_typ)
    (fun (tvs, ans_typ, more_num) ->
      List.map2
        (fun (prem,concl) more -> prem, more @ concl)
        brs_num more_num)

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
  Aux.bind_opt (abd_typ cmp_v uni_v brs_typ)
    (fun (tvs, ans_typ, more_num) ->
      let brs_num = List.map2
        (fun (prem,concl) more -> prem, more @ concl)
        brs_num more_num in
      let ans_num = NumS.abd cmp_v uni_v brs_num in
      Aux.map_opt ans_num
        (fun (nvs, ans_num) ->
          (nvs @ tvs,
           Aux.map_append (fun (v,(t,lc)) -> Eqty (TVar v,t,lc))
             ans_typ ans_num)))

let abd_s cmp_v uni_v prem concl =
  (* Do not change the order and no. of branches afterwards. *)
  let prem_opt =
    try Some (unify ~use_quants:false cmp_v uni_v prem)
    with Contradiction _ -> None in
  match prem_opt with
  | Some (prem_typ, prem_num, prem_so) when
      List.for_all (function CFalse _ -> false | _ -> true) prem_so ->
    (try
       let concl_typ, concl_num, concl_so =
         unify ~use_quants:false cmp_v uni_v concl in
       if List.exists (function CFalse _ -> true | _ -> false) prem_so
       then None
       else if not (NumS.satisfiable concl_num) then None
       else
         Aux.bind_opt
           (abd_simple cmp_v uni_v (fun _ _ -> ()) 0 ([], [])
              (prem_typ, concl_typ))
           (fun (tvs, ans_typ) ->
             let more_num =
                 try
                   let cnj_ty, cnj_num =
                     combine_sbs ~use_quants:false ~params:tvs cmp_v uni_v
                       [prem_typ; ans_typ] in
                   let res_ty, res_num =
                     residuum cmp_v uni_v tvs cnj_ty concl_typ in
                   assert (res_ty = []);
                   cnj_num @ res_num
                 with Contradiction _ -> assert false in
             let ans_num =
               NumS.abd_s cmp_v uni_v prem_num (more_num @ concl_num) in
             Aux.map_opt ans_num
               (fun (nvs, ans_num) ->
                 (nvs @ tvs,
                  Aux.map_append (fun (v,(t,lc)) -> Eqty (TVar v,t,lc))
                    ans_typ ans_num)))
     with Contradiction _ -> None)
  | _ -> Some ([], [])



