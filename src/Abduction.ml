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

let abd_simple cmp_v uni_v ?(init_params=VarSet.empty) validate skip
    (vs, ans) (prem, concl) =
  let skip = ref skip in
  let skipped = ref [] in
  let allvs = ref VarSet.empty in
  let params = VarSet.union (vars_of_list vs) init_params in
  let pms vs = VarSet.union (vars_of_list vs) init_params in
  try
    let prem, _ =
      subst_solved ~use_quants:false ~params cmp_v uni_v ans
        ~cnj:prem in
    let concl, _ =
      subst_solved ~use_quants:false ~params cmp_v uni_v ans
        ~cnj:concl in
    let prem_and vs ans =
      (* TODO: optimize, don't redo work *)
      combine_sbs ~use_quants:false ~params:(pms vs) cmp_v uni_v [prem; ans] in
    let implies_concl vs ans =
      let cnj_typ, cnj_num = prem_and vs ans in
      let res_ty, res_num = residuum cmp_v uni_v (pms vs) cnj_typ concl in
      let num = res_num @ cnj_num in
      (*Format.printf "abd_simple:@ implies?@ %b@ #res_ty=%d@\nans=@ %a@\nres_ty=@ %a@\n%!"
        (res_ty = [] && NumS.satisfiable num) (List.length res_ty) pr_subst ans pr_subst res_ty;*)
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
            (* Format.printf "skipped:@ @[<2>%a@]@\n%!" pr_subst ans; *)
            decr skip)
          else raise (Result (vs, ans))
      | (x, (t, lc))::cand ->
        if implies_concl vs (ans @ cand) then (
          (* Choice 1: drop premise/conclusion atom from answer *)
      (*Format.printf "abd_simple:@ choice 1@ drop %s =@ %a@\n%!"
        (var_str x) (pr_ty false) t;*)
          abstract repls vs ans cur_ans cand);
        step x lc {typ_sub=t; typ_ctx=[]} repls vs ans cur_ans cand
    and step x lc loc repls vs ans cur_ans cand =
      (* Choice 2: preserve current premise/conclusion subterm for answer *)
      (*Format.printf "abd_simple:@ choices 2-5@ %s =@ %a@\n%!"
        (var_str x) (pr_ty false) (typ_out loc);*)
      (match typ_next loc with
        | None ->
          let ans =
            try
              (*Format.printf
                "abd_simple: trying choice 2 params=%s@ sb=@ %a@\n%!"
                (String.concat ", "
                   (List.map var_str (VarSet.elements (pms vs)))) pr_subst ans;*)
              let ans, _, so =
                unify ~use_quants:true ~params:(pms vs) ~sb:ans
                  cmp_v uni_v [Eqty (TVar x, typ_out loc, lc)] in
              (*Format.printf
                "abd_simple: validate 2 ans=@ %a@\n%!" pr_subst ans;*)
              validate vs ans;
              (* Format.printf "abd_simple: choice 2 OK@\n%!"; *)
              assert (so = []); Some ans
            with Contradiction _ ->
              (* Format.printf "abd_simple: choice 2 failed@\n%!"; *)
              None in
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
        (*Format.printf "abd_simple:@ choice 3@ repls'=@ %a@\n%!"
          pr_subst (List.map (fun (x,y) -> y,(x,dummy_loc)) repls');*)
        let vs' = a::vs in
        let loc' = {loc with typ_sub = TVar a} in
        let t' = typ_out loc' in
        (*Format.printf "abd_simple:@ choice 3@ remove subterm %s =@ %a@\n%!"
          (var_str x) (pr_ty false) t';*)
        let cur_ans' = (x, (t', lc))::cur_ans in
        (match typ_next loc' with (* x bound when leaving step *)
        | None ->
          (try
             let ans', _, so =
               unify ~use_quants:true ~params:(pms vs') ~sb:ans
                 cmp_v uni_v [Eqty (TVar x, t', lc)] in
              (*Format.printf
                "abd_simple: validate 3 ans=@ %a@\n%!" pr_subst ans;*)
             validate vs' ans';
             (*Format.printf "abd_simple: choice 3 OK@\n%!";*)
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
          (*Format.printf "abd_simple:@ choice 4 x=%s@ repls=@ %a@\n%!"
            (var_str x)
            pr_subst (List.map (fun (x,y) -> y,(x,dummy_loc)) repls);
          Format.printf "abd_simple:@ choice 4@ sub=@ %a@ repl=@ %s@\n%!"
            (pr_ty false) loc.typ_sub
            (String.concat ", " (List.map var_str repl));*)
          List.iter
            (fun b ->
              let loc' = {loc with typ_sub = TVar b} in
              let t' = typ_out loc' in
              let cur_ans' = (x, (t', lc))::cur_ans in
              match typ_next loc' with
              | None ->
                (try
                   (*Format.printf
                     "abd_simple:@ c.4 unify x=%s@ t'=%a@ sb=@ %a@\n%!"
                     (var_str x) (pr_ty false) t' pr_subst ans;*)
                   let ans', _, so =
                     (*try*)
                     unify ~use_quants:true ~params:(pms vs') ~sb:ans
                       cmp_v uni_v [Eqty (TVar x, t', lc)]
                     (*with Terms.Contradiction (msg,Some (ty1,ty2),_) as exn ->
                       Format.printf
                         "abd_simple:@ c.4 above failed:@ %s@ %a@ %a@\n%!" msg
                         (pr_ty true) ty1 (pr_ty true) ty2;
                       (match (ty1, ty2) with
                         TVar v1, TVar v2 ->
                           Format.printf
                             "uni_v %s=%b; uni_v %s=%b; cmp_v =%s@\n%!"
                             (var_str v1) (uni_v v1)
                             (var_str v2) (uni_v v2)
                             (str_of_cmp (cmp_v v1 v2))
                       | _ -> ()); 
                       ignore (Format.flush_str_formatter ());
                       Terms.pr_exception Format.str_formatter exn;
                       raise exn*) in
                   (*Format.printf
                     "abd_simple: validate 4 ans=@ %a@\n%!" pr_subst ans;*)
                   validate vs ans';
                   (* Format.printf "abd_simple: choice 4 OK@\n%!"; *)
                   assert (so = []);
                   (*Format.printf
                     "abd_simple:@ choice 4@ match earlier %s =@ %a@\n%!"
                     (var_str x) (pr_ty false) t';*)
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
            (* Format.printf "abd_simple:@ choice 5@ try subterms@\n%!"; *)
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

(* let max_skip = ref 20 *)

let abd_typ cmp_v uni_v ?(init_params=VarSet.empty) ?fincheck brs =
  Format.printf "abd_typ:@ init params=@ %s@\n%!"
    (String.concat ", " (List.map var_str (VarSet.elements init_params)));
  let br0 = 0, List.hd brs in
  let more_brs = List.map (fun br -> -1, br) (List.tl brs) in
  let pms vs = VarSet.union (vars_of_list vs) init_params in
  let validate vs ans = List.iter
    (fun (prem, concl) ->
      ignore (combine_sbs ~use_quants:false ~params:(pms vs) cmp_v uni_v
                [prem; concl; ans]))
    brs in
  let time = ref (Sys.time ()) in
  let rec loop acc runouts = function
    | [] ->
      let _, (prem, concl) =
        Aux.maximum ~leq:(fun (i,_) (j,_) -> i<=j) runouts in
      raise (Suspect (fst acc, to_formula (snd acc @ prem @ concl)))      
    | (skip, br as obr)::more_brs ->
      Format.printf
        "abd_typ-loop: skip=%d, #runouts=%d@\n@[<2>%a@ ⟹@ %a@]@\n%!"
        skip (List.length runouts) pr_subst (fst br) pr_subst (snd br);
      match abd_simple cmp_v uni_v ~init_params validate skip acc br with
      | Some acc ->
        let ntime = Sys.time () in
          Format.printf "ans: (%.2fs)@ @[<2>%a@]@\n%!" (ntime -. !time)
          pr_subst (snd acc); time := ntime;
        check_runouts acc obr more_brs [] runouts
      | None ->
        Format.printf "reset first at skip=%d@\n%!" skip;
        loop ([], []) ((0, br)::runouts) more_brs

  and check_runouts acc (dskip, dbr as done_br) more_brs done_runouts = function
    | [] -> check_brs acc (List.rev done_runouts) [done_br] more_brs
    | (confls, br as obr)::more_runouts ->
      Format.printf
        "abd_typ-check_runouts: confls=%d, #done=%d@\n@[<2>%a@ ⟹@ %a@]@\n%!"
        confls (List.length done_runouts) pr_subst (fst br) pr_subst (snd br);
      match abd_simple cmp_v uni_v ~init_params validate 0 acc br with
      | Some acc ->
        let ntime = Sys.time () in
          Format.printf "ans: (%.2fs)@ @[<2>%a@]@\n%!" (ntime -. !time)
          pr_subst (snd acc); time := ntime;
        check_runouts acc done_br more_brs (obr::done_runouts) more_runouts
      | None ->
        Format.printf "reset runouts at confls=%d@\n%!" confls;
        loop ([], [])
          ((confls+1, br)::List.rev_append done_runouts more_runouts)
          ((dskip+1, dbr)::more_brs)
      
  and check_brs acc runouts done_brs = function
    | [] ->
      (match fincheck with None -> acc
      | Some f -> if f acc then acc else
          match List.rev done_brs with
          | [] -> assert false
          | (skip, br)::more_brs ->
            loop ([], []) runouts ((skip+1, br)::more_brs))
    | (skip, br as obr)::more_brs ->
      Format.printf
        "abd_typ-check_brs: skip=%d, #done=%d@\n@[<2>%a@ ⟹@ %a@]@\n%!"
        skip (List.length done_brs) pr_subst (fst br) pr_subst (snd br);
      match abd_simple cmp_v uni_v ~init_params validate 0 acc br with
      | Some acc ->
        let ntime = Sys.time () in
          Format.printf "ans: (%.2fs)@ @[<2>%a@]@\n%!" (ntime -. !time)
          pr_subst (snd acc); time := ntime;
        check_brs acc runouts (obr::done_brs) more_brs
      | None ->
        Format.printf "reset check at skip=%d@\n%!" skip;
        loop ([], [])
          runouts ((skip+1, br)::List.rev_append done_brs more_brs) in

  let vs, ans = loop ([], []) [] (br0::more_brs) in
  let num = List.map
    (fun (prem, concl) ->
      try
        let cnj_ty, cnj_num =
          combine_sbs ~use_quants:false ~params:(pms vs) cmp_v uni_v
            [prem; ans] in
        let res_ty, res_num =
          residuum cmp_v uni_v (pms vs) cnj_ty concl in
        assert (res_ty = []);
        cnj_num @ res_num
      with Contradiction _ -> assert false)
    brs in
  vs, ans, num  

let abd_mockup_num cmp_v uni_v ?(init_params=VarSet.empty) brs =
  (* Do not change the order and no. of branches afterwards. *)
  let brs_typ, brs_num, brs_so = Aux.split3
    (Aux.map_some (fun (prem, concl) ->
      let prems_opt =
        try Some (unify ~use_quants:false ~params:init_params cmp_v uni_v prem)
        with Contradiction _ -> None in
      match prems_opt with
      | Some (prem_typ, prem_num, prem_so) ->
        if List.exists
          (function CFalse _ -> true | _ -> false) prem_so
        then None
        else                          (* can raise Contradiction *)
          let concl_typ, concl_num, concl_so =
            unify ~use_quants:false ~params:init_params cmp_v uni_v concl in
          List.iter (function
          | CFalse loc ->
            raise (Contradiction ("assert false is possible", None, loc))
          | _ -> ()) concl_so;
          if not (NumS.satisfiable concl_num) then None
          else Some ((prem_typ, concl_typ), (prem_num, concl_num),
                     (prem_so, concl_so))
      | None -> None)
       brs) in
  try
    let tvs, ans_typ, more_num = abd_typ cmp_v uni_v ~init_params brs_typ in
    Some (List.map2
            (fun (prem,concl) more -> prem, more @ concl)
            brs_num more_num)
  with Suspect _ -> None

let abd cmp_v uni_v ?(init_params=VarSet.empty) ?fincheck brs =
  (* Do not change the order and no. of branches afterwards. *)
  Format.printf "abd: prepare branches@\n%!";
  let brs_typ, brs_num, brs_so = Aux.split3
    (Aux.map_some (fun (prem, concl) ->
      let prems_opt =
        try Some (unify ~use_quants:false ~params:init_params cmp_v uni_v prem)
        with Contradiction _ -> None in
      match prems_opt with
      | Some (prem_typ, prem_num, prem_so) ->
        if List.exists
          (function CFalse _ -> true | _ -> false) prem_so
        then None
        else                          (* can raise Contradiction *)
          let concl_typ, concl_num, concl_so =
            unify ~use_quants:false ~params:init_params cmp_v uni_v concl in
          List.iter (function
          | CFalse loc ->
            raise (Contradiction ("assert false is possible", None, loc))
          | _ -> ()) concl_so;
          if not (NumS.satisfiable prem_num) then None
          else Some ((prem_typ, concl_typ), (prem_num, concl_num),
                     (prem_so, concl_so))
      | None -> None)
       brs) in
  Format.printf "abd: solve for types@\n%!";
  let tvs, ans_typ, more_num =
    abd_typ cmp_v uni_v ~init_params ?fincheck brs_typ in
  let brs_num = List.map2
    (fun (prem,concl) more -> prem, more @ concl)
    brs_num more_num in
  Format.printf "abd: solve for numbers@\n%!";
  let nvs, ans_num = NumS.abd ~init_params cmp_v uni_v brs_num in
  nvs @ tvs,
  Aux.map_append (fun (v,(t,lc)) -> Eqty (TVar v,t,lc))
    ans_typ ans_num

let abd_s cmp_v uni_v ?(init_params=VarSet.empty) prem concl =
  (* Do not change the order and no. of branches afterwards. *)
  let pms vs = VarSet.union (vars_of_list vs) init_params in
  let prem_opt =
    try Some (unify ~use_quants:false ~params:init_params cmp_v uni_v prem)
    with Contradiction _ -> None in
  match prem_opt with
  | Some (prem_typ, prem_num, prem_so) when
      List.for_all (function CFalse _ -> false | _ -> true) prem_so ->
    (try
       let concl_typ, concl_num, concl_so =
         unify ~use_quants:false ~params:init_params cmp_v uni_v concl in
       if List.exists (function CFalse _ -> true | _ -> false) prem_so
       then None
       else if not (NumS.satisfiable concl_num) then None
       else
         Aux.bind_opt
           (abd_simple cmp_v uni_v ~init_params (fun _ _ -> ()) 0 ([], [])
              (prem_typ, concl_typ))
           (fun (tvs, ans_typ) ->
             let more_num =
                 try
                   let cnj_ty, cnj_num =
                     combine_sbs ~use_quants:false ~params:(pms tvs)
                       cmp_v uni_v [prem_typ; ans_typ] in
                   let res_ty, res_num =
                     residuum cmp_v uni_v (pms tvs) cnj_ty concl_typ in
                   assert (res_ty = []);
                   cnj_num @ res_num
                 with Contradiction _ -> assert false in
             let ans_num =
               NumS.abd_s cmp_v uni_v ~init_params
                 prem_num (more_num @ concl_num) in
             Aux.map_opt ans_num
               (fun (nvs, ans_num) ->
                 (nvs @ tvs,
                  Aux.map_append (fun (v,(t,lc)) -> Eqty (TVar v,t,lc))
                    ans_typ ans_num)))
     with Contradiction _ -> None)
  | _ -> Some ([], [])



