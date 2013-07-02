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

exception Result of VarSet.t * (var_name list * subst)
let debug_dep = ref 0

let fill_params = ref true

let rec pms_con x params vs t old_ans =
  let tvs = fvs_typ t in
  Format.printf
    "pms_con: x=%s params=%s@ vs=%s@ tvs=%s@ t=%a@\n%!"
    (var_str x)
    (String.concat ","(List.map var_str (VarSet.elements params)))
    (String.concat ","(List.map var_str vs))
    (String.concat ","(List.map var_str (VarSet.elements tvs)))
    (pr_ty false) t; (* *)
  let params' =
    if VarSet.mem x params && not (List.mem x vs) ||
      VarSet.exists (fun x -> VarSet.mem x params && not (List.mem x vs)) tvs
    then VarSet.union (VarSet.add x tvs) params
    else params in
  if not !fill_params || params == params' then params'
  else match old_ans with
  | [] -> params'
  | (x, (t, _))::old_ans -> pms_con x params' vs t old_ans    

let cleanup vs ans =
  let clean, ans = Aux.partition_map
    (function x, _ as sx when List.mem x vs -> Aux.Left sx
    | y, (TVar x, lc) when List.mem x vs -> Aux.Left (x, (TVar y, lc))
    | sy -> Aux.Right sy) ans in
  let clean, cn_num, cn_so = unify ~use_quants:false
    (fun _ _ -> Same_quant) (fun _ -> false) (to_formula clean) in
  let sb, more_ans = List.partition
    (function x, _ when List.mem x vs -> true
    | _ -> false) clean in    
  assert (cn_num = []);
  assert (cn_so = []);
  let ans = subst_sb ~sb (more_ans @ ans) in
  let ansvs = fvs_sb ans in
  List.filter (Aux.flip VarSet.mem ansvs) vs, ans

let abd_simple cmp_v uni_v ~params
    ~validate ~discard skip
    (vs, ans) (prem, concl) =
  let skip = ref skip in
  let skipped = ref [] in
  let allvs = ref VarSet.empty in
  try
    let prem, _ =
      subst_solved ~use_quants:false ~params cmp_v uni_v ans
        ~cnj:prem in
    let concl, _ =
      subst_solved ~use_quants:false ~params cmp_v uni_v ans
        ~cnj:concl in
    Format.printf
      "abd_simple: params=@ %s@\n%!"
      (String.concat "," (List.map var_str (VarSet.elements params))); (* *)
    Format.printf
      "abd_simple: skip=%d,@ vs=@ %s;@ ans=@ %a@ --@\n@[<2>%a@ ⟹@ %a@]@\n%!"
      !skip (String.concat "," (List.map var_str vs))
      pr_subst ans pr_subst prem pr_subst concl; (* *)
    let prem_and ~params ans =
      (* TODO: optimize, don't redo work *)
      combine_sbs ~use_quants:false ~params cmp_v uni_v [ans; prem] in
    let implies_concl ~params ans =
      let cnj_typ, cnj_num = prem_and ~params ans in
      let res_ty, res_num = residuum cmp_v uni_v params cnj_typ concl in
      let num = res_num @ cnj_num in
      Format.printf "abd_simple:@ implies?@ %b@ #res_ty=%d@\nans=@ %a@\nres_ty=@ %a@\n%!"
        (res_ty = [] && NumS.satisfiable num) (List.length res_ty) pr_subst ans pr_subst res_ty; (* *)
      res_ty = [] && NumS.satisfiable num in
    let rec abstract repls params vs ans cur_ans = function
      | [] ->
        let ddepth = incr debug_dep; !debug_dep in
        Format.printf
          "abd_simple-abstract: [%d] @ repls=%a@ params=%s@ vs=%s@ ans=%a@ cur_ans=%a@\n%!"
          ddepth pr_subst (List.map (fun (x,y) -> y,(x,dummy_loc)) repls)
          (String.concat ","(List.map var_str (VarSet.elements params)))
          (String.concat ","(List.map var_str vs))
          pr_subst ans pr_subst cur_ans; (* *)
        if implies_concl ~params ans then
          let ans = List.sort compare ans in
          allvs := List.fold_right VarSet.add vs !allvs;
          let repeated =
            (* TODO: (FIXME?) isn't this pruning too excessive? *)
            try
              let old_ans (* _ *) = List.find
                (fun xs ->
                  List.for_all (fun (y,_) -> VarSet.mem y !allvs)
                    (Aux.sorted_diff xs ans)) !skipped in
              Format.printf "skipping: [%d] ans=@ %a --@ old_ans=@ %a...@\n%!"
                ddepth pr_subst ans pr_subst old_ans; (* *)
              true
            with Not_found -> false in
          if repeated
          then (
            Format.printf "repeated: [%d] skip=%d --@ @[<2>%a@]@\n%!"
              ddepth !skip pr_subst ans; (* *)
            ())
          else if !skip > 0 then (
            skipped := ans :: !skipped;
            Format.printf "skipped: [%d]@ @[<2>%a@]@\n%!" ddepth pr_subst ans; (* *)
            decr skip)
          (* TODO: optimize by passing clean_ans along with ans *)
          else if List.exists (fun sx -> List.mem sx discard)
              (snd (cleanup vs ans))
          then (
              Format.printf "discarding: [%d] skip=%d --@ @[<2>%a@]@\n%!"
                ddepth !skip pr_subst ans; (* *)
              ())
          else (
              Format.printf
                "returning: [%d] skip=%d params=%s --@ vs=%s@ ans=@\n@[<2>%a@]@\n%!"
                ddepth !skip
                (String.concat ","(List.map var_str (VarSet.elements params)))
                (String.concat ","(List.map var_str vs))
                pr_subst ans; (* *)
              raise (Result (params, cleanup vs ans)))
      | (x, (t, lc))::cand ->
        let ddepth = incr debug_dep; !debug_dep in
        Format.printf
          "abd_simple-abstract: [%d] @ repls=%a@ params=%s@ vs=%s@ ans=%a@ cur_ans=%a@ x=%s@ cand=%a@\n%!"
          ddepth pr_subst (List.map (fun (x,y) -> y,(x,dummy_loc)) repls)
          (String.concat ","(List.map var_str (VarSet.elements params)))
          (String.concat ","(List.map var_str vs))
          pr_subst ans pr_subst cur_ans (var_str x) pr_subst cand; (* *)

        if implies_concl ~params (ans @ cand) then (
          (* Choice 1: drop premise/conclusion atom from answer *)
          Format.printf "abd_simple: [%d]@ choice 1@ drop %s =@ %a@\n%!"
            ddepth (var_str x) (pr_ty false) t; (* *)
          try abstract repls params vs ans cur_ans cand
          with Result (params, (vs, ans)) as e ->
            (* FIXME: remove try-with after debug over *)
            Format.printf "abd_simple: [%d]@ preserve choice 1@ %s =@ %a@ -- returned@ ans=%a@\n%!"
              ddepth (var_str x) (pr_ty false) t pr_subst ans; (* *)
            raise e);
        Format.printf
          "abd_simple: [%d]@ recover after choice 1@ %s =@ %a@\n%!"
          ddepth (var_str x) (pr_ty false) t; (* *)

        step x lc {typ_sub=t; typ_ctx=[]} repls params vs ans cur_ans cand
    and step x lc loc repls params vs ans cur_ans cand =
      (* Choice 2: preserve current premise/conclusion subterm for answer *)
        let ddepth = incr debug_dep; !debug_dep in
        Format.printf
          "abd_simple-step: [%d] @ loc=%a@ repls=%a@ vs=%s@ ans=%a@
cur_ans=%a@ x=%s@ cand=%a@\n%!"
          ddepth (pr_ty false) (typ_out loc) pr_subst (List.map (fun (x,y) -> y,(x,dummy_loc)) repls)
          (String.concat ","(List.map var_str vs))
          pr_subst ans pr_subst cur_ans (var_str x) pr_subst cand; (* *)
      (match typ_next loc with
      | None ->
          (try
            Format.printf
              "abd_simple: [%d] trying choice 2 params=%s@ sb=@ %a@\n%!"
              ddepth (String.concat ", "
                 (List.map var_str (VarSet.elements params))) pr_subst ans; (* *)
            let t = typ_out loc in
            let params = pms_con x params vs t ans in
            let ans, _, so =
              unify ~use_quants:true ~params ~sb:ans
                cmp_v uni_v [Eqty (TVar x, t, lc)] in
            Format.printf
              "abd_simple: [%d] validate 2 ans=@ %a@\n%!" ddepth pr_subst ans; (* *)
            validate params vs ans;
            Format.printf "abd_simple: [%d] choice 2 OK@\n%!" ddepth; (* *)
            assert (so = []);
            abstract repls params vs ans cur_ans cand
          with Contradiction (msg, Some (ty1, ty2), _) ->
            (* FIXME: change to [with Contradiction _ -> ()] after debug  *)
            Format.printf
              "abd_simple: [%d] @ c.2 failed:@ %s@ %a@ %a@\n%!" ddepth
              msg (pr_ty true) ty1 (pr_ty true) ty2;
            (match (ty1, ty2) with
              TVar v1, TVar v2 ->
                Format.printf
                  "uni_v %s=%b; uni_v %s=%b; cmp_v =%s@\n%!"
                  (var_str v1) (uni_v v1)
                  (var_str v2) (uni_v v2)
                  (str_of_cmp (cmp_v v1 v2))
            | _ -> ()); 
             Format.printf "abd_simple: [%d] choice 2 failed@\n%!" ddepth; (* *)
            ())
      | Some loc ->
        Format.printf "abd_simple: [%d] neighbor loc@\n%!" ddepth; (* *)
        step x lc loc repls params vs ans cur_ans cand);
      if not (num_sort_typ loc.typ_sub)
      then
        (* Choice 3: remove subterm from answer *)
        let a = Infer.fresh_typ_var () in
        let repls' = (loc.typ_sub, a)::repls in
        Format.printf "abd_simple: [%d]@ choice 3@ repls'=@ %a@\n%!"
          ddepth pr_subst (List.map (fun (x,y) -> y,(x,dummy_loc)) repls'); (* *)
        let params' = VarSet.add a params in
        let vs' = a::vs in
        let loc' = {loc with typ_sub = TVar a} in
        let t' = typ_out loc' in
        Format.printf "abd_simple: [%d]@ choice 3@ remove subterm %s =@ %a@\n%!"
          ddepth (var_str x) (pr_ty false) t'; (* *)
        let cur_ans' = (x, (t', lc))::cur_ans in
        let params' = pms_con x params' vs' t' ans in
        (match typ_next loc' with (* x bound when leaving step *)
        | None ->
          (try
             let ans', _, so =
               unify ~use_quants:true ~params:params' ~sb:ans
                 cmp_v uni_v [Eqty (TVar x, t', lc)] in
             Format.printf
               "abd_simple: [%d] validate 3 ans=@ %a@\n%!" ddepth pr_subst ans; (* *)
             validate params' vs' ans';
             Format.printf "abd_simple: [%d] choice 3 OK@\n%!" ddepth; (* *)
             assert (so = []);
             abstract repls' params' vs' ans' cur_ans' cand
           with Contradiction _ ->
             ())
        | Some loc' ->
          step x lc loc' repls' params' vs' ans cur_ans cand);
        (* Choice 4: match subterm with an earlier occurrence *)
        if not (implies_concl params' cur_ans')
        then (
          let repl = Aux.assoc_all loc.typ_sub repls in
          Format.printf "abd_simple: [%d]@ choice 4 x=%s@ repls=@ %a@\n%!"
            ddepth (var_str x)
            pr_subst (List.map (fun (x,y) -> y,(x,dummy_loc)) repls); (* *)
          Format.printf "abd_simple: [%d]@ choice 4@ sub=@ %a@ repl=@ %s@\n%!"
            ddepth (pr_ty false) loc.typ_sub
            (String.concat ", " (List.map var_str repl)); (* *)
          List.iter
            (fun b ->
              let loc' = {loc with typ_sub = TVar b} in
              let t' = typ_out loc' in
              let cur_ans' = (x, (t', lc))::cur_ans in
              match typ_next loc' with
              | None ->
                (try
                   Format.printf
                     "abd_simple: [%d]@ c.4 unify x=%s@ t'=%a@ sb=@ %a@\n%!"
                     ddepth (var_str x) (pr_ty false) t' pr_subst ans; (* *)
                   let params = pms_con x params vs t' ans in
                   let ans', _, so =
                     (* try *)
                       unify ~use_quants:true ~params ~sb:ans
                         cmp_v uni_v [Eqty (TVar x, t', lc)]
                     (*with Terms.Contradiction (msg,Some (ty1,ty2),_) as exn ->
                        Format.printf
                         "abd_simple: [%d] @ c.4 above failed:@ %s@ %a@ %a@\n%!" ddepth
                         msg (pr_ty true) ty1 (pr_ty true) ty2;
                       (match (ty1, ty2) with
                         TVar v1, TVar v2 ->
                           Format.printf
                             "uni_v %s=%b; uni_v %s=%b; cmp_v =%s@\n%!"
                             (var_str v1) (uni_v v1)
                             (var_str v2) (uni_v v2)
                             (str_of_cmp (cmp_v v1 v2))
                       | _ -> ()); 
                       raise exn * *) in
                   Format.printf
                     "abd_simple: [%d] validate 4 ans'=@ %a@\n%!"
                     ddepth pr_subst ans'; (* *)
                   (*try*)
                   validate params vs ans';
                     (*with Terms.Contradiction (msg,Some (ty1,ty2),_) as exn ->
                        Format.printf
                         "abd_simple: [%d] @ c.4 validate failed:@ %s@ %a@ %a@\n%!" ddepth
                         msg (pr_ty true) ty1 (pr_ty true) ty2;
                       (match (ty1, ty2) with
                         TVar v1, TVar v2 ->
                           Format.printf
                             "uni_v %s=%b; uni_v %s=%b; cmp_v =%s@\n%!"
                             (var_str v1) (uni_v v1)
                             (var_str v2) (uni_v v2)
                             (str_of_cmp (cmp_v v1 v2))
                       | _ -> ()); 
                       raise exn); * *)
                   Format.printf "abd_simple: choice 4 OK@\n%!"; (* *)
                   assert (so = []);
                   Format.printf
                     "abd_simple: [%d]@ choice 4@ match earlier %s =@ %a@\n%!"
                     ddepth (var_str x) (pr_ty false) t'; (* *)
                   abstract repls params vs ans' cur_ans' cand
                 with Contradiction _ ->
                   ())
              | Some loc' ->
                step x lc loc' repls params vs ans cur_ans cand)
            repl;
          (* Choice 5: try subterms of the subterm *)
          Format.printf
            "abd_simple: [%d] approaching choice 5@ for@ %a@ @@ %s =@ %a@\n%!"
            ddepth (pr_ty false) loc.typ_sub (var_str x) (pr_ty false)
            (typ_out loc); (* *)
          (match typ_up loc with
          | None ->
            ()        
          | Some loc ->
            Format.printf
              "abd_simple: [%d]@ choice 5@ try subterms@\n%!" ddepth; (* *)
            step x lc loc repls params vs ans cur_ans cand);
        )
    in
    if implies_concl params ans then Some (params, (vs, ans))
    else
      let cnj_typ, _ = prem_and params concl in
      let cnj_typ = List.sort
        (fun (_,(t1,_)) (_,(t2,_)) -> typ_size t2 - typ_size t1)
        (Aux.list_diff cnj_typ discard) in
      Format.printf
        "abd_simple: init cnj=@ %a@\n%!" pr_subst cnj_typ; (* *)
      try abstract [] params vs ans [] cnj_typ; None
      with Result (params, vs_ans) -> Some (params, vs_ans)
  with Contradiction _ -> None          (* subst_solved or implies_concl *)

(* let max_skip = ref 20 *)

let abd_typ cmp_v uni_v ?(init_params=VarSet.empty) ~validate ~discard brs =
  Format.printf "abd_typ:@ init params=@ %s@\n%!"
    (String.concat ", " (List.map var_str (VarSet.elements
     init_params))); (* *)
  let br0 = 0, List.hd brs in
  let more_brs = List.map (fun br -> -1, br) (List.tl brs) in
  let time = ref (Sys.time ()) in
  let rec loop (params, a_acc (* as acc *)) runouts = function
    | [] ->
      let _, (prem, concl) =
        Aux.maximum ~leq:(fun (i,_) (j,_) -> i<=j) runouts in
      raise (Suspect (fst a_acc,
                      to_formula (snd a_acc @ prem @ concl)))
    | (skip, br as obr)::more_brs ->
      let ddepth = incr debug_dep; !debug_dep in
      Format.printf
        "abd_typ-loop: [%d] skip=%d, #runouts=%d@\n@[<2>%a@ ⟹@ %a@]@\n%!"
        ddepth skip (List.length runouts) pr_subst (fst br) pr_subst
     (snd br); (* *)
      match abd_simple cmp_v uni_v ~params
        ~validate ~discard skip a_acc br with
      | Some acc ->
        let ntime = Sys.time () in
          Format.printf "ans: [%d] (%.2fs)@ @[<2>%a@]@\n%!" ddepth (ntime -. !time)
          pr_subst (snd a_acc); time := ntime; (* *)
        check_runouts acc obr more_brs [] runouts
      | None ->
        Format.printf "reset first [%d] at skip=%d@\n%!" ddepth
          skip; (* *)
        loop (init_params, ([], [])) ((0, br)::runouts) more_brs

  and check_runouts (params, a_acc as acc) (dskip, dbr as done_br)
      more_brs done_runouts = function
    | [] -> check_brs acc (List.rev done_runouts) [done_br] more_brs
    | (confls, br as obr)::more_runouts ->
      let ddepth = incr debug_dep; !debug_dep in
      Format.printf
        "abd_typ-check_runouts: [%d] confls=%d, #done=%d@\n@[<2>%a@ ⟹@ %a@]@\n%!"
        ddepth confls (List.length done_runouts) pr_subst (fst br)
     pr_subst (snd br); (* *)
      match abd_simple cmp_v uni_v ~params
        ~validate ~discard 0 a_acc br with
      | Some acc ->
        let ntime = Sys.time () in
          Format.printf "ans: [%d] (%.2fs)@ @[<2>%a@]@\n%!" ddepth (ntime -. !time)
          pr_subst (snd a_acc); time := ntime; (* *)
        check_runouts acc done_br more_brs (obr::done_runouts) more_runouts
      | None ->
        Format.printf "reset runouts [%d] at confls=%d@\n%!" ddepth
          confls; (* *)
        loop (init_params, ([], []))
          ((confls+1, br)::List.rev_append done_runouts more_runouts)
          ((dskip+1, dbr)::more_brs)
      
  and check_brs (params, a_acc as acc) runouts done_brs = function
    | [] -> acc
    | (skip, br as obr)::more_brs ->
      let ddepth = incr debug_dep; !debug_dep in
      Format.printf
        "abd_typ-check_brs: [%d] skip=%d, #done=%d@\n@[<2>%a@ ⟹@ %a@]@\n%!"
        ddepth skip (List.length done_brs) pr_subst (fst br) pr_subst
        (snd br); (* *)
      match abd_simple cmp_v uni_v ~params
        ~validate ~discard 0 a_acc br with
      | Some acc ->
        let ntime = Sys.time () in
          Format.printf "ans: [%d] (%.2fs)@ @[<2>%a@]@\n%!" ddepth (ntime -. !time)
          pr_subst (snd a_acc); time := ntime; (* *)
        check_brs acc runouts (obr::done_brs) more_brs
      | None ->
        Format.printf "reset check [%d] at skip=%d@\n%!" ddepth
     skip; (* *)
        loop (init_params, ([], []))
          runouts ((skip+1, br)::List.rev_append done_brs more_brs) in

  let params, (vs, ans) = loop (init_params, ([], [])) [] (br0::more_brs) in
  Format.printf "abd_typ: result params=%s@ vs=%s@\nans=%a@\n%!"
    (String.concat ","(List.map var_str (VarSet.elements params)))
    (String.concat ","(List.map var_str vs))
    pr_subst ans; (* *)
  let num = List.map
    (fun (prem, concl) ->
      try
        let cnj_ty, cnj_num =
          combine_sbs ~use_quants:false ~params cmp_v uni_v
            [prem; ans] in
        let res_ty, res_num =
          residuum cmp_v uni_v params cnj_ty concl in
        Format.printf "abd_typ: vs=%s@ res_ty=%a@ res_num=%a@\nconcl=%a@\n%!"
          (String.concat ","(List.map var_str vs))
          pr_subst res_ty pr_formula res_num pr_subst concl; (* *)
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
  let validate params vs ans = List.iter2
    (fun (prem_ty, concl_ty) (prem_num, concl_num) ->
      (* Do not use quantifiers, because premise is in the conjunction. *)
      (* TODO: after cleanup optimized in abd_simple, pass clean_ans
         and remove cleanup here *)
      let vs, ans = cleanup vs ans in
      let sb_ty, ans_num =
        combine_sbs ~use_quants:false ~params cmp_v uni_v
          [prem_ty; concl_ty; ans] in
      let cnj_num = ans_num @ prem_num @ concl_num in
      ignore (NumS.holds (fun _ _ -> Same_quant) (fun _ -> false)
                NumS.empty_state cnj_num))
    brs_typ brs_num in
  try
    let tvs, ans_typ, more_num =
      abd_typ cmp_v uni_v ~init_params ~validate ~discard:[] brs_typ in
    Some (List.map2
            (fun (prem,concl) more -> prem, more @ concl)
            brs_num more_num)
  with Suspect _ -> None

let abd cmp_v uni_v ?(init_params=VarSet.empty) ~discard
    ~fallback brs =
  (* Do not change the order and no. of branches afterwards. *)
  Format.printf "abd: prepare branches@\n%!"; (* *)
  let discard_typ, discard_num = List.partition
    (function Eqty (_, t2, _) when typ_sort_typ t2 -> true | _ -> false)
    discard in
  let discard_typ = List.map
    (function Eqty (TVar v, t, lc) -> v, (t, lc) | _ -> assert false)
    discard_typ in
  let prepare_brs brs = Aux.split3
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
  let fallback, (brs_typ, brs_num, brs_so) =
    try false, prepare_brs brs
    with Contradiction _ as e ->
      if fallback == brs then raise e
      else (
      Format.printf "abd: prepare fallback@\n%!"; (* *)
      true, prepare_brs fallback) in
  let validate params vs ans = List.iter2
    (fun (prem_ty, concl_ty) (prem_num, concl_num) ->
      (* Do not use quantifiers, because premise is in the conjunction. *)
      (* TODO: after cleanup optimized in abd_simple, pass clean_ans
         and remove cleanup here *)
      let vs, ans = cleanup vs ans in
      let sb_ty, ans_num =
        combine_sbs ~use_quants:false ~params cmp_v uni_v
          [prem_ty; concl_ty; ans] in
      let cnj_num = ans_num @ prem_num @ concl_num in
      Format.printf "validate-typ: sb_ty=@ %a@\ncnj_num=@ %a@\n%!"
        pr_subst sb_ty pr_formula cnj_num; (* *)
      let num_state = NumS.holds (fun _ _ -> Same_quant) (fun _ -> false)
        NumS.empty_state cnj_num in
      Format.printf "validate-typ: num_state=@ %a@\n%!"
        pr_formula (NumS.formula_of_state num_state); (* *)
    )
    brs_typ brs_num in
  Format.printf "abd: discard_typ=@ %a@\n%!" pr_subst discard_typ;
     (* *)
  let tvs, ans_typ, more_num =
    abd_typ cmp_v uni_v ~init_params ~validate ~discard:discard_typ brs_typ in
  let brs_num = List.map2
    (fun (prem,concl) more -> prem, more @ concl)
    brs_num more_num in
  Format.printf "abd: solve for numbers@\n%!"; (* *)
  (* FIXME: add [discard] to NumS.abd *)
  let nvs, ans_num = NumS.abd ~init_params cmp_v uni_v brs_num in
  fallback,
  (nvs @ tvs,
   Aux.map_append (fun (v,(t,lc)) -> Eqty (TVar v,t,lc))
    ans_typ ans_num)

let abd_s cmp_v uni_v ?(init_params=VarSet.empty) prem concl =
  (* Do not change the order and no. of branches afterwards. *)
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
           (abd_simple cmp_v uni_v ~params:init_params
              ~validate:(fun _ _ _ -> ()) ~discard:[] 0 ([], [])
              (prem_typ, concl_typ))
           (fun (params, (tvs, ans_typ)) ->
             let more_num =
                 try
                   let cnj_ty, cnj_num =
                     combine_sbs ~use_quants:false ~params
                       cmp_v uni_v [prem_typ; ans_typ] in
                   let res_ty, res_num =
                     residuum cmp_v uni_v params cnj_ty concl_typ in
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



