(** Abduction for InvarGenT.

    Released under the GNU General Public Licence (version 2 or
    higher), NO WARRANTY of correctness etc. (C) Lukasz Stafiniak 2013
    @author Lukasz Stafiniak lukstafi (AT) gmail.com
    @since Mar 2013
*)
open Terms
open Aux
open Joint

let timeout_count = ref 700(* 1000 *)(* 5000 *)(* 50000 *)
let fail_timeout_count = ref 5

let residuum q prem concl =
  let concl = to_formula concl in
  let res_ty, res_num, res_so =
    unify ~use_quants:false q (subst_formula prem concl) in
  assert (res_so = []);
  res_ty, res_num

exception Result of VarSet.t * var_name list * subst

let empty_q =
  {cmp_v = (fun _ _ -> Same_quant); uni_v = (fun _ -> false);
   same_as = (fun _ _ -> ())}

(* TODO: optimize use of [cleanup] *)

type skip_kind = Superset_old_mod | Equ_old_mod
let skip_kind = ref Superset_old_mod

let more_general = ref false

let rich_return_type_heur bvs ans cand =
  let types = map_some
    (fun (v,(t,_)) -> if VarSet.mem v bvs then Some t else None)
    ans in
  let ret_vars = List.fold_left
      (fun vs t -> VarSet.union (fvs_typ (return_type t)) vs)
      VarSet.empty types in
  let arg_vars = List.fold_left
      (fun vs t -> VarSet.union
          (fvs_typ (TCons (tuple, arg_types t))) vs)
      VarSet.empty types in
  let arg_only_vars = VarSet.diff arg_vars ret_vars in
  let ret_only_vars = VarSet.diff ret_vars arg_vars in
  let sb = map_some
    (function
      | _, (TVar v2, _) as sx when VarSet.mem v2 arg_only_vars ->
        Some sx
      | v1, (TVar v2, lc) when VarSet.mem v1 arg_only_vars ->
        Some (v2, (TVar v1, lc))
      | _ -> None)
    cand in
  let b_sb = List.filter (fun (v,_) -> not (VarSet.mem v arg_vars)) sb in
  if sb=[] && b_sb=[] then cand
  else List.map
      (function
        | v, (t, lc) when VarSet.mem v bvs ->
          (*[* Format.printf "ret_typ_heur: %s= %a := %a@\n%!"
            (var_str v) (pr_ty false) t (pr_ty false) (subst_typ b_sb t);
          *]*)
          v, (subst_typ b_sb t, lc)
        | v, (t, lc) when VarSet.mem v ret_only_vars ->
          (*[* Format.printf "ret_typ_heur: %s= %a := %a@\n%!"
            (var_str v) (pr_ty false) t (pr_ty false) (subst_typ sb t);
          *]*)
          v, (subst_typ sb t, lc)
        | v1, (TVar v2, lc) when VarSet.mem v2 ret_only_vars ->
          (*[* Format.printf "ret_typ_heur: %s= %s := %a@\n%!"
            (var_str v2) (var_str v1) (pr_ty false)
            (subst_typ sb (TVar v1)); *]*)
          v2, (subst_typ sb (TVar v1), lc)
        | sx -> sx)
      cand

(* let revert_uni_in_all = ref (\* false *\) true *)
let rich_return_type = ref true

(* FIXME: should [bvs] variables be considered not universal? *)
let revert_cst_n_uni q ~bvs ~pms ~dissociate alien_prem ans cand =
  let fresh_id = ref 0 in
  let cand =
    if (* true *)dissociate then cand
    else
      let prem_sb, _ = Infer.separate_subst q ~keep_uni:true alien_prem in
      let prem_sb = map_some
          (function
            | v1, (TVar v2, lc)
              when not (VarSet.mem v2 bvs) && q.uni_v v2 ->
              Some (v2, (TVar v1, lc))
            | v1, (TVar v2, lc) as sv
              when not (VarSet.mem v1 bvs) &&
                   (VarSet.mem v2 bvs || not (q.uni_v v2)) -> Some sv
            | _ -> None)
          prem_sb in
      (*[* Format.printf
        "revert_cst_n_uni: cand with aliens=@ %a@ prem_sb=%a@ alien_prem=%a@\n%!"
        pr_subst cand pr_subst prem_sb pr_formula alien_prem;
      *]*)
      subst_sb ~sb:prem_sb cand in
  let old_sb, cand = partition_map
      (function
        | v2, (TVar v1, loc) when q.uni_v v2 && not (q.uni_v v1) ->
          incr fresh_id;
          Left ((TVar v2, (v1, (loc,!fresh_id))),
                (v2, (TVar v1, (loc,!fresh_id))))
        | v1, (TVar v2 as tv2, loc) when q.uni_v v2 && not (q.uni_v v1) ->
          incr fresh_id;
          Left ((tv2, (v1, (loc,!fresh_id))),
                (v1, (TVar v2, (loc,!fresh_id))))
        | v1, (TCons (n, []) as c, loc) when not (q.uni_v v1) ->
          incr fresh_id;
          Left ((c, (v1, (loc,!fresh_id))),
                (v1, (TCons (n, []), (loc,!fresh_id))))
        | sv -> Right sv)
      cand in
  let c6_sb, old_sb = List.split old_sb in
  let c6_sb =
    concat_map
      (fun (b, avs) ->
         (* Maximum should be the leftmost here. *)
         let leq (v1,_) (v2,_) = not (q.cmp_v v1 v2 = Left_of) in
         let ov, olc = maximum ~leq avs in
         let o = TVar ov in
         map_some
           (fun (cv, lc) -> if cv=ov then None else Some (TVar cv, (o, lc)))
           avs
         @ [b, (o, olc)])
      (collect c6_sb) in
  let c6_cnj = List.map
      (function
        | TVar v, s -> v, s
        | t, (TVar v, lc) -> v, (t, lc)
        | _ -> assert false)
      c6_sb in
  let old_cnj = List.map
      (fun (_, (_, (_,id1))) ->
         List.find (fun (_,(_,(_,id2))) -> id1=id2)
           old_sb)
      c6_cnj in
  let drop_id l = List.map (fun (v,(t,(lc,_))) -> v,(t,lc)) l in
  let c6_cnj = drop_id c6_cnj and old_cnj = drop_id old_cnj
  (*[* and old_sb = drop_id old_sb *]*) and c6_sb = drop_id c6_sb in
  (*[* Format.printf "revert:@ old_sb=%a@ c6_cnj=%a@ old_cnj=%a@\n%!"
    pr_subst old_sb pr_subst c6_cnj pr_subst old_cnj; *]*)
  let old_cand = old_cnj @ cand in
  let c6_cand =
    c6_cnj @
      List.map (fun (w,(t,loc)) ->
          w, (c_subst_typ c6_sb t, loc))
        cand in
  let c6_cand =
    if !rich_return_type
    then rich_return_type_heur bvs ans c6_cand
    else c6_cand in
  old_cand, c6_cand

let implies_cnj ans c_ans =
  List.for_all (fun (v,(t,_)) ->
    try fst (List.assoc v ans) = subst_typ ans t
    with Not_found -> false
  ) c_ans

let implies_ans ans (_,c_ans) = implies_cnj ans c_ans

(* Simple constraint abduction for terms

   For purposes of invariant inference, we need to account for the
   parameters.

   * [abstract] is the entry point
   ** if [cand=[]], it checks for repeated answers, skipping,
      and discarded answers
   ** otherwise it picks the next atom and checks if it's connected,
      if no, it loops with reordered candidates (possibly without the atom)
   ** if the answer + remaining candidates are workable, tries to drop
      the atom -- choice 1, otherwise proceeds straight to [step]
   ** it tries to keep a form of current atom with constants
      substituted away -- choice 6
   * [step] works through a single atom of the form [x=t]
   ** choice 2 replaces the current subterm of the atom with a fresh
      parameter, adding the subterm to replacements; if at the root of
      the atom, check connected and validate before proceeding to
      remaining candidates
   ** choice 3 steps into subterms of the current subterm, if any
   ** choice 4 keeps the current part of the atom unchanged; if at the
      root of the atom, check connected and validate before proceeding
      to remaining candidates
   ** choice 5 replaces the current subterm with a parameter
      introduced for an earlier occurrence; branch over all matching
      parameters; if at the root of the atom, check connected and
      validate before proceeding to remaining candidates
   ** choices 2-5 are guarded by try-with, as tests raise
      [Contradiction] if they fail, choice 1 only tests
      [implies_concl] which returns a boolean
   * we recompute modifications of parameters due to partial answer,
     e.g. [cparams], for clarity of [abd_typ] and [abd]
   * we sort the initial candidates by decreasing size
   * if [more_general] is false, the ordering of choices is instead:
     1, 6, 2, 4, 3, 5
 *)

exception Timeout

let abd_simple q ?without_quant ~bvs ~pms ~dissociate
    ~validate ~discard skip (vs, ans) (prem, alien_prem, concl) =
  let counter = ref 0 in
  let pms = add_vars vs pms in
  let skip = ref skip in
  let skipped = ref [] in
  let allvs = ref VarSet.empty in
  try
    let prem, prem_num = subst_solved ~use_quants:false q ans ~cnj:prem in
    (*[* Format.printf "abd_simple:@ prem_num=%a@\n%!" pr_formula prem_num;
    *]*)
    let concl, _ = subst_solved ~use_quants:false q ans ~cnj:concl in
    (*[* Format.printf
      "abd_simple: skip=%d,@ bvs=@ %a;@ vs=@ %s;@ ans=@ %a@ --@\n@[<2>%a@ ⟹@ %a@]@\n%!"
      !skip pr_vars bvs (String.concat "," (List.map var_str vs))
      pr_subst ans pr_subst prem pr_subst concl; *]*)
    let prem_and ans =
      (* TODO: optimize, don't redo work *)
      combine_sbs ~use_quants:false q [ans; prem] in
    let implies_concl vs ans =
      let cnj_typ, cnj_num = prem_and ans in
      let res_ty, res_num = residuum q cnj_typ concl in
      let num = res_num @ cnj_num in
      let impl_ty = res_ty = [] in
      let impl_num = is_right (NumS.satisfiable num) in
      (*[* Format.printf "abd_simple:@ implies?@ %b@ #res_ty=%d@\nans=@ %a@\nres_ty=@ %a@\n%!"
        (impl_ty && impl_num)
        (List.length res_ty) pr_subst ans pr_subst res_ty; *]*)
      impl_ty && impl_num in
    let reorder bvs init_cand =
      let rec aux acc c6acc cand =
        match cand with
        | (_,(TVar y,_) as sx)::cand, (c6x,(c6t,_) as c6sx)::c6cand
          when VarSet.mem y bvs ->
          true, sx, c6sx, (cand @ List.rev acc, c6cand @ List.rev c6acc)
        | (x,(t,_) as sx)::cand, (c6x,(c6t,_) as c6sx)::c6cand
          when VarSet.mem x bvs ->
          true, sx, c6sx, (cand @ List.rev acc, c6cand @ List.rev c6acc)
        | sx::cand, c6sx::c6cand ->
          aux (sx::acc) (c6sx::c6acc) (cand, c6cand)
        | [], [] ->
          let cand, c6cand = init_cand in
          false, List.hd cand, List.hd c6cand,
          (List.tl cand, List.tl c6cand)
        | _ -> assert false in
      aux [] [] init_cand in
    let rec abstract deep repls bvs pms vs ans = function
      | [], [] ->
        (*[* let ddepth = incr Joint.debug_dep; !Joint.debug_dep in *]*)
        (*[* Format.printf
          "abd_simple-abstract: [%d] @ repls=%a@ @ bvs=%a@ vs=%s@ ans=%a@\n%!"
          ddepth pr_subst (List.map (fun (x,y) -> y,(x,dummy_loc)) repls)
          pr_vars bvs
          (String.concat ","(List.map var_str vs))
          pr_subst ans; *]*)
        if implies_concl vs ans then
          let _, clean_ans = cleanup q vs ans in
          (*[* Format.printf "abd_simple-abstract:@\nclean_ans=%a@\n%!"
            pr_subst clean_ans          (* skipped=%a@\n *)
          (* (pr_line_list "|" pr_subst) !skipped *); *]*)
          allvs := add_vars vs !allvs;
          let repeated =
            try
              let (*[*old_ans*]*) _ =
                match !skip_kind with
                | Superset_old_mod ->
                  List.find
                    (fun xs ->
                       List.for_all (fun sx -> List.mem sx clean_ans) xs)
                    !skipped
                | Equ_old_mod ->
                  List.find
                    (fun xs ->
                       List.for_all (fun sx -> List.mem sx clean_ans) xs
                       && List.for_all (fun sx -> List.mem sx xs) clean_ans)
                    !skipped in
              (*[* Format.printf "skipping: [%d] ans=@ %a --@ old_ans=@ %a...@\n%!"
                ddepth pr_subst ans pr_subst old_ans; *]*)
              true
            with Not_found -> false in
          if repeated
          then (
            (*[* Format.printf "repeated: [%d] skip=%d --@ @[<2>%a@]@\n%!"
              ddepth !skip pr_subst ans; *]*)
            ())
          else if !skip > 0 then (
            skipped := clean_ans :: !skipped;
            (*[* Format.printf "skipped: [%d]@ @[<2>%a@]@\n%!" ddepth pr_subst ans; *]*)
            decr skip)
          (* TODO: optimize by passing clean_ans along with ans *)
          else if List.exists (implies_ans clean_ans) discard
          then (
            (*[* Format.printf "discarding: [%d] skip=%d --@ @[<2>%a@]@\n%!"
              ddepth !skip pr_subst ans; *]*)
            ())
          else (
            (*[* Format.printf
              "returning: [%d] skip=%d counter=%d --@\nvs=%s@ ans=@\n@[<2>%a@]@\n%!"
              ddepth !skip !counter
              (String.concat ","(List.map var_str vs))
              pr_subst ans; *]*)
            raise (Result (bvs, vs, ans)))
      | cand ->
        let is_p, (x, (t, lc) as sx), (c6x, (c6t, c6lc) as c6sx), cand =
          reorder bvs cand in
        incr counter; if !counter > !timeout_count then raise Timeout;
        (*[* let ddepth = incr Joint.debug_dep; !Joint.debug_dep in *]*)
        (*[* Format.printf
          "abd_simple-abstract: [%d] @ repls=%a@ bvs=%a@ vs=%s@ ans=%a@\nx=%s@ t=%a@ #cand=%d@\ncand=%a@\n%!"
          ddepth pr_subst (List.map (fun (x,y) -> y,(x,dummy_loc)) repls)
          pr_vars bvs
          (String.concat ","(List.map var_str vs))
          pr_subst ans (var_str x) (pr_ty false) t
          (List.length (fst cand)) pr_subst (fst cand); *]*)
        (* Choice 1: drop premise/conclusion atom from answer *)
        if implies_concl vs (ans @ fst cand)
        then (
          (*[* Format.printf
            "abd_simple: [%d] choice 1@ drop %s = %a@ (%s = %a)@\n%!"
            ddepth (var_str x) (pr_ty false) t
            (var_str c6x) (pr_ty false) c6t; *]*)
          (* try *)
            abstract deep repls bvs pms vs ans cand);
            (*[* Format.printf "abd_simple: [%d] choice 1 failed@\n%!"
              ddepth; *]*)               
          (*[* with Result (bvs, vs, ans) as e ->
            (* FIXME: remove try-with after debug over *)
            Format.printf "abd_simple: [%d] preserve choice 1@ %s =@ %a@ -- returned@ ans=%a@\n%!"
              ddepth (var_str x) (pr_ty false) t pr_subst ans;
            raise e); *]*)
        (*[* Format.printf
          "abd_simple: [%d]@ recover after choice 1@ %s =@ %a (%s = %a)@\ncand=%a@\n%!"
          ddepth (var_str x) (pr_ty false) t
          (var_str c6x) (pr_ty false) c6t pr_subst (fst cand); *]*)
        (* Choice 6: preserve atom in a "generalized" form *)
        if not !more_general && implies_concl vs (ans @ c6sx::fst cand)
        then (
          (*[* Format.printf
            "abd_simple: [%d]@ choice 6@ keep %s = %a@ (%s = %a)@\n%!"
            ddepth (var_str c6x) (pr_ty false) c6t
            (var_str x) (pr_ty false) t; *]*)
          try
            let bvs' =
              if is_p then VarSet.union
                  (VarSet.filter (not % q.uni_v)
                     (VarSet.add c6x (fvs_typ c6t))) bvs
              else bvs in
            let ans', _, so =
              unify ~bvs:bvs' ~pms ~sb:ans
                q [Eqty (TVar c6x, c6t, c6lc)] in
            (*[* Format.printf
              "abd_simple: [%d] validate 6 ans'=@ %a@\n%!" ddepth pr_subst ans'; *]*)
            validate (vs, ans');
            (*[* Format.printf "abd_simple: [%d] choice 6 OK@\n%!" ddepth; *]*)
            assert (so = []);
            abstract deep repls bvs' pms vs ans' cand
          with
          (*[* | Result (bvs, vs, ans) as e ->
            (* FIXME: remove try-with case after debug over *)
            Format.printf "abd_simple: [%d]@ preserve choice 6@ %s =@ %a@ -- returned@ ans=%a@\n%!"
              ddepth (var_str c6x)
              (pr_ty false) c6t pr_subst ans;
            raise e *]*)
          | Contradiction _ (*[* as e *]*) ->
            (*[* Format.printf
              "abd_simple: [%d]@ invalid choice 6 reason:@\n%a@\n%!"
              ddepth pr_exception e; *]*)
            ());
        (*[* Format.printf
          "abd_simple: [%d]@ recover after choice 6@ %s =@ %a@\n%!"
          ddepth (var_str c6x) (pr_ty false) c6t; *]*)
        step deep x lc {typ_sub=t; typ_ctx=[]} repls
          is_p bvs pms vs ans cand
    and step deep x lc loc repls is_p bvs pms vs ans cand =
      incr counter; if !counter > !timeout_count then raise Timeout;
      (*[* let ddepth = incr Joint.debug_dep; !Joint.debug_dep in *]*)
      (*[* Format.printf
        "abd_simple-step: [%d] @ loc=%a@ repls=%a@ vs=%s@ ans=%a@ x=%s@ cand=%a@\n%!"
        ddepth (pr_ty false) (typ_out loc) pr_subst (List.map (fun (x,y) -> y,(x,dummy_loc)) repls)
        (String.concat ","(List.map var_str vs))
        pr_subst ans (var_str x) pr_subst (fst cand); *]*)
      (* Choice 2: remove subterm from answer *)
      let choice2 () =
        let a = Infer.fresh_typ_var () in
        let repls' = (loc.typ_sub, a)::repls in
        (*[* Format.printf "abd_simple: [%d]@ choice 2@ repls'=@ %a@\n%!"
          ddepth pr_subst (List.map (fun (x,y) -> y,(x,dummy_loc)) repls'); *]*)
        let vs' = a::vs and pms' = VarSet.add a pms in
        let loc' = {loc with typ_sub = TVar a} in
        let t' = typ_out loc' in
        (*[* Format.printf "abd_simple: [%d]@ choice 2@ remove subterm %s =@ %a@\n%!"
          ddepth (var_str x) (pr_ty false) t'; *]*)
        (* FIXME: add [a] to [cparams]? *)
        match typ_next loc' with (* x bound when leaving step *)
        | None ->
          (try
             let bvs' =
               if is_p then VarSet.union
                   (VarSet.filter (not % q.uni_v)
                      (VarSet.add x (fvs_typ t'))) bvs
               else bvs in
             let ans', _, so =
               unify ~bvs:bvs' ~pms:pms' ~sb:ans
                 q [Eqty (TVar x, t', lc)] in
             (*[* Format.printf
               "abd_simple: [%d] validate 2 ans=@ %a@\n%!" ddepth pr_subst ans; *]*)
             validate (vs', ans');
             (*[* Format.printf "abd_simple: [%d] choice 2 OK@\n%!" ddepth; *]*)
             assert (so = []);
             abstract deep repls' bvs' pms' vs' ans' cand
           with Contradiction _ ->
             ())
        | Some loc' ->
          step deep x lc loc' repls' is_p bvs pms' vs' ans cand in
      (* Choice 3: try subterms of the subterm *)
      let choice3 () =
        (*[* Format.printf
          "abd_simple: [%d] approaching choice 3@ for@ %a@ @@ %s =@ %a@\n%!"
          ddepth (pr_ty false) loc.typ_sub (var_str x) (pr_ty false)
          (typ_out loc); *]*)
        if typ_sort loc.typ_sub = Type_sort
        then match typ_up loc with
          | None -> ()        
          | Some loc ->
            (*[* Format.printf
              "abd_simple: [%d]@ choice 3@ try subterms@\n%!" ddepth; *]*)
            step deep x lc loc repls is_p bvs pms vs ans cand in
      (* Choice 4: preserve current premise/conclusion subterm for answer *)
      let choice4 () =
        match typ_next loc with
        | None ->
          (try
             let t = typ_out loc in
             (*[* Format.printf
               "abd_simple: [%d] trying choice 4 a=%a@ sb=@ %a@\n%!"
               ddepth pr_formula [Eqty (TVar x, t, lc)] pr_subst ans; *]*)
             let ans, _, so =
               unify ~bvs ~pms ~sb:ans
                 q [Eqty (TVar x, t, lc)] in
             (*[* Format.printf
               "abd_simple: [%d] validate 4 ans=@ %a@\n%!" ddepth pr_subst ans; *]*)
             validate (vs, ans);
             (*[* Format.printf "abd_simple: [%d] choice 4 OK@\n%!" ddepth; *]*)
             assert (so = []);
             abstract deep repls bvs pms vs ans cand
           with Contradiction _ ->
             incr counter;
             if !counter > !timeout_count then raise Timeout;
             ());
           (*[* with Contradiction (_, msg, Some (ty1, ty2), _) ->
             (* FIXME: change to [with Contradiction _ ->
                incr counter;
                if !counter > !timeout_count then raise Timeout;
                ()] after debug  *)
             Format.printf
               "abd_simple: [%d] @ c.4 failed:@ %s@ %a@ %a@\n%!" ddepth
               msg (pr_ty true) ty1 (pr_ty true) ty2;
             (match ty1 with
                TVar v1 ->
                VarSet.iter (fun v2 ->
                    Format.printf
                      "q.uni_v %s=%b; q.uni_v %s=%b; q.cmp_v =%s@\n%!"
                      (var_str v1) (q.uni_v v1)
                      (var_str v2) (q.uni_v v2)
                      (var_scope_str (q.cmp_v v1 v2)))
                  (fvs_typ ty2)
              | _ -> ()); 
             Format.printf "abd_simple: [%d] choice 4 failed@\n%!" ddepth;
             incr counter;
             if !counter > !timeout_count then raise Timeout;
             () *]*)
        | Some loc ->
          (*[* Format.printf "abd_simple: [%d] neighbor loc@\n%!" ddepth; *]*)
          step deep x lc loc repls is_p bvs pms vs ans cand in
      (* Choice 5: match subterm with an earlier occurrence *)
      let choice5 () =
        let repl = assoc_all loc.typ_sub repls in
        (*[* Format.printf "abd_simple: [%d]@ choice 5 x=%s@ repls=@ %a@\n%!"
          ddepth (var_str x)
          pr_subst (List.map (fun (x,y) -> y,(x,dummy_loc)) repls); *]*)
        (*[* Format.printf "abd_simple: [%d]@ choice 5@ sub=@ %a@ repl=@ %s@\n%!"
          ddepth (pr_ty false) loc.typ_sub
          (String.concat ", " (List.map var_str repl)); *]*)
        List.iter
          (fun b ->
             let loc' = {loc with typ_sub = TVar b} in
             let t' = typ_out loc' in
             match typ_next loc' with
             | None ->
               (try
                  (*[* Format.printf
                    "abd_simple: [%d]@ c.5 unify x=%s@ t'=%a@ sb=@ %a@\n%!"
                    ddepth (var_str x) (pr_ty false) t' pr_subst ans; *]*)
                  let bvs' =
                    if is_p then VarSet.union
                        (VarSet.filter (not % q.uni_v)
                           (VarSet.add x (fvs_typ t'))) bvs
                    else bvs in
                  let ans', _, so =
                    (* try *)
                    unify ~bvs:bvs' ~pms ~sb:ans
                      q [Eqty (TVar x, t', lc)]
                      (*[* with Terms.Contradiction (msg,Some (ty1,ty2),_) as exn ->
                        Format.printf
                        "abd_simple: [%d] @ c.5 above failed:@ %s@ %a@ %a@\n%!" ddepth
                        msg (pr_ty true) ty1 (pr_ty true) ty2;
                        (match (ty1, ty2) with
                        TVar v1, TVar v2 ->
                        Format.printf
                        "q.uni_v %s=%b; q.uni_v %s=%b; q.cmp_v =%s@\n%!"
                        (var_str v1) (q.uni_v v1)
                        (var_str v2) (q.uni_v v2)
                        (str_of_cmp (q.cmp_v v1 v2))
                        | _ -> ()); 
                        raise exn *]*) in
                  (*[* Format.printf
                    "abd_simple: [%d] validate 5 ans'=@ %a@\n%!"
                    ddepth pr_subst ans'; *]*)
                  (*(try*)
                  validate (vs, ans');
                  (*with Terms.Contradiction (msg,Some (ty1,ty2),_) as exn ->
                    Format.printf
                    "abd_simple: [%d] @ c.5 validate failed:@ %s@ %a@ %a@\n%!" ddepth
                    msg (pr_ty true) ty1 (pr_ty true) ty2;
                    (match (ty1, ty2) with
                    TVar v1, TVar v2 ->
                    Format.printf
                    "q.uni_v %s=%b; q.uni_v %s=%b; q.cmp_v =%s@\n%!"
                    (var_str v1) (q.uni_v v1)
                    (var_str v2) (q.uni_v v2)
                    (str_of_cmp (q.cmp_v v1 v2))
                    | _ -> ()); 
                    raise exn); *]*)
                  (*[* Format.printf "abd_simple: choice 5 OK@\n%!"; *]*)
                  assert (so = []);
                  (*[* Format.printf
                    "abd_simple: [%d]@ choice 5@ match earlier %s =@ %a@\n%!"
                    ddepth (var_str x) (pr_ty false) t'; *]*)
                  abstract deep repls bvs' pms vs ans' cand
                with Contradiction _ ->
                  incr counter;
                  if !counter > !timeout_count then raise Timeout;
                  ())
             | Some loc' ->
               step deep x lc loc' repls is_p bvs pms vs ans cand)
          repl in
      if not deep then ()
      else if !more_general
      then (choice2 (); choice3 (); choice4 (); choice5 ())
      else (choice4 (); choice2 (); choice3 (); choice5 ())
    in
    if implies_concl vs ans then Some (bvs, (vs, ans))
    else
      let cnj_typ, more_alien = prem_and ((* ans @ *) concl) in
      let alien_prem = more_alien @ prem_num @ alien_prem in
      (* FIXME: hmm... *)
      (* let cnj_typ = list_diff cnj_typ discard in *)
      let init_cand =
        revert_cst_n_uni q ~bvs ~pms ~dissociate alien_prem ans cnj_typ in
      (* From shortest to longest. *)
      let init_cand = List.sort
          (fun ((_,(t1,_)),_) ((_,(t2,_)),_) -> typ_size t1 - typ_size t2)
          (uncurry List.combine init_cand) in
      let init_cand = List.split init_cand in
      (*[* Format.printf
        "abd_simple:@\ninit=@ %a@\nc6init=@ %a@\n%!"
        pr_subst (fst init_cand) pr_subst (snd init_cand); *]*)
      try
        if not !more_general
        then abstract false [] bvs pms vs ans init_cand;
        (*[* Format.printf
          "abd_simple: starting full depth (choices 1-6)@\n%!"; *]*)
        abstract true [] bvs pms vs ans init_cand; None
      with Result (bvs, vs, ans) ->
        (*[* Format.printf "abd_simple: Final validation@\n%!"; *]*)
        let ans, cnj_num, _ =
          unify ~bvs ~pms q (to_formula ans) in
        assert (cnj_num = []);
        validate (vs, ans);
        (*[* Format.printf
          "abd_simple: Final validation passed@\nans=%a@\n%!"
           pr_subst ans; *]*)
        Some (bvs, cleanup q vs ans)
  with
  | Contradiction _ ->
    (*[* Format.printf
      "abd_simple: conflicts with premises skip=%d,@ vs=@ %s;@ ans=@ %a@ --@\n@[<2>%a@ ⟹@ %a@]@\n%!"
      !skip (String.concat "," (List.map var_str vs))
      pr_subst ans pr_subst prem pr_subst concl; *]*)
    None          (* subst_solved or implies_concl *)
  | Timeout ->
    (*[* Format.printf
      "abd_simple: TIMEOUT conflicts with premises skip=%d,@ vs=@ %s;@ ans=@ %a@ --@\n@[<2>%a@ ⟹@ %a@]@\n%!"
      !skip (String.concat "," (List.map var_str vs))
      pr_subst ans pr_subst prem pr_subst concl; *]*)
    None

(* let max_skip = ref 20 *)

module TermAbd = struct
  type accu = VarSet.t * (var_name list * subst)
  type args = quant_ops * VarSet.t * bool
  type answer = var_name list * subst
  type discarded = answer
  (* premise, alien premise, conclusion *)
  type branch = subst * formula * subst

  let abd_fail_timeout = !fail_timeout_count

  let abd_simple (q, pms, dissociate) ~discard ~validate (bvs, acc) br =
    abd_simple q ~bvs ~pms ~dissociate ~validate ~discard 0 acc br

  let extract_ans (bvs, vs_ans) = vs_ans
  let discard_ans = extract_ans

  let concl_of_br (prem, alien_prem, concl) = to_formula concl

  let is_taut (vs, ans) = ans=[]

  let pr_branch pp (prem, _, concl) =
    Format.fprintf pp "@[<2>%a@ ⟹@ %a@]" pr_subst prem pr_subst concl

  let pr_ans pp (vs, ans) = pr_subst pp ans
end

module JCA = Joint.JointAbduction (TermAbd)

let abd_typ q ~bvs ?(dissociate=false) ~validate ~discard brs =
  (*[* Format.printf "abd_typ:@ bvs=@ %a@\n%!"
    pr_vars bvs; *]*)
  let alien_vs = ref [] in
  let alien_eqs = ref [] in
  let rec purge = function
    | t when typ_sort t = Num_sort ->
      let n = Infer.fresh_num_var () in
      (* Alien vars become abduction answer vars. *)
      alien_eqs := (n, (t, dummy_loc)):: !alien_eqs;
      alien_vs := n :: !alien_vs; TVar n
    | TCons (n, tys) -> TCons (n, List.map purge tys)
    | Fun (t1, t2) -> Fun (purge t1, purge t2)
    | (TVar _ | NCst _ | Nadd _) as t -> t in
  let brs =
    if dissociate
    then List.map
        (fun (prem,prem_num,concl) ->
           map_in_subst purge prem, prem_num,
           map_in_subst purge concl)
        brs
    else brs in
  let pms = vars_of_list !alien_vs in
  let cand_bvs, (vs, ans) =
    JCA.abd (q, pms, dissociate) ~discard ~validate (bvs, ([], [])) brs in
  (*[* Format.printf "abd_typ: result vs=%s@\nans=%a@\n%!"
    (String.concat ","(List.map var_str vs))
    pr_subst ans; *]*)
  let ans =
    if dissociate
    then List.map (fun (v,(t,lc)) -> v, (purge t, lc)) ans
    else ans in
  let vs = !alien_vs @ vs in
  (*[* Format.printf "abd_typ: dissociated %b vs=%s@\nalien=@ %a@\nans=%a@\n%!"
    dissociate (String.concat ","(List.map var_str vs))
    pr_subst !alien_eqs
    pr_subst ans; *]*)
  let num = List.map
    (fun (prem, _, concl) ->
      try
        (* FIXME: rethink, JCAQPAS *)
        let cnj_ty, cnj_num =
          combine_sbs ~use_quants:false q [prem; ans] in
        let res_ty, res_num =
          residuum q cnj_ty concl in
        (*[* Format.printf
          "abd_typ-num:@ prem=%a@ concl=%a@ res_ty=%a@ res_num=%a@\ncnj_num=%a@\n%!"
          pr_subst prem pr_subst concl
          pr_subst res_ty pr_formula res_num pr_formula cnj_num; *]*)
        (* FIXME *)
        assert (res_ty = []);
        cnj_num, res_num
      with Contradiction _ -> assert false)
    brs in
  cand_bvs, !alien_eqs, vs, ans, num

let abd_mockup_num q ~bvs brs =
  (* Do not change the order and no. of branches afterwards. *)
  let brs_typ, brs_num, brs_so = split3
    (map_some (fun (prem, concl) ->
      let prems_opt =
        try Some (unify q prem)
        with Contradiction _ -> None in
      match prems_opt with
      | Some (prem_typ, prem_num, prem_so) ->
        if List.exists
          (function CFalse _ -> true | _ -> false) prem_so
        then None
        else                          (* can raise Contradiction *)
          let concl_typ, concl_num, concl_so =
            unify q concl in
          List.iter (function
          | CFalse loc ->
            raise (Contradiction (Type_sort,
                                  "assert false is possible", None, loc))
          | _ -> ()) concl_so;
          if not (is_right (NumS.satisfiable concl_num)) then None
          else Some ((prem_typ, prem_num, concl_typ),
                     (prem_num, concl_num),
                     (prem_so, concl_so))
      | None -> None)
       brs) in
  let validate (vs, ans) = List.iter2
    (fun (prem_ty, _, concl_ty) (prem_num, concl_num) ->
      (* Do not use quantifiers, because premise is in the conjunction. *)
      (* TODO: after cleanup optimized in abd_simple, pass clean_ans
         and remove cleanup here *)
      let vs, ans = cleanup q vs ans in
      let sb_ty, ans_num =
        combine_sbs q [prem_ty; concl_ty; ans] in
      let cnj_num = ans_num @ prem_num @ concl_num in
      ignore (NumS.satisfiable cnj_num))
    brs_typ brs_num in
  try
    let cand_bvs, alien_eqs, tvs, ans_typ, more_num =
      abd_typ q ~bvs ~validate ~discard:[] brs_typ in
    Some (List.map2
            (fun (prem,concl) (more_p, more_c) ->
              more_p @ prem, more_c @ concl)
            brs_num more_num)
  with Suspect _ -> None

let abd q ~bvs ?(iter_no=2) ~discard brs =
  let dissociate = iter_no <= 0 in
  (* Do not change the order and no. of branches afterwards. *)
  (*[* Format.printf "abd: prepare branches@\n%!"; *]*)
  let discard_typ =
    try List.assoc Type_sort discard with Not_found -> [] in
  let discard_num =
    try List.assoc Num_sort discard with Not_found -> [] in
  let discard_typ = List.map
      (fun ans ->
         [], List.map
           (function Eqty (TVar v, t, lc) -> v, (t, lc)
                   | _ -> assert false) ans)
    discard_typ in
  let brs_typ, brs_num, brs_so = split3
    (map_some (fun (nonrec, prem, concl) ->
      let prems_opt =
        try Some (unify ~use_quants:false q prem)
        with Contradiction _ -> None in
      match prems_opt with
      | Some (prem_typ, prem_num, prem_so) ->
        if List.exists
          (function CFalse _ -> true | _ -> false) prem_so
        then None
        else                          (* can raise Contradiction *)
          let concl_typ, concl_num, concl_so =
            unify ~use_quants:false q concl in
          assert (concl_so = []);
          if not (is_right (NumS.satisfiable prem_num)) then None
          else Some ((prem_typ, prem_num, concl_typ),
                     (nonrec, prem_num, concl_num),
                     (prem_so, concl_so))
      | None -> None)
       brs) in
  (* FIXME: remove the fallback mechanism, move it to [Invariants]. *)
  let validate (vs, ans) = List.iter2
    (fun (prem_ty, _, concl_ty) (nonrec, prem_num, concl_num) ->
      (* Do not use quantifiers, because premise is in the conjunction. *)
      (* TODO: after cleanup optimized in abd_simple, pass clean_ans
         and remove cleanup here *)
      let vs, ans = cleanup q vs ans in
      let sb_ty, ans_num =
        combine_sbs ~use_quants:false q [prem_ty; concl_ty; ans] in
      if not dissociate then
        let cnj_num = ans_num @ prem_num @ concl_num in
        (*[* Format.printf "validate-typ: sb_ty=@ %a@\ncnj_num=@ %a@\n%!"
           pr_subst sb_ty pr_formula cnj_num; *]*)
        let (*[* num_state *]*) _ =
          (* FIXME: It's like [satisfiable] because of [empty_q]. *)
          NumS.holds empty_q VarSet.empty NumS.empty_state cnj_num in
        (*[* Format.printf "validate-typ: num_state=@ %a@\n%!"
           pr_formula (NumS.formula_of_state num_state); *]*)
        ()
    )
    brs_typ brs_num in
  (* We do not remove nonrecursive branches for types -- it will help
     other sorts do better validation. *)
  let cand_bvs, alien_eqs, tvs, ans_typ, more_num =
    try
      abd_typ q ~bvs ~dissociate ~validate ~discard:discard_typ brs_typ
    with Suspect (cnj, lc) ->
      (*[* Format.printf
        "abd: fallback abd_typ loc=%a@\nsuspect=%a@\n%!"
        pr_loc lc pr_formula cnj;
      *]*)
      raise (NoAnswer (Type_sort, "term abduction failed", None, lc)) in
  let brs_num = List.map2
    (fun (nonrec,prem,concl) (more_p, more_c) ->
      nonrec, more_p @ prem, more_c @ concl)
    brs_num more_num in
  (*[* Format.printf "abd: solve for numbers@\n%!"; *]*)
  let nvs, ans_num =
    try
      if dissociate then [], []
      (* [tvs] includes alien variables! *)
      else NumS.abd q ~bvs ~discard:discard_num ~iter_no brs_num
    with
    | Suspect (cnj, lc) ->
      (*[* Format.printf
        "abd: fallback NumS.abd loc=%a@\nsuspect=%a@\n%!"
        pr_loc lc pr_formula cnj;
      *]*)
      raise (NoAnswer (Num_sort, "numerical abduction failed",
                       None, lc)) in
  let n_sb = subst_of_cnj ~elim_uni:true q ans_num in
  (*[* Format.printf "abd: n_sb=@ %a@\n@\n%!" pr_subst n_sb; *]*)
  let ans_typ = subst_formula n_sb (to_formula ans_typ) in
  cand_bvs, alien_eqs,
  (nvs @ tvs, ans_typ @ ans_num)



