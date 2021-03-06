(** Abduction for InvarGenT.

    Released under the GNU General Public Licence (version 2 or
    higher), NO WARRANTY of correctness etc. (C) Lukasz Stafiniak 2013
    @author Lukasz Stafiniak lukstafi (AT) gmail.com
    @since Mar 2013
*)
let timeout_count = ref 700(* 5000 *)(* 50000 *)
let fail_timeout_count = ref (* 4 *)10
let no_alien_prem = ref true(* false *)
let guess_eqs_nonvar = ref true
let prefer_guess = ref false
let neg_before_abd = ref true
let num_neg_since = ref 1
let term_neg_since = ref (* 1 *)0
let more_general = ref false
let richer_answers = ref false
let no_num_abduction = ref false
let revert_cst = ref true
let revert_at_uni = ref true
let verif_all_brs = ref (* true *)false

open Defs
open Terms
open Aux
open Joint
(* Also depends on OCaml.ml. *)

let abd_fail_flag = ref false
let abd_timeout_flag = ref false

let residuum q prem concl =
  let concl = to_formula concl in
  solve ~use_quants:false q (subst_formula prem concl)

type t_validation = (VarSet.t * (subst * NumS.state)) list
(* Result remembers the invariant parameters [bvs]. *)
exception Result of VarSet.t * var_name list * subst * t_validation

let empty_q =
  {cmp_v = (fun _ _ -> Same_quant); uni_v = (fun _ -> false);
   same_as = (fun _ _ -> ());
   upward_of = (fun _ _ -> true)}

(* TODO: optimize use of [cleanup] *)

let rich_return_type_heur bvs ans cand =
  let types = VarMap.fold
    (fun v (t,_) acc -> if VarSet.mem v bvs then t::acc else acc)
    ans [] in
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
  let sb = varmap_of_assoc sb in
  let b_sb = VarMap.filter
      (fun v _ -> not (VarSet.mem v arg_vars)) sb in
  if VarMap.is_empty sb && VarMap.is_empty b_sb then cand
  else List.map
      (function
        | v, (t, lc) as sx when VarSet.mem v bvs ->
          (*[* Format.printf "ret_typ_heur: %s= %a := %a@\n%!"
            (var_str v) pr_ty t pr_ty (subst_typ b_sb t);
          *]*)
          let t' = subst_typ b_sb t in
          if TVar v = t' then sx else v, (t', lc)
        | v, (t, lc) as sx when VarSet.mem v ret_only_vars ->
          (*[* Format.printf "ret_typ_heur: %s= %a := %a@\n%!"
            (var_str v) pr_ty t pr_ty (subst_typ sb t);
          *]*)
          let t' = subst_typ sb t in
          if TVar v = t' then sx else v, (t', lc)
        | v1, (TVar v2, lc) as sx when VarSet.mem v2 ret_only_vars ->
          (*[* Format.printf "ret_typ_heur: %s= %s := %a@\n%!"
            (var_str v2) (var_str v1) pr_ty
            (subst_typ sb (TVar v1)); *]*)
          let t' = subst_typ sb (TVar v1) in
          if TVar v2 = t' then sx else v2, (t', lc)
        | sx -> sx)
      cand

let rich_return_type = ref true

exception Distinct
let eq_mod_aliens t1 t2 =
  let rec aux t1 t2 =
    match t1, t2 with
    | TVar v1, TVar v2
      when var_sort v1 <> Type_sort && var_sort v2 <> Type_sort -> ()
    | TVar v1, TVar v2
      when v1 = v2 -> ()
    | TCons (f, args1), TCons (g, args2) when f=g ->
      List.iter2 aux args1 args2
    | Fun (a1, r1), Fun (a2, r2) -> aux a1 a2; aux r1 r2
    | Alien _, Alien _ -> ()
    | _ -> raise Distinct in
  try aux t1 t2; true with Distinct -> false

let implies_cnj mod_aliens ans c_ans =
  VarMap.for_all (fun v (t,_) ->
    try
      if mod_aliens
      then eq_mod_aliens (fst (VarMap.find v ans)) (subst_typ ans t)
      else fst (VarMap.find v ans) = subst_typ ans t
    with Not_found -> false
  ) c_ans

let implies_ans mod_aliens ans (_,c_ans) =
  implies_cnj mod_aliens ans c_ans

exception Timeout

let revert_uni q ~bvs ~dissociate ans prem cand =
  let univar v = not (VarSet.mem v bvs) && q.uni_v v in
  let u_sb = map_some
      (function
        | v2, (t, _) as sv
          when univar v2 && not (VarSet.exists univar (fvs_typ t)) ->
          Some sv
        | v1, (TVar v2, loc) when univar v2 && not (univar v1) ->
          Some (v2, (TVar v1, loc))
        | _ -> None) cand in
  let u_sb = varmap_of_assoc u_sb in
  let cand = List.map
      (fun (v, (t, lc)) ->
         let v, t =
           if univar v then
             match t with
             | TVar v2 -> v2, TVar v
             | _ -> v, t
           else v, t in
         let vs = fvs_typ t in
         let t' =
           if not (VarSet.exists univar vs) then t
           else subst_typ u_sb t in
         (*[* if VarSet.exists univar vs then
           Format.printf "revert_uni: v=%s %s t=%a t'=%a@\n%!"
             (var_str v) (var_scope_str (q.cmp_v v (VarSet.choose vs)))
             pr_ty t pr_ty t'; *]*)
         if TVar v = t' then (v, (t, lc))
         else (v, (t', lc)))
      cand in
  let c_sb =
    if not !revert_cst then []
    else map_some
        (function
          | v, (t, lc)
            when not (univar v) && VarSet.is_empty (fvs_typ t) ->
            Some (t, (v, lc))
          | _ -> None)
        prem in
  let c_sb =
    if not !revert_cst then []
    else concat_map
        (fun (c, avs) ->
           (* Maximum should be the leftmost here. *)
           let leq (v1,_) (v2,_) = not (q.cmp_v v1 v2 = Left_of) in
           let ov, olc = maximum ~leq avs in
           let o = TVar ov in
           map_some
             (fun (cv, lc) -> if cv=ov then None else Some (TVar cv, (o, lc)))
             avs
           @ [c, (o, olc)])
        (collect c_sb) in
  let tu_sb =
    if not !revert_at_uni then []
    else map_some
        (function
          | v, (TVar _, _) -> None
          | v, (t, lc)
            when VarSet.exists univar (fvs_typ t) ->
            Some (t, (v, lc))
          | _ -> None)
        prem in
  let tu_sb =
    if not !revert_at_uni then []
    else List.map
        (fun (tu, vs) ->
           (* Maximum should be the leftmost here. *)
           let leq (v1,_) (v2,_) = not (q.cmp_v v1 v2 = Left_of) in
           let ov, olc = maximum ~leq vs in
           let o = TVar ov in
           tu, (o, olc))
        (collect tu_sb) in
  (*[* Format.printf "revert_uni:@ prem=%a@ cand=%a@\n%!"
    pr_subst (varmap_of_assoc prem) pr_subst (varmap_of_assoc cand); *]*)
  let cand =
    if !rich_return_type
    then rich_return_type_heur bvs ans cand
    else cand in
  let rev_sb = List.filter
      (fun (lhs, (rhs, _)) -> not (VarSet.exists univar (fvs_typ rhs)))
      (tu_sb @ c_sb) in
  (*[* Format.printf "revert_uni: revert sb=@ %a@\nres=%a@\n%!"
    (pr_sep_list "; "
       (fun ppf (lhs,(rhs,_)) ->
          Format.fprintf ppf "%a:=%a" pr_ty lhs pr_ty rhs)) rev_sb
    pr_subst (varmap_of_assoc cand); *]*)
  rev_sb, cand

let cand_var_eqs q bvs cnj_typ =
  let cands = List.filter
      (function _, (TVar _, _) when !guess_eqs_nonvar -> false
              | v, _ ->  VarSet.mem v bvs)
      (varmap_to_assoc cnj_typ) in
  concat_map
    (fun ((v1,(t1,lc1)), (v2,(t2,lc2))) ->
       try
         let loc = loc_union lc1 lc2 in
         (* We also rely on the substitution to build the answer --
            without it, it would still need the equations v1=t1 and v2=t2. *)
         let sb = unify ~use_quants:false q [Eqty (t1, t2, loc)] in
         (v1, (TVar v2, loc))::varmap_to_assoc sb.cnj_typ
       with Contradiction _ -> [])
    (triangle cands)

let connected_vs target sb =
  List.fold_left
    (fun acc (v, (s, _)) ->
       if VarSet.mem target (fvs_typ s) then VarSet.add v acc else acc)
    (VarSet.singleton target) sb

let connecteds_vs tvs sb =
  VarMap.fold
    (fun v (s, _) acc ->
       if VarSet.exists (fun v -> VarSet.mem v tvs) (fvs_typ s)
       then VarSet.add v acc else acc)
    sb tvs

(* FIXME: do we need to check the state of numerical constraints? *)
let validate q validation added_vs x t lc =
  List.map
    (fun (br_vs, (state_typ, state_num) as br) ->
       if not (VarSet.is_empty (VarSet.inter added_vs br_vs))
       then
         try
           let t', _ = VarMap.find x state_typ in
           let upd =
             unify ~use_quants:false ~sb:state_typ q [Eqty (t, t', lc)] in
           let state_num =
             NumS.satisfiable_exn ~state:state_num upd.cnj_num in
           VarSet.union added_vs br_vs, (upd.cnj_typ, state_num)
         with Not_found ->
           VarSet.union added_vs br_vs,
           (VarMap.add x (t, lc) state_typ, state_num)
       else br)
    validation

let assoc_to_formula sb =
  List.fold_left
    (fun acc (v, (t,loc)) -> Eqty (TVar v, t, loc)::acc) [] sb
let renaming_sb = VarMap.map (fun w -> TVar w, dummy_loc)

(* [obvs] stands for original [bvs], excluding candidates. *)
(* FIXME: ensure that only upward parameters are escaping. *)
let abd_simple q ?without_quant ~obvs ~bvs ~dissociate
    ~validation ~neg_validate ~discard skip (vs, ans0) (prem, concl) =
  let counter = ref 0 in
  let skip = ref skip in
  let skipped = ref [] in
  let allvs = ref VarSet.empty in
  try
    let more_prem =
      subst_solved ~use_quants:false q ans0 ~cnj:prem.cnj_typ in
    let prem = update_sep ~typ_updated:true ~more:more_prem prem in
    (*[* Format.printf
      "abd_simple:@ prem.num=%a@\ndiscard=%a@\n%!"
      NumDefs.pr_formula prem.cnj_num
      (pr_line_list "| " pr_subst) (List.map snd discard);
    *]*)
    let {cnj_typ=concl; _} =
      subst_solved ~use_quants:false q ans0 ~cnj:concl in
    (*[* Format.printf
      "abd_simple: skip=%d,@ bvs=@ %a;@ vs=@ %s;@ ans0=@ %a@ \
       --@\n@[<2>%a@ ⟹@ %a@]@\n%!"
      !skip pr_vars bvs (String.concat "," (List.map var_str vs))
      pr_subst ans0 pr_subst prem.cnj_typ pr_subst concl; *]*)
    let prem_and ans =
      (* TODO: optimize, don't redo work *)
      let res =
        unify ~use_quants:false q ~sb:prem.cnj_typ ans in
      {cnj_typ = res.cnj_typ; cnj_num = prem.cnj_num @ res.cnj_num;
       cnj_ord = prem.cnj_ord @ res.cnj_ord;
       cnj_so = prem.cnj_so @ res.cnj_so} in
    let implies_concl vs ans cand =
      let more_prem = prem_and
          (assoc_to_formula cand @ to_formula ans) in
      (* Add [impl_X] for new sort [X] below. *)
      let {cnj_typ=_; cnj_num=_; cnj_so=_} as res =
        residuum q more_prem.cnj_typ concl in
      let cnj = update_sep ~typ_updated:true ~more:res more_prem in
      let impl_ty = VarMap.is_empty res.cnj_typ in
      let impl_num = is_right (NumS.satisfiable cnj.cnj_num) in
      (*[* Format.printf "abd_simple: implies? %b impl_num=%b@ \
    #res_ty=%d@\nans=@ %a@\nmore_prem=@ %a@\nconcl=@ %a@\nres_ty=@ %a@\n%!"
        (impl_ty && impl_num) impl_num
        (VarMap.cardinal res.cnj_typ) pr_subst ans
        pr_subst more_prem.cnj_typ pr_subst concl
        pr_subst res.cnj_typ; *]*)
      impl_ty && impl_num in
    let unpack_cand reorder bvs init_cand =
      let rec aux acc cand =
        match cand with
        | (_,(TVar y,_) as sx)::cand when VarSet.mem y bvs ->
          true, sx, cand @ List.rev acc
        | (x,(t,_) as sx)::cand when VarSet.mem x bvs ->
          true, sx, cand @ List.rev acc
        | sx::cand when reorder -> aux (sx::acc) cand
        | _ ->
          false, List.hd init_cand, List.tl init_cand in
      aux [] init_cand in
    let rec abstract deep c_sb repls bvs vs ans validation = function
      | [], [] ->
        (*[* let ddepth = incr Joint.debug_dep; !Joint.debug_dep in *]*)
        (*[* Format.printf
          "abd_simple-abstract: [%d] @ repls=%a@ @ bvs=%a@ vs=%s@ ans=%a@\n%!"
          ddepth pr_subst
          (varmap_of_assoc (List.map (fun (x,y) -> y,(x,dummy_loc)) repls))
          pr_vars bvs
          (String.concat ","(List.map var_str vs))
          pr_subst ans; *]*)
        if implies_concl vs ans [] then
          let _, clean_ans = cleanup q vs ans in
          (*[* Format.printf "abd_simple-abstract:@\nclean_ans=%a@\n%!"
            pr_subst clean_ans          (* skipped=%a@\n *)
          (* (pr_line_list "|" pr_subst) !skipped *); *]*)
          allvs := add_vars vs !allvs;
          let repeated =
            try
              let (*[*old_ans*]*) _ =
                  List.find
                    (fun xs ->
                       try
                         VarMap.for_all
                           (fun x t ->
                              let t' = VarMap.find x clean_ans in
                              t' = t) xs
                       with Not_found -> false)
                    !skipped in
              (*[* Format.printf
                "skipping: [%d] ans=@ %a --@ old_ans=@ %a...@\n%!"
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
          else if List.exists (implies_ans dissociate clean_ans) discard
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
            raise (Result (bvs, vs, ans, validation)))
      | guess_cand, full_cand ->
        let is_guess_cand = guess_cand <> [] in
        let is_p, (x, (t, lc) as sx), (guess_cand, full_cand as rem_cand) =
          if guess_cand = [] then
            let is_p, sx, full_cand = unpack_cand true bvs full_cand in
            is_p, sx, (guess_cand, full_cand)
          else
            let is_p, sx, guess_cand = unpack_cand false bvs guess_cand in
            is_p, sx, (guess_cand, full_cand) in
        incr counter; if !counter > !timeout_count then raise Timeout;
        (*[* let ddepth = incr Joint.debug_dep; !Joint.debug_dep in *]*)
        (*[* Format.printf
          "abd_simple-abstract: [%d] @ repls=%a@ bvs=%a@ vs=%s@ \
           ans=%a@\nx=%s@ t=%a@ #guess_cand=%d@ #full_cand=%d@\n\
           guess_cand=%a@\nfull_cand=%a@\n%!"
          ddepth pr_subst
          (varmap_of_assoc (List.map (fun (x,y) -> y,(x,dummy_loc)) repls))
          pr_vars bvs
          (String.concat ","(List.map var_str vs))
          pr_subst ans (var_str x) pr_ty t
          (List.length guess_cand) (List.length full_cand)
          pr_subst (varmap_of_assoc guess_cand)
          pr_subst (varmap_of_assoc full_cand); *]*)
        let choice1 () =
          (* Choice 1: drop premise/conclusion atom from answer *)
          if implies_concl vs ans full_cand
          then (
            (*[* Format.printf
              "abd_simple: [%d] choice 1@ drop %s = %a@\n%!"
              ddepth (var_str x) pr_ty t; *]*)
            (*[* try *]*)
              abstract deep c_sb repls bvs vs ans validation rem_cand
              (*[*; Format.printf "abd_simple: [%d] choice 1 failed@\n%!"
                ddepth; *]*)               
              (*[* with Result (bvs, vs, ans, validation) as e ->
              Format.printf "abd_simple: [%d] preserve choice 1@ %s =@ %a@ -- returned@ ans=%a@\n%!"
                ddepth (var_str x) pr_ty t pr_subst ans;
              raise e *]*) );
          (*[* Format.printf
            "abd_simple: [%d]@ recover after choice 1@ %s =@ %a@\n\
             guess_cand=%a@\nfull_cand=%a@\n%!"
            ddepth (var_str x) pr_ty t
            pr_subst (varmap_of_assoc guess_cand)
            pr_subst (varmap_of_assoc full_cand); *]*)
          () in
        let choice6 () =
          (* Choice 6: preserve atom in a "generalized" form *)
          let (c6x, (c6t, c6lc) as c6sx) =
            if !revert_cst then x, (c_subst_typ c_sb t, lc)
            else sx in
          if not !more_general && implies_concl vs ans (c6sx::full_cand)
          then (
            (*[* Format.printf
              "abd_simple: [%d]@ choice 6@ keep %s = %a@ (%s = %a)@\n%!"
              ddepth (var_str c6x) pr_ty c6t
              (var_str x) pr_ty t; *]*)
            try
              let c6vs = VarSet.add c6x (fvs_typ c6t) in
              let bvs' =
                if is_p then VarSet.union
                    (VarSet.filter (not % q.uni_v) c6vs) bvs
                else bvs in
              (* Use the answer before updating. *)
              let all_new_vs =
                if !verif_all_brs then VarSet.empty
                else connecteds_vs c6vs ans in
              let {cnj_typ=ans'; _} =
                unify ~bvs:bvs' ~sb:ans
                  q [Eqty (TVar c6x, c6t, c6lc)] in
              (*[* Format.printf
                "abd_simple: [%d] validate 6 ans'=@ %a@\n%!"
                ddepth pr_subst ans'; *]*)
              let validation =
                validate q validation all_new_vs c6x c6t c6lc in
              (*[* Format.printf "abd_simple: [%d] choice 6 OK@\n%!" ddepth; *]*)
              abstract deep c_sb repls bvs' vs ans' validation rem_cand
            with
            (*[* | Result (bvs, vs, ans, validation) as e ->
              (* FIXME: remove try-with case after debug over *)
              Format.printf "abd_simple: [%d]@ preserve choice 6@ %s =@ %a@ -- returned@ ans=%a@\n%!"
                ddepth (var_str c6x)
                pr_ty c6t pr_subst ans;
              raise e *]*)
                  | Contradiction _ (*[* as e *]*) ->
                    (*[* Format.printf
                      "abd_simple: [%d]@ invalid choice 6 reason:@\n%a@\n%!"
                      ddepth pr_exception e; *]*)
                    ());
          (*[* Format.printf
            "abd_simple: [%d]@ recover after choice 6@ %s =@ %a@\n%!"
            ddepth (var_str c6x) pr_ty c6t; *]*)
          () in
        if !richer_answers then (choice6 (); choice1 ())
        else (
          let c6sx =
            if !revert_cst then x, (c_subst_typ c_sb t, lc)
            else sx in
          if !prefer_guess && is_guess_cand ||
             (* TODO: only check if there are negative branches *)
             neg_validate (vs, add_to_varmap full_cand ans) >
             neg_validate (vs, add_to_varmap (c6sx::full_cand) ans)
          then (
            (*[* Format.printf
              "abd_simple: [%d] guess/negation=%b choice inversion@\n%!"
              ddepth (!prefer_guess && is_guess_cand); *]*)
            choice6 (); choice1 ())
          else (choice1 (); choice6 ()));
        step deep c_sb x lc {typ_sub=t; typ_ctx=[]} repls
          is_p bvs vs ans validation rem_cand
    and step deep c_sb x lc loc repls is_p bvs vs ans validation
        (_, full_cand as rem_cand) =
      incr counter; if !counter > !timeout_count then raise Timeout;
      (*[* let ddepth = incr Joint.debug_dep; !Joint.debug_dep in *]*)
      (*[* Format.printf
        "abd_simple-step: [%d] @ loc=%a@ repls=%a@ vs=%s@ ans=%a@ x=%s@ full_cand=%a@\n%!"
        ddepth pr_ty (typ_out loc) pr_subst
        (varmap_of_assoc (List.map (fun (x,y) -> y,(x,dummy_loc)) repls))
        (String.concat ","(List.map var_str vs))
        pr_subst ans (var_str x) pr_subst
        (varmap_of_assoc full_cand); *]*)
      (* Choice 2: remove subterm from answer *)
      let choice2 () =
        let a = fresh_var (typ_sort loc.typ_sub) in
        let repls' = (loc.typ_sub, a)::repls in
        (*[* Format.printf "abd_simple: [%d]@ choice 2@ repls'=@ %a@\n%!"
          ddepth pr_subst
          (varmap_of_assoc (List.map (fun (x,y) -> y,(x,dummy_loc))
                              repls')); *]*)
        let vs' = a::vs in
        let loc' = {loc with typ_sub = TVar a} in
        let t' = typ_out loc' in
        (*[* Format.printf "abd_simple: [%d]@ choice 2@ remove subterm %s =@ %a@\n%!"
          ddepth (var_str x) pr_ty t'; *]*)
        (* FIXME: add [a] to [cparams]? *)
        match typ_next loc' with (* x bound when leaving step *)
        | None ->
          (try
             let c2vs = VarSet.add x (fvs_typ t') in
             let bvs' =
               if is_p then VarSet.union
                   (VarSet.filter (not % q.uni_v) c2vs) bvs
               else bvs in
             let all_new_vs =
               if !verif_all_brs then VarSet.empty
               else connecteds_vs c2vs ans in
             let {cnj_typ=ans'; _} =
               unify ~bvs:bvs' ~sb:ans
                 q [Eqty (TVar x, t', lc)] in
             (*[* Format.printf
               "abd_simple: [%d] validate 2 ans=@ %a@\n%!" ddepth
               pr_subst ans; *]*)
             let validation =
               validate q validation all_new_vs x t' lc in
             (*[* Format.printf "abd_simple: [%d] choice 2 OK@\n%!"
               ddepth; *]*)
             abstract deep c_sb repls' bvs' vs' ans' validation rem_cand
           with Contradiction _ ->
             ())
        | Some loc' ->
          step deep c_sb x lc loc' repls' is_p bvs vs' ans
            validation rem_cand in
      (* Choice 3: try subterms of the subterm *)
      let choice3 () =
        (*[* Format.printf
          "abd_simple: [%d] approaching choice 3@ for@ %a@ @@ %s =@ %a@\n%!"
          ddepth pr_ty loc.typ_sub (var_str x) pr_ty
          (typ_out loc); *]*)
        if typ_sort loc.typ_sub = Type_sort
        then match typ_up loc with
          | None -> ()        
          | Some loc ->
            (*[* Format.printf
              "abd_simple: [%d]@ choice 3@ try subterms@\n%!" ddepth; *]*)
            step deep c_sb x lc loc repls is_p bvs vs ans
              validation rem_cand in
      (* Choice 4: preserve current premise/conclusion subterm for answer *)
      let choice4 () =
        match typ_next loc with
        | None ->
          (try
             let t = typ_out loc in
             (*[* Format.printf
               "abd_simple: [%d] trying choice 4 a=%a@ sb=@ %a@\n%!"
               ddepth pr_formula [Eqty (TVar x, t, lc)] pr_subst ans; *]*)
             let c4vs = VarSet.add x (fvs_typ t) in
             let bvs' =
               if is_p then VarSet.union
                   (VarSet.filter (not % q.uni_v) c4vs) bvs
               else bvs in 
             let all_new_vs =
               if !verif_all_brs then VarSet.empty
               else connecteds_vs c4vs ans in
             let {cnj_typ=ans; _} =
               unify ~bvs:bvs' ~sb:ans
                 q [Eqty (TVar x, t, lc)] in
             (*[* Format.printf
               "abd_simple: [%d] validate 4 ans=@ %a@\n%!"
               ddepth pr_subst ans; *]*)
             let validation =
               validate q validation all_new_vs x t lc in
             (*[* Format.printf "abd_simple: [%d] choice 4 OK@\n%!" ddepth; *]*)
             abstract deep c_sb repls bvs' vs ans
               validation rem_cand
           with Contradiction
                      (*[* (_, msg, Some (ty1, ty2), *]*) _ (*[* ) *]*) ->
             (*[*Format.printf
               "abd_simple: [%d] @ c.4 failed:@ %s@ %a@ %a@\n%!" ddepth
               msg pr_ty ty1 pr_ty ty2;
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
             Format.printf "abd_simple: [%d] choice 4 failed@\n%!"
               ddepth;
             *]*)
             incr counter;
             if !counter > !timeout_count then raise Timeout;
             ())
        | Some loc ->
          (*[* Format.printf "abd_simple: [%d] neighbor loc@\n%!" ddepth; *]*)
          step deep c_sb x lc loc repls is_p bvs vs ans
            validation rem_cand in
      (* Choice 5: match subterm with an earlier occurrence *)
      let choice5 () =
        let repl = assoc_all loc.typ_sub repls in
        (*[* Format.printf "abd_simple: [%d]@ choice 5 x=%s@ repls=@ %a@\n%!"
          ddepth (var_str x)
          pr_subst
          (varmap_of_assoc (List.map (fun (x,y) -> y,(x,dummy_loc))
                              repls)); *]*)
        (*[* Format.printf "abd_simple: [%d]@ choice 5@ sub=@ %a@ repl=@ %s@\n%!"
          ddepth pr_ty loc.typ_sub
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
                    ddepth (var_str x) pr_ty t' pr_subst ans; *]*)
                  let c5vs = VarSet.add x (fvs_typ t') in
                  let bvs' =
                    if is_p then VarSet.union
                        (VarSet.filter (not % q.uni_v) c5vs) bvs
                    else bvs in
                  let all_new_vs =
                    if !verif_all_brs then VarSet.empty
                    else connecteds_vs c5vs ans in
                  let {cnj_typ=ans'; _} =
                    (*[* try *]*)
                      unify ~bvs:bvs' ~sb:ans
                        q [Eqty (TVar x, t', lc)]
                  (*[* with Terms.Contradiction _ as e ->
                    Format.printf
                      "abd_simple: [%d] @ c.5 above failed:@\n%a@\n%!" ddepth
                      pr_exception e;
                    raise e *]*) in
                  (*[* Format.printf
                    "abd_simple: [%d] validate 5 ans'=@ %a@\n%!"
                    ddepth pr_subst ans'; *]*)
                  let validation =
                  (*[*try*]*)
                    validate q validation all_new_vs x t' lc
                  (*[*with Terms.Contradiction _ as e ->
                       Format.printf
                       "abd_simple: [%d] @ c.5 validate failed:@\n%a@\n%!"
                           ddepth pr_exception e;
                         raise e *]*) in
                  (*[* Format.printf "abd_simple: choice 5 OK@\n%!"; *]*)
                  (*[* Format.printf
                    "abd_simple: [%d]@ choice 5@ match earlier %s =@ %a@\n%!"
                    ddepth (var_str x) pr_ty t'; *]*)
                  abstract deep c_sb repls bvs' vs ans'
                    validation rem_cand
                with Contradiction _ ->
                  incr counter;
                  if !counter > !timeout_count then raise Timeout;
                  ())
             | Some loc' ->
               step deep c_sb x lc loc' repls is_p bvs vs ans
                 validation rem_cand)
          repl in
      if not deep then ()
      else if !more_general
      then (choice2 (); choice3 (); choice4 (); choice5 ())
      else (choice4 (); choice2 (); choice3 (); choice5 ())
    in
    if implies_concl vs ans0 [] then Some ((bvs, (vs, ans0)), validation)
    else
      let {cnj_typ; _} as prem_n_concl =
        prem_and ((* ans @ *)to_formula concl) in
      (* FIXME: hmm... *)
      (* let cnj_typ = list_diff cnj_typ discard in *)
      let guess_cand = cand_var_eqs q bvs prem_n_concl.cnj_typ in
      let c_sb, init_cand =
        revert_uni q ~bvs ~dissociate ans0
          (varmap_to_assoc prem.cnj_typ)
          (varmap_to_assoc prem_n_concl.cnj_typ) in
      (* From longest to shortest. *)
      (* FIXME: revert to shortest-to-longest, have better idea how
         to deal with badly dropped short atoms. *)
      let init_cand =
        unique_sorted
          ~cmp:(fun (v1,(t1,_)) (v2,(t2,_)) ->
              let c = typ_size t2 - typ_size t1 in
              if c=0 then Pervasives.compare (v1,t1) (v2,t2) else c)
          init_cand in
      (*[* Format.printf
        "abd_simple: before xcrosses filtering@\ninit=@ %a@\nguess=@ %a@\n%!"
        pr_subst (varmap_of_assoc init_cand)
        pr_subst (varmap_of_assoc guess_cand); *]*)
      let filter_cand = List.filter
          (fun (v,(t,_)) ->
             not (VarSet.mem v bvs) ||
             not (crosses_xparams ~cmp_v:q.cmp_v ~bvs:obvs
                    (VarSet.add v (fvs_typ t)))) in
      let init_cand = filter_cand init_cand
      and guess_cand = filter_cand guess_cand in
      (*[* Format.printf
        "abd_simple: xcrosses filtered@\ninit=@ %a@\nguess=@ %a@\n%!"
        pr_subst (varmap_of_assoc init_cand)
        pr_subst (varmap_of_assoc guess_cand); *]*)
      try
        if not !more_general
        then abstract false c_sb [] bvs vs ans0
            validation (guess_cand, init_cand);
        (*[* Format.printf
          "abd_simple: starting full depth (choices 1-6)@\n%!"; *]*)
        abstract true c_sb [] bvs vs ans0
          validation (guess_cand, init_cand); None
      with Result (bvs, vs, ans, validation) ->
        (*[* Format.printf "abd_simple: Final validation@\n%!"; *]*)
        let {cnj_typ=ans; cnj_num; cnj_so=_} =
          unify ~bvs q (to_formula ans) in
        assert (cnj_num = []);
        (*[* Format.printf
          "abd_simple: Final validation passed@\nans=%a@\n%!"
          pr_subst ans; *]*)
        Some ((bvs, cleanup q vs ans), validation)
  with
  | Contradiction _ (*[* as e *]*) ->
    (*[* Format.printf
      "abd_simple: conflicts with premises exc=@ %a@\nskip=%d,@ vs=@ %s;@ ans0=@ %a@ --@\n@[<2>%a@ ⟹@ %a@]@\n%!"
      pr_exception e
      !skip (String.concat "," (List.map var_str vs))
      pr_subst ans0 pr_subst prem.cnj_typ pr_subst concl; *]*)
    None          (* subst_solved or implies_concl *)
  | Timeout ->
    (*[* Format.printf
      "abd_simple: TIMEOUT conflicts with premises skip=%d,@ \
       vs=@ %s;@ ans0=@ %a@ --@\n@[<2>%a@ ⟹@ %a@]@\n%!"
      !skip (String.concat "," (List.map var_str vs))
      pr_subst ans0 pr_subst prem.cnj_typ pr_subst concl; *]*)
    abd_timeout_flag := true;
    None

(* let max_skip = ref 20 *)

module TermAbd = struct
  type accu = VarSet.t * (var_name list * subst)
  type args = VarSet.t * quant_ops * bool
  type answer = var_name list * subst
  type discarded = answer
  (* premise including alien premise, conclusion *)
  type branch = sep_formula * subst
  type br_state = subst * NumS.state
  type validation = t_validation

  let abd_fail_timeout = fail_timeout_count
  let abd_fail_flag = abd_fail_flag

  let abd_simple (obvs, q, dissociate) ~discard ~validation
      ~validate ~neg_validate
      (bvs, acc) br =
    abd_simple q ~obvs ~bvs ~dissociate ~validation ~neg_validate
        ~discard 0 acc br

  let extract_ans (bvs, vs_ans) = vs_ans
  let discard_ans = extract_ans

  let concl_of_br (prem, concl) = to_formula concl

  let is_taut (vs, ans) = VarMap.is_empty ans

  let pr_branch pp (prem, concl) =
    Format.fprintf pp "@[<2>%a@ ⟹@ %a@]"
      pr_subst prem.cnj_typ pr_subst concl

  let pr_ans pp (vs, ans) = pr_subst pp ans
end

module JCA = Joint.JointAbduction (TermAbd)

let abd_typ q ~bvs ?(dissociate=false) ~validation ~neg_validate ~discard
    (brs : TermAbd.branch list) =
  (*[* Format.printf "abd_typ:@ bvs=@ %a@\n%!"
    pr_vars bvs; *]*)
  abd_timeout_flag := false;
  let alien_vs = ref [] in
  let alien_eqs = ref VarMap.empty in
  let rec purge = function
    | t when typ_sort t <> Type_sort ->
      let n = fresh_var (typ_sort t) in
      (* Alien vars become abduction answer vars. *)
      alien_eqs :=
        VarMap.add n (subst_typ !alien_eqs t, dummy_loc) !alien_eqs;
      alien_vs := n :: !alien_vs;
      TVar n
    | TCons (n, tys) -> TCons (n, List.map purge tys)
    | Fun (t1, t2) -> Fun (purge t1, purge t2)
    | TVar _ as t -> t
    | Alien _ -> assert false in
  let brs =
    if dissociate
    then List.map
        (fun (prem,concl) ->
           {prem with cnj_typ = map_in_subst purge prem.cnj_typ},
           map_in_subst purge concl)
        brs
    else brs in
  (*[* Format.printf "abd_typ: alien_eqs=%a@\n%!"
    pr_subst !alien_eqs; *]*)
  let validate _ _ = () in
  let cand_bvs, (vs, ans) =
    JCA.abd (bvs, q, dissociate) ~discard validation ~validate ~neg_validate
      (bvs, ([], VarMap.empty)) brs in
  (*[* Format.printf "abd_typ: result vs=%s@\nans=%a@\n%!"
    (String.concat ","(List.map var_str vs))
    pr_subst ans; *]*)
  let ans =
    if dissociate
    then VarMap.map (fun (t,lc) -> purge t, lc) ans
    else ans in
  let vs = !alien_vs @ vs in
  (*[* Format.printf "abd_typ: dissociated %b vs=%s@\nalien=@ %a@\nans=%a@\n%!"
    dissociate (String.concat ","(List.map var_str vs))
    pr_subst !alien_eqs
    pr_subst ans; *]*)
  let more_in_brs = List.map
    (fun (prem, concl) ->
      try
        let more_prem =
          combine_sbs ~use_quants:false q [prem.cnj_typ; ans] in
        let more_res =
          residuum q more_prem.cnj_typ concl in
        (*[* Format.printf
          "abd_typ-num:@ prem=%a@ concl=%a@ res_ty=%a@ \
          res_num=%a@\nprem_num=%a@\n%!"
          pr_subst prem.cnj_typ pr_subst concl
          pr_subst more_res.cnj_typ NumDefs.pr_formula more_res.cnj_num
          NumDefs.pr_formula more_prem.cnj_num; *]*)
        assert (VarMap.is_empty more_res.cnj_typ);
        (*let more_concl =
          combine_sbs ~use_quants:false q
            [prem.cnj_typ; concl; ans] in*)
        more_prem, more_res(* more_concl *)
      with Contradiction _ -> assert false)
    brs in
  cand_bvs, !alien_eqs, vs, ans, more_in_brs

let abd_mockup_num q ~bvs brs =
  (* Do not change the order and no. of branches afterwards. *)
  let brs_typ, brs_num = List.split
      (map_some (fun (prem, concl) ->
           let prems_opt =
             try Some (unify ~use_quants:false q prem)
             with Contradiction _ -> None in
           match prems_opt with
           | Some prem ->
             if List.exists
                 (function CFalse _ -> true | _ -> false) prem.cnj_so
             then None
             else                          (* can raise Contradiction *)
               let {cnj_typ=concl_typ; cnj_num=concl_num; cnj_so=concl_so} =
                 solve ~use_quants:false q concl in
               List.iter (function
                   | CFalse loc ->
                     raise (Contradiction (Type_sort,
                                           "assert false is possible", None, loc))
                   | _ -> ()) concl_so;
               if not (is_right (NumS.satisfiable concl_num)) then None
               else Some ((prem, concl_typ),
                          (prem.cnj_num, concl_num))
           | None -> None)
          brs) in
  let verif_brs = List.map2
      (fun (prem, concl_ty) (_, concl_num) ->
         VarSet.union (fvs_sb prem.cnj_typ)
           (VarSet.union (NumDefs.fvs_formula prem.cnj_num)
              (VarSet.union (fvs_sb concl_ty)
                 (NumDefs.fvs_formula concl_num))),
         prem, concl_ty, concl_num)
      brs_typ brs_num in
  let validation =
    map_some
      (fun (br_vs, prem, concl_ty, concl_num) ->
         (* Do not use quantifiers, because premise is in the conjunction. *)
         (* TODO: after cleanup optimized in abd_simple, pass clean_ans
            and remove cleanup here *)
         try
           let {cnj_typ=sb_ty; cnj_num=ans_num; cnj_so=_} =
             combine_sbs q [prem.cnj_typ; concl_ty] in
           let cnj_num = ans_num @ prem.cnj_num @ concl_num in
           Some (br_vs, (sb_ty, NumS.satisfiable_exn cnj_num))
         with Contradiction _ -> None)
      verif_brs in
  let neg_validate _ = 0 in
  try
    let cand_bvs, alien_eqs, tvs, ans_typ, more_in_brs =
      abd_typ q ~bvs ~validation ~neg_validate ~discard:[] brs_typ in
    Some (List.map2
            (fun (prem_num,concl_num) (more_p, more_c) ->
               prem_num @ more_p.cnj_num,
               concl_num @ more_c.cnj_num)
            brs_num more_in_brs)
  with Suspect _ -> None

type discarded =
  (TermAbd.answer list, NumDefs.formula list,
   OrderDefs.formula list, unit) sep_sorts

let abd q ~bvs ~xbvs ?orig_ren ?b_of_v ~upward_of ~nonparam_vars
    ?(iter_no=2) ~discard brs neg_brs =
  let dissociate = iter_no <= 0 in
  (* Do not change the order and no. of branches afterwards. *)
  (*[* Format.printf "abd: iter_no=%d prepare branches@\n%!" iter_no; *]*)
  let brs_typ, brs_num = List.split
      (map_some (fun (nonrec, chi_pos, prem, concl) ->
           let prems_opt =
             try Some (unify ~use_quants:false q prem)
             with Contradiction _ as e ->
               if !nodeadcode then (deadcode_flag := true; raise e)
               else None in
           match prems_opt with
           | Some prem ->
             if List.exists
                 (function CFalse _ -> true | _ -> false) prem.cnj_so
             then None
             else                          (* can raise Contradiction *)
               let concl = solve ~use_quants:false q concl in
               (*[* if concl.cnj_so <> [] then Format.printf
                   "abd-br: concl-so=%a@\n%!" pr_formula concl.cnj_so; *]*)
               assert (concl.cnj_so = []);
               if not (is_right (NumS.satisfiable prem.cnj_num)) then None
               else (
                 (*[* Format.printf "br-num: prem=%a; concl=%a@\n%!"
                   NumDefs.pr_formula prem.cnj_num
                   NumDefs.pr_formula concl.cnj_num; *]*)
                 Some ((prem, concl.cnj_typ),
                       (nonrec, chi_pos, prem.cnj_num, concl.cnj_num)))
           | None -> None)
          brs) in
  (* Negative constraint prior to abduction. *)
  let neg_cns_pre =
    if not !neg_before_abd || iter_no < !term_neg_since then []
    else map_some
        (fun (cnj, loc) ->
           try
             (*[* Format.printf
               "abd-neg-pre: trying neg=%a...@\n%!" pr_formula cnj;
              *]*)
             let cnj = unify ~use_quants:false q cnj in
             (*[* Format.printf "abd-neg-pre: passed@\n%!"; *]*)
             Some (cnj, loc)
           with Contradiction _ -> None)
        neg_brs in
  let verif_brs = List.map2
      (fun (prem, concl_ty) (_, _, prem_num, concl_num) ->
         VarSet.union (fvs_sb concl_ty) (NumDefs.fvs_formula concl_num),
         prem, concl_ty, prem_num @ concl_num)
      brs_typ brs_num in
  let validation =
    map_some
      (fun (br_vs, prem, concl_ty, concl_num) ->
         try
           (* Do not use quantifiers, because premise is in the conjunction. *)
           (* TODO: after cleanup optimized in abd_simple, pass clean_ans
              and remove cleanup here *)
           let {cnj_typ=sb_ty; cnj_num=ans_num; cnj_so=_} =
             combine_sbs q [prem.cnj_typ; concl_ty] in
           let cnj_num = ans_num @ prem.cnj_num @ concl_num in
           (* FIXME: need num state? *)
           Some (br_vs, (sb_ty, NumS.satisfiable_exn cnj_num))
         with Contradiction _ -> None)
      verif_brs in
  (* TODO: could be optimized too. *)
  let neg_validate (vs, ans) =
    (* Returns the number of negative constraints not contradicted by
       the answer, i.e. the closer to 0 the better. *)
    (*[* Format.printf "Abd.neg_validate: for ans=@ %a@\n%!"
      pr_subst ans; *]*)
    List.fold_left
      (fun acc (cnj, _) ->
         acc +
           try
             (*[* Format.printf
               "Abd.neg_validate: checking cnj_typ=@ %a@\n%!"
               pr_subst cnj.cnj_typ; *]*)
             ignore
               (combine_sbs ~use_quants:false q [cnj.cnj_typ; ans]);
             (*[* Format.printf "not contradicted@\n%!"; *]*)
             1
           with Contradiction _ ->
             (*[* Format.printf "success: contradicted@\n%!"; *]*)
             0)
      0 neg_cns_pre in
  let neg_term =
    (* Select [bvs] variables equated with constructors participating in
       phantom type families. Filter candidates through validation. *)
    let dsjs =
      (* TODO: For now, we conjoin multiple disjuncts rather than
         choosing one; reconsider since it might not be consistent. *)
      concat_map
        (fun (cnj, loc) ->
           map_some
             (function
               | v, (TCons (c_name, args), loc)
                 when VarSet.mem v bvs &&
                      Hashtbl.mem Infer.phantom_enumeration c_name ->
                 let enum =
                   Hashtbl.find Infer.phantom_enumeration c_name in
                 let enum =
                   List.filter
                     (fun name ->
                        try
                          ignore (validate q validation
                                    (VarSet.singleton v)
                                    v (TCons (name, [])) loc); true
                        with Contradiction _ -> false)
                     enum in
                 if enum = [] then None
                 else Some (v, (enum, loc))
               | _ -> None)
             (varmap_to_assoc cnj.cnj_typ))
        neg_cns_pre in
    (* Coordinate with other negative constraints, and select the
       unambiguous ones. *)
    let dsjs = List.map
        (function
          | v, (names, loc)::rem_names ->
            v, List.fold_left list_inter names (List.map fst rem_names), loc
          | _ -> assert false)
        (collect dsjs) in
    map_some
      (function
        | v, [name], loc -> Some (v, (TCons (name, []), loc))
        | _ -> None)
      dsjs in
  let neg_term = varmap_of_assoc neg_term in
  (*[* if !neg_before_abd && iter_no >= !term_neg_since then
    Format.printf "neg_term=%a@\n" pr_subst neg_term; *]*)
  (* We do not remove nonrecursive branches for types -- it will help
     other sorts do better validation. *)
  let cand_bvs, alien_eqs, tvs, ans_typ, more_in_brs =
    try
      abd_typ q ~bvs ~dissociate ~validation ~neg_validate
        ~discard:discard.at_typ
        ((sep_formulas [], neg_term)::brs_typ)
    with Suspect (cnj, lc) ->
      (*[* Format.printf
        "abd: fallback abd_typ loc=%a@\nsuspect=%a@\n%!"
        pr_loc lc pr_formula cnj;
       *]*)
      raise (NoAnswer (Type_sort, "term abduction failed", None, lc)) in
  (* Drop the pseudo-branch with term negation. *)
  let more_in_brs = List.tl more_in_brs in
  let verif_brs_num = List.map2
      (fun (nonrec, chi_pos, prem, concl) (more_p, more_c) ->
         nonrec, chi_pos, more_p.cnj_num @ prem, more_c.cnj_num @ concl)
      brs_num more_in_brs in
  (* OK, we can change [brs_num] now. *)
  let brs_num = List.filter
      (fun (_, _, _, concl) -> concl<>[]) verif_brs_num in
  (* Filter out negated constraints that already are contradicted. Of
     the result, use only sorts other than [Type_sort] as negated
     constraints. *)
  let neg_cns_post =
    if iter_no < !num_neg_since +
                   (if !OCaml.drop_assert_false then 0 else 1) then []
    else map_some
        (fun (cnj, loc) ->
           try
             (*[* Format.printf
               "abd-neg: trying neg=%a...@\n%!" pr_formula cnj;
              *]*)
             let cnj =
               combine_sbs ~use_quants:false q ~more_phi:cnj [ans_typ] in
             (*[* Format.printf "abd-neg: passed@\n%!"; *]*)
             Some (cnj, loc)
           with Contradiction _ -> None)
        neg_brs in
  let neg_num ans_num =
    if neg_cns_post = [] then []
    else
      (* Branches to verify disjuncts from negative
         constraints. Coalesce facts from subsumed branches. *)
      let verif_cns_num =
        map_some
          (fun (_,_,prem,_) ->
             (*[* Format.printf
               "abd-neg: verif_br prem=@ %a@\n%!" NumDefs.pr_formula
               prem; *]*)
             let allconcl = concat_map
                 (fun (_,_,prem2,concl2) ->
                    if NumDefs.subformula prem2 prem then concl2 else [])
                 verif_brs_num in
             try Some (NumS.satisfiable_exn (ans_num @ prem @ allconcl))
             with Contradiction _ -> None)
          verif_brs_num in
      (* Filter out already solved negative constraints. *)
      let num_neg_cns = map_some
          (fun (c,lc)->
             let cnj = c.cnj_num in
             let elimvs =
               VarSet.diff (NumDefs.fvs_formula cnj) bvs in
             try Some (snd (NumS.simplify q elimvs cnj), lc)
             with Contradiction _ -> None)
          neg_cns_post in
      NumS.negation_elim q ~bvs ~verif_cns:verif_cns_num
        num_neg_cns in
  let neg_num_res =
    if !neg_before_abd then neg_num []
    else [] in
  (*[* Format.printf "abd: solve for numbers@\n%!"; *]*)
  let nvs, ans_num =
    if dissociate || !no_num_abduction then [], []
    else
      try
        (* [tvs] includes alien variables! *)
        NumS.abd q ~bvs ~xbvs ?orig_ren ?b_of_v ~upward_of ~nonparam_vars
          ~discard:discard.at_num ~iter_no
          (* [true] means non-recursive *)
          ((true, [], [], neg_num_res)::brs_num)
      with
      | Contradiction _ as e ->
        (*[* Format.printf "abd: num dead code@\n%!"; *]*)
        raise e
      | Suspect (cnj, lc) ->
        (*[* Format.printf
          "abd: fallback NumS.abd loc=%a@\nsuspect=%a@\n%!"
          pr_loc lc pr_formula cnj;
         *]*)
        raise (NoAnswer (Num_sort, "numerical abduction failed",
                         None, lc)) in
  let ans_typ = to_formula ans_typ in
  let neg_num_res =
    if not !neg_before_abd then neg_num ans_num
    else neg_num_res in
  cand_bvs, alien_eqs,
  (nvs @ tvs, ans_typ @ NumS.formula_of_sort (neg_num_res @ ans_num))
