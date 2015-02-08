(** Solving second-order i.e. formula variables for InvarGenT.

    Released under the GNU General Public Licence (version 2 or
    higher), NO WARRANTY of correctness etc. (C) Lukasz Stafiniak 2013
    @author Lukasz Stafiniak lukstafi (AT) gmail.com
    @since Mar 2013
*)
let early_postcond_abd = ref true(* false *)
let timeout_count = ref 7
let timeout_flag = ref false
let unfinished_postcond_flag = ref false
let use_prior_discards = ref (* false *)true
let use_solution_in_postcond = ref false (* true *)

open Defs
open Terms
open Aux
type chi_subst = (int * (var_name list * formula)) list

type q_with_bvs = {
  op : quant_ops;
  cmp_v : var_name -> var_name -> var_scope;
  uni_v : var_name -> bool;
  positive_b : var_name -> bool;
  (** Whether a binary predicate variable. *)
  is_chiK : int -> bool;
  (** Add local variables of [chi(b)] instance, paired with keys
      -- corresponding variables of formal [chi(delta)]. *)
  add_b_vs_of : var_name -> (var_name * var_name) list -> unit;
  b_vs : (var_name, VarSet.t) Hashtbl.t;
  b_qvs : (var_name, var_name list) Hashtbl.t;
  (** Renaming into [b_qvs], redundant but more idiot-proof *)
  b_renaming : (var_name, (var_name * var_name) list) Hashtbl.t;
  add_bchi : var_name -> int -> posi:bool -> chiK:bool -> unit;
  (** The [a0] variable at the introduction point of existential type. *)
  chiK_anchor : (int, var_name) Hashtbl.t;
  get_recbvs : unit -> VarSet.t;
  param_renaming : var_name -> bool;
  find_b : int -> var_name list;
  find_b_of_v : var_name -> var_name;
  find_chi : var_name -> int;
  mutable allbvs : VarSet.t;
  mutable allchi : Ints.t;
  mutable negbs : var_name list;
  recover_escaping : (int, subst) Hashtbl.t;
}
  
let new_q q_ops =
  let posi_b = Hashtbl.create 8 in
  let chiK_i = Hashtbl.create 8 in
  let chiK_anchor = Hashtbl.create 8 in
  let positive_b v = Hashtbl.mem posi_b v in
  let is_chiK i = Hashtbl.mem chiK_i i in
  let b_vs = Hashtbl.create 16 in
  let b_renaming = Hashtbl.create 16 in
  let b_qvs = Hashtbl.create 16 in
  let chi_b = Hashtbl.create 16 in
  let b_chi = Hashtbl.create 16 in
  let v_b = Hashtbl.create 16 in
  let recbvs = ref VarSet.empty in
  let param_ren = Hashtbl.create 16 in
  let get_recbvs () = !recbvs in
  let param_renaming v =
    Hashtbl.mem param_ren v in
  let find_b i = Hashtbl.find_all chi_b i in
  let find_b_of_v v = Hashtbl.find v_b v in
  let find_chi b = Hashtbl.find b_chi b in
  let rec add_bchi b i ~posi ~chiK =
    Hashtbl.replace v_b b b;
    if Hashtbl.mem b_chi b
    then (
      let old = Hashtbl.find b_chi b in
      (*[* Format.printf "add_bchi: exist old=%d chi%d(%s);@ posi=%b@\n%!"
        old i (var_str b) posi; *]*)
      assert (old = i)
    ) else (
      (*[* Format.printf "add_bchi: chi%d(%s);@ posi=%b@\n%!"
        i (var_str b) posi; *]*)
      if posi then Hashtbl.add posi_b b ()
      else q.negbs <- b::q.negbs;
      if chiK then Hashtbl.add chiK_i i ()
      else if not posi then recbvs := VarSet.add b !recbvs;
      q.allchi <- Ints.add i q.allchi;
      Hashtbl.add chi_b i b;
      Hashtbl.add b_chi b i;
      q.add_b_vs_of b [delta, b])
  and add_b_vs_of b rvs =
    assert (Hashtbl.mem b_chi b);
    let qvs = try Hashtbl.find b_qvs b with Not_found -> [] in
    let rvs = List.filter
      (fun (_,v) -> not (List.mem v qvs)) rvs in
    let vs = List.map snd rvs in
    let vss = vars_of_list vs in
    if not (positive_b b) && not (is_chiK (find_chi b))
    then recbvs := VarSet.union vss !recbvs;
    if not (positive_b b) && is_chiK (find_chi b)
    then List.iter
        (fun (o, v) ->
           (* FIXME: also include existential type variables. *)
           if VarSet.mem o !recbvs then Hashtbl.add param_ren v ())
        rvs;
    List.iter (fun v -> q_ops.same_as v b; Hashtbl.replace v_b v b) vs;
    q.allbvs <- VarSet.union q.allbvs vss;
    if Hashtbl.mem posi_b b
    then List.iter (fun v -> Hashtbl.add posi_b v ()) vs;
    try
      let ovs = Hashtbl.find b_vs b in
      Hashtbl.replace b_vs b (VarSet.union ovs vss);
      let orenaming = Hashtbl.find b_renaming b in
      Hashtbl.replace b_renaming b (rvs @ orenaming);
      Hashtbl.replace b_qvs b (vs @ qvs);
    with Not_found ->
      (* FIXME: b_vs contains b, but b_qvs doesn't, right? *)
      Hashtbl.add b_vs b (vars_of_list (b::vs));
      Hashtbl.add b_renaming b rvs;
      Hashtbl.add b_qvs b vs;
  and q = {
    op = q_ops; cmp_v = q_ops.cmp_v; uni_v = q_ops.uni_v;
    add_b_vs_of; allchi = Ints.empty; chiK_anchor;
    b_vs; b_renaming; b_qvs; allbvs = VarSet.empty;
    add_bchi; find_b; find_b_of_v; find_chi; is_chiK;
    positive_b; negbs = []; get_recbvs; param_renaming;
    recover_escaping = Hashtbl.create 8;
  } in q

let modify_q ~uni_vars q =
  let q_uni = q.uni_v in
  let uni_v v = if VarSet.mem v uni_vars then true else q_uni v in
  let op = {q.op with uni_v} in
  {q with op; uni_v}  

let renaming_sb =
  List.map (fun (v,w) -> v, (TVar w, dummy_loc))

(* Return renaming of [vs], creating fresh [rvs] pairs when
   needed and adding them as locals of [b] in [q].
   [self_owned] means [vs] will be reused as new [b] parameters. *)
let matchup_vars ~self_owned q b vs =
  let orvs =
    try Hashtbl.find q.b_renaming b with Not_found -> assert false in
  let nvs = List.filter (fun v->not (List.mem_assoc v orvs)) vs in
  let nrvs =
    if self_owned
    then List.map (fun v->v, v) nvs
    else List.map (fun v->v, freshen_var v) nvs in
  (*[* Format.printf "matchup_vars: b=%s;@ vs=%s;@ orvs=%s;@ nrvs=%s@\n%!"
    (var_str b)
    (String.concat ", " (List.map var_str vs))
    (String.concat ", "
       (List.map (fun (v,w)->var_str v^":="^var_str w) orvs))
    (String.concat ", "
       (List.map (fun (v,w)->var_str v^":="^var_str w) nrvs)); *]*)
  q.add_b_vs_of b nrvs;
  (* [orvs] stores a [delta] substitution, [delta] is absent from [vs] *)
  nrvs @ orvs

let sb_atom_PredU q posi psb = function
  | PredVarU (i, (TVar b as t), loc) ->
    (try
       let vs, phi = List.assoc i psb in
       (*[* Format.printf
         "sb_atom_pred: U posi=%b@ chi%d(%s)=@ %a@\n%!"
         posi i (var_str b) pr_ans (vs,phi); *]*)
       let renaming =
         renaming_sb (matchup_vars ~self_owned:(not posi) q b vs) in
       replace_loc loc
         (sb_phi_unary t (subst_formula renaming phi))
     with Not_found ->
       (*[* Format.printf
         "sb_atom_pred: Not_found U posi=%b@ chi%d(%s)@\n%!"
         posi i (var_str b); *]*)
       [])  
  | PredVarB _ -> []
  | a -> [a]

let sb_formula_PredU q posi psb phi =
  concat_map (sb_atom_PredU q posi psb) phi

let sb_brs_PredU q sol brs = List.map
  (fun (nonrec, prem, concl) ->
    nonrec,
    map_some                            (* chi_pos *)
      (function PredVarU (i,t,_) -> Some (i, t) | _ -> None) concl,
    map_some                            (* chiK_neg *)
      (function PredVarB (i,t1,t2,lc) -> Some (i,t1,t2,lc) | _ -> None) prem,
    map_some                            (* chiK_pos *)
      (function PredVarB (i,t1,t2,lc) -> Some (i,t1,t2,lc) | _ -> None) concl,
    sb_formula_PredU q false sol prem,
    sb_formula_PredU q true sol concl)
  brs

let sb_PredB q posi psb (i, t1, t2, lc) =
  match t1 with TVar b ->
    (try
       let vs, phi = List.assoc i psb in
       (*[* Format.printf
         "sb_chiK: chi%d(%s,%a)=@ %a@\n%!"
         i (var_str b) pr_ty t2 pr_ans (vs,phi); *]*)
       let renaming =
         renaming_sb (matchup_vars ~self_owned:posi q b vs) in
       (*[* Format.printf
         "sb_chiK: chi%d(%s,%a) renaming@ %a@\n%!"
         i (var_str b) pr_ty t2 pr_subst renaming; *]*)
       replace_loc lc
         (sb_phi_binary t1 t2 (subst_formula renaming phi))
     with Not_found -> [])
  | _ -> []

let sb_PredB_par q psb (i, t2) =
  try
    let vs, phi = List.assoc i psb in
    (*[* Format.printf
      "sb_chiK_par: chi%d(%a)=@ %a@\n%!"
      i pr_ty t2 pr_ans (vs,phi); *]*)
    (* We need to replace delta' so we use sb_phi_binary. *)
    sb_phi_binary t2 t2 phi
  with Not_found -> []

let sb_brs_PredB q rol par brs = List.map
  (fun (nonrec, chi_pos, chiK_neg, chiK_pos, prem, concl) ->
    nonrec, chi_pos, chiK_pos,
    concat_map (sb_PredB q false rol) chiK_neg @ prem,
    (* This will only substitute the unary chiK predicates. *)
    concat_map (sb_PredB_par q par) chi_pos @
    (* The below substitution roughly equivalent effect to the above
       substitution -- the above fixes parameters once globally, the
       commented-out fixes the same parameters for each case. *)
    (* concat_map (sb_PredB q true par) chiK_pos @ *)
      concl)
  brs

let sb_atom_pred q posi rol sol = function
  | PredVarU (i, (TVar b as t), loc) as a ->
    (try
       let vs, phi = List.assoc i sol in
       (*[* Format.printf
         "sb_atom_pred: U posi=%b@ chi%d(%s)=@ %a@\n%!"
         posi i (var_str b) pr_ans (vs,phi); *]*)
       let renaming =
         renaming_sb (matchup_vars (not posi) q b vs) in
       replace_loc loc
         (sb_phi_unary t (subst_formula renaming phi))
     with Not_found -> [a])  
  | PredVarB (i, (TVar b as t1), t2, loc) as a ->
    (try
       let vs, phi = List.assoc i rol in
       (*[* Format.printf
         "sb_atom_pred: B posi=%b@ chi%d(%s,%a)=@ %a@\n%!"
         posi i (var_str b) pr_ty t2 pr_ans (vs,phi); *]*)
       let renaming =
         renaming_sb (matchup_vars posi q b vs) in
       replace_loc loc
         (sb_phi_binary t1 t2 (subst_formula renaming phi))
     with Not_found -> [a])
  | a -> [a]

let sb_formula_pred q posi rol sol phi =
  concat_map (sb_atom_pred q posi rol sol) phi

(* Using "script kappa" because "script chi" is not available. *)
let pr_chi_subst ppf chi_sb =
  pr_sep_list ";" (fun ppf (i,ans) ->
    Format.fprintf ppf "X%d:=%a" i pr_ans ans) ppf chi_sb

let pr_bchi_subst ppf chi_sb =
  pr_sep_list ";" (fun ppf (v,ans) ->
    Format.fprintf ppf "X(%s):=%a" (var_str v) pr_ans ans) ppf chi_sb

type state = subst * NumS.state

let empty_state : state = [], NumS.empty_state

let holds q ~avs (ty_st, num_st) cnj =
  let {cnj_typ=ty_st; cnj_num; cnj_so=_} =
    solve ~use_quants:true ~sb:ty_st q.op cnj in
  let num_st = NumS.holds q.op avs num_st cnj_num in
  ty_st, num_st

let satisfiable q (ty_st, num_st) cnj =
  let {cnj_typ=ty_st; cnj_num; cnj_so=_} =
    solve ~use_quants:false ~sb:ty_st q.op cnj in
  let num_st = NumS.satisfiable_exn ~state:num_st cnj_num in
  ty_st, num_st

let implies q (ty_st, num_st) cnj =
  let {cnj_typ; cnj_num; cnj_so=_} =
    solve ~use_quants:false q.op
      (subst_formula ty_st cnj) in
  let {cnj_typ=res_ty; cnj_num=res_num; cnj_so=_} =
    solve ~use_quants:false ~sb:ty_st q.op
      (to_formula cnj_typ) in
  (*[* Format.printf
    "Invariants.implies: cnj_typ=%a;@ res_ty=%a;@ res_num=%a@\n%!"
    pr_subst cnj_typ pr_subst res_ty NumDefs.pr_formula res_num; *]*)
  (*[* let res = *]*)
  cnj_typ = [] && res_num = [] && NumS.implies_cnj num_st cnj_num
    (*[* in Format.printf "Invariants.implies: res=%b@\n%!" res; res *]*)

(* 4, 6 *)
let abductive_holds q ~avs ~bvs (ty_st, num_st) cnj =
  let {cnj_typ=ty_st; cnj_num; cnj_so=_} =
    solve ~use_quants:true ~sb:ty_st q.op cnj in
  (* No need to use avs. *)
  let num_st, more = NumS.abductive_holds
      q.op ~bvs num_st cnj_num in
  (* 5 *)
  let old, more = List.partition
      (fun c -> List.exists (NumDefs.eq_atom c) cnj_num) more in
  (ty_st, num_st), NumS.num_to_formula old, NumS.num_to_formula more

let satisfiable q (ty_st, num_st) cnj =
  let {cnj_typ=ty_st; cnj_num; cnj_so=_} =
    solve ~use_quants:false ~sb:ty_st q.op cnj in
  ty_st, NumS.satisfiable_exn ~state:num_st cnj_num

(* 10 *)
let strat q bvs b ans =
  let (_, ans_r), ans = fold_map
      (fun (pvs, ans_r) c ->
         let vs = VarSet.elements (VarSet.diff (fvs_atom c) pvs) in
         let vs = List.filter
             (fun v -> q.cmp_v b v = Left_of) vs in
         let loc = atom_loc c in
         let is_uni v = q.uni_v v && not (VarSet.mem v bvs) in 
         if List.exists is_uni vs then
           (let bad = List.find is_uni vs in
            raise (NoAnswer
                     (var_sort bad, "Escaping universal variable",
                      Some (TVar b, TVar bad), loc)));
         let avs = List.map freshen_var vs in
         let ans_r =
           List.map2 (fun a b -> b, (TVar a, loc)) avs vs @ ans_r in
         (VarSet.union pvs (vars_of_list vs), ans_r),
         (avs, subst_atom ans_r c))
      (VarSet.empty, []) ans in
  let avs, ans_l = List.split ans in
  List.concat avs, ans_l, ans_r

let split do_postcond ~avs ans negchi_locs ~bvs ~cand_bvs q =
  (* 1 FIXME: do we really need this? *)
  let cmp_v v1 v2 =
    let a = q.cmp_v v1 v2 in
    if a <> Same_quant then a
    else
      let c1 = VarSet.mem v1 q.allbvs
      and c2 = VarSet.mem v2 q.allbvs in
      if c1 && c2 then Same_quant
      else if c1 then Left_of
      else if c2 then Right_of
      else Same_quant in
  let negbs =
    if do_postcond then q.negbs
    else List.filter (fun b->not (q.is_chiK (q.find_chi b))) q.negbs in
  (* Need to be ordered from leftmost in the quantifier prefix. *)
  (* FIXME: check that it's guaranteed. *)
  let negbs = List.rev negbs in
  let context = ref empty_state in
  let rec loop ~avs ~bvs ans discard sol =
    (* 2 *)
    (*[* Format.printf
      "split-loop: starting@ avs=%a@\nans=@ %a@\nsol=@ %a@\n%!"
      pr_vars avs pr_formula ans
      pr_bchi_subst (List.map (fun (b,a)->b,([],a)) sol); *]*)
    let ans0, ab_eqs = List.partition
        (function
          | Eqty (TVar a, TVar b, _)
            when not (q.uni_v a) && VarSet.mem b q.allbvs &&
                 cmp_v a b = Right_of -> false
          | Eqty (TVar b, TVar a, _)
            when not (q.uni_v a) && VarSet.mem b q.allbvs &&
                 cmp_v a b = Right_of -> false
          | _ -> true) ans in
    (* 3 *)
    let ans_cand = List.map
        (fun b ->
           (*[* Format.printf "@\nsplit-loop-3: b=%s@ target=%a@\n%!"
             (var_str b) pr_vars (Hashtbl.find q.b_vs b); *]*)
           let xbvs = VarSet.add b (Hashtbl.find q.b_vs b) in
           let postcond = q.is_chiK (q.find_chi b) in
           let ans = List.filter
               (fun c ->
                  let cvs = fvs_atom c in
                  let prim_constr_v = prim_constr_var c in
                  let xbvs_prim_constr =
                    match prim_constr_v with
                    | None -> false | Some v -> VarSet.mem v xbvs in
                  (*[* Format.printf
                    "c=%a@\nxbvs_prim_constr=%b@\n%!"
                    pr_atom c xbvs_prim_constr; *]*)
                  VarSet.exists (fun cv -> VarSet.mem cv xbvs) cvs &&
                  VarSet.for_all
                    (fun cv ->
                       (*[* Format.printf
                         "cv=%s, %s, up=%b, down=%b, uni=%b, xbvs=%b, bvs=%b;@ "
                         (var_str cv)
                         (var_scope_str (q.cmp_v cv b))
                         (q.op.upward_of cv b) (q.op.upward_of b cv)
                       (q.uni_v cv) (VarSet.mem cv xbvs)
                       (VarSet.mem cv bvs); *]*)
                       not (q.uni_v cv) || VarSet.mem cv xbvs ||
                       (* FIXME: postcond? *)
                       (postcond || VarSet.mem cv bvs) &&
                       Some cv <> prim_constr_v &&
                       (xbvs_prim_constr && VarSet.mem cv bvs ||
                        q.cmp_v cv b = Left_of))
                    cvs)
               ans0 in
           b, ans)
        negbs in
    (*[* Format.printf "@\nsplit-loop-3: ans1=@\n%a@\n%!"
      pr_bchi_subst
      (List.map (fun (b,a)->b, (VarSet.elements (Hashtbl.find q.b_vs b),a))
         ans_cand); *]*)
    (* 7 *)
    let init_res = List.filter
        (fun c -> not (List.exists (List.memq c % snd) ans_cand)) ans0 in
    (*[* Format.printf "split-loop-6: ans0=@\n%a@\ninit_res=%a@\n%!"
      pr_formula ans0 pr_formula init_res; *]*)
    let init_state =
      try holds q ~avs empty_state init_res
      with Contradiction _ as e -> raise (convert e) in
    (* 5, 7 *)
    (* TODO: would it be better to implement it through
       [connected ~validate]? *)
    let ans_res = ref init_res and state = ref init_state in
    let ans_ps, more_ans =
      List.split
        (List.map
           (fun (b,ans) ->
              let ans, more =
                List.split
                  (List.map
                     (fun c ->
                        try
                          let state', old_ans, more_ans =
                            abductive_holds q ~avs ~bvs !state [c] in
                          state := state';
                          let more_ans = List.filter
                              (fun c -> not (implies q !context [c]))
                              more_ans in
                          context := satisfiable q !context old_ans;
                          (* If the original atom holds under the
                             quantifier given [more_ans], keep it in
                             the residuum. *)
                          if old_ans = [] then ans_res := c :: !ans_res;
                          (*[* Format.printf
                              "split-more: b=%s; c=%a@\n\
                               old_ans=@ %a@\nmore_ans=@ %a@\n%!"
                              (var_str b) pr_atom c pr_formula old_ans
                              pr_formula more_ans; *]*)
                          old_ans, more_ans
                        with Contradiction _ (*[*as e*]*) ->
                          context := satisfiable q !context [c];
                          (*[* Format.printf
                            "split-rejected: b=%s; c=%a@\nbecause: %a@\n%!"
                            (var_str b) pr_atom c pr_exception e; *]*)
                          [c], []) ans) in
              (b, List.concat ans), List.concat more)
           ans_cand) in
    let more_ans = List.concat more_ans in
    (*[* Format.printf
      "split-loop-7: ans+=@\n%a@\nmore_ans=%a@\nans_res=%a@\n%!"
      pr_bchi_subst (List.map (fun (b,a)->b,([],a)) ans_ps)
      pr_formula more_ans pr_formula !ans_res; *]*)
    let ans_res = more_ans @ !ans_res in    
    let more_discard = concat_map snd ans_ps in
    let bvs = ref bvs in
    (* 9 *)
    let ans_strat = List.map
        (fun (b, ans_p) ->
           let (avs_p, ans_l, ans_r) = strat q !bvs b ans_p in
           (*[* Format.printf "select: ans_l(%s)=@ %a@\n%!"
             (var_str b) pr_formula ans_l; *]*)
           (* Negatively occurring [b] "owns" these formal parameters *)
           q.add_b_vs_of b (List.map (fun v->v,v) avs_p);
           bvs := add_vars avs_p !bvs;
           (* 10 *)
           let ans0 = List.assoc b sol in
           let ans = ans0 @ ans_l in
           (* 11 *)
           let avs0 = VarSet.inter avs (fvs_formula ans) in
           (* 12.a *)
           let avs = VarSet.union avs0 (vars_of_list avs_p) in
           (b, avs), (b, ans), (avs_p, ans_r))
        ans_ps in
    let avss, sol', more = split3 ans_strat in
    let bvs = !bvs in
    let nvs = List.fold_left
        (fun avs (_,bvs) -> VarSet.union avs bvs) VarSet.empty avss in
    let avs_ps, ans_rs = List.split more in
    (* 12.b *)
    let avss = List.map
        (fun (b, avs) ->
           let lbs = List.filter
               (fun b' -> q.cmp_v b b' = Right_of) negbs in
           let uvs = List.fold_left VarSet.union VarSet.empty
               (List.map (flip List.assoc avss) lbs) in
           VarSet.diff avs uvs)
        avss in
    (* 13 *)
    let ans_p = List.concat ans_rs in
    (*[* Format.printf "split: ans_p=@ %a@ --@ ans_res=@ %a@\n%!"
      pr_subst ans_p pr_formula ans_res; *]*)
    let ans_res = to_formula ans_p @ subst_formula ans_p ans_res in
    (*[* Format.printf "split: ans_res'=@ %a@\n%!"
      pr_formula ans_res; *]*)
    let avsl = List.map VarSet.elements avss in
    let ans_res = ab_eqs @ ans_res in
    (* 14 *)
    if not (VarSet.is_empty nvs) || more_ans <> []
    then
      (* 15 *)
      let avs = VarSet.diff avs
          (List.fold_left VarSet.union VarSet.empty avss) in
      let ans_res', discard', sol' =
        loop ~avs ~bvs ans_res (more_discard @ discard) sol' in (* *)
      (* 16 *)
      ans_res', discard',
      List.map2
        (fun avs (b, (avs', ans')) -> b, (avs@avs', ans')) avsl sol'
    else
      (* 17 *)
      ans_res, more_discard @ discard,
      List.map2 (fun avs (b, ans) -> b, (avs, ans)) avsl sol' in
  let solT = List.map (fun b->b, []) negbs in
  let ans_res, discard, sol =
    loop ~avs:(vars_of_list avs) ~bvs ans [] solT in
  ans_res, discard, sol

(** Eliminate provided variables if they do not contribute to
    constraints and generally simplify the formula. *)
(* FIXME: cleanup, also see FIXME at converge *)
let simplify q_ops ~bvs ?keepvs ?guard ?initstep (vs, cnj) =
  let vs = vars_of_list vs in
  (*[* Format.printf "simplify: keepvs=%a@ vs=%a@ cnj=%a@\n%!"
    (pr_some pr_vars) keepvs pr_vars vs pr_formula cnj; *]*)
  let cmp_v v1 v2 =
    let c1 = VarSet.mem v1 vs and c2 = VarSet.mem v2 vs in
    if c1 && c2 then Same_params
    else if c1 then Right_of
    else if c2 then Left_of
    else q_ops.Defs.cmp_v v1 v2 in
  let q = {q_ops with cmp_v} in
  let {cnj_typ=ty_ans; cnj_num=num_ans; cnj_so=_} =
    unify ~use_quants:false q cnj in
  (*[* Format.printf "simplify: ty ";
  List.iter
    (function
      | v, (TVar v2, _) ->
        Format.printf "v=%s %s v2=%s;@ "
          (var_str v) (var_scope_str (q_ops.cmp_v v v2)) (var_str v2)
      | _ -> ()) ty_ans;
  Format.printf "@\n%!"; *]*)
  (* Remove "orphaned" variables. *)
  let sb, ty_ans = List.partition
      (function
        | v, (TVar v2, _)
          when q_ops.cmp_v v v2 = Same_params &&
               (VarSet.mem v vs || VarSet.mem v2 vs) &&
               not (VarSet.mem v vs && VarSet.mem v2 vs) -> true
        | _ -> false) ty_ans in
  let sb = List.map
      (function
        | v, (TVar v2, _) as sv
          when q_ops.cmp_v v v2 = Same_params &&
               VarSet.mem v2 vs &&
               not (VarSet.mem v vs) -> sv
        | v, (TVar v2, lc) -> v2, (TVar v, lc)
        | _ -> assert false)
      sb in
  let ty_ans = subst_sb ~sb ty_ans in
  (* We "cheat": eliminate variables introduced later, so that
     convergence check has easier job (i.e. just syntactic). *)
  let ty_sb, ty_ans = List.partition
      (function
        | v, (TVar v2, _)
          when VarSet.mem v vs && VarSet.mem v2 vs && v < v2 -> true
        | _ -> false) ty_ans in
  let ty_sb = List.map
      (function
        | v, (TVar v2, lc) -> v2, (TVar v, lc)
        | _ -> assert false)
      ty_sb in
  (*[* Format.printf "simplify: vs=%a@ sb=%a@ ty_sb=%a@\n%!" pr_vars vs
    pr_subst sb pr_subst ty_sb; *]*)
  let ty_ans = update_sb ~more_sb:ty_sb ty_ans in
  let ty_ans, keepvs' =
    match keepvs with
    | None -> ty_ans, VarSet.empty
    | Some keepvs ->
      List.filter (fun (v, _) -> VarSet.mem v keepvs) ty_ans, keepvs in
  let num_sb, num_nsb, num_ans =
    NumS.separate_subst q ~keep:(VarSet.diff keepvs' vs) ~bvs
      ~no_csts:true ~apply:true num_ans in
  (*let num_sb, more_num_ans =
    match keepvs with
    | None ->
      List.partition
        (fun (v,_) -> true (* VarSet.mem v vs || not (VarSet.mem v bvs) *))
        num_sb
    | Some keepvs ->
      List.partition (fun (v,_) -> not (VarSet.mem v keepvs)) num_sb in
  let num_ans = NumS.sort_of_subst more_num_ans @ num_ans in*)
  (* We "cheat": eliminate variables introduced later, so that
     convergence check has easier job (i.e. just syntactic). *)
  let num_sb = List.map
      (function
        | v, (TVar v2, lc) when v < v2 -> v2, (TVar v, lc)
        | v, (Alien (Num_term (NumDefs.Lin (1, 1, v2))), lc) when v < v2 ->
          v2, (TVar v, lc)
        | sv -> sv)
      num_sb
  and num_nsb = List.map
      (function
        | v, NumDefs.Lin (1, 1, v2) when v < v2 -> v2, NumDefs.Lin (1, 1, v)
        | sv -> sv)                  
      num_nsb in
  (*[* Format.printf "simplify:@\nnum_sb=%a@\nnum_ans0=%a@\n%!"
    pr_subst num_sb NumDefs.pr_formula num_ans; *]*)
  let num_ans = List.map (NumDefs.nsubst_atom num_nsb) num_ans in
  let guard = map_opt guard
    (fun cnj -> (sep_formulas cnj).cnj_num) in
  let localvs =
    match initstep with
    | None | Some true -> None
    | Some false -> Some vs in
  (* Passing [localvs] will prune atoms with non-local variables. *)
  let _, num_ans' =
    NumS.simplify q ?keepvs ?localvs ?guard VarSet.empty num_ans in
  (*[* Format.printf "simplify:@\nnum_ans=%a@\nnum_ans'=%a@\n%!"
    NumDefs.pr_formula num_ans NumDefs.pr_formula num_ans'; *]*)
  let ty_ans = subst_sb ~sb:num_sb ty_ans in
  let ty_sb, ty_ans =
    match keepvs with
    | Some keepvs ->
      List.partition
        (fun (v,_) -> VarSet.mem v vs || not (VarSet.mem v keepvs)) ty_ans
    | None ->
      List.partition (fun (v,_) -> VarSet.mem v vs) ty_ans in
  let ans = to_formula ty_ans @ NumS.formula_of_sort num_ans' in
  let vs = VarSet.inter vs (fvs_formula ans) in
  (*[* Format.printf "simplify: vs=%a@ ty_sb=%a@ num_sb=%a@ ans=%a@\n%!"
    pr_vars vs pr_subst ty_sb pr_subst num_sb pr_formula ans; *]*)
  ty_sb @ num_sb, (vs, ans)

let vsimplify q_ops ~bvs ?keepvs ?guard ?initstep ans =
  let num_sb, (vs, ans) = simplify q_ops ~bvs ?keepvs ?guard ?initstep ans in
  num_sb, (VarSet.elements vs, ans)

(** Generally simplify the formula. Do not normalize non-type sort atoms. *)
let prune_redund q_ops ?localvs ?guard ~initstep (vs, cnj) =
  let vs = vars_of_list vs in
  (*[* Format.printf "simplify: vs=%a@ cnj=%a@\n%!"
    pr_vars vs pr_formula cnj; *]*)
  let cmp_v v1 v2 =
    let c1 = VarSet.mem v1 vs and c2 = VarSet.mem v2 vs in
    if c1 && c2 then Same_params
    else if c1 then Right_of
    else if c2 then Left_of
    else q_ops.Defs.cmp_v v1 v2 in
  let q_ops = {q_ops with cmp_v} in
  let {cnj_typ=ty_ans; cnj_num=num_ans; cnj_so=_} =
    unify ~use_quants:false q_ops cnj in
  (* We "cheat": eliminate variables introduced earlier, so that
     convergence check has easier job (i.e. just syntactic). *)
  let ty_sb, ty_ans = List.partition
      (function
        | v, (TVar v2, _)
          when VarSet.mem v vs && VarSet.mem v2 vs && v < v2 -> true
        | _ -> false) ty_ans in
  let ty_sb = List.map
      (function
        | v, (TVar v2, lc) -> v2, (TVar v, lc)
        | _ -> assert false)
      ty_sb in
  let ty_ans = update_sb ~more_sb:ty_sb ty_ans in
  let guard = map_opt guard
    (fun cnj -> (sep_formulas cnj).cnj_num) in
  let num_ans =
    NumS.prune_redundant q_ops ?localvs ?guard ~initstep num_ans in
  (*[* Format.printf "prune-simplified:@\nnum_ans=%a@\n%!"
    NumDefs.pr_formula num_ans; *]*)
  let ty_sb, ty_ans = List.partition
      (fun (v,_) -> VarSet.mem v vs && v <> delta && v <> delta') ty_ans in
  let ans = to_formula ty_ans @ NumS.formula_of_sort num_ans in
  let vs = VarSet.inter vs (fvs_formula ans) in
  (*[* Format.printf "prune-simplify: vs=%a@ ty_sb=%a@ ans=%a@\n%!"
    pr_vars vs pr_subst ty_sb pr_formula ans; *]*)
  VarSet.elements vs, ans

(* Rename the new solution to match variables of the old solution. *)
(* TODO: ugly, rewrite or provide a medium-level description. *)
(* FIXME: coordinate with NumS.disjelim_simplify. *)
let converge q_ops ~initstep ?guard ~check_only
    (vs1, cnj1) (vs2, cnj2) =
  (*[* Format.printf
    "converge: check_only=%b@ vs1=%a@ vs2=%a@\ncnj1=%a@\ncnj2=%a\n%!"
    check_only pr_vars (vars_of_list vs1) pr_vars (vars_of_list vs2)
    pr_formula cnj1 pr_formula cnj2; *]*)
  let {cnj_typ=c1_ty; cnj_num=c1_num; cnj_so=c1_so} =
    unify ~use_quants:false q_ops cnj1 in
  let {cnj_typ=c2_ty; cnj_num=c2_num; cnj_so=c2_so} =
    unify ~use_quants:false q_ops cnj2 in
  let recover_param c_ty cnj =
    try match
        List.find
          (function Eqty (t1, t2, _) -> t1=tdelta' || t2=tdelta'
                  | _ -> false) cnj
      with
      | Eqty (TVar v, tpar, lc) when v = delta' ->
        tpar, lc, List.remove_assoc delta' c_ty
      | Eqty (tpar, TVar v, lc) when v = delta' ->
        tpar, lc, List.remove_assoc delta' c_ty
      | _ -> assert false
    with Not_found -> TCons (tuple, []), dummy_loc, c_ty in
  let tpar_old, lc_old, c1_ty = recover_param c1_ty cnj1 in
  let tpar_new, lc_new, c2_ty = recover_param c2_ty cnj2 in
  assert (c1_so = []); assert (c2_so = []);
  (* Recover old variable names. *)
  let pms_old = fvs_typ tpar_old and pms_new = fvs_typ tpar_new in
  let vs_old = VarSet.diff (vars_of_list vs1) pms_old in
  let vs_new = VarSet.diff (vars_of_list vs2) pms_new in
  let valid_sb = map_some
      (function
        | v1, (TVar v2, _) as sx
          when VarSet.mem v2 vs_old && VarSet.mem v1 vs_new -> Some sx
        | v2, (TVar v1, lc)
          when VarSet.mem v2 vs_old && VarSet.mem v1 vs_new ->
          Some (v1, (TVar v2, lc))
        | _ -> None) in
  let cmp (v1,_) (v2,_) = compare v1 v2 in
  let c1_ty = List.sort cmp c1_ty and c2_ty = List.sort cmp c2_ty in
  let cnj_tys = inter_merge cmp
      (fun (v,(t1,_)) (_,(t2,_)) ->
         Eqty (t1,t2,dummy_loc)) c1_ty c2_ty in
  let {cnj_typ=renaming; cnj_num=ren_num; cnj_so=_} =
    unify ~use_quants:false q_ops cnj_tys in
  (*[* Format.printf "converge: cnj_tys=%a@\nren_num=%a@\nrenaming1=%a@\n%!"
    pr_formula cnj_tys NumDefs.pr_formula ren_num pr_subst renaming; *]*)
  let v_notin_vs_num vs =
    map_some
      NumDefs.(function
          | Eq (Lin (j,k,v), t, lc) when not (List.mem v vs) ->
            let t =
              if j=1 && k=1 then num t
              else num (scale_term k j t) in
            Some (v, (t, lc))
          | Eq (t, Lin (j,k,v), lc) when not (List.mem v vs) ->
            let t =
              if j=1 && k=1 then num t
              else num (scale_term k j t) in
            Some (v, (t, lc))
          | _ -> None) in 
  let valid_num =
    map_some
      NumDefs.(function
          | Eq (Lin (j1,k1,v1), Lin (j2,k2,v2), lc)
            when VarSet.mem v2 vs_old && VarSet.mem v1 vs_new ->
            let t =
              if j1=1 && k1=1 && j2=1 && k2=1 then TVar v2
              else num (Lin (j2*k1,k2*j1,v2)) in
            Some (v1, (t, lc))
          | Eq (Lin (j2,k2,v2), Lin (j1,k1,v1), lc)
            when VarSet.mem v2 vs_old && VarSet.mem v1 vs_new ->
            let t =
              if j1=1 && k1=1 && j2=1 && k2=1 then TVar v2
              else num (Lin (j2*k1,k2*j1,v2)) in
            Some (v1, (t, lc))
          | _ -> None) in 
  let valid_cn =
      map_some
        (function
          | Eqty (TVar v1, (TVar v2 as t), lc)
            when VarSet.mem v2 vs_old && VarSet.mem v1 vs_new ->
            Some (v1, (t, lc))
          | Eqty (TVar v2 as t, TVar v1, lc)
            when VarSet.mem v2 vs_old && VarSet.mem v1 vs_new ->
            Some (v1, (t, lc))
          | _ -> None) in 
  let renaming = valid_num ren_num @ valid_sb renaming in
  (*[* Format.printf "converge: renaming2=%a@\n%!" pr_subst renaming; *]*)
  let c1_nr = List.sort cmp (v_notin_vs_num vs1 c1_num)
  and c2_nr = List.sort cmp (v_notin_vs_num vs2 c2_num) in
  let num_ren = inter_merge
      (fun (v1,_) (v2,_) -> compare v1 v2)
      (fun (_,(t1,_)) (_,(t2,_)) -> Eqty (t1,t2,dummy_loc))
      c1_nr c2_nr in
  let renaming = valid_cn num_ren @ renaming in
  (*[* Format.printf
    "converge: pms_old=%a@ pms_new=%a@ vs_old=%a@ vs_new=%a@
    renaming3=%a@ old c2_ty=%a@ old c2_num=%a@\n%!"
    pr_vars pms_old pr_vars pms_new pr_vars vs_old pr_vars vs_new
    pr_subst renaming pr_subst c2_ty NumDefs.pr_formula c2_num; *]*)
  let c2_ty = subst_sb ~sb:renaming c2_ty
  and c2_num = NumS.subst_formula renaming c2_num
  and vs2 = List.map
      (fun v ->
         try match List.assoc v renaming with
           | TVar v2, _ -> v2 | _ -> assert false
         with Not_found -> v)
      vs2 in
  let vs2 = vars_of_list vs2 in
  let localvs = VarSet.diff vs2 pms_new in
  (*[* Format.printf "converge: initstep=%b localvs=%a@\n%!"
    initstep pr_vars localvs; *]*)
  let guard = map_opt guard
    (fun cnj -> (sep_formulas cnj).cnj_num) in
  let c_num =
    if check_only
    then NumS.prune_redundant q_ops ~localvs ?guard ~initstep c2_num
    else NumS.converge q_ops ~localvs ?guard ~initstep
        c1_num c2_num in
  let res = to_formula c2_ty @ NumS.formula_of_sort c_num in
  let res_vs = fvs_formula res in
  let res_pms = map_some (fun v ->
      let v = 
        try match List.assoc v renaming with
          | TVar v2, _ -> v2 | _ -> assert false
        with Not_found -> v in
      if VarSet.mem v res_vs then Some v else None)
      (VarSet.elements pms_new) in
  let res_tpar = TCons
      (tuple, List.map (fun v -> TVar v) res_pms) in
  (*[* Format.printf
    "converge: check_only=%b vs2=%a@\nc2_ty=%a@\nc2_num=%a@\nc_num=%a@\n%!"
    check_only pr_vars vs2
    pr_subst c2_ty NumDefs.pr_formula c2_num NumDefs.pr_formula c_num; *]*)
  renaming, res_tpar,
  (VarSet.elements (VarSet.inter res_vs vs2),
   Eqty (tdelta', res_tpar, lc_new)::res)


let neg_constrns = ref true

let empty_disc = {at_typ=[],[]; at_num=[]; at_ord=[]; at_so=()}
let empty_dl = {at_typ=[]; at_num=[]; at_ord=[]; at_so=()}

(* Captures where the repeat step is/are. *)
let disj_step = [|1; 1; 2; 3; 4|]

let solve q_ops new_ex_types exty_res_chi brs =
  timeout_flag := false;
  (* DEBUG *)
  (*[* List.iter
    (fun (prem,concl) ->
       try ignore (solve ~use_quants:false q_ops (prem@concl))
       with Contradiction _ as e ->
         Format.printf
           "solve: bad branch@\n%a@ ⟹@ %a@\nreason: %a@\n%!"
           pr_formula prem pr_formula concl pr_exception e;
    )
    brs; *]*)
  let q = new_q q_ops in
  (* Unfortunately we cannot delegate [upward_of] directly to [q.op] *)
  let upward_of v1 v2 =
    let b1 = try q.find_b_of_v v1 with Not_found -> v1 in
    let b2 = try q.find_b_of_v v2 with Not_found -> v2 in
    q.op.upward_of b1 b2 in
  (* let cmp_v = q.cmp_v and uni_v = q.uni_v in *)
  let tpar_vs = Hashtbl.create 16 in
  List.iter
    (fun (prem,concl) ->
       List.iter
         (function
           | PredVarB (i, _, TVar a, _) ->
             (*[* Format.printf "PredVarB: prem i=%d a=%s@\n%!"
               i (var_str a); *]*)
             Hashtbl.replace tpar_vs a ()
           | PredVarB _ -> assert false
           | Eqty (TCons (Extype _, [TVar a]), _, _)
           | Eqty (_, TCons (Extype _, [TVar a]), _) ->
             (*[* Format.printf "Eqty-exty: prem a=%s@\n%!"
               (var_str a); *]*)
             Hashtbl.replace tpar_vs a ()
           | _ -> ()) prem;
       List.iter
         (function
           | PredVarB (i, _, TVar a, _) ->
             (*[* Format.printf "PredVarB: concl i=%d a=%s@\n%!"
               i (var_str a); *]*)
             Hashtbl.replace tpar_vs a ()
           | PredVarB _ -> assert false
           | Eqty (TCons (Extype _, [TVar a]), _, _)
           | Eqty (_, TCons (Extype _, [TVar a]), _) ->
             (*[* Format.printf "Eqty-exty: concl a=%s@\n%!"
               (var_str a); *]*)
             Hashtbl.replace tpar_vs a ()
           | _ -> ()) concl;
    ) brs;
  let neg_brs, brs = List.partition
      (fun (_,concl) -> List.exists
          (function CFalse _ -> true | _ -> false) concl) brs in
  (* Variables not in quantifier will behave like rightmost. *)
  (* Enrich the negative branches -- they need it. *)
  let neg_brs = List.map
      (fun (prem,concl) ->
         let more = concat_map snd
             (List.filter (fun (prem2, _) -> list_diff prem2 prem = [])
                brs) in
         more @ prem, concl)
      neg_brs in
  (*[* Format.printf "solve: pos_brs=@ %a@\n%!" Infer.pr_rbrs brs; *]*)
  (*[* Format.printf "solve: neg_brs=@ %a@\n%!" Infer.pr_rbrs neg_brs; *]*)
  let neg_cns = List.map
      (fun (prem, concl) ->
         let loc =
           match List.find (function CFalse _ -> true | _ -> false) concl
           with CFalse loc -> loc | _ -> assert false in
         prem, loc)
      neg_brs in
  (*[* Format.printf "solve: neg_cns=@ %a@\n%!" Infer.pr_rbrs
    (List.map (fun (cnj,_) -> cnj, []) neg_cns); *]*)
  let negchi_locs = Hashtbl.create 8 in
  let alphasK = Hashtbl.create 8 in
  let chi_rec = Hashtbl.create 2 in
  (* FIXME: rethink which parts need to be done for negative brs too *)
  List.iter
    (fun (prem, concl) ->
       List.iter
         (function
           | PredVarU (i, TVar b, lc_p) ->
             let lc_c = formula_loc concl in
             Hashtbl.add negchi_locs b (loc_union lc_p lc_c);
             Hashtbl.replace chi_rec i ();
             q.add_bchi b i ~posi:false ~chiK:false
           | PredVarB (i, TVar b, TVar _, lc_p) ->
             let lc_c = formula_loc concl in
             Hashtbl.add negchi_locs b (loc_union lc_p lc_c);
             q.add_bchi b i ~posi:false ~chiK:true
           | PredVarU _ | PredVarB _ -> assert false
           | _ -> ()) prem;
       List.iter
         (function
           | PredVarB (i, TVar b, TVar a, _) ->
             Hashtbl.replace alphasK a ();
             q.add_bchi b i ~posi:true ~chiK:true
           | PredVarB _ -> assert false
           | _ -> ()) concl;
    ) brs;
  List.iter
    (fun (_, concl) ->
       List.iter
         (function
           | PredVarU (i, TVar a, _) when q.is_chiK i ->
             Hashtbl.add q.chiK_anchor i a
           | PredVarU (i, TVar b, _) when not (q.is_chiK i) ->
             q.add_bchi b i ~posi:true ~chiK:false
           | PredVarU _ -> assert false
           | _ -> ()) concl;
    ) brs;
  let exty_of_chi = Hashtbl.create 4 in
  List.iter
    (fun (ety, _) ->
       match Hashtbl.find sigma (Extype ety) with
       | _, (PredVarB (chi,_,_,_))::_, _, _, _ ->
         Hashtbl.add exty_of_chi chi ety
       | _ -> assert false)
    new_ex_types;
  let is_rec_exchi exchi =
    let exty = Hashtbl.find exty_of_chi exchi in
    Hashtbl.mem exty_res_chi exty in
  let brs = List.map
      (fun (prem,concl) ->
         not (List.exists (function
             | PredVarU (i, _, _) -> Hashtbl.mem chi_rec i
             | _ -> false) concl) &&
         not (List.exists (function
             | PredVarB (i, _, _, _) -> is_rec_exchi i
             | _ -> false) prem),
         prem, concl)
      brs in
  let bparams iter_no =
    if iter_no = 0 && not !early_postcond_abd then q.get_recbvs ()
    else
      List.fold_left
        (fun bvs b ->
           (*[* Format.printf
             "solve: bvs += %s -> %a@\n%!"
             (var_str b) pr_vars (Hashtbl.find q.b_vs b); *]*)
           VarSet.union bvs (Hashtbl.find q.b_vs b))
        VarSet.empty q.negbs in
  (* keys in sorted order! *)
  let solT = List.map
      (fun i -> i, ([], []))
      (Ints.elements q.allchi) in
  let rolT, solT = List.partition (q.is_chiK % fst) solT in
  (*[* Format.printf "rol-chiK: %a@\nsol-chi: %a@\n%!"
    pr_ints (ints_of_list (List.map fst rolT))
    pr_ints (ints_of_list (List.map fst solT)); *]*)
  (*[* Format.printf "chiK_anchor:";
    Hashtbl.iter (fun k v -> Format.printf "@ %d->%s" k (var_str v))
    q.chiK_anchor; Format.printf "@\n%!"; *]*)
  let rec loop iter_no discard rol1 sol1 ans1_res =
    (* 1 *)
    (*[* Format.printf
      "solve: substituting invariants at step 1@\n%!"; *]*)
    let brs0 = sb_brs_PredU q sol1 brs in
    let get_g_par rol =
      List.map (fun (i, _) ->
          try
            let pv =
              find_some
                (fun (_, _, _, chiK_pos, _, _) ->
                   try
                     Some (find_some
                             (fun (j, t1, t2, lc) ->
                                if j = i then Some t2 else None)
                             chiK_pos)
                   with Not_found -> None)
                brs0 in
            let pms =
              find_some
                (function
                  | Eqty (v, tpar, lc) when v = tdelta' ->
                    Some (Eqty (pv, tpar, lc))
                  | _ -> None)
                (snd (List.assoc i rol)) in
            i, ([], [pms])
          with Not_found -> i, ([], []))
        rol in
    let g_par = get_g_par rol1 in
    (*[* Format.printf
      "solve: substituting postconds at step 1@\n%!"; *]*)
    let brs1 = sb_brs_PredB q rol1 g_par brs0 in
    (* Collect all relevant constraints together. *)
    let verif_brs = map_some
        (fun (nonrec, chi_pos, chiK, prem, _) ->
           let allconcl = concat_map
               (fun (_, _, _, prem2, concl2) ->
                  (*[* Format.printf
                    "solve-verif_brs: subformula? %b@\nprem2=%a@\nprem=%a@\n%!"
                    (subformula prem2 prem)
                    pr_formula prem2 pr_formula prem; *]*)
                  if subformula prem2 prem
                  then concl2 else [])
               brs1 in
           (* Even though a correct program should not have dead
              cases other than dead code -- [prem] unsatisfiable --
              it does not make sense to keep dead cases for validation. *)
           let dead_case =
             try
               ignore
                 (satisfiable q ([], NumS.empty_state)
                    (prem @ allconcl));
               false
             with Contradiction _ (*[* as e *]*) ->
               (*[* Format.printf
                 "verif_brs: dead premise case: prem=@ %a@\nallconcl=@ \
                  %a@\nexc=@ %a@\n%!"
                 pr_formula prem pr_formula allconcl pr_exception e; *]*)
               true in
           if dead_case then None
           else
             Some (nonrec, chi_pos, chiK, prem, allconcl))
        brs1 in
    (*[* Format.printf "solve: loop iter_no=%d@\nsol=@ %a@\n%!"
      iter_no pr_chi_subst sol1; *]*)
    (*[* Format.printf "brs=@ %a@\n%!" Infer.pr_rbrs5 brs1; *]*)
    (* Guard to prune postconditions. *)
    (* FIXME: is here the right place to collect it, or after
       variable lifting? *)
    let guard = concat_map
        (fun (_,(_,cnj)) -> cnj) sol1 in
    let initstep = iter_no < disj_step.(2) in
    let sol1, brs1, abdsjelim, dissoc_abdsj, g_rol, g_rol_brs =
      if iter_no < disj_step.(0)
      then sol1, brs1, [], false, rol1,
           List.map (fun (i, ans) -> i, ans, []) rol1
      else
        (* 2 *)
        (* The [t2] arguments should become equal in the solution! *)
        let g_collect broad =
          collect
            (concat_map
               (fun (nonrec, chi_pos, chiK_pos, prem, concl) ->
                  if nonrec || broad
                  then
                    List.map
                      (fun (i,t1,t2,lc) ->
                         let phi =
                           Eqty (tdelta, t1, lc) :: prem @ concl in
                         (*[* Format.printf
                           "chiK: i=%d@ t1=%a@ t2=%a@ prem=%a@\nphi=%a@\n%!"
                           i pr_ty t1 pr_ty t2
                           pr_formula prem pr_formula phi;
                          *]*)
                         i, (prem, phi))
                      chiK_pos
                      (*[* else if chiK_pos <> [] then (
                        Format.printf "chiK: skipped %a@\n%!" pr_ints
                          (ints_of_list
                             (List.map (fun (i,_,_,_) -> i)
                                chiK_pos)); []) *]*)
                  else [])
               verif_brs) in
        let g_rol = g_collect (disj_step.(2) <= iter_no) in
        (*[* Format.printf
          "g_rol: g_collect keys %a@\n%!"
          pr_ints (ints_of_list (List.map fst g_rol)); *]*)
        let g_rol_all =
          if iter_no < disj_step.(2) then lazy (g_collect true)
          else lazy [] in
        (* 2 *)
        (* let dsj_preserve exchi =
           let exty = Hashtbl.find exty_of_chi exchi in
           try
            let chi = Hashtbl.find exty_res_chi exty in
            let _, ans = List.assoc chi sol1 in
            fvs_formula ans
           with Not_found -> VarSet.empty in *)
        let bvs = bparams iter_no in    (* for [disjelim] *)
        let abdsjelim = ref [] in
        let dissoc_abdsj = ref false in
        let g_rol_brs = List.map
            (fun (i, (_, old_ans)) ->
               let anchor =
                 try Hashtbl.find q.chiK_anchor i
                 with Not_found -> assert false in
               (*[* Format.printf
                 "solve: iter_no=%d approaching disjelim for %d, \
                  #brs=%d of %d, anchor=%s@\n%!" iter_no i
                 (try List.length (List.assoc i g_rol)
                  with Not_found -> 0)
                 (try List.length (List.assoc i (Lazy.force g_rol_all))
                  with Not_found -> 0) (var_str anchor); *]*)
               try
                 (*let old_delta =
                   try
                     Some
                       (find_some
                          (function
                            | Eqty (TVar v, t, _) when v = delta -> Some t
                            | Eqty (t, TVar v, _) when v = delta -> Some t
                            | _ -> None) old_ans)
                   with Not_found -> None in*)
                 let cnjs =
                   try List.assoc i g_rol
                   with Not_found -> List.assoc i (Lazy.force g_rol_all) in
                 (* let preserve =
                    VarSet.add delta (dsj_preserve i) in *)
                 let param_bvs =
                   VarSet.filter
                     (fun v ->
                        let b1 = try q.find_b_of_v v with Not_found -> v in
                        (*[*
                          Format.printf "@ v=%s b1=%s up=%b ren=%b,"
                          (var_str v) (var_str b1)
                          (upward_of b1 anchor) (q.param_renaming v); *]*)
                        upward_of b1 anchor && not (q.param_renaming v))
                     bvs in
                 (*[* Format.printf "@\n%!"; *]*)
                 (* [usb] is additional abductive the answer. *)
                 let up_of_anchor v = upward_of v anchor in
                 let dissoc, g_abd, (g_vs, g_ans), g_brs =
                   DisjElim.disjelim q_ops (* ?old_delta *)
                     ~bvs ~param_bvs (* ~preserve *)
                     ~up_of_anchor
                     ~do_num:(disj_step.(1) <= iter_no)
                     ~guess:((iter_no < disj_step.(3)))
                     ~initstep
                     ~residuum:(if !use_solution_in_postcond
                                then ans1_res else []) cnjs in
                 dissoc_abdsj := !dissoc_abdsj || dissoc;
                 (*[* Format.printf
                   "solve-3: disjelim pre-simpl g_ans=%a@\n%!"
                   pr_formula g_ans; *]*)
                 abdsjelim := g_abd @ !abdsjelim;
                 let ans = g_vs, g_ans in
                 i,
                 (* FIXME: unnecessary? *)
                 (if initstep
                  then connected [delta] ans
                  else ans),
                 g_brs
               with Not_found ->
                 (*[* Format.printf
                   "solve: disjelim branches for %d not found [2]@\n%!"
                   i; *]*)
                 i, ([], []), [])
            rol1 in
        (*[* let g_rol = List.map
            (fun (i, ans, _) -> i, ans) g_rol_brs in *]*)
        let abdsjelim = List.filter
            (* eliminate old parameter tracking *)
            (function
              | Eqty (TVar v, TCons (cn, _), _) when cn = tuple ->
                not (Hashtbl.mem tpar_vs v)
              | _ -> true)
            !abdsjelim in
        (*[* Format.printf
          "solve: iter_no=%d@\nabdsjelim=%a@\n@\ng_rol.A=%a@\n%!"
          iter_no pr_formula abdsjelim pr_chi_subst g_rol;
         *]*)
        (* 4a *)
        (* Collected invariants, for filtering postconditions. *)
        let lift_ex_types cmp_v i (g_vs, g_ans) =
          (* let keepvs =
             add_vars [delta; delta'] (VarSet.union localvs bvs) in *)
          (*[* Format.printf
            "lift_ex_types: g_vs=%a@ init g_ans=%a@\n%!"
            pr_vars (vars_of_list g_vs) pr_formula g_ans;
           *]*)
          (* 3 *)
          let fvs = VarSet.diff (fvs_formula g_ans)
              (vars_of_list [delta; delta']) in
          let localvs = VarSet.inter (vars_of_list g_vs) fvs in
          let anchor =
            try Hashtbl.find q.chiK_anchor i
            with Not_found -> assert false in
          let pvs, e_vs = VarSet.partition
              (fun v -> upward_of v anchor) fvs in
          (* [e_vs] does not contain [chi_vs] while [fvs] may have
             eliminated variables. *)
          let pvs = VarSet.diff pvs localvs in
          let pvs = VarSet.elements pvs in
          (* FIXME: ensure universal variables are eliminated? *)
          let pvs, uvs = List.partition
              (fun v -> not (q.uni_v v) ||
                        VarSet.mem v bvs) pvs in
          let targs = List.map (fun v -> TVar v) pvs in
          let tpar = TCons (tuple, targs) in
          let phi =
            Eqty (tdelta', tpar, dummy_loc)
            :: g_ans in
          (*[* Format.printf
            "lift_ex_types: anchor=%s@ fvs=%a@ pvs=%a@ uvs=%a@ tpar=%a@ \
             g_ans=%a@ e_vs=%a@ phi=%a@\n%!" (var_str anchor)
            pr_vars fvs pr_vars (vars_of_list pvs) pr_vars (vars_of_list uvs)
            pr_ty tpar pr_formula g_ans pr_vars e_vs pr_formula phi;
           *]*)
          (* FIXME: g_vs should be ignored? *)
          tpar, (VarSet.elements e_vs, phi) in
        (* 4b *)
        let rn_sb, g_rol = rev_fold_map2
            (fun rn_acc (i, ans1) (j, ans2, g_brs) ->
               assert (i = j);
               (*[* Format.printf
                 "solve.loop-dK: i=%d@\nrn_acc=%a@\n%!" i
                 pr_subst rn_acc; *]*)
               let ans2 = map_snd (subst_formula rn_acc) ans2 in
               let _ (* tpar *), ans2 = lift_ex_types q.op i ans2 in
               let rn_sb, tpar, ans2 =
                 converge q.op ~guard
                   ~initstep
                   ~check_only:(iter_no < disj_step.(4)) ans1 ans2 in
               (*[* Format.printf "solve.loop-dK: final@ tpar=%a@ ans2=%a@\n%!"
                 pr_ty tpar pr_ans ans2; *]*)
               (* No [b] "owns" these formal parameters. Their instances
                  will be added to [q] by [sb_brs_pred]. *)
               rn_sb @ rn_acc, ((i, tpar), (i, ans2, g_brs)))
            [] (List.rev rol1) (List.rev g_rol_brs) in
        let tpars, g_rol_brs = List.split g_rol in
        let g_rol_brs = List.map
            (fun (i, ans2, g_brs) ->
               let g_brs = List.map (subst_formula rn_sb) g_brs in
               i, ans2, g_brs) g_rol_brs in
        let g_rol = List.map (fun (i, ans2, _) -> i, ans2) g_rol_brs in
        (* FIXME: recheck this definition of [g_par] *)
        let g_par = get_g_par g_rol in
        (*[* Format.printf
          "solve: loop iter_no=%d@ g_par=%a@\ng_rol.B=@ %a@\n%!"
          iter_no pr_chi_subst g_par pr_chi_subst g_rol; *]*)
        (* 5 *)
        let esb = List.map
            (fun (i, tpar) ->
               let n = Extype (Hashtbl.find exty_of_chi i) in
               n, fun old ->
                 (*[* Format.printf "esb-6: old=%a new=%a@\n%!"
                   pr_ty (TCons (n, old))
                   pr_ty (TCons (n, [tpar])); *]*)
                 TCons (n, [tpar]))
            tpars in
        let esb_formula = List.map
            (function
              | Eqty (t1, t2, lc) ->
                Eqty (n_subst_typ esb t1, n_subst_typ esb t2, lc)
              | a -> a) in
        let sol1 = List.map
            (fun (i, (vs, old_phi)) ->
               let recover_escaping =
                 try Hashtbl.find q.recover_escaping i
                 with Not_found -> [] in
               let phi = subst_formula recover_escaping
                   (esb_formula old_phi) in
               let b =
                 try List.find (not % q.positive_b) (q.find_b i)
                 with Not_found -> assert false in
               let fvs = VarSet.elements
                   (VarSet.diff (fvs_formula phi)
                      (vars_of_list (delta::delta'::vs))) in
               let ibvs = Hashtbl.find q.b_vs b in
               (* Restored parameters. *)
               let rvs = List.filter
                   (fun v -> VarSet.mem v ibvs && not (List.mem v vs))
                   fvs in
               let nvs = List.filter
                   (fun v -> q.cmp_v b v = Left_of) fvs in
               let nvs = List.map (fun v -> v, freshen_var v) nvs in
               let escaping_sb = renaming_sb nvs in
               Hashtbl.replace q.recover_escaping
                 i (escaping_sb @ recover_escaping);
               let phi = subst_formula escaping_sb phi in
               (*[* Format.printf
                 "lift-params: i=%d@ vs=%a@ fvs=%a@ nvs=%a@ \
                  phi=%a@ phi'=%a@\n%!"
                 i pr_vars (vars_of_list vs)
                 pr_vars (vars_of_list fvs)
                 pr_vars (vars_of_list (List.map snd nvs)) pr_formula old_phi
                 pr_formula phi; *]*)
               if nvs <> [] then q.add_b_vs_of b nvs;
               i, (List.map snd nvs @ rvs @ vs, phi))
            sol1 in
        (*[* Format.printf
          "solve: substituting invariants at step 5@\n%!"; *]*)
        let brs0 = sb_brs_PredU q sol1 brs in
        (*[* Format.printf
          "solve: substituting postconds at step 5@\n%!"; *]*)
        let brs1 = sb_brs_PredB q g_rol g_par brs0 in
        sol1, brs1, abdsjelim, !dissoc_abdsj, g_rol, g_rol_brs in
    (*[* Format.printf
      "solve-loop: iter_no=%d -- ex. brs substituted@\n%!"
      iter_no; *]*)
    (*[* Format.printf "brs=@ %a@\n%!" Infer.pr_rbrs5 brs1; *]*)
    (* 7a *)
    let neg_cns1 = List.map
        (fun (prem,loc) -> sb_formula_pred q false g_rol sol1 prem, loc)
        neg_cns in
    let bvs = bparams iter_no in
    let recbvs = q.get_recbvs () in
    let early_chiKbs =
      if iter_no>0 || !early_postcond_abd then VarSet.empty
      else VarSet.diff (bparams 1) bvs in
    (* 6 *)
    let brs1 = List.map
        (fun (nonrec, chi_pos, _, prem, concl) ->
           let chi_pos = List.map
               (fun (i, t) ->
                  match t with
                  | TVar b ->
                    (try
                       let vs, _ = List.assoc i sol1 in
                       let renaming =
                         matchup_vars ~self_owned:false q b vs in
                       (*[* Format.printf
                         "sb_chi_pos: chi%d(%s)@ lvs=%a;@ rvs=%a@\n%!"
                         i (var_str b)
                         pr_vars (vars_of_list (List.map fst renaming))
                         pr_vars (vars_of_list (List.map snd renaming));
                        *]*)
                       i, renaming
                     with Not_found -> i, [])
                  | _ -> assert false)
               chi_pos in
           let concl =
             if iter_no>0 || !early_postcond_abd then concl
             else
               List.filter
                 (fun a->VarSet.is_empty
                     (VarSet.inter (fvs_atom a) early_chiKbs))
                 concl in
           nonrec, chi_pos, prem, concl) brs1 in
    let brs1 =
      if abdsjelim=[] then brs1
      else (true, [], [], abdsjelim)::brs1 in
    let xbvs = Hashtbl.fold
        (fun x xvs acc ->
           if q.positive_b x then acc
           else (q.find_chi x, xvs)::acc)
        q.b_vs [] in
    let answer =
      try
        let cand_bvs, alien_eqs, (vs, ans) =
          Abduction.abd q.op ~bvs ~xbvs ~upward_of ~iter_no
            ~discard brs1 neg_cns1 in
        (*[* Format.printf
          "solve: iter_no=%d abd answer=@ %a@\n%!"
          iter_no pr_formula ans; *]*)
        (* 7b *)
        (* Check negative constraints ("assert false" clauses) once
           all positive constraints have been involved in answering. *)
        if !neg_constrns && iter_no > 1 then List.iter
            (* raise [NoAnswer] when needed *)
            (fun (cnj, loc) ->
               try
                 (*[* Format.printf "neg_cl_check: cnj=@ %a@\n%!" pr_formula
                   cnj; *]*)
                 let {cnj_typ=ty_cn; cnj_num=num_cn; cnj_so=_} =
                   unify ~use_quants:false q.op (ans @ cnj) in
                 if num_cn = [] then (
                   (*[* Format.printf
                     "neg_cl_check: fallback typ@ ty_cn=@ %a@\n%!"
                     pr_subst ty_cn; *]*)
                   raise
                     (NoAnswer (Type_sort, "negative clause", None, loc)));
                 if Aux.is_right (NumS.satisfiable num_cn) then (
                   (*[* Format.printf
                     "neg_cl_check: fallback num@ num_cn=@ %a@\n%!"
                     NumDefs.pr_formula num_cn; *]*)
                   raise
                     (NoAnswer (Num_sort,
                                "negative clause", None, loc)));
                 (*[* Format.printf
                   "neg_cl_check: passed (num)@ ty_cn=@ %a@\nnum_cn=@ %a@\n%!"
                   pr_subst ty_cn NumDefs.pr_formula num_cn; *]*)
               with Contradiction _ (*[*as e*]*) ->
                 (*[* Format.printf
                   "neg_cl_check: passed (typ) by contradicting=@\n%a@\n%!"
                   pr_exception e; *]*)
                 ())
            neg_cns1;
        let ans_res, more_discard, ans_sol =
          split (iter_no>0 || !early_postcond_abd)
            ~avs:vs ans negchi_locs ~bvs ~cand_bvs q in
        (*[* Format.printf
          "solve: loop -- answer split@ more_discard=@ %a@\nans_res=@ %a@\n%!"
          pr_formula more_discard pr_formula ans_res; *]*)
        Aux.Right (alien_eqs, ans_res, more_discard, ans_sol)
      with
      (* it does not seem to make a difference *)
      | (NoAnswer (sort, msg, tys, lc)
        | Contradiction (sort, msg, tys, lc)) as e ->
        (*[* Format.printf
          "Fallback: iter_no=%d; sort=%s;@ error=@\n%a@\n%!"
          iter_no (sort_str sort) pr_exception e;
         *]*)
        Aux.Left (sort, e) in
    match answer with
    | Aux.Left _ as e -> e
    | Aux.Right (alien_eqs, ans_res, more_discard, ans_sol) ->
      let more_discard =
        if alien_eqs = [] then more_discard
        else subst_formula alien_eqs more_discard in
      (* 11 *)
      let finish rol2 sol2 =
        (* start fresh at (iter_no+1) *)
        match loop (iter_no+1)
                (if !use_prior_discards then discard else empty_dl)
                rol2 sol2 ans_res
        with Aux.Right _ as res -> res
           | Aux.Left (sort, e) ->
             (*[* Format.printf
               "solve-finish: fallback call iter_no=%d sort=%s@\ndisc=%a@\n%!"
               iter_no (sort_str sort) pr_formula more_discard; *]*)
             let sort, s_discard =
               let s_discard = sep_formulas more_discard in
               (* The complication is because we do not always do
                  alien subterm dissociation. *)
               let disc =
                 match sort with
                 | Type_sort ->
                   (* Abduction answer variables do not have an
                      effect on checking the discard list anyway. *)
                   {empty_disc with at_typ=[],s_discard.cnj_typ}
                 | Num_sort ->
                   {empty_disc with at_num=s_discard.cnj_num}
                 | Order_sort ->
                   {empty_disc with at_ord=s_discard.cnj_ord} in
               (*[* Format.printf
                 "solve-finish: sep_disc.typ=%a@ \
                  sep_disc.num=%a@\n%!" pr_subst s_discard.cnj_typ
                 NumDefs.pr_formula s_discard.cnj_num; *]*)
               if disc <> empty_disc || sort <> Type_sort
               then sort, disc
               else if s_discard.cnj_num <> []
               then Num_sort, {empty_disc with at_num=s_discard.cnj_num}
               else sort, empty_disc in
             if s_discard = empty_disc then (
               (*[* Format.printf
                 "solve-finish: fallback has no discard@\ndisc.typ=%a@ \
                  disc.num=%a@\n%!" pr_subst (snd s_discard.at_typ)
                 NumDefs.pr_formula s_discard.at_num; *]*)
               raise e);
             (*[* Format.printf
               "solve-finish: ultimately sort=%s@ disc_ty=%a@ disc_num=%a@\n%!"
               (sort_str sort) pr_subst (snd s_discard.at_typ)
               NumDefs.pr_formula s_discard.at_num; *]*)
             let discard =
               match sort with
               | Type_sort ->
                 {discard with at_typ=s_discard.at_typ::discard.at_typ}
               | Num_sort ->
                 {discard with at_num=s_discard.at_num::discard.at_num}
               | Order_sort ->
                 {discard with at_ord=s_discard.at_ord::discard.at_ord} in
             loop iter_no discard rol1 sol1 ans_res in
      (* 7-8 *)
      (* Avoid substituting [bvs] -- treat them like leftmost. *)
      let ans_sb, _ =
        let cmp_v v1 v2 =
          let c1 = VarSet.mem v1 bvs and c2 = VarSet.mem v2 bvs in
          if c1 && c2 then Same_quant
          else if c1 then Left_of
          else if c2 then Right_of
          else q.op.Defs.cmp_v v1 v2 in
        let q_op = {q.op with cmp_v} in
        (* FIXME: after splitting there are more bvs? *)
        Infer.separate_subst ~avoid:bvs ~bvs ~apply:false q_op ans_res in
      (* Do not substitute in postconditions -- they do not have free
                 variables! *)
      unfinished_postcond_flag := false;
      let unfinished_postcond = ref [] in
      let postcond_forcing = ref [] in
      let rol2 =
        if disj_step.(0) > iter_no then rol1
        else
          List.map
            (fun (i, (gvs, g_ans), g_brs) ->
               (* FIXME: code duplication with [lift_ex_types]? *)
               let tpar, g_ans = List.partition
                   (function
                     | Eqty (tv, tpar, _) when tv = tdelta' -> true
                     | _ -> false)
                   g_ans in
               (*[* Format.printf "solve-loop-9:@ g_ans=%a@\n%!"
                 pr_formula g_ans; *]*)
               let tpar =
                 match tpar with
                 | [Eqty (tv, tpar, _)] -> tpar
                 | [] -> assert false
                 | _::_ -> assert false in
               let source =
                 try
                   Some
                     (List.find
                        (function
                          | Eqty (tv, _, _) when tv = tdelta -> true
                          | Eqty (_, tv, _) when tv = tdelta -> true
                          | _ -> false)
                        g_ans)
                 with Not_found -> None in
               let source, source_vs =
                 match source with
                 | Some (Eqty (tv, source, lc)) when tv = tdelta ->
                   Some (lc, source), fvs_typ source
                 | Some (Eqty (source, tv, lc)) when tv = tdelta ->
                   Some (lc, source), fvs_typ source
                 | _ -> None, VarSet.empty in
               let bs =
                 if iter_no=0 && not !early_postcond_abd then []
                 else List.filter (not % q.positive_b) (q.find_b i) in
               let ds = List.map (fun b-> b, List.assoc b ans_sol) bs in
               let dans = List.map
                   (fun (b, (dvs, dans)) ->
                      (*[* Format.printf
                        "solve-loop-9: chi%d(%s)=@ %a@ +@ %a@\n%!"
                        i (var_str b) pr_ans (dvs,dans) pr_ans
                        (gvs,g_ans); *]*)
                      let target, dans = List.partition
                          (function
                            | Eqty (tv, _, _) when tv = TVar b -> true
                            | Eqty (_, tv, _) when tv = TVar b -> true
                            | _ -> false)
                          dans in
                      let target =
                        match target with
                        | [Eqty (tv, target, lc)] when tv = TVar b ->
                          Some (target, lc)
                        | [Eqty (target, tv, lc)] when tv = TVar b ->
                          Some (target, lc)
                        | [] -> None
                        | _::_ -> assert false in
                      (* No need to substitute, because variables will be
                         freshened when predicate variable is instantiated. *)
                      let sb =
                        (* FIXME: what does this b_renaming do? *)
                        List.map (fun (v,w) -> w,v)
                          (Hashtbl.find q.b_renaming b) in
                      let sb = List.filter (fun (v, w) -> v <> w) sb in
                      let sb = renaming_sb ((b, delta)::sb) in
                      let sb, dans =
                        match source, target with
                        | None, _ | _, None -> sb, dans
                        | Some (source_lc, source), Some (target, lc) ->
                          let target_cnj =
                            unify ~use_quants:false ~sb q.op
                              [Eqty (target, source, lc)] in
                          let sb, more_dans = Infer.separate_sep_subst
                              ~keep_uni:true ~apply:true q.op target_cnj in
                          let more_cnj =
                            to_formula
                              (List.filter
                                 (fun (v, _) -> VarSet.mem v source_vs)
                                 sb) in
                          (*[* Format.printf
                            "solve-loop-9: target=%a@\ntarget_cnj=%a@\n%!"
                            pr_ty target pr_formula
                            (unsep_formulas target_cnj); *]*)
                          sb,
                          more_cnj @ unsep_formulas more_dans @ dans in
                      (*[* Format.printf
                        "solve-loop-9: renaming=@ %a@\ndans'=%a@\n%!"
                        pr_subst sb pr_formula (subst_formula sb dans); *]*)
                      let dvs = List.filter
                          (fun v -> not (List.mem_assoc v sb)) dvs in
                      dvs, subst_formula sb dans)
                   ds in
               let dvs, dans = List.split dans in
               let dvs = gvs @ List.concat dvs in
               let dans = List.concat dans in
               if dans <> [] then (
                 unfinished_postcond_flag := true;
                 unfinished_postcond := dans @ !unfinished_postcond;
                 let dvs = vars_of_list dvs in
                 (* Some redone work because we want the answer prior
                    to variable renaming. *)
                 (*[* Format.printf
                   "postcond-forced: dvs=%a@ dans=@ %a@\n%!"
                   pr_vars dvs pr_formula dans; *]*)
                 let uvs = VarSet.diff dvs recbvs in
                 let q' = modify_q ~uni_vars:uvs q in
                 let brs = List.map
                     (fun br ->
                        let br_vs = fvs_formula br in
                        let b_ans = List.filter
                            (fun c -> var_subset (fvs_atom c) br_vs)
                            dans in
                        false, [], br, b_ans) g_brs in
                 (*[* Format.printf
                   "Invariants: iter_no=%d postcond-forced \
                    abduction:@\n%!" iter_no; *]*)
                 let _, alien_eqs, (vs, dans_ans) =
                   Abduction.abd q'.op ~bvs:recbvs ~xbvs ~upward_of ~iter_no
                     ~discard brs [] in
                 assert (alien_eqs = []); assert (vs = []);
                 postcond_forcing := dans_ans @ !postcond_forcing);
               let pvs = fvs_typ tpar in
               (* TODO: the precautionary step seems unnecessary:
                  localvs=dvs. *)
               let localvs = VarSet.diff (vars_of_list dvs) pvs in
               (*[* Format.printf
                 "solve-loop-9: localvs=%a;@ pvs=%a; iter_no=%d@\n%!"
                 pr_vars localvs pr_vars pvs iter_no; *]*)
               let vs = VarSet.elements localvs in
               let ans = dans @ g_ans in
               let pvs = VarSet.elements pvs in
               let vs = vs @ pvs in
               (* FIXME: are generalization variables impossible in tpar'? *)
               let targs =
                 List.map (fun v -> TVar v) pvs in
               let tpar' = TCons (tuple, targs) in
               let i_res = vs, Eqty (tdelta', tpar', dummy_loc) :: ans in
               (*[* Format.printf
                 "solve-loop: pvs=%a@ dvs=%a@ vs=%a dans=%a@ chi%d(.)=@ %a@\n%!"
                 pr_vars (vars_of_list pvs) pr_vars (vars_of_list dvs)
                 pr_vars (vars_of_list vs)
                 pr_formula dans i pr_ans i_res; *]*)
               i, i_res)
            g_rol_brs in
      (* 8-9 *)
      (*[* Format.printf "postcond-forced: split@\n%!"; *]*)
      let ans_res', more_discard', ans_sol' =
        split false ~avs:[] !postcond_forcing negchi_locs
          ~bvs:recbvs ~cand_bvs:recbvs q in
      assert (ans_res' = []);
      (* 9 *)
      let sol2 = List.map
          (fun (i, (vs, ans)) ->
             (* This is supposed to substitute parent-context
                 answers. FIXME: verify formally. *)
             let ans = subst_formula ans_sb ans in
             let bs = List.filter (not % q.positive_b) (q.find_b i) in
             let b = match bs with [b] -> b | _ -> assert false in
             let dvs, dans = List.assoc b ans_sol in
             let _, g_ans = List.assoc b ans_sol' in
             (*[* Format.printf
               "solve-loop-10: chi%d(%s)=@ %a@ +@ %a@\n%!"
               i (var_str b) pr_ans (dvs,dans) pr_ans (vs,ans); *]*)
             (* No need to substitute, because variables will be
                freshened when predicate variable is instantiated. *)
             let dans = subst_formula [b, (tdelta, dummy_loc)] dans in
             let vs' = dvs @ vs in
             (* FIXME: perhaps filter-out atoms contained upstream *)
             (* FIXME: after splitting there are more bvs? *)
             let sb, (_, ans') = simplify q.op ~bvs
                 (vs', g_ans @ dans @ ans) in
             (*[* Format.printf
               "solve-loop-10: vs=%a@ ans=%a@ chi%d(.)=@ %a@\n%!"
               pr_vars (vars_of_list vs) pr_formula ans i
               pr_ans (vs', ans'); *]*)
             sb, (i, (vs', ans')))
          sol1 in
      let new_sbs, sol2 = List.split sol2 in
      (* FIXME: is it possible to have non-disjoint domains of [new_sbs]? *)
      let new_sb = List.concat new_sbs in
      (*[* Format.printf "Invariants.new_sb=%a@\n%!" pr_subst new_sb; *]*)
      let sol2 = List.map
          (fun (i, (vs, ans)) ->
             let ans = subst_formula new_sb ans in
             let ans_vs = fvs_formula ans in
             let vs = List.filter (fun v->VarSet.mem v ans_vs) vs in
             i, (vs, ans))
          sol2 in
      (* 10 *)
      let finished1 =
        iter_no >= 1 && List.for_all2
          (fun (i,(_,ans2)) (j,(_,ans1)) -> assert (i=j);
            (*[* Format.printf
              "solve-finished: comparing X%d@\nans2=%a@\nans1=%a@\n\
               subformula=%b@\n%!"
              i pr_formula ans2 pr_formula ans1 (subformula ans2 ans1); *]*)
            subformula ans2 ans1)
          sol2 sol1 in
      let finished2 =
        List.for_all2
          (fun (i,(_,ans2)) (j,(_,ans1)) -> assert (i=j);
            (*[* Format.printf
              "solve-finished: comparing ex.2>1 X%d@\nans2=%a@\n\
               ans1=%a@\nsubformula=%b@\n%!"
              i pr_formula ans2 pr_formula ans1 (subformula ans2 ans1); *]*)
            subformula ans2 ans1)
          rol2 rol1 in
      let finished3 =
        List.for_all2
          (fun (i,(_,ans1)) (j,(_,ans2)) -> assert (i=j);
            (*[* Format.printf
              "solve-finished: comparing ex.1>2 X%d@\nans2=%a@\n\
               ans1=%a@\nsubformula=%b@\n%!"
              i pr_formula ans2 pr_formula ans1 (subformula ans1 ans2); *]*)
            subformula ans1 ans2)
          rol1 rol2 in
      let finished = not dissoc_abdsj && not !unfinished_postcond_flag &&
                     finished1 && finished2 && finished3 in
      (*[* Format.printf "solve-loop: dissoc_abdsj=%b \
                           finished 1=%b, 2=%b, 3=%b, r=%b@\n%!"
        dissoc_abdsj finished1 finished2 finished3 finished; *]*)
      if iter_no >= disj_step.(2) && finished
      then                              (* final solution *)
        Aux.Right (ans_res, rol2, sol2)
        (* Do at least three iterations: 0, 1, 2. *)
      else if iter_no <= 1 && finished
      then loop (iter_no+1)
          (if !use_prior_discards then discard else empty_dl)
          rol2 sol1 ans_res
      else if iter_no >= !timeout_count
      then
        let unfinished1 =
          concat_map2
            (fun (i,(_,ans2)) (j,(_,ans1)) ->
               formula_diff ans2 ans1)
            sol2 sol1 in
        let unfinished2 =
          concat_map2
            (fun (i,(_,ans2)) (j,(_,ans1)) ->
               formula_diff ans2 ans1)
            rol2 rol1 in
        let unfinished3 =
          concat_map2
            (fun (i,(_,ans1)) (j,(_,ans2)) ->
               formula_diff ans1 ans2)
            rol1 rol2 in
        (*[* Format.printf
          "solve-loop: unfinished!@\nunf1=%a@\nunf2=%a@\nunf3=%a@\n%!"
          pr_formula unfinished1 pr_formula unfinished2
          pr_formula unfinished3; *]*)
        let loc = formula_loc
            (!unfinished_postcond @
               unfinished1 @ unfinished2 @ unfinished3) in
        timeout_flag := true;
        raise (NoAnswer (Type_sort, "Answers do not converge", None, loc))
      else finish rol2 sol2 in
  match loop 0 empty_dl rolT solT [] with
  | Aux.Left (_, e) -> raise e
  | Aux.Right (ans_res, rol, sol) ->
    (*[* Format.printf "solve: checking assert false@\n%!"; *]*)
    List.iter (fun (cnj, loc) ->
        try
          let cnj = sb_formula_pred q false rol sol cnj in
          (* FIXME: rethink. *)
          ignore (satisfiable q empty_state cnj);
          raise (Contradiction (
              (* FIXME *) Type_sort,
                          "A branch with \"assert false\" is possible",
                          None, loc))
        with Contradiction _ -> ()
      ) neg_cns;
    let bvs = bparams !timeout_count in
    (* Push parameters to the right so that they are kept in answers. *)
    let q_op =
      let cmp_v v1 v2 =
        let c1 = VarSet.mem v1 bvs and c2 = VarSet.mem v2 bvs in
        if c1 && c2 then Same_quant
        else if c1 then Left_of
        else if c2 then Right_of
        else q.op.Defs.cmp_v v1 v2 in
      {q.op with cmp_v} in
    let ans_sb, _ =
      Infer.separate_subst ~bvs ~apply:false q_op ans_res in
    (*[* Format.printf "solve: final@\nans_res=%a@\nans_sb=%a@\n%!"
      pr_formula ans_res pr_subst ans_sb;
     *]*)
    (* Substitute the solutions for existential types. *)
    let etys_sb = List.map
        (fun (ex_i,_) ->
           let n = Extype ex_i in
           n, (function
               | [TCons (t, args)] when t=tuple -> TCons (n, args)
               | targs -> TCons (n, targs)))
        new_ex_types in
    let esb_formula = List.map
        (function
          | Eqty (t1, t2, lc) ->
            Eqty (n_subst_typ etys_sb t1, n_subst_typ etys_sb t2, lc)
          | a -> a) in
    let esb_ans (i, (vs, ans)) =
      i, (vs, esb_formula ans) in
    let ans_res = esb_formula ans_res in
    (*[* Format.printf "solve: final@\nans_res'=%a@\n%!"
      pr_formula ans_res; *]*)
    let sol = List.map esb_ans sol in
    List.iter
      (fun (ex_i, loc) ->
         let _, exphi, ty, _, pvs = Hashtbl.find sigma (Extype ex_i) in
         let ty = match ty with [ty] -> ty | _ -> assert false in
         let chi_i, t1, t2 =
           match exphi with
           | PredVarB (chi_i,t1,t2,_) :: _ -> chi_i, t1, t2
           | _ -> assert false in
         assert (ty = t1 && t1 = tdelta);
         assert (t2 = tdelta' && pvs = [delta']);
         let chi_vs, phi =
           try List.assoc chi_i rol
           with Not_found ->
             (* FIXME *)
             (*[* Format.printf
               "solve-new_ex_types: chi_i=%d out of %s@\n%!"
               chi_i (String.concat ","
                        (List.map (string_of_int % fst) rol)); *]*)
             [], [] in
         let sb, rphi =
           Infer.separate_subst ~bvs:(vars_of_list (chi_vs @ pvs))
             ~apply:true q_op phi in
         let sb = update_sb ~more_sb:ans_sb sb in
         let sb = List.map
             (function
               | v, (TVar v2, lc) when v2=delta || v2=delta' ->
                 v2, (TVar v, lc)
               | sv -> sv) sb in
         (* FIXME: shouln't we propagate [sb] to other answers? *)
         let rty = subst_typ sb ty
         and rphi = subst_formula sb rphi in
         (* FIXME: We ignore the "predicted" parameters and instead
            collect the free variables as actual parameters. *)
         let pvs =
           try
             match fst (List.assoc delta' sb) with
             | TCons (t, args) when t=tuple ->
               concat_map
                 (fun a -> VarSet.elements (fvs_typ a)) args
             | t -> VarSet.elements (fvs_typ t)
           with Not_found -> [delta'] in
         let allvs = VarSet.union (fvs_formula rphi) (fvs_typ rty) in
         (*[* Format.printf
           "solve-ex_types: ex_i=%d@ t1=%a@ t2=%a@ ty=%a@ chi_vs=%a@ rty=%a@ allvs=%a@ pvs=%a@ rphi=%a@ @\nphi=%a@\n%!"
           ex_i pr_ty t1 pr_ty t2 pr_ty ty
           pr_vars (vars_of_list chi_vs) pr_ty rty
           pr_vars allvs pr_vars (vars_of_list pvs)
           pr_formula rphi pr_formula phi;
          *]*)
         let ety_n = Extype ex_i in
         Hashtbl.replace sigma ety_n
           (VarSet.elements allvs, rphi, [rty], ety_n, pvs)) new_ex_types;
    (*[* Format.printf "solve: returning@\n%!"; *]*)
    q.op, ans_res, sol
