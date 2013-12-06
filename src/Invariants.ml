(** Solving second-order i.e. formula variables for InvarGenT.

    Released under the GNU General Public Licence (version 2 or
    higher), NO WARRANTY of correctness etc. (C) Lukasz Stafiniak 2013
    @author Lukasz Stafiniak lukstafi (AT) gmail.com
    @since Mar 2013
*)
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
  find_b : int -> var_name list;
  find_chi : var_name -> int;
  mutable allbvs : VarSet.t;
  mutable allchi : Ints.t;
  mutable negbs : var_name list;
}
  
let new_q q_ops =
  let posi_b = Hashtbl.create 16 in
  let chiK_i = Hashtbl.create 16 in
  let positive_b v = Hashtbl.mem posi_b v in
  let is_chiK i = Hashtbl.mem chiK_i i in
  let b_vs = Hashtbl.create 16 in
  let b_renaming = Hashtbl.create 16 in
  let b_qvs = Hashtbl.create 16 in
  let chi_b = Hashtbl.create 16 in
  let b_chi = Hashtbl.create 16 in
  let find_b i = Hashtbl.find_all chi_b i in
  let find_chi b = Hashtbl.find b_chi b in
  let rec add_bchi b i ~posi ~chiK =
    if Hashtbl.mem b_chi b
    then (
      let old = Hashtbl.find b_chi b in
      (*[*) Format.printf "add_bchi: exist old=%d chi%d(%s);@ posi=%b@\n%!"
        old i (var_str b) posi; (*]*)
      assert (old = i)
    ) else (
      (*[*) Format.printf "add_bchi: chi%d(%s);@ posi=%b@\n%!"
        i (var_str b) posi; (*]*)
      if posi then Hashtbl.add posi_b b ()
      else q.negbs <- b::q.negbs;
      if chiK then Hashtbl.add chiK_i i ();
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
    List.iter (fun v -> q_ops.same_as v b) vs;
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
    add_b_vs_of; allchi = Ints.empty;
    b_vs; b_renaming; b_qvs; allbvs = VarSet.empty;
    add_bchi; find_b; find_chi; is_chiK;
    positive_b; negbs = [];
  } in q

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
    else List.map (fun v->v, Infer.freshen_var v) nvs in
  (*[*) Format.printf "matchup_vars: b=%s;@ vs=%s;@ orvs=%s;@ nrvs=%s@\n%!"
    (var_str b)
    (String.concat ", " (List.map var_str vs))
    (String.concat ", "
       (List.map (fun (v,w)->var_str v^":="^var_str w) orvs))
    (String.concat ", "
       (List.map (fun (v,w)->var_str v^":="^var_str w) nrvs)); (*]*)
  q.add_b_vs_of b nrvs;
  let res = nrvs @ orvs in
  (* [orvs] stores a [delta] substitution, [delta] is absent from [vs] *)
  renaming_sb res

let sb_atom_PredU q posi psb = function
  | PredVarU (i, (TVar b as t), loc) ->
    (try
       let vs, phi = List.assoc i psb in
       (*[*) Format.printf
         "sb_atom_pred: U posi=%b@ chi%d(%s)=@ %a@\n%!"
         posi i (var_str b) pr_ans (vs,phi); (*]*)
       let renaming = matchup_vars ~self_owned:(not posi) q b vs in
       replace_loc loc
         (sb_phi_unary t (subst_formula renaming phi))
     with Not_found ->
       (*[*) Format.printf
         "sb_atom_pred: Not_found U posi=%b@ chi%d(%s)@\n%!"
         posi i (var_str b); (*]*)
       [])  
  | PredVarB _ -> []
  | a -> [a]

let sb_formula_PredU q posi psb phi =
  concat_map (sb_atom_PredU q posi psb) phi

let sb_brs_PredU q sol brs = List.map
  (fun (nonrec,prem,concl) ->
    nonrec,
    Aux.map_some                        (* chiK_neg *)
      (function PredVarB (i,t1,t2,lc) -> Some (i,t1,t2,lc) | _ -> None) prem,
    Aux.map_some                        (* chiK_pos *)
      (function PredVarB (i,t1,t2,lc) -> Some (i,t1,t2,lc) | _ -> None) concl,
    Aux.map_some                        (* vK *)
      (function PredVarU (i,_,_) as a when q.is_chiK i -> Some a
              | _ -> None) concl,
    sb_formula_PredU q false sol prem,
    sb_formula_PredU q true sol concl)
  brs

let sb_PredB q psb (i, t1, t2, lc) =
  match t1 with TVar b ->
    (try
       let vs, phi = List.assoc i psb in
       (*[*) Format.printf
         "sb_chiK_neg: chi%d(%s,%a)=@ %a@\n%!"
         i (var_str b) (pr_ty false) t2 pr_ans (vs,phi); (*]*)
       let renaming = matchup_vars ~self_owned:false q b vs in
       replace_loc lc
         (sb_phi_binary t1 t2 (subst_formula renaming phi))
     with Not_found -> [])
  | _ -> []

let sb_brs_PredB q rol par brs = List.map
  (fun (nonrec,chiK_neg,chiK_pos,vK,prem,concl) ->
    nonrec,
    chiK_pos, vK,
    concat_map (sb_PredB q rol) chiK_neg @ prem,
    concat_map (sb_PredB q par) chiK_pos @ concl)
  brs

let sb_brs_vK q par brs = List.map
  (fun (nonrec,chiK_pos,vK,prem,concl) ->
    nonrec,
    chiK_pos, vK, prem,
    sb_formula_PredU q true par vK @ concl)
  brs

let sb_atom_pred q posi rol sol = function
  | PredVarU (i, (TVar b as t), loc) as a ->
    (try
       let vs, phi = List.assoc i sol in
       (*[*) Format.printf
         "sb_atom_pred: U posi=%b@ chi%d(%s)=@ %a@\n%!"
         posi i (var_str b) pr_ans (vs,phi); (*]*)
       let renaming = matchup_vars (not posi) q b vs in
       replace_loc loc
         (sb_phi_unary t (subst_formula renaming phi))
     with Not_found -> [a])  
  | PredVarB (i, (TVar b as t1), t2, loc) as a ->
    (try
       let vs, phi = List.assoc i rol in
       (*[*) Format.printf
         "sb_atom_pred: B posi=%b@ chi%d(%s,%a)=@ %a@\n%!"
         posi i (var_str b) (pr_ty false) t2 pr_ans (vs,phi); (*]*)
       let renaming = matchup_vars false q b vs in
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

let holds q avs (ty_st, num_st) cnj =
  let ty_st, num_cnj, _ =
    unify ~pms:avs ~sb:ty_st q.op cnj in
  let num_st = NumS.holds q.op avs num_st num_cnj in
  ty_st, num_st

let satisfiable q (ty_st, num_st) cnj =
  let ty_st, num_cnj, _ = unify ~use_quants:false ~sb:ty_st q.op cnj in
  let num_st =
    match NumS.satisfiable ~state:num_st num_cnj with
    | Right s -> s | Left e -> raise e in
  ty_st, num_st

(* 10 *)
let strat q b ans =
  let (_, ans_r), ans = fold_map
      (fun (pvs, ans_r) c ->
         let vs = VarSet.elements (VarSet.diff (fvs_atom c) pvs) in
         (* FIXME: after prenexization, this does not do much! *)
         let vs = List.filter
             (fun v -> q.cmp_v b v = Left_of) vs in
         let loc = atom_loc c in
         if List.exists q.uni_v vs then
           (let bad = List.find q.uni_v vs in
            raise (NoAnswer
                     (var_sort bad, "Escaping universal variable",
                      Some (TVar b, TVar bad), loc)));
         let avs = List.map Infer.freshen_var vs in
         let ans_r =
           List.map2 (fun a b -> b, (TVar a, loc)) avs vs @ ans_r in
         (VarSet.union pvs (vars_of_list vs), ans_r),
         (avs, subst_atom ans_r c))
      (VarSet.empty, []) ans in
  let avs, ans_l = List.split ans in
  List.concat avs, ans_l, ans_r
  
let split avs ans negchi_locs bvs cand_bvs q =
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
  let rec loop avs ans discard sol =
    (* 2 *)
    (*[*) Format.printf "split-loop: starting@ avs=%a@\nans=@ %a@\nsol=@ %a@\n%!"
      pr_vars avs
      pr_formula ans pr_bchi_subst (List.map (fun (b,a)->b,([],a))
     sol); (*]*)
    let ans0 = List.filter
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
        (*[*) Format.printf "split-loop-3: b=%s@ target=%a@\n%!"
          (var_str b) pr_vars (Hashtbl.find q.b_vs b); (*]*)
        b,
        snd (connected ~directed:true
               (b::VarSet.elements (Hashtbl.find q.b_vs b)) ([],ans0)))
      q.negbs in
    (*[*) Format.printf "split-loop-3: ans1=@\n%a@\n%!"
      pr_bchi_subst (List.map (fun (b,a)->b,(VarSet.elements (Hashtbl.find q.b_vs b),a))
                       ans_cand); (*]*)
    (* 4 *)
    let ans_cand = List.map
      (fun (b,ans) -> b,
       let chi_locs = Hashtbl.find_all negchi_locs b in
       (*[*) Format.printf "chi_locs: b=%s@ locs=%a@\n%!"
         (var_str b) (pr_sep_list "; " pr_loc_pos_only) chi_locs;
       (*]*)
       List.filter
         (fun c -> let lc = atom_loc c in
                   (*[*) Format.printf "ans_loc: c=%a@ loc=%a@\n%!"
                     pr_atom c pr_loc_pos_only lc;
                   (*]*)
                   List.exists (interloc lc) chi_locs)
         ans)
      ans_cand in
    (*[*) Format.printf "split-loop-4: ans2=@\n%a@\n%!"
      pr_bchi_subst (List.map (fun (b,a)->b,([],a))
                       ans_cand); (*]*)
    (* 5 *)
    let ans_cand = List.map
      (fun (b,ans) -> b,
       List.filter
         (fun c ->
           List.for_all (fun (b',ans') ->
             cmp_v b b' <> Left_of
             || not (List.memq c ans')) ans_cand)
         ans)
      ans_cand in
    (*[*) Format.printf "split-loop-5: ans3=@\n%a@\ncand_bvs=%a@\n%!"
      pr_bchi_subst (List.map (fun (b,a)->b,([],a))
                       ans_cand)
      pr_vars cand_bvs; (*]*)
    (* 6 *)
    let ans_cand = List.map
      (fun (b, ans) ->
        (*[*) Format.printf "split-loop-6: b=%s@ target=%a@\n%!"
          (var_str b) pr_vars (VarSet.inter (fvs_formula ans) cand_bvs); (*]*)
        let avs = fvs_formula ans in
        let ans = List.filter
            (fun c ->
               let dvs =
                 VarSet.diff (fvs_atom c) avs in
               let dsvs = VarSet.inter dvs cand_bvs in
               VarSet.cardinal dsvs <= 1 &&
               VarSet.for_all (not % q.uni_v) dvs)
            ans0 in
        (*let ans = snd
            (connected ~directed:false (*q.is_chiK (q.find_chi b)*)
               (VarSet.elements avs) ([],ans0)) in*)
        b, ans)
      ans_cand in
    (*[*) Format.printf "split-loop-6: ans4=@\n%a@\n%!"
      pr_bchi_subst (List.map (fun (b,a)->b,(VarSet.elements (Hashtbl.find q.b_vs b),a))
                       ans_cand); (*]*)
    (* 7 *)
    let init_res = List.filter
      (fun c -> not (List.exists (List.memq c % snd) ans_cand)) ans0 in
    let init_state =
      try holds q avs empty_state init_res
      with Contradiction _ as e -> raise (convert e) in
    (* 8 *)
    (* TODO: would it be better to implement it through
       [connected ~validate]? *)
    let ans_res = ref init_res and state = ref init_state in
    let ans_ps = List.map
      (fun (b,ans) -> b,
        List.filter (fun c ->
          try
            state := holds q avs !state [c];
            ans_res := c :: !ans_res;
            false
          with Contradiction _ -> true) ans)
      ans_cand in
    (*[*) Format.printf "split-loop: ans+=@\n%a@\n%!"
      pr_bchi_subst (List.map (fun (b,a)->b,([],a))
                       ans_ps); (*]*)
    let ans_res = !ans_res in    
    let more_discard = concat_map snd ans_ps in
    (* 9 *)
    let ans_strat = List.map
      (fun (b, ans_p) ->
        let bvs = Hashtbl.find q.b_vs b in
        let ans_p' =
          snd (connected ~directed:true
                 (b::VarSet.elements bvs)
                 ([],ans_p)) in
        (*[*) Format.printf
          "select-10: directed=%b@ bvs=%a@\nb=%s@\nans_p=%a@\nans_p'=%a@\n%!"
          (q.is_chiK (q.find_chi b)) pr_vars bvs
          (var_str b) pr_formula ans_p pr_formula ans_p'; (*]*)
        (* 10 *)
        let (avs_p, ans_l, ans_r) = strat q b ans_p' in
        (*[*) Format.printf "select: ans_l(%s)=@ %a@\n%!"
          (var_str b) pr_formula ans_l; (*]*)
        (* Negatively occurring [b] "owns" these formal parameters *)
        q.add_b_vs_of b (List.map (fun v->v,v) avs_p);
        (* 11 *)
        let ans0 = List.assoc b sol in
        let ans = ans0 @ ans_l in
        (* 12 *)
        let avs0 = VarSet.inter avs (fvs_formula ans) in
        (* 13.a *)
        let avs = VarSet.union avs0 (vars_of_list avs_p) in
        (b, avs), (b, ans), (avs_p, ans_r))
      ans_ps in
    let avss, sol', more = split3 ans_strat in
    let avs_ps, ans_rs = List.split more in
    (* 13.b *)
    let avss = List.map
      (fun (b, avs) ->
        let lbs = List.filter
          (fun b' -> q.cmp_v b b' = Right_of) q.negbs in
        let uvs = List.fold_left VarSet.union VarSet.empty
          (List.map (flip List.assoc avss) lbs) in
        VarSet.diff avs uvs)
      avss in
    (* 14 *)
    let ans_p = List.concat ans_rs in
    (*[*) Format.printf "split: ans_p=@ %a@ --@ ans_res=@ %a@\n%!"
      pr_subst ans_p pr_formula ans_res; (*]*)
    let ans_res = to_formula ans_p @ subst_formula ans_p ans_res in
    (*[*) Format.printf "split: ans_res'=@ %a@\n%!"
      pr_formula ans_res; (*]*)
    let avs_p = List.concat avs_ps in
    let avsl = List.map VarSet.elements avss in
    (* 15 *)
    if avs_p <> []
    then
      (* 16 *)
      let avs' = VarSet.diff avs
        (List.fold_left VarSet.union VarSet.empty avss) in
      let ans_res', discard', sol' =
        loop avs' ans_res (more_discard @ discard) sol' in
      (* 17 *)
      ans_res', discard',
      List.map2
        (fun avs (b, (avs', ans')) -> b, (avs@avs', ans')) avsl sol'
    else
      (* 18 *)
      ans_res, more_discard @ discard,
      List.map2 (fun avs (b, ans) -> b, (avs, ans)) avsl sol' in
  let solT = List.map (fun b->b, []) q.negbs in
  loop (vars_of_list avs) ans [] solT  

(** Eliminate provided variables if they do not contribute to
    constraints and generally simplify the formula. *)
let simplify q_ops (vs, cnj) =
  let vs = vars_of_list vs in
  (*[*) Format.printf "simplify: vs=%a@ cnj=%a@\n%!"
    pr_vars vs pr_formula cnj; (*]*)
  let cmp_v v1 v2 =
    let c1 = VarSet.mem v1 vs and c2 = VarSet.mem v2 vs in
    (*[*) Format.printf "cmp_v: %s(%b), %s(%b)@\n%!"
       (var_str v1) c1 (var_str v2) c2; (*]*)
    if c1 && c2 then Same_quant
    else if c1 then Right_of
    else if c2 then Left_of
    else q_ops.Terms.cmp_v v1 v2 in
  let q_ops = {q_ops with cmp_v} in
  let ty_ans, num_ans, _ =
    unify ~use_quants:false q_ops cnj in
  (* We "cheat": eliminate variables introduced earlier, so that
     convergence check has easier job (just syntactic). *)
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
  let num_sb, num_ans =
    NumS.separate_subst q_ops num_ans in
  let num_sb, more_num_ans = List.partition
      (fun (v,_) -> VarSet.mem v vs && v <> delta && v <> delta') num_sb in
  let num_ans = to_formula more_num_ans @ num_ans in
  let _, num_ans' = NumS.simplify q_ops VarSet.empty num_ans in
  (*[*) Format.printf "simplify:@\nnum_ans=%a@\nnum_ans'=%a@\n%!"
    pr_formula num_ans pr_formula num_ans'; (*]*)
  let ty_ans = subst_sb ~sb:num_sb ty_ans in
  let ty_sb, ty_ans = List.partition
      (fun (v,_) -> VarSet.mem v vs && v <> delta && v <> delta') ty_ans in
  let ans = to_formula ty_ans @ num_ans' in
  let vs = VarSet.inter vs (fvs_formula ans) in
  (*[*) Format.printf "simplify: vs=%a@ ty_sb=%a@ num_sb=%a@ ans=%a@\n%!"
    pr_vars vs pr_subst ty_sb pr_subst num_sb pr_formula ans; (*]*)
  VarSet.elements vs, ans

let converge q_ops ~check_only (vs1, cnj1) (vs2, cnj2) =
  (*[*) Format.printf
    "converge: check_only=%b@ vs1=%a@ vs2=%a@\ncnj1=%a@\ncnj2=%a\n%!"
    check_only pr_vars (vars_of_list vs1) pr_vars (vars_of_list vs2)
    pr_formula cnj1 pr_formula cnj2; (*]*)
  let c1_ty, c1_num, c1_so = unify ~use_quants:false q_ops cnj1 in
  let c2_ty, c2_num, c2_so = unify ~use_quants:false q_ops cnj2 in
  assert (c1_so = []); assert (c2_so = []);
  (* Recover old variable names. *)
  let pms_old =
    try fvs_typ (fst (List.assoc delta' c1_ty))
    with Not_found -> VarSet.empty in
  let vs_old = VarSet.diff (vars_of_list vs1) pms_old in
  let pms_new =
    try fvs_typ (fst (List.assoc delta' c2_ty))
    with Not_found -> VarSet.empty in
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
      if v=delta'
      then Eqty (TCons (tuple,[]), TCons (tuple,[]),dummy_loc) (* i.e. none *)
      else Eqty (t1,t2,dummy_loc)) c1_ty c2_ty in
  let renaming, ren_num, _ = unify ~use_quants:false q_ops cnj_tys in
  (*[*) Format.printf "converge: cnj_tys=%a@\nren_num=%a@\nrenaming1=%a@\n%!"
    pr_formula cnj_tys pr_formula ren_num pr_subst renaming; (*]*)
  let v_notin_vs_cn vs =
      map_some
        (function
          | Eqty (TVar v, t, lc) when not (List.mem v vs) -> Some (v, (t, lc))
          | Eqty (t, TVar v, lc) when not (List.mem v vs) -> Some (v, (t, lc))
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
  let renaming = valid_cn ren_num @ valid_sb renaming in
  (*[*) Format.printf "converge: renaming2=%a@\n%!" pr_subst renaming; (*]*)
  let c1_nr = List.sort cmp (v_notin_vs_cn vs1 c1_num)
  and c2_nr = List.sort cmp (v_notin_vs_cn vs2 c2_num) in
  let num_ren = inter_merge
      (fun (v1,_) (v2,_) -> compare v1 v2)
      (fun (_,(t1,_)) (_,(t2,_)) -> Eqty (t1,t2,dummy_loc))
      c1_nr c2_nr in
  let renaming = valid_cn num_ren @ renaming in
  (*[*) Format.printf
    "converge: pms_old=%a@ pms_new=%a@ vs_old=%a@ vs_new=%a@ renaming3=%a@\n%!"
    pr_vars pms_old pr_vars pms_new pr_vars vs_old pr_vars vs_new
    pr_subst renaming; (*]*)
  let c2_ty = subst_sb ~sb:renaming c2_ty
  and c2_num = subst_formula renaming c2_num
  and vs2 = List.map
    (fun v ->
      try match List.assoc v renaming with
      | TVar v2, _ -> v2 | _ -> assert false
      with Not_found -> v)
    vs2 in
  let c_num =
    if check_only then c2_num
    else NumS.converge q_ops c1_num c2_num in
  (*[*) Format.printf
    "converge: check_only=%b vs2=%a@\nc2_ty=%a@\nc2_num=%a@\nc_num=%a\n%!"
    check_only pr_vars (vars_of_list vs2)
    pr_subst c2_ty pr_formula c2_num pr_formula c_num; (*]*)
  vs2, to_formula c2_ty @ c_num


let neg_constrns = ref true

(* Captures where the repeat step is/are. *)
let disj_step = [|0; 0; 2; 4|]

let solve q_ops new_ex_types exty_res_chi brs =
  (* DEBUG *)
  (*[*) List.iter
    (fun (prem,concl) ->
       try ignore (unify ~use_quants:false q_ops (prem@concl))
       with Contradiction _ as e ->
         Format.printf
           "solve: bad branch@\n%a@ ⟹@ %a@\nreason: %a@\n%!"
           pr_formula prem pr_formula concl pr_exception e;
    )
    brs; (*]*)
  let q = new_q q_ops in
  (* let cmp_v = q.cmp_v and uni_v = q.uni_v in *)
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
  (*[*) Format.printf "solve: neg_brs=@ %a@\n%!" Infer.pr_rbrs neg_brs; (*]*)
  let neg_cns = List.map
      (fun (prem, concl) ->
         let loc =
           match List.find (function CFalse _ -> true | _ -> false) concl
           with CFalse loc -> loc | _ -> assert false in
         prem, loc)
      neg_brs in
  (*[*) Format.printf "solve: neg_cns=@ %a@\n%!" Infer.pr_rbrs
    (List.map (fun (cnj,_) -> cnj, []) neg_cns); (*]*)
  let negchi_locs = Hashtbl.create 8 in
  let alphasK = Hashtbl.create 8 in
  let chi_rec = Hashtbl.create 2 in
  List.iter
    (fun (prem,concl) ->
       List.iter
         (function
           | PredVarU (i, TVar b, lc_p) ->
             let lc_c = formula_loc concl in
             Hashtbl.add negchi_locs b (loc_union lc_p lc_c);
             Hashtbl.replace chi_rec i ();
             q.add_bchi b i ~posi:false ~chiK:false
           | PredVarB (i, TVar b, _, lc_p) ->
             let lc_c = formula_loc concl in
             Hashtbl.add negchi_locs b (loc_union lc_p lc_c);
             q.add_bchi b i ~posi:false ~chiK:true
           | _ -> ()) prem;
       List.iter
         (function
           | PredVarU (i, TVar b, _) ->
             q.add_bchi b i ~posi:true ~chiK:false
           | PredVarB (i, TVar b, TVar a, _) ->
             Hashtbl.add alphasK a ();
             q.add_bchi b i ~posi:true ~chiK:true
           | _ -> ()) concl;
    ) brs;
  let brs = List.map
      (fun (prem,concl) ->
         not (List.exists (function
             | PredVarU (i, _, _) -> Hashtbl.mem chi_rec i
             | _ -> false) concl) &&
         not (List.exists (function
             | PredVarB (i, _, _, _) -> true
             | _ -> false) prem),
         prem, concl)
      brs in
  let exty_of_chi = Hashtbl.create 4 in
  List.iter
    (fun (ety, _) ->
       match Hashtbl.find sigma (Extype ety) with
       | _, (PredVarB (chi,_,_,_))::_, _, _, _ ->
         Hashtbl.add exty_of_chi chi ety
       | _ -> assert false)
    new_ex_types;
  let remove_alphaK =
    List.filter
      (function
        | Eqty (TVar a, _, _) when Hashtbl.mem alphasK a -> false
        | Eqty (_, TVar a, _) when Hashtbl.mem alphasK a -> false
        | _ -> true) in
  let bparams () =
    List.fold_left
      (fun bvs b -> VarSet.union bvs (Hashtbl.find q.b_vs b))
      VarSet.empty q.negbs in
  (* keys in sorted order! *)
  let solT = List.map
      (fun i -> i, ([], []))
      (Ints.elements q.allchi) in
  let rolT, solT = List.partition (q.is_chiK % fst) solT in
  let rec loop iter_no discard rol1 sol1 =
    (* 1 *)
    let sol1 = List.map
        (fun (i,(vs,ans)) -> i,(vs,remove_alphaK ans)) sol1 in
    (*[*) Format.printf
      "solve: substituting invariants at step 1@\n%!"; (*]*)
    let brs0 = sb_brs_PredU q sol1 brs in
    let g_par = List.map (fun (i,_) -> i,([],[]))
      (* function (i,(_,[])) -> i,([],[])
              | (i,(_,pms::_)) -> i, ([],[pms]) *) rol1 in
    (*[*) Format.printf "solve: substituting postconds at step 1@\n%!"; (*]*)
    let brs1 = sb_brs_PredB q rol1 g_par brs0 in
    (* Collect all relevant constraints together. *)
    let verif_brs = List.map
        (fun (nonrec, chiK, vK, prem, _) ->
           nonrec, chiK, vK, prem,
           concat_map
             (fun (_,_,_,prem2,concl2) ->
                (*[*) Format.printf
                  "solve-verif_brs: subformula? %b@\nprem2=%a@\nprem=%a@\n%!"
                  (subformula prem2 prem)
                  pr_formula prem2 pr_formula prem; (*]*)
                if subformula prem2 prem then concl2 else [])
             brs1)
        brs1 in
    (*[*) Format.printf "solve: loop iter_no=%d@\nsol=@ %a@\n%!"
      iter_no pr_chi_subst sol1; (*]*)
    (*[*) Format.printf "brs=@ %a@\n%!" Infer.pr_rbrs5 brs1; (*]*)
    let validate ans = List.iter
        (fun (nonrec, _, _, prem, concl) ->
           (* Do not use quantifiers, because premise is in the
              conjunction. *)
           (* FIXME *)
           if (* false && *) not nonrec then (
             (*[*) Format.printf
               "validate-postcond: ans=%a@ prem=%a@ concl=%a@\n%!"
               pr_formula ans pr_formula prem pr_formula concl; (*]*)
             let sb_ty, ans_num, ans_so =
               unify ~use_quants:false q_ops (ans @ prem @ concl) in
             (*[*) Format.printf
               "validate-postcond: sb_ty=@ %a@\nans_num=@ %a@\n%!"
               pr_subst sb_ty pr_formula ans_num; (*]*)
             let (*[*)num_state(*]*) =
               NumS.satisfiable_exn ans_num in
             (*[*) Format.printf "validate-postcond: num_state=@ %a@\n%!"
               pr_formula (NumS.formula_of_state num_state); (*]*)
             ()))
        verif_brs in
    let sol1, brs1, g_rol =
      if iter_no < disj_step.(0) then sol1, brs1, rol1
      else
        (* 2 *)
        (* The [t2] arguments should in the solution become equal! *)
        let g_rol = collect
            (concat_map
               (fun (nonrec,chiK_pos,vK,prem,concl) ->
                  if nonrec || disj_step.(2) <= iter_no
                  then
                    List.map
                      (fun (i,t1,t2,lc) ->
                         let phi = Eqty (tdelta, t1, lc) :: prem @ concl in
                         (*[*) Format.printf
                           "chiK: i=%d@ t1=%a@ t2=%a@ prem=%a@\nphi=%a@\n%!"
                           i (pr_ty false) t1 (pr_ty false) t2
                           pr_formula prem pr_formula phi;
                         (*]*)
                         i, phi)
                      chiK_pos
                  else [])
               verif_brs) in
        (* 3 *)
        let dsj_preserve exchi =
          let exty = Hashtbl.find exty_of_chi exchi in
          let chi = Hashtbl.find exty_res_chi exty in
          let _, ans = List.assoc chi sol1 in
          fvs_formula ans in
        let g_rol = List.map
            (fun (i,_) ->
               (*[*) Format.printf "solve: approaching disjelim for %d@\n%!"
                 i; (*]*)
               try
                 let cnjs = List.assoc i g_rol in
                 let preserve = dsj_preserve i in
                 let g_vs, g_ans =
                   (* FIXME *)
                   DisjElim.disjelim q_ops ~preserve
                     ~do_num:(disj_step.(1) <= iter_no) cnjs in
                 let target = delta::g_vs in
                 let g_ans = List.filter
                     (fun c ->
                        let cvs = fvs_atom c in
                        List.exists (flip VarSet.mem cvs) target)
                     g_ans in
                 (* FIXME *) 
                 let g_ans =
                   if iter_no < disj_step.(2)
                   then
                     DisjElim.initstep_heur q.op ~preserve g_ans
                   else g_ans in
                 i, connected ~validate ~directed:true [delta; delta']
                   (g_vs, g_ans)
               with Not_found ->
                 (*[*) Format.printf "solve: disjelim branches for %d not found@\n%!"
                   i; (*]*)
                 i, ([], []))
            rol1 in
        (*[*) Format.printf "solve: iter_no=%d@\ng_rol.A=%a@\n%!"
          iter_no pr_chi_subst g_rol;
        (*]*)
        (* 4 *)
        let lift_ex_types cmp_v i (g_vs, g_ans) =
          let g_vs, g_ans = simplify q_ops (g_vs, g_ans) in
          let fvs = VarSet.elements
              (VarSet.diff (fvs_formula g_ans)
                 (vars_of_list [delta;delta'])) in
          let pvs = VarSet.diff (vars_of_list fvs) (vars_of_list g_vs) in
          let pvs = VarSet.elements pvs in
          let chi_vs = dsj_preserve i in
          let pvs = List.filter
              (fun v -> not (q.uni_v v) || VarSet.mem v chi_vs) pvs in
          let targs = List.map (fun v -> TVar v) pvs in
          let tpar = TCons (tuple, targs) in
          let phi =
            Eqty (tdelta', tpar, dummy_loc)
            :: g_ans in
          (*[*) Format.printf
            "lift_ex_types: fvs=%a@ pvs=%a@ g_vs=%a@ tpar=%a@ g_ans=%a@ phi=%a@\n%!"
            pr_vars (vars_of_list fvs)
            pr_vars (vars_of_list pvs)
            pr_vars (vars_of_list g_vs) (pr_ty false) tpar
            pr_formula g_ans pr_formula phi;
          (*]*)
          tpar, (pvs @ g_vs, phi) in
        (* 5 *)
        let g_rol = List.map2
            (fun (i,ans1) (j,ans2) ->
               assert (i = j);
               let tpar, ans2 = lift_ex_types q.op i ans2 in
               let ans2 =
                 converge q.op
                   ~check_only:(iter_no < disj_step.(3)) ans1 ans2 in
               (*[*) Format.printf "solve.loop-dK: final@ tpar=%a@ ans2=%a@\n%!"
                 (pr_ty false) tpar pr_ans ans2; (*]*)
               (* No [b] "owns" these formal parameters. Their instances
                  will be added to [q] by [sb_brs_pred]. *)
               (i, tpar), (i, ans2)
            ) rol1 g_rol in
        let tpars, g_rol = List.split g_rol in
        let g_par = List.map
            (fun (i,(_,phi)) -> i, ([],[List.hd phi])) g_rol in
        let v_par = List.map
            (fun (i,tpar) ->
               let vs = fvs_typ tpar in
               i, (VarSet.elements vs,
                   [Eqty (tdelta, tpar, dummy_loc)])) tpars in
        (*[*) Format.printf "solve: loop iter_no=%d@ g_par=%a@\ng_rol.B=@ %a@\n%!"
          iter_no pr_chi_subst g_par pr_chi_subst g_rol; (*]*)
        (* 6 *)
        let esb = List.map
            (fun (i, tpar) ->
               let n = Extype (Hashtbl.find exty_of_chi i) in
               n, fun old ->
                 (*[*) Format.printf "esb-6: old=%a new=%a@\n%!"
                   (pr_ty false) (TCons (n, old))
                   (pr_ty false) (TCons (n, [tpar])); (*]*)
                 TCons (n, [tpar]))
            tpars in
        let esb_formula = List.map
            (function
              | Eqty (t1, t2, lc) ->
                Eqty (n_subst_typ esb t1, n_subst_typ esb t2, lc)
              | a -> a) in
        let sol1 = List.map
            (fun (i, (vs, old_phi)) ->
               let phi = esb_formula old_phi in
               let b =
                 try List.find (not % q.positive_b) (q.find_b i)
                 with Not_found -> assert false in
               let fvs = VarSet.elements
                   (VarSet.diff (fvs_formula phi)
                      (vars_of_list (delta::delta'::vs))) in
               let nvs = List.filter
                   (fun v -> not (q.uni_v v) && q.cmp_v b v = Left_of) fvs in
               let nvs = List.map (fun v -> v, Infer.freshen_var v) nvs in
               let phi = subst_formula (renaming_sb nvs) phi in
               (*[*) Format.printf
                 "lift-params: i=%d@ vs=%a@ fvs=%a@ nvs=%a@ phi=%a@ phi'=%a@\n%!"
                 i pr_vars (vars_of_list vs)
                 pr_vars (vars_of_list fvs)
                 pr_vars (vars_of_list (List.map snd nvs)) pr_formula old_phi
                 pr_formula phi; (*]*)
               if nvs <> [] then q.add_b_vs_of b nvs;
               i, (List.map snd nvs @ vs, phi))
            sol1 in
        (*[*) Format.printf "solve: substituting invariants at step 5@\n%!"; (*]*)
        let brs0 = sb_brs_PredU q sol1 brs in
        (*[*) Format.printf "solve: substituting postconds at step 5@\n%!"; (*]*)
        let brs1 = sb_brs_PredB q g_rol g_par brs0 in
        (*[*) Format.printf "solve: substituting params at step 5@\n%!"; (*]*)
        let brs1 = sb_brs_vK q v_par brs1 in
        sol1, brs1, g_rol in
    (*[*) Format.printf "solve-loop: iter_no=%d -- ex. brs substituted@\n%!"
      iter_no; (*]*)
    (*[*) Format.printf "brs=@ %a@\n%!" Infer.pr_rbrs5 brs1; (*]*)
    (* 7a *)
    let neg_cns1 = List.map
        (fun (prem,loc) -> sb_formula_pred q false g_rol sol1 prem, loc)
        neg_cns in
    let bvs = bparams () in
    let answer =
      try
        (* 7b *)
        (* Check negative constraints ("assert false" clauses) once
           all positive constraints have been involved in answering. *)
        if !neg_constrns && iter_no > 1 then List.iter
            (* raise [NoAnswer] when needed *)
            (fun (cnj, loc) ->
               try
                 (*[*) Format.printf "neg_cl_check: cnj=@ %a@\n%!" pr_formula
                   cnj; (*]*)
                 let ty_cn (*_*), num_cn, _ =
                   unify ~use_quants:false q.op cnj in
                 if num_cn = [] then (
                   (*[*) Format.printf
                     "neg_cl_check: fallback typ@ ty_cn=@ %a@\n%!"
                     pr_subst ty_cn; (*]*)
                   raise
                     (NoAnswer (Type_sort, "negative clause", None, loc)));
                 if Aux.is_right (NumS.satisfiable num_cn) then (
                   (*[*) Format.printf
                     "neg_cl_check: fallback num@ num_cn=@ %a@\n%!"
                     pr_formula num_cn; (*]*)
                   raise
                     (NoAnswer (Num_sort,
                                "negative clause", None, loc)));
                 (*[*) Format.printf
                   "neg_cl_check: passed (num)@ ty_cn=@ %a@\nnum_cn=@ %a@\n%!"
                   pr_subst ty_cn pr_formula num_cn; (*]*)
               with Contradiction _ (*[*)as e(*]*) ->
                 (*[*) Format.printf
                   "neg_cl_check: passed (typ) by contradicting=@\n%a@\n%!"
                   pr_exception e; (*]*)
                 ())
            neg_cns1;
        (* 8 *)
        let brs1 = List.map
            (fun (nonrec,_,_,prem,concl) -> nonrec,prem,concl) brs1 in
        let cand_bvs, alien_eqs, (vs, ans) =
          Abduction.abd q.op ~bvs ~iter_no ~discard brs1 in
        let ans_res, more_discard, ans_sol =
          split vs ans negchi_locs bvs cand_bvs q in
        (*[*) Format.printf
          "solve: loop -- answer split@ more_discard=@ %a@\nans_res=@ %a@\n%!"
          pr_formula more_discard pr_formula ans_res; (*]*)
        Aux.Right (alien_eqs, ans_res, more_discard, ans_sol)
      with
      (* it does not seem to make a difference *)
      | (NoAnswer (sort, msg, tys, lc)
        | Contradiction (sort, msg, tys, lc)) as e ->
        (*[*) Format.printf
          "Fallback: iter_no=%d; sort=%s;@ error=@\n%a@\n%!"
          iter_no (sort_str sort) pr_exception e;
        (*]*)
        Aux.Left (sort, e) in
    match answer with
    | Aux.Left _ as e -> e
    | Aux.Right (alien_eqs, ans_res, more_discard, ans_sol) ->
      let more_discard =
        if alien_eqs = [] then more_discard
        else subst_formula alien_eqs more_discard in
      (* 12 *)
      let finish rol2 sol2 =
        (* start fresh at (iter_no+1) *)
        match loop (iter_no+1) [] rol2 sol2
        with Aux.Right _ as res -> res
           | Aux.Left (sort, e) ->
             (*[*) Format.printf
               "solve-finish: fallback call iter_no=%d sort=%s@\ndisc=%a@\n%!"
               iter_no (sort_str sort) pr_formula more_discard; (*]*)
             let sort, s_discard =
               let s_discard = split_sorts more_discard in
               (* The complication is because we do not always do
                  alien subterm dissociation. *)
               let disc = List.assoc sort s_discard in
               if disc <> [] || sort <> Type_sort then sort, disc
               else match
                   List.filter (fun (_,cnj) -> cnj<>[]) s_discard
                 with
                 | [s_disc] -> s_disc
                 | _ -> sort, [] in
             if s_discard = [] then (
               (*[*) Format.printf
                 "solve-finish: fallback has no discard@\n%!"; (*]*)
               raise e);
             (*[*) Format.printf
               "solve-finish: ultimately sort=%s@ disc=%a@\n%!"
               (sort_str sort) pr_formula s_discard; (*]*)
             let discard =
               update_assoc sort [] (fun dl -> s_discard::dl) discard in
             loop iter_no discard rol1 sol1 in
      (* 9 *)
      let ans_sb, _ = Infer.separate_subst ~avoid:bvs q.op ans_res in
      let rol2 =
        if disj_step.(0) > iter_no then rol1
        else
          List.map
            (fun (i, (gvs,g_ans)) ->
               (* FIXME: code duplication with [lift_ex_types]? *)
               let g_ans = subst_formula ans_sb g_ans in
               let tpar, g_ans = List.partition
                   (function
                     | Eqty (tv, tpar, _) when tv = tdelta' -> true
                     | _ -> false)
                   g_ans in
               let tpar =
                 match tpar with
                 | [Eqty (tv, tpar, _)] -> tpar
                 | [] -> assert false
                 | _::_ -> assert false in
               let bs = List.filter (not % q.positive_b) (q.find_b i) in
               let ds = List.map (fun b-> b, List.assoc b ans_sol) bs in
               let dans = concat_map
                   (fun (b, (dvs, dans)) ->
                      (*[*) Format.printf
                        "solve-loop-9: chi%d(%s)=@ %a@ +@ %a@\n%!"
                        i (var_str b) pr_ans (dvs,dans) pr_ans
                        (gvs,g_ans); (*]*)
                      (* No need to substitute, because variables will be
                         freshened when predicate variable is instantiated. *)
                      let sb =
                        List.map (fun (v,w) -> w,v)
                          (Hashtbl.find q.b_renaming b) in
                      let sb = renaming_sb ((b, delta)::sb) in
                      (*[*) Format.printf
                        "solve-loop-9: renaming=@ %a@\ndans'=%a@\n%!"
                        pr_subst sb pr_formula (subst_formula sb dans); (*]*)
                      subst_formula sb dans)
                   ds in
               let dvs = gvs @ concat_map (fun (_,(dvs,_))->dvs) ds in
               let pvs = fvs_typ tpar in
               let svs =
                 VarSet.elements (VarSet.diff (vars_of_list dvs) pvs) in
               let vs, ans =
                 simplify q.op
                   (connected ~directed:true [delta; delta']
                      (svs, dans @ g_ans)) in
               let pvs = VarSet.elements pvs in
               let vs = vs @ pvs in
               (* FIXME: are generalization variables impossible in tpar'? *)
               let targs =
                 List.map (fun v -> TVar v) pvs in
               let tpar' = TCons (tuple, targs) in
               let i_res = vs, Eqty (tdelta', tpar', dummy_loc) :: ans in
               (*[*) Format.printf
                 "solve-loop: pvs=%a@ dvs=%a@ svs=%a@ vs=%a dans=%a@ chi%d(.)=@ %a@\n%!"
                 pr_vars (vars_of_list pvs) pr_vars (vars_of_list dvs)
                 pr_vars (vars_of_list svs) pr_vars (vars_of_list vs)
                 pr_formula dans i pr_ans i_res; (*]*)
               i, i_res)
            g_rol in
      (* 10 *)
      let sol2 = List.map
          (fun (i, (vs, ans)) ->
             let bs = List.filter (not % q.positive_b) (q.find_b i) in
             let b = match bs with [b] -> b | _ -> assert false in
             let dvs, dans = List.assoc b ans_sol in
             (*[*) Format.printf
               "solve-loop-10: chi%d(%s)=@ %a@ +@ %a@\n%!"
               i (var_str b) pr_ans (dvs,dans) pr_ans (vs,ans); (*]*)
             (* No need to substitute, because variables will be
                freshened when predicate variable is instantiated. *)
             let dans = subst_formula [b, (tdelta, dummy_loc)] dans in
             let i_res = simplify q.op (dvs @ vs, dans @ ans) in
             (*[*) Format.printf
               "solve-loop-10: vs=%a@ ans=%a@ chi%d(.)=@ %a@\n%!"
               pr_vars (vars_of_list vs) pr_formula ans i pr_ans i_res; (*]*)
             i, i_res)
          sol1 in    
      (* 11 *)
      let finished1 =
        iter_no >= 1 && List.for_all2
          (fun (i,(_,ans2)) (j,(_,ans1)) -> assert (i=j);
            subformula ans2 ans1)
          sol2 sol1 in
      let finished2 =
        List.for_all2
          (fun (i,(_,ans2)) (j,(_,ans1)) -> assert (i=j);
            subformula ans2 ans1)
          rol2 rol1 in
      let finished3 =
        List.for_all2
          (fun (i,(_,ans1)) (j,(_,ans2)) -> assert (i=j);
            subformula ans1 ans2)
          rol1 rol2 in
      let finished = finished1 && finished2 && finished3 in
      (*[*) Format.printf "solve-loop: finished 1=%b, 2=%b, 3=%b, r=%b@\n%!"
        finished1 finished2 finished3 finished; (*]*)
      if iter_no > 1 && finished
      then                              (* final solution *)
        Aux.Right (ans_res, rol2, sol2)
        (* Do at least three iterations: 0, 1, 2. *)
      else if iter_no <= 1 && finished
      then loop (iter_no+1) [] rol2 sol1
      else finish rol2 sol2 in
  match loop 0 [] rolT solT with
  | Aux.Left (_, e) -> raise e
  | Aux.Right (ans_res, rol, sol) ->
    (*[*) Format.printf "solve: checking assert false@\n%!"; (*]*)
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
    let ans_sb, _ = Infer.separate_subst q.op ans_res in
    (*[*) Format.printf "solve: final@\nans_res=%a@\nans_sb=%a@\n%!"
      pr_formula ans_res pr_subst ans_sb;
    (*]*)
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
    (*[*) Format.printf "solve: final@\nans_res'=%a@\n%!"
      pr_formula ans_res; (*]*)
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
             (*[*) Format.printf
               "solve-new_ex_types: chi_i=%d out of %s@\n%!"
               chi_i (String.concat ","
                        (List.map (string_of_int % fst) rol)); (*]*)
             [], [] in
         let sb, rphi = Infer.separate_subst q.op phi in
         let sb = update_sb ~more_sb:ans_sb sb in
         let sb = List.map
             (function
               | v, (TVar v2, lc) when v2=delta || v2=delta' ->
                 v2, (TVar v, lc)
               | sv -> sv) sb in
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
         (*[*) Format.printf
           "solve-ex_types: ex_i=%d@ t1=%a@ t2=%a@ ty=%a@ chi_vs=%a@ rty=%a@ allvs=%a@ pvs=%a@ rphi=%a@ @\nphi=%a@\n%!"
           ex_i (pr_ty false) t1 (pr_ty false) t2 (pr_ty false) ty
           pr_vars (vars_of_list chi_vs) (pr_ty false) rty
           pr_vars allvs pr_vars (vars_of_list pvs)
           pr_formula rphi pr_formula phi;
         (*]*)
         let ety_n = Extype ex_i in
         Hashtbl.replace sigma ety_n
           (VarSet.elements allvs, rphi, [rty], ety_n, pvs)) new_ex_types;
    (*[*) Format.printf "solve: returning@\n%!"; (*]*)
    q.op, ans_res, sol
