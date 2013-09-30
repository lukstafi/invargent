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
  
let new_q cmp_v uni_v =
  let same_q = Hashtbl.create 32 in
  let posi_b = Hashtbl.create 16 in
  let chiK_i = Hashtbl.create 16 in
  let cmp_v v1 v2 =
    let v1 = try Hashtbl.find same_q v1 with Not_found -> v1 in
    let v2 = try Hashtbl.find same_q v2 with Not_found -> v2 in
    cmp_v v1 v2 in
  let uni_v v =
    if Hashtbl.mem same_q v then
      let bv = Hashtbl.find same_q v in
      not (Hashtbl.mem posi_b bv)
    else uni_v v in
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
      Format.printf "add_bchi: exist old=%d chi%d(%s);@ posi=%b@\n%!"
        old i (var_str b) posi; (* *)
      assert (Hashtbl.find b_chi b = i)
    ) else (
      Format.printf "add_bchi: chi%d(%s);@ posi=%b@\n%!"
        i (var_str b) posi; (* *)
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
    List.iter (fun v -> Hashtbl.add same_q v b) vs;
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
    cmp_v; uni_v; add_b_vs_of;
    allchi = Ints.empty;
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
  Format.printf "matchup_vars: b=%s;@ vs=%s;@ orvs=%s;@ nrvs=%s@\n%!"
    (var_str b)
    (String.concat ", " (List.map var_str vs))
    (String.concat ", "
       (List.map (fun (v,w)->var_str v^":="^var_str w) orvs))
    (String.concat ", "
       (List.map (fun (v,w)->var_str v^":="^var_str w) nrvs)); (* *)
  q.add_b_vs_of b nrvs;
  let res = nrvs @ orvs in
  (* [orvs] stores a [delta] substitution, [delta] is absent from [vs] *)
  renaming_sb res

let sb_atom_PredU q posi psb = function
  | PredVarU (i, (TVar b as t), loc) as a ->
    (try
       let vs, phi = List.assoc i psb in
       Format.printf
         "sb_atom_pred: U posi=%b@ chi%d(%s)=@ %a@\n%!"
         posi i (var_str b) pr_ans (vs,phi); (* *)
       let renaming = matchup_vars ~self_owned:(not posi) q b vs in
       replace_loc loc
         (sb_phi_unary t (subst_formula renaming phi))
     with Not_found -> [a])  
  | PredVarB _ -> []
  | a -> [a]

let sb_formula_PredU q posi psb phi =
  concat_map (sb_atom_PredU q posi psb) phi

let sb_brs_PredU q sol brs = List.map
  (fun (prem,concl) ->
    List.for_all                        (* is_nonrec *)
      (function PredVarU _ -> false | _ -> true) concl &&
      List.for_all
      (function PredVarB _ -> false | _ -> true) prem,
    Aux.map_some                        (* chiK_neg *)
      (function PredVarB (i,t1,t2,lc) -> Some (i,t1,t2,lc) | _ -> None) prem,
    Aux.map_some                        (* chiK_pos *)
      (function PredVarB (i,t1,t2,lc) -> Some (i,t1,t2,lc) | _ -> None) concl,
    sb_formula_PredU q false sol prem,
    sb_formula_PredU q true sol concl)
  brs

let sb_PredB q psb (i, t1, t2, lc) =
  match t1 with TVar b ->
    (try
       let vs, phi = List.assoc i psb in
       Format.printf
         "sb_chiK_neg: chi%d(%s,%a)=@ %a@\n%!"
         i (var_str b) (pr_ty false) t2 pr_ans (vs,phi); (* *)
       let renaming = matchup_vars ~self_owned:false q b vs in
       replace_loc lc
         (sb_phi_binary t1 t2 (subst_formula renaming phi))
     with Not_found -> [])
  | _ -> []

let sb_brs_PredB q rol brs = List.map
  (fun (nonrec,chiK_neg,chiK_pos,prem,concl) ->
    nonrec,
    chiK_pos,
    concat_map (sb_PredB q rol) chiK_neg @ prem,
    concl)
  brs

let sb_atom_pred q posi rol sol = function
  | PredVarU (i, (TVar b as t), loc) as a ->
    (try
       let vs, phi = List.assoc i sol in
       Format.printf
         "sb_atom_pred: U posi=%b@ chi%d(%s)=@ %a@\n%!"
         posi i (var_str b) pr_ans (vs,phi); (* *)
       let renaming = matchup_vars (not posi) q b vs in
       replace_loc loc
         (sb_phi_unary t (subst_formula renaming phi))
     with Not_found -> [a])  
  | PredVarB (i, (TVar b as t1), t2, loc) as a ->
    (try
       let vs, phi = List.assoc i rol in
       Format.printf
         "sb_atom_pred: B posi=%b@ chi%d(%s,%a)=@ %a@\n%!"
         posi i (var_str b) (pr_ty false) t2 pr_ans (vs,phi); (* *)
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
    Format.fprintf ppf "ϰ%d:=%a" i pr_ans ans) ppf chi_sb

let pr_bchi_subst ppf chi_sb =
  pr_sep_list ";" (fun ppf (v,ans) ->
    Format.fprintf ppf "ϰ(%s):=%a" (var_str v) pr_ans ans) ppf chi_sb

type state = subst * NumS.state

let empty_state : state = [], NumS.empty_state

let no_params = VarSet.empty, VarSet.empty

let holds q (ty_st, num_st) cnj =
  let ty_st, num_cnj, _ =
    unify ~use_quants:no_params ~sb:ty_st q.cmp_v q.uni_v cnj in
  let num_st = NumS.holds q.cmp_v q.uni_v num_st num_cnj in
  ty_st, num_st

let satisfiable q (ty_st, num_st) cnj =
  let ty_st, num_cnj, _ =
    unify ~sb:ty_st q.cmp_v q.uni_v cnj in
  let num_st =
    match NumS.satisfiable (* q.cmp_v q.uni_v *) ~state:num_st num_cnj with
    | Right s -> s | Left e -> raise e in
  ty_st, num_st

(* 10 *)
let strat q b ans =
  let (_, ans_r), ans = fold_map
    (fun (pvs, ans_r) c ->
      let vs = VarSet.elements (VarSet.diff (fvs_atom c) pvs) in
      let vs = List.filter
        (fun v -> q.cmp_v b v = Upstream) vs in
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
  
let split avs ans negchi_locs params zparams q =
  (* 1 FIXME: do we really need this? *)
  let cmp_v v1 v2 =
    let a = q.cmp_v v1 v2 in
    if a <> Same_quant && a <> Not_in_scope then a
    else
      let c1 = VarSet.mem v1 q.allbvs
      and c2 = VarSet.mem v2 q.allbvs in
      if c1 && c2 then Same_quant
      else if c1 then Downstream
      else if c2 then Upstream
      else Same_quant in
  let rec loop avs ans discard sol =
    (* 2 *)
    Format.printf "split-loop: starting ans=@ %a@\nsol=@ %a@\n%!"
      pr_formula ans pr_bchi_subst (List.map (fun (b,a)->b,([],a))
     sol); (* *)
    let ans0 = List.filter
      (function
      | Eqty (TVar a, TVar b, _)
          when not (q.uni_v a) && VarSet.mem b q.allbvs &&
            cmp_v a b = Downstream -> false
      | Eqty (TVar b, TVar a, _)
          when not (q.uni_v a) && VarSet.mem b q.allbvs &&
            cmp_v a b = Downstream -> false
      | _ -> true) ans in
    (* 3 *)
    let ans_cand = List.map
      (fun b -> b,
        snd (connected ~directed:(q.is_chiK (q.find_chi b))
               (VarSet.elements (Hashtbl.find q.b_vs b)) ([],ans0)))
      q.negbs in
    Format.printf "split-loop: ans1=@\n%a@\n%!"
      pr_bchi_subst (List.map (fun (b,a)->b,(VarSet.elements (Hashtbl.find q.b_vs b),a))
                       ans_cand); (* *)
    (* 4 DEBUG *)
    let ans_cand = List.map
      (fun (b,ans) -> b,
       let chi_locs = Hashtbl.find_all negchi_locs b in
       Format.printf "chi_locs: b=%s@ locs=%a@\n%!"
         (var_str b) (pr_sep_list "; " pr_loc_pos_only) chi_locs;
       (* *)
       List.filter
         (fun c -> let lc = atom_loc c in
                   Format.printf "ans_loc: c=%a@ loc=%a@\n%!"
                     pr_atom c pr_loc_pos_only lc;
                   (* *)
                   List.exists (interloc lc) chi_locs)
         ans)
      ans_cand in
    Format.printf "split-loop: ans2=@\n%a@\n%!"
      pr_bchi_subst (List.map (fun (b,a)->b,([],a))
                       ans_cand); (* *)
    (* 5 *)
    let ans_cand = List.map
      (fun (b,ans) -> b,
       List.filter
         (fun c ->
           List.for_all (fun (b',ans') ->
             cmp_v b b' <> Upstream
             || not (List.memq c ans')) ans_cand)
         ans)
      ans_cand in
    Format.printf "split-loop: ans3=@\n%a@\n%!"
      pr_bchi_subst (List.map (fun (b,a)->b,([],a))
                       ans_cand); (* *)
    (* 6 *)
    let ans_cand = List.map
      (fun (b,ans) ->
        let bvs = Hashtbl.find q.b_vs b in
        let res = snd
          (connected ~directed:(q.is_chiK (q.find_chi b))
             (VarSet.elements bvs) ([],ans)) in
        Format.printf "split-loop-6: b=%s;@ vs=%a;@ res=%a@\n%!"
          (var_str b) pr_vars bvs pr_formula res;
        b, res)
      ans_cand in
    Format.printf "split-loop: ans4=@\n%a@\n%!"
      pr_bchi_subst (List.map (fun (b,a)->b,([],a))
                       ans_cand); (* *)
    (* 7 *)
    let init_res = List.filter
      (fun c -> not (List.exists (List.memq c % snd) ans_cand)) ans0 in
    let init_state =
      try holds q empty_state init_res
      with Contradiction _ as e -> raise (convert e) in
    (* 8 *)
    (* TODO: would it be better to implement it through
       [connected ~validate]? *)
    let ans_res = ref init_res and state = ref init_state in
    let ans_ps = List.map
      (fun (b,ans) -> b,
        List.filter (fun c ->
          try
            state := holds q !state [c];
            ans_res := c :: !ans_res;
            false
          with Contradiction _ -> true) ans)
      ans_cand in
    Format.printf "split-loop: ans+=@\n%a@\n%!"
      pr_bchi_subst (List.map (fun (b,a)->b,([],a))
                       ans_ps); (* *)
    let ans_res = !ans_res in    
    let more_discard = concat_map snd ans_ps in
    (* 9 *)
    let ans_strat = List.map
      (fun (b, ans_p) ->
        Format.printf "select: ans_chi(%s)=@ %a@\n%!"
          (var_str b) pr_formula ans_p; (* *)
        (* 10 *)
        let (avs_p, ans_l, ans_r) = strat q b ans_p in
        Format.printf "select: ans_l(%s)=@ %a@\n%!"
          (var_str b) pr_formula ans_l; (* *)
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
          (fun b' -> q.cmp_v b b' = Downstream) q.negbs in
        let uvs = List.fold_left VarSet.union VarSet.empty
          (List.map (flip List.assoc avss) lbs) in
        VarSet.diff avs uvs)
      avss in
    (* 14 *)
    let ans_p = List.concat ans_rs in
    Format.printf "split: ans_p=@ %a@ --@ ans_res=@ %a@\n%!"
      pr_subst ans_p pr_formula ans_res; (* *)
    let ans_res = to_formula ans_p @ subst_formula ans_p ans_res in
    Format.printf "split: ans_res'=@ %a@\n%!"
      pr_formula ans_res; (* *)
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

(** Perform quantifier elimination on provided variables and generally
    simplify the formula. *)
let simplify cmp_v uni_v (vs, cnj) =
  let vs = vars_of_list vs in
  let cmp_v v1 v2 =
    let c1 = VarSet.mem v1 vs and c2 = VarSet.mem v2 vs in
    if c1 && c2 then Same_quant
    else if c1 then Downstream
    else if c2 then Upstream
    else cmp_v v1 v2 in
  let ty_ans, num_ans, _ =
    unify cmp_v uni_v cnj in
  let ty_sb, ty_ans = List.partition
    (fun (v,_) -> VarSet.mem v vs && v <> delta && v <> delta') ty_ans in
  let ty_ans = subst_formula ty_sb (to_formula ty_ans) in
  let ty_vs = VarSet.inter vs (fvs_formula ty_ans)
  and num_vs = VarSet.inter vs (fvs_formula num_ans) in
  let elimvs = VarSet.diff num_vs ty_vs in
  let _, num_ans =
    NumS.simplify cmp_v uni_v elimvs num_ans in
  VarSet.elements ty_vs,
  ty_ans @ num_ans

let converge cmp_v uni_v ~check_only (vs1, cnj1) (vs2, cnj2) =
  Format.printf "converge: check_only=%b@\ncnj1=%a@\ncnj2=%a\n%!"
    check_only pr_formula cnj1 pr_formula cnj2; (* *)
  let c1_ty, c1_num, c1_so = unify cmp_v uni_v cnj1 in
  let c2_ty, c2_num, c2_so = unify cmp_v uni_v cnj2 in
  assert (c1_so = []); assert (c2_so = []);
  let cmp (v1,_) (v2,_) = compare v1 v2 in
  let c1_ty = List.sort cmp c1_ty and c2_ty = List.sort cmp c2_ty in
  let cnj_tys = inter_merge cmp
    (fun (_,(t1,_)) (_,(t2,_)) -> Eqty (t1,t2,dummy_loc)) c1_ty c2_ty in
  let renaming, ren_num, _ = unify cmp_v uni_v cnj_tys in
  Format.printf "converge: cnj_tys=%a@\nren_num=%a@\nrenaming1=%a@\n%!"
    pr_formula cnj_tys pr_formula ren_num pr_subst renaming; (* *)
  let renaming =
      map_some
        (function
          | Eqty (TVar v, t, lc) -> Some (v, (t, lc))
          | Eqty (t, TVar v, lc) -> Some (v, (t, lc))
          | _ -> None)
        ren_num
      @ renaming in
  Format.printf "converge: renaming2=%a@\n%!" pr_subst renaming; (* *)
  let ren_of_cn vs =
      map_some
        (function
          | Eqty (TVar v, t, lc) when not (List.mem v vs) -> Some (v, (t, lc))
          | Eqty (t, TVar v, lc) when not (List.mem v vs) -> Some (v, (t, lc))
          | _ -> None) in
  let vs = vars_of_list vs1 in
  let c1_nr = List.sort cmp (ren_of_cn vs1 c1_num)
  and c2_nr = List.sort cmp (ren_of_cn vs2 c2_num) in
  let num_ren = inter_merge
      (fun (v1,_) (v2,_) -> compare v1 v2)
      (fun (_,(t1,_)) (_,(t2,_)) -> Eqty (t1,t2,dummy_loc))
      c1_nr c2_nr in
  (* Recover old variable names. *)
  let renaming = map_some
    (function
    | _, (TVar v2, _) as sx when VarSet.mem v2 vs -> Some sx
    | v1, (TVar v2, lc) when VarSet.mem v1 vs -> Some (v2, (TVar v1, lc))
    | _ -> None)
    renaming in
  let renaming =
    map_some
      (function
        | Eqty (TVar v, (TVar v2 as t), lc) when VarSet.mem v2 vs ->
          Some (v, (t, lc))
        | Eqty ((TVar v2 as t), TVar v, lc) when VarSet.mem v2 vs ->
          Some (v, (t, lc))
        | _ -> None)
      num_ren
    @ renaming in
  Format.printf "converge: renaming3=%a@\n%!" pr_subst renaming; (* *)
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
    else NumS.converge cmp_v uni_v c1_num c2_num in
  Format.printf "converge: check_only=%b@\nc2_num=%a@\nc_num=%a\n%!"
    check_only pr_formula c2_num pr_formula c_num; (* *)
  (* FIXME: will it not remove important atoms 'cause of [vs2]? *)
  simplify cmp_v uni_v (vs2, to_formula c2_ty @ c_num)

let neg_constrns = ref true

(* Captures where the repeat step is/are. *)
let disj_step = [|0; 0; 0; 5|]

let solve cmp_v uni_v brs =
  (* DEBUG *)
  List.iter
      (fun (prem,concl) ->
         try ignore (unify cmp_v uni_v (prem@concl))
         with Contradiction _ as e ->
           Format.printf
             "solve: bad branch@\n%a@ ⟹@ %a@\nreason: %a@\n%!"
             pr_formula prem pr_formula concl pr_exception e; (* *)
      )
      brs;
  let q = new_q cmp_v uni_v in
  let cmp_v = q.cmp_v and uni_v = q.uni_v in
  let neg_brs, brs = List.partition
      (fun (_,concl) -> List.exists
          (function CFalse _ -> true | _ -> false) concl) brs in
  let cmp_v' gvs v1 v2 =
    let c1 = List.mem v1 gvs and c2 = List.mem v2 gvs in
    if c1 && c2 then Same_quant
    else if c1 then Downstream
    else if c2 then Upstream
    else cmp_v v1 v2 in
  (* Enrich the negative branches -- they need it. *)
  let neg_brs = List.map
      (fun (prem,concl) ->
         let more = concat_map snd
             (List.filter (fun (prem2, _) -> list_diff prem2 prem = [])
                brs) in
         more @ prem, concl)
      neg_brs in
  Format.printf "solve: neg_brs=@ %a@\n%!" Infer.pr_rbrs neg_brs; (* *)
  let neg_cns = List.map
      (fun (prem, concl) ->
         let loc =
           match List.find (function CFalse _ -> true | _ -> false) concl
           with CFalse loc -> loc | _ -> assert false in
         prem, loc)
      neg_brs in
  Format.printf "solve: neg_cns=@ %a@\n%!" Infer.pr_rbrs
    (List.map (fun (cnj,_) -> cnj, []) neg_cns); (* *)
  let negchi_locs = Hashtbl.create 8 in
  List.iter
    (fun (prem,concl) ->
       List.iter
         (function
           | PredVarU (i, TVar b, lc_p) ->
             let lc_c = formula_loc concl in
             Hashtbl.add negchi_locs b (loc_union lc_p lc_c);
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
           | PredVarB (i, TVar b, _, _) ->
             q.add_bchi b i ~posi:true ~chiK:true
           | _ -> ()) concl;
    ) brs;
  let bparams () = List.map
      (fun b -> b, Hashtbl.find q.b_vs b) q.negbs in
  let zparams = List.map (fun b -> b, ref VarSet.empty) q.negbs in
  Format.printf "zparams: init=@ %a@\n%!" Abduction.pr_vparams
    (List.map (fun (v,p)->v,!p) zparams); (* *)
  let modified = ref true in
  let add_atom a =
    let avs = VarSet.filter
        (fun v -> not (uni_v v) || List.mem v q.negbs) (fvs_atom a) in
    List.iter
      (fun (b, zpms) ->
         (* FIXME: [cmp_v b v = Upstream]? *)
         let avs = VarSet.filter
             (fun v->cmp_v b v <> Downstream) avs in
         let zvs = VarSet.add b !zpms in
         if VarSet.exists (fun a -> VarSet.mem a zvs) avs
         && not (VarSet.is_empty (VarSet.diff avs zvs))
         then (zpms := VarSet.union avs !zpms; modified := true))
      zparams in
  while !modified do
    modified := false;
    List.iter
      (fun (prem,concl) ->
         List.iter add_atom prem; List.iter add_atom concl)
      brs
  done;
  let zparams = List.map
      (fun (b,pms) -> b, VarSet.diff !pms (Hashtbl.find q.b_vs b)) zparams in
  Format.printf "zparams: prior=@ %a@\n%!" Abduction.pr_vparams zparams;
  let zparams = List.map
      (fun (b1, pms) ->
         b1, List.fold_left
           (fun pms (b2, pms2) ->
              if cmp_v b1 b2 = Upstream
              then VarSet.diff pms
                  (VarSet.union (Hashtbl.find q.b_vs b2) pms2)
              else pms)
           pms zparams)
      zparams in
  Format.printf "zparams: post=@ %a@\n%!" Abduction.pr_vparams zparams;
  (* keys in sorted order! *)
  let solT = List.map
      (fun i -> i, ([], []))
      (Ints.elements q.allchi) in
  let rolT, solT = List.partition (q.is_chiK % fst) solT in
  let rec loop iter_no discard rol1 sol1 =
    let brs0 = sb_brs_PredU q sol1 brs in
    let brs1 = sb_brs_PredB q rol1 brs0 in
    (* Collect all relevant constraints together. *)
    let verif_brs = List.map
        (fun (nonrec, chiK, prem, _) ->
           nonrec, chiK, prem,
           concat_map
             (fun (_,_,prem2,concl2) ->
                if subformula prem2 prem then concl2 else [])
             brs1)
        brs1 in
    Format.printf "solve: loop iter_no=%d@\nsol=@ %a@\n%!"
      iter_no pr_chi_subst sol1; (* *)
    Format.printf "brs=@ %a@\n%!" Infer.pr_rbrs4 brs1; (* *)
    let validate ans = List.iter
        (fun (nonrec, _, prem, concl) ->
           (* Do not use quantifiers, because premise is in the
              conjunction. *)
           if not nonrec then (
             Format.printf
               "validate-postcond: ans=%a@ prem=%a@ concl=%a@\n%!"
               pr_formula ans pr_formula prem pr_formula concl; (* *)
             let sb_ty, ans_num, ans_so =
               unify cmp_v uni_v (ans @ prem @ concl) in
             Format.printf
               "validate-postcond: sb_ty=@ %a@\nans_num=@ %a@\n%!"
               pr_subst sb_ty pr_formula ans_num; (* *)
             let num_state (* _ *) =
               NumS.satisfiable_exn ans_num in
             Format.printf "validate-postcond: num_state=@ %a@\n%!"
               pr_formula (NumS.formula_of_state num_state); (* *)
             ()))
        verif_brs in
    let brs1, g_rol =
      if iter_no < disj_step.(0) then brs1, rol1
      else
        (* 1 *)
        let g_rol = collect
            (concat_map
               (fun (nonrec,chiK_pos,prem,concl) ->
                  if nonrec || disj_step.(2) <= iter_no
                  then
                    List.map
                      (fun (i,t1,t2,lc) ->
                         let phi = Eqty (tdelta, t1, lc) :: prem @ concl in
                         Format.printf
                           "chiK: i=%d@ t1=%a@ t2=%a@ prem=%a@\nphi=%a@\n%!"
                           i (pr_ty false) t1 (pr_ty false) t2
                           pr_formula prem pr_formula phi;
                         (* *)
                         (i,t2), phi)
                      chiK_pos
                  else [])
               verif_brs) in
        let g_rol = List.map (fun ((i,t2),cnjs) -> i, (t2, cnjs)) g_rol in
        Format.printf "solve: g_rol keys=%a@\n%!"
          (pr_sep_list "| " (fun ppf (i,(t,_)) ->
               Format.fprintf ppf "%d,%a" i (pr_ty false) t)) g_rol;
        (* *)
        assert (is_unique (List.map fst g_rol));
        (* 2 *)
        let g_rol = List.map
            (fun (i,(t2,cnjs)) ->
               i, t2, connected ~validate ~directed:true [delta; delta']
                  (DisjElim.disjelim cmp_v uni_v
                     ~do_num:(disj_step.(1) <= iter_no) cnjs))
            g_rol in
        Format.printf "solve: iter_no=%d@\ng_rol.A=%a@\n%!"
          iter_no pr_chi_subst (List.map (fun (i,_,a)->i,a) g_rol);
        (* *)
        (* 3 *)
        let lift_ex_types cmp_v (g_vs, g_ans) =
          let fvs = VarSet.elements
              (VarSet.diff (fvs_formula g_ans)
                 (vars_of_list [delta;delta'])) in
          let vs, g_ans = simplify cmp_v uni_v (fvs, g_ans) in
          let pvs = VarSet.elements
              (VarSet.diff (vars_of_list vs) (vars_of_list g_vs)) in
          let targs = List.map (fun v -> TVar v) pvs in
          (* FIXME *)
          let phi =
            match targs with
            | [targ] ->
              Eqty (tdelta', targ, dummy_loc) :: g_ans
            | _ ->
              Eqty (tdelta', TCons (CNam "Tuple", targs), dummy_loc)
              :: g_ans in
          Format.printf
            "lift_ex_types: pvs=%a@ g_vs=%a@ g_ans=%a@ phi=%a@\n%!"
            pr_vars (vars_of_list pvs)
            pr_vars (vars_of_list g_vs) pr_formula g_ans pr_formula phi;
          (* *)
          pvs @ g_vs, phi in
        (* 4 *)
        let g_rol = List.map2
            (fun (i,ans1) (j,t2,(g_vs,g_ans)) ->
               assert (i = j);
               let g_cmp_v = cmp_v' g_vs in
               let g_ans = List.filter
                   (function Eqty (t, _, _) when t=t2 -> false
                           | _ -> true) g_ans in
               let ans2 =
                 converge g_cmp_v uni_v
                   ~check_only:(iter_no < disj_step.(3)) ans1 (g_vs, g_ans) in
               let ans2 =
                 (* simplify g_cmp_v uni_v *) (lift_ex_types g_cmp_v ans2) in
               Format.printf "solve.loop-dK: t2=%a final@ ans2=%a@\n%!"
                 (pr_ty false) t2 pr_ans ans2; (* *)
               (* No [b] "owns" these formal parameters. Their instances
                  will be added to [q] by [sb_brs_pred]. *)
               i, ans2
            ) rol1 g_rol in
        Format.printf "solve: loop iter_no=%d@\ng_rol.B=@ %a@\n%!"
          iter_no pr_chi_subst g_rol; (* *)
        sb_brs_PredB q g_rol brs0, g_rol in
    Format.printf "solve-loop: iter_no=%d -- ex. brs substituted@\n%!"
      iter_no; (* *)
    Format.printf "brs=@ %a@\n%!" Infer.pr_rbrs4 brs1; (* *)
    (* 5a *)
    let neg_cns1 = List.map
        (fun (prem,loc) -> sb_formula_pred q false g_rol sol1 prem, loc)
        neg_cns in
    let bparams = bparams () in
    (* let bvs =
       VarSet.filter (fun v->not (q.positive_b v)) q.allbvs in *)
    let bvs = List.fold_left            (* equivalent *)
        (fun pms (_, bpms) -> VarSet.union pms bpms)
        VarSet.empty bparams in
    let zvs = List.fold_left
        (fun pms (_, zpms) -> VarSet.union pms zpms)
        VarSet.empty zparams in
    let params = VarSet.union bvs zvs in
    let answer =
      try
        (* 5b *)
        (* Check negative constraints ("assert false" clauses) once
           all positive constraints have been involved in answering. *)
        if !neg_constrns && iter_no > 1 then List.iter
            (* raise [NoAnswer] when needed *)
            (fun (cnj, loc) ->
               try
                 Format.printf "neg_cl_check: cnj=@ %a@\n%!" pr_formula
                   cnj; (* *)
                 let ty_cn (*_*), num_cn, _ =
                   unify cmp_v uni_v cnj in
                 if num_cn = [] then (
                   Format.printf
                     "neg_cl_check: fallback typ@ ty_cn=@ %a@\n%!"
                     pr_subst ty_cn; (* *)
                   raise
                     (NoAnswer (Type_sort, "negative clause", None, loc)));
                 if Aux.is_right (NumS.satisfiable num_cn) then (
                   Format.printf
                     "neg_cl_check: fallback num@ num_cn=@ %a@\n%!"
                     pr_formula num_cn; (* *)
                   raise
                     (NoAnswer (Num_sort,
                                "negative clause", None, loc)));
                 Format.printf
                   "neg_cl_check: passed (num)@ ty_cn=@ %a@\nnum_cn=@ %a@\n%!"
                   pr_subst ty_cn pr_formula num_cn; (* *)
               with Contradiction (sort, msg, tys, lc) ->
                 Format.printf "neg_cl_check: passed (typ) msg=%s@\n%!" msg;
                 (match tys with
                  | Some (t1, t2) ->
                    Format.printf
                      "types involved: ty1=%a;@ ty2=%a@\n%!"
                      (pr_ty false) t1 (pr_ty false) t2
                  | None -> ()); (* *)
                 ())
            neg_cns1;
        (* 6 *)
        let brs1 = List.map
            (fun (nonrec,_,prem,concl) -> nonrec,prem,concl) brs1 in
        let alien_eqs, (vs, ans) =
          Abduction.abd cmp_v uni_v ~bvs ~zvs ~bparams ~zparams
            ~iter_no ~discard brs1 in
        let ans_res, more_discard, ans_sol =
          split vs ans negchi_locs params zparams q in
        Format.printf
          "solve: loop -- answer split@ more_discard=@ %a@\nans_res=@ %a@\n%!"
          pr_formula more_discard pr_formula ans_res; (* *)
        Aux.Right (alien_eqs, ans_res, more_discard, ans_sol)
      with
      (* it does not seem to make a difference *)
      | (NoAnswer (sort, msg, tys, lc)
        | Contradiction (sort, msg, tys, lc)) as e ->
        Format.printf
          "Fallback: iter_no=%d; sort=%s;@ msg=%s@\n%!"
          iter_no (sort_str sort) msg;
        (match tys with None -> ()
                      | Some (t1, t2) ->
                        Format.printf "types involved:@ t1=%a@ t2=%a@\n%!"
                          (pr_ty false) t1 (pr_ty false) t2);
        (* *)
        Aux.Left (sort, e) in
    match answer with
    | Aux.Left _ as e -> e
    | Aux.Right (alien_eqs, ans_res, more_discard, ans_sol) ->
      let more_discard =
        if alien_eqs = [] then more_discard
        else subst_formula alien_eqs more_discard in
      (* 10 *)
      let finish rol2 sol2 =
        (* start fresh at (iter_no+1) *)
        match loop (iter_no+1) [] rol2 sol2
        with Aux.Right _ as res -> res
           | Aux.Left (sort, e) ->
             let s_discard =
               List.assoc sort (split_sorts more_discard) in
             if s_discard = [] then raise e;
             let discard =
               update_assoc sort [] (fun dl -> s_discard::dl) discard in
             loop iter_no discard rol1 sol1 in
      (* 7 *)
      let rol2 =
        if disj_step.(0) > iter_no then rol1
        else
          List.map
            (fun (i, (gvs,g_ans)) ->
               let bs = List.filter (not % q.positive_b) (q.find_b i) in
               let ds = List.map (fun b-> b, List.assoc b ans_sol) bs in
               let dans = concat_map
                   (fun (b, (dvs, dans)) ->
                      Format.printf
                        "solve-loop-9: chi%d(%s)=@ %a@ +@ %a@\n%!"
                        i (var_str b) pr_ans (dvs,dans) pr_ans
                        (gvs,g_ans);
                      (* *)
                      (* No need to substitute, because variables will be
                         freshened when predicate variable is instantiated. *)
                      let sb = renaming_sb
                          ((b, delta)::Hashtbl.find q.b_renaming b) in
                      subst_formula sb dans)
                   ds in
               let dvs = gvs @ concat_map (fun (_,(dvs,_))->dvs) ds in
               let i_res =
                 simplify (cmp_v' dvs) uni_v
                   (connected ~directed:true [delta; delta']
                      (dvs, dans @ g_ans)) in
               Format.printf
                 "solve-loop: dans=%a@ chi%d(.)=@ %a@\n%!"
                 pr_formula dans i pr_ans i_res; (* *)
               i, i_res)
            g_rol in
      (* 8 *)
      let sol2 = List.map
          (fun (i, (vs, ans)) ->
             let bs = List.filter (not % q.positive_b) (q.find_b i) in
             let b = match bs with [b] -> b | _ -> assert false in
             let dvs, dans = List.assoc b ans_sol in
             Format.printf
               "solve-loop-9: chi%d(%s)=@ %a@ +@ %a@\n%!"
               i (var_str b) pr_ans (dvs,dans) pr_ans (vs,ans); (* *)
             (* No need to substitute, because variables will be
                freshened when predicate variable is instantiated. *)
             let dans = subst_formula [b, (tdelta, dummy_loc)] dans in
             let dvs, ans' =
               simplify (cmp_v' dvs) uni_v (dvs, dans @ ans) in
             let i_res = dvs @ vs, ans' in
             Format.printf
               "solve-loop: vs=%a@ ans=%a@ chi%d(.)=@ %a@\n%!"
               pr_vars (vars_of_list vs) pr_formula ans i pr_ans i_res; (* *)
             i, i_res)
          sol1 in    
      (* 9 *)
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
      Format.printf "solve-loop: finished 1=%b, 2=%b, 3=%b, r=%b@\n%!"
        finished1 finished2 finished3 finished; (* *)
      if iter_no > 1 && finished
      then                              (* final solution *)
        Aux.Right (ans_res, rol2, sol2)
        (* Do at least three iterations: 0, 1, 2. *)
      else if iter_no <= 1 && finished
      then loop (iter_no+1) [] rol2 sol1
      else finish rol2 sol2 in
  match loop 0 [] rolT solT with
  | Aux.Left (_, e) -> raise e
  | Aux.Right (ans_res, rol, sol as ans) ->
    Format.printf "solve: checking assert false@\n%!"; (* *)
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
    let ans_sb, _ = Infer.separate_subst cmp_v uni_v ans_res in
    (* Substitute the solutions for existential types. *)
    List.iter
      (fun (ex_i, loc) ->
         let _, exphi, ty, _, pvs = Hashtbl.find ex_types ex_i in
         let ty = match ty with [ty] -> ty | _ -> assert false in
         let chi_i, t1, t2 =
           match exphi with
           | [PredVarB (chi_i,t1,t2,_)] -> chi_i, t1, t2
           | _ -> assert false in
         assert (ty = t1 && t1 = tdelta);
         assert (t2 = tdelta' && pvs = [delta']);
         let chi_vs, phi = List.assoc chi_i rol in
         let sb, rphi = Infer.separate_subst cmp_v uni_v phi in
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
           try fvs_typ (fst (List.assoc delta' sb))
           with Not_found -> VarSet.singleton delta' in
         let allvs = VarSet.union (fvs_formula rphi) (fvs_typ rty) in
         Format.printf
           "solve-ex_types: ex_i=%d@ t1=%a@ t2=%a@ ty=%a@ chi_vs=%a@ rty=%a@ allvs=%a@ pvs=%a@ rphi=%a@ @\nphi=%a@\n%!"
           ex_i (pr_ty false) t1 (pr_ty false) t2 (pr_ty false) ty
           pr_vars (vars_of_list chi_vs) (pr_ty false) rty
           pr_vars allvs pr_vars pvs
           pr_formula rphi pr_formula phi;
         (* *)
         let pvs = VarSet.elements pvs and ety_n = Extype ex_i in
         Hashtbl.replace ex_types ex_i
           (VarSet.elements allvs, rphi, [rty], ety_n, pvs)) !new_ex_types;
    Format.printf "solve: returning@\n%!"; (* *)
    cmp_v, uni_v, ans
