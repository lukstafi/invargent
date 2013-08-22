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
  (** Add local variables of [chi(b)] instance, paired with keys
      -- corresponding variables of formal [chi(delta)]. *)
  add_b_vs_of : var_name -> (var_name * var_name) list -> unit;
  b_vs : (var_name, VarSet.t) Hashtbl.t;
  b_qvs : (var_name, var_name list) Hashtbl.t;
  (** Renaming into [b_qvs], redundant but more idiot-proof *)
  b_renaming : (var_name, (var_name * var_name) list) Hashtbl.t;
  add_bchi : var_name -> int -> bool -> unit;
  find_b : int -> var_name list;
  find_chi : var_name -> int;
  mutable allbvs : VarSet.t;
  mutable allchi : Ints.t;
  mutable negbs : var_name list;
}
  
let new_q cmp_v uni_v =
  let same_q = Hashtbl.create 32 in
  let posi_b = Hashtbl.create 16 in
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
  let b_vs = Hashtbl.create 16 in
  let b_renaming = Hashtbl.create 16 in
  let b_qvs = Hashtbl.create 16 in
  let chi_b = Hashtbl.create 16 in
  let b_chi = Hashtbl.create 16 in
  let find_b i = Hashtbl.find_all chi_b i in
  let find_chi b = Hashtbl.find b_chi b in
  let rec add_bchi b i posi =
    if Hashtbl.mem b_chi b
    then assert (Hashtbl.find b_chi b = i)
    else (
      Format.printf "add_bchi: chi%d(%s);@ posi=%b@\n%!"
        i (var_str b) posi; (* *)
      if posi then Hashtbl.add posi_b b ()
      else q.negbs <- b::q.negbs;
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
    add_bchi; find_b; find_chi;
    positive_b; negbs = [];
  } in q

(* Return renaming of [vs], creating fresh [rvs] pairs when
   needed and adding them as locals of [b] in [q]. *)
let matchup_vars ?dK self_owned q b vs =
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
  (* [~dK] only substitutes new variables from disjunction elimination *)
  (* FIXME: seems to work but breaks the assert. *)
  (* if dK=None then assert (List.length res = List.length vs + 1); *)
  List.map (fun (v,w) -> v, (TVar w, dummy_loc)) res

let sb_chiK_neg q psb (i, t1, t2) =
  match t1 with TVar b ->
    (try
       let vs, phi = List.assoc i psb in
       Format.printf
         "sb_chiK_neg: chi%d(%s,%a)=@ %a@\n%!"
         i (var_str b) (pr_ty false) t2 pr_ans (vs,phi); (* *)
       let renaming = matchup_vars ~dK:() false q b vs in
       sb_phi_binary t1 t2 (subst_formula renaming phi)
     with Not_found -> [])
  | _ -> []

let sb_atom_pred q posi psb = function
  | PredVarU (i, (TVar b as t)) as a ->
    (try
       let vs, phi = List.assoc i psb in
       Format.printf
         "sb_atom_pred: U posi=%b@ chi%d(%s)=@ %a@\n%!"
         posi i (var_str b) pr_ans (vs,phi); (* *)
       let renaming = matchup_vars (not posi) q b vs in
       sb_phi_unary t (subst_formula renaming phi)
     with Not_found -> [a])  
  | PredVarB (i, (TVar b as t1), t2) as a ->
    (try
       let vs, phi = List.assoc i psb in
       Format.printf
         "sb_atom_pred: B posi=%b@ chi%d(%s,%a)=@ %a@\n%!"
         posi i (var_str b) (pr_ty false) t2 pr_ans (vs,phi); (* *)
       let renaming = matchup_vars false q b vs in
       sb_phi_binary t1 t2 (subst_formula renaming phi)
     with Not_found -> [a])
  | a -> [a]

let sb_formula_pred q posi psb phi =
  concat_map (sb_atom_pred q posi psb) phi

let sb_brs_allpred q psb brs = List.map
  (fun (prem,concl) ->
    List.for_all                        (* is_nonrec *)
      (function PredVarU _ -> false | _ -> true) concl,
    Aux.map_some                        (* chiK_neg *)
      (function PredVarB (i,t1,t2) -> Some (i,t1,t2) | _ -> None) prem,
    Aux.map_some                        (* chiK_pos *)
      (function PredVarB (i,t1,t2) -> Some (i,t1,t2) | _ -> None) concl,
    sb_formula_pred q false psb prem, sb_formula_pred q true psb concl)
  brs

let sb_brs_dK q psb brs = List.map
  (fun (nonrec,chiK_neg,chiK_pos,prem,concl) ->
    nonrec,
    concat_map (sb_chiK_neg q psb) chiK_neg @ prem, concl)
  brs

let pr_chi_subst ppf chi_sb =
  pr_sep_list ";" (fun ppf (i,ans) ->
    Format.fprintf ppf "𝛘%d:=%a" i pr_ans ans) ppf chi_sb

let pr_bchi_subst ppf chi_sb =
  pr_sep_list ";" (fun ppf (v,ans) ->
    Format.fprintf ppf "𝛘(%s):=%a" (var_str v) pr_ans ans) ppf chi_sb

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

(* 4 *)
let select check_max_b q ans ans_max =
  let allmax = concat_map snd ans_max in
  let init_res = list_diff ans allmax in
  Format.printf "select: allmax=@ %a@\ninit_res=@ %a@\n%!"
      pr_formula allmax pr_formula init_res; (* *)
  (* Raises [Contradiction] here if solution impossible. *)
  let init_state = holds q empty_state init_res in
  let rec loop state ans_res ans_p = function
    | [] -> ans_res, ans_p
    | c::cands ->
      try
        let state = holds q state [c] in
        Format.printf "select: dropping@ %a@\n%!"
          pr_atom c; (* *)
        loop state (c::ans_res) ans_p cands
      with Contradiction _ ->
        let vs = fvs_atom c in
        Format.printf "select: preserving@ %a@\n%!" pr_atom c; (* *)
        let ans_p = List.map
          (fun (b,ans as b_ans) ->
            if check_max_b vs b then b, c::ans else b_ans)
          ans_p in
        Format.printf "select: preserving ans_p=@\n%a@\n%!"
          (pr_line_list "| " pr_formula)
          (List.map (fun (b,ans) ->
            Eqty (TVar b, TVar b, dummy_loc)::ans) ans_p); (* *)
        loop state ans_res ans_p cands in
  let ans_p = List.map (fun (b,_)->b,[]) ans_max in
  loop init_state init_res ans_p allmax

(* 5 *)
let strat q b ans =
  let (_, ans_r), ans = fold_map
    (fun (pvs, ans_r) c ->
      let vs = VarSet.elements (VarSet.diff (fvs_atom c) pvs) in
      let vs = List.filter
        (fun v -> q.cmp_v b v = Upstream) vs in
      let loc = atom_loc c in
      if List.exists q.uni_v vs then
        (let bad = List.find q.uni_v vs in
         raise (Contradiction
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
  
let split avs ans params zparams q =
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
  let smaller_v v1 v2 = cmp_v v1 v2 = Downstream in
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
    let ans0 = List.map (fun c -> c, fvs_atom c) ans0 in
    (* 3a *)
    let b_pms = List.map
      (fun b ->
        let pms = Hashtbl.find q.b_vs b in
        let pms = VarSet.union pms (List.assoc b zparams) in
        b, pms)
      q.negbs in
    let check_max_b vs b =
      let pms = List.assoc b b_pms in
      (* most downstream *)
      let vmax = minimal ~less:smaller_v
        (VarSet.elements (VarSet.inter vs params)) in
      Format.printf "check_max_b:@ vs=%a@ pms=%a@ vmax=%a@ max?=%b@\n%!"
        pr_vars vs pr_vars pms pr_vars (vars_of_list vmax)
        (List.exists (fun v -> VarSet.mem v pms) vmax); (* *)
      List.exists (fun v -> VarSet.mem v pms) vmax in
    let ans_cap = List.map
      (fun b ->
        b, map_some
          (fun (c, vs) -> if check_max_b vs b then Some c else None)
          ans0)
      q.negbs in
    (* 4, 9a *)
    let ans_res, ans_ps =
      try select check_max_b q ans ans_cap
      with Contradiction (sort,msg,tys,lc) ->
        let cnj = concat_map snd ans_cap in
        (* It would make sense to fallback from here, but for
           efficiency these violations should have been already
           detected by abduction. *)
        (* raise
          (NoAnswer (sort, cnj, msg, tys, lc)) *)
        Format.printf
          "split-NoAnswer: sort=%s;@ msg=%s;@ cnj=%a@\n%!"
          (sort_str sort) msg pr_formula cnj;
        (match tys with None -> ()
        | Some (t1, t2) ->
          Format.printf "types involved:@ t1=%a@ t2=%a@\n%!"
            (pr_ty false) t1 (pr_ty false) t2);
        (* *)
        assert false in
    let more_discard = concat_map snd ans_ps in
    (* 5 *)
    let ans_strat = List.map
      (fun (b, ans_p) ->
        Format.printf "select: ans_chi(%s)=@ %a@\n%!"
          (var_str b) pr_formula ans_p; (* *)
        let (avs_p, ans_l, ans_r) = strat q b ans_p in
        Format.printf "select: ans_l(%s)=@ %a@\n%!"
          (var_str b) pr_formula ans_l; (* *)
        (* Negatively occurring [b] "owns" these formal parameters *)
        q.add_b_vs_of b (List.map (fun v->v,v) avs_p);
        (* 6 *)
        let ans0 = List.assoc b sol in
        let ans = ans0 @ ans_l in
        (* 7 *)
        let avs0 = VarSet.inter avs (fvs_formula ans) in
        (* 8.a *)
        let avs = VarSet.union avs0 (vars_of_list avs_p) in
        (b, avs), (b, ans), (avs_p, ans_r))
      ans_ps in
    let avss, sol', more = split3 ans_strat in
    let avs_ps, ans_rs = List.split more in
    (* 8.b *)
    let avss = List.map
      (fun (b, avs) ->
        let lbs = List.filter
          (fun b' -> q.cmp_v b b' = Downstream) q.negbs in
        let uvs = List.fold_left VarSet.union VarSet.empty
          (List.map (flip List.assoc avss) lbs) in
        VarSet.diff avs uvs)
      avss in
    (* 9b *)
    let ans_p = List.concat ans_rs in
    Format.printf "split: ans_p=@ %a@ --@ ans_res=@ %a@\n%!"
      pr_subst ans_p pr_formula ans_res; (* *)
    let ans_res = to_formula ans_p @ subst_formula ans_p ans_res in
    Format.printf "split: ans_res'=@ %a@\n%!"
      pr_formula ans_res; (* *)
    let avs_p = List.concat avs_ps in
    let avsl = List.map VarSet.elements avss in
    (* 10 *)
    if avs_p <> []
    then
      (* 11 *)
      let avs' = VarSet.diff avs
        (List.fold_left VarSet.union VarSet.empty avss) in
      let ans_res', discard', sol' =
        loop avs' ans_res (more_discard @ discard) sol' in
      (* 12 *)
      ans_res', discard',
      List.map2
        (fun avs (b, (avs', ans')) -> b, (avs@avs', ans')) avsl sol'
    else
      (* 13 *)
      ans_res, more_discard @ discard,
      List.map2 (fun avs (b, ans) -> b, (avs, ans)) avsl sol' in
  let solT = List.map (fun b->b, []) q.negbs in
  loop (vars_of_list avs) ans [] solT  

(** Perform quantifier elimination on provided variables and generally
    simplify the formula. *)
let simplify cmp_v uni_v vs cnj =
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
    (fun (v,_) -> VarSet.mem v vs) ty_ans in
  let ty_ans = subst_formula ty_sb (to_formula ty_ans) in
  let ty_vs = VarSet.inter vs (fvs_formula ty_ans)
  and num_vs = VarSet.inter vs (fvs_formula num_ans) in
  let elimvs = VarSet.diff num_vs ty_vs in
  let _, num_ans =
    NumS.simplify cmp_v uni_v elimvs num_ans in
  VarSet.elements ty_vs,
  ty_ans @ num_ans

let converge sol0 sol1 sol2 =
  (* TODO *)
  sol2

let neg_constrns = ref true

(* FIXME: remove t26 from pms for t1 *)
let solve cmp_v uni_v brs =
  let q = new_q cmp_v uni_v in
  let cmp_v = q.cmp_v and uni_v = q.uni_v in
  let neg_brs, brs = List.partition
    (fun (_,concl) -> List.exists
      (function CFalse _ -> true | _ -> false) concl) brs in
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
  List.iter
    (fun (prem,concl) ->
      List.iter
        (function
        | PredVarU (i, TVar b) | PredVarB (i, TVar b, _) ->
          q.add_bchi b i false
        | _ -> ()) prem;
      List.iter
        (function
        | PredVarU (i, TVar b) | PredVarB (i, TVar b, _) ->
          q.add_bchi b i true
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
  let rec loop iter_no discard sol0 sol1 =
    let brs1 = sb_brs_allpred q sol1 brs in
    Format.printf "solve: loop iter_no=%d -- brs substituted@\n%!"
      iter_no; (* *)
    Format.printf "brs=@ %a@\n%!" Infer.pr_rbrs5 brs1; (* *)
    (* 1 *)
    let chiK = collect
      (concat_map
         (fun (_,_,chiK_pos,prem,concl) -> List.map
           (fun (i,t1,t2) ->
             let phi = Eqty (tdelta, t1, dummy_loc) :: prem @ concl in
             Format.printf "chiK: i=%d@ t1=%a@ t2=%a@ phi=%a@\n%!"
               i (pr_ty false) t1 (pr_ty false) t2 pr_formula phi;
             (* *)
             (i,t2), phi)
           chiK_pos)
         brs1) in
    let chiK = List.map (fun ((i,t2),cnjs) -> i, (t2, cnjs)) chiK in
    (* 2 *)
    let dK = List.map
      (fun (i,(t2,cnjs)) ->
        i, connected [delta] (DisjElim.disjelim cmp_v uni_v cnjs)) chiK in
    let dK = map_some
      (fun (i,(gvs, g_ans)) ->
        let vs, ans = List.assoc i sol1 in
        (* Adding to quantifier for [abd_s] and [simplify]. *)
        let cmp_v' gvs v1 v2 =
          let c1 = List.mem v1 gvs and c2 = List.mem v2 gvs in
          if c1 && c2 then Same_quant
          else if c1 then Downstream
          else if c2 then Upstream
          else cmp_v v1 v2 in
        Format.printf "solve.loop-dK: before abd_s@ gvs=%a@ g_ans=%a@\n%!"
          pr_vars (vars_of_list gvs) pr_formula g_ans; (* *)
        (* FIXME: what about quantifiers? parameters? *)
        match Abduction.abd_s (cmp_v' gvs) uni_v ans g_ans with
        | None -> None
        | Some (gvs', g_ans') ->
          (* 3 *)
          Format.printf "solve.loop-dK: before simpl@ gvs'=%a@ g_ans'=%a@\n%!"
            pr_vars (vars_of_list gvs') pr_formula g_ans'; (* *)
          let gvs', g_ans' =
            simplify (cmp_v' (gvs' @ gvs)) uni_v gvs' g_ans' in
          if g_ans' = [] then None
          else
            let gvs = VarSet.elements
              (VarSet.inter (vars_of_list (gvs @ gvs')) (fvs_formula g_ans')) in
            Format.printf "solve.loop-dK: final@ gvs=%a@ g_ans=%a@\n%!"
              pr_vars (vars_of_list gvs) pr_formula g_ans'; (* *)
            (* No [b] "owns" these formal parameters. Their instances
               will be added to [q] by [sb_brs_pred]. *)
            Some ((i, (gvs @ vs, g_ans' @ ans)),
                  (i, (gvs, g_ans')))
      ) dK in
    let repl_dK, upd_dK = List.split dK in
    Format.printf "solve: loop; #dK=%d@ upd_dK=%a@\n%!"
      (List.length dK) pr_chi_subst upd_dK; (* *)
    (* 4 *)
    let sol1 = replace_assocs ~repl:repl_dK sol1 in
    let brs1 = sb_brs_dK q upd_dK brs1 in
    Format.printf "solve-loop: iter_no=%d -- ex. brs substituted@\n%!"
      iter_no; (* *)
    Format.printf "brs=@ %a@\n%!" Infer.pr_rbrs3 brs1; (* *)
    let neg_cns1 = List.map
      (fun (prem,loc) -> sb_formula_pred q false sol1 prem, loc)
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
        (* 5 *)
        let res =
          Abduction.abd cmp_v uni_v ~bvs ~zvs ~bparams ~zparams
            ~iter_no ~discard brs1 in
        (* Beyond this point exceptions mean unsolvability. *)
        Aux.Right res
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
    | Aux.Right (alien_eqs, (vs, ans)) ->
      let ans_res, more_discard, sol2 = split vs ans params zparams q in
      let more_discard =
        if alien_eqs = [] then more_discard
        else subst_formula alien_eqs more_discard in
      Format.printf
        "solve: loop -- answer split@ more_discard=@ %a@\nans_res=@ %a@\nsol=@ %a@\n%!"
        pr_formula more_discard pr_formula ans_res pr_chi_subst sol1; (* *)
      (* 6 *)
      let lift_ex_types t2 (vs, ans) =
        let fvs = fvs_formula ans in
        let dvs = VarSet.elements
          (VarSet.diff fvs (vars_of_list (delta::vs))) in
        let targs = List.map (fun v -> TVar v) dvs in
        let a2 = match t2 with TVar a2 -> a2 | _ -> assert false in
        let phi =
          Eqty (tdelta', TCons (CNam "Tuple", targs), dummy_loc) ::
          subst_formula [a2, (tdelta', dummy_loc)] ans in
        Format.printf
          "lift_ex_types: t2=%a@ vs=%a@ dvs=%a@ ans=%a@ phi=%a@\n%!"
          (pr_ty false) t2 pr_vars (vars_of_list vs)
          pr_vars (vars_of_list dvs) pr_formula ans pr_formula phi;
        (* *)
        vs @ dvs, phi in
      (* 7 *)
      let finish sol2 =
        (* start fresh at (iter_no+1) *)
        match loop (iter_no+1) [] sol1 sol2
        with Aux.Right _ as res -> res
        | Aux.Left (sort, e) ->
          let s_discard =
            List.assoc sort (split_sorts more_discard) in
          if s_discard = [] then raise e;
          let discard =
            update_assoc sort [] (fun dl -> s_discard::dl) discard in
          loop iter_no discard sol0 sol1 in
      if iter_no > 1 && List.for_all (fun (_,(_,ans)) -> ans=[]) sol2
      then                              (* final solution *)
        let sol = List.map
          (fun ((i,sol) as isol) ->
            (* 8 *)
            try let t2, _ = List.assoc i chiK in
                i, lift_ex_types t2 sol
            with Not_found -> isol)
          sol1 in
        (* FIXME: isn't all this simplification redundant? *)
        let res = fold_map
          (fun ans_res (i,(vs0,ans0)) ->
            let d_vs =
              let d = Aux.map_some
                (function Eqty (t1,t2,_) when t1=tdelta' ->
                  Some t2 | _ -> None)
                ans0 in
              VarSet.elements (fvs_typ (TCons (CNam "", d))) in
            let vs0, ans =
              simplify cmp_v uni_v (list_diff vs0 d_vs) ans0 in
            let vs = d_vs @ vs0 in
            let allbs = (* VarSet.union q.allbvs *)
              (vars_of_list (delta::vs)) in
            let more, ans = List.partition
              (fun c-> VarSet.is_empty (VarSet.inter allbs (fvs_atom c)))
              ans in
            Format.printf
              "finish: simplify i=%d@ vs0=%a@ ans0=%a@ vs=%a@ ans=%a@\n%!"
              i pr_vars (vars_of_list vs0) pr_vars (vars_of_list vs)
              pr_formula ans0 pr_formula ans;
            (* *)
            more @ ans_res, (i, (vs, ans)))
          ans_res sol in
        Aux.Right res
      (* Do at least three iterations: 0, 1, 2. *)
      else if iter_no <= 1 && List.for_all (fun (_,(_,ans)) -> ans=[]) sol2
      then loop (iter_no+1) [] sol0 sol1
      else
        (* 9 *)
        let sol2 = List.map
          (fun (i, (vs, ans)) ->
            let bs = List.filter (not % q.positive_b) (q.find_b i) in
            let ds = List.map (fun b-> b, List.assoc b sol2) bs in
            let dans = concat_map
              (fun (b, (dvs, dans)) ->
                Format.printf
                  "solve-loop-9: chi%d(%s)=@ %a@ +@ %a@\n%!"
                  i (var_str b) pr_ans (dvs,dans) pr_ans (vs,ans); (* *)
                (* No need to substitute, because variables will be
                   freshened when predicate variable is instantiated. *)
                subst_formula [b, (tdelta, dummy_loc)] dans
              ) ds in
            let dvs = concat_map (fun (_,(dvs,_))->dvs) ds in
            let i_res = dvs @ vs, dans @ ans in
            Format.printf
              "solve-loop: vs=%a@ ans=%a@ chi%d(.)=@ %a@\n%!"
              pr_vars (vars_of_list vs) pr_formula ans i pr_ans i_res; (* *)
            i, i_res)
          sol1 in    
        (* 10 *)
        finish (converge sol0 sol1 sol2) in
  match loop 0 [] solT solT with
  | Aux.Left (_, e) -> raise e
  | Aux.Right (ans_res, ans_so as sol) ->
    Format.printf "solve: checking assert false@\n%!"; (* *)
    List.iter (fun (cnj, loc) ->
      try
        let cnj = sb_formula_pred q false (snd sol) cnj in
      (* FIXME: rethink. *)
        ignore (satisfiable q empty_state cnj);
        raise (Contradiction (
          (* FIXME *) Type_sort,
          "A branch with \"assert false\" is possible",
          None, loc))
      with Contradiction _ -> ()
    ) neg_cns;
    (* Substitute the solutions for existential types. *)
    ex_types := List.map
      (function
      | ex_i, (([], [PredVarB (chi_i,t1,t2)], ty), loc) ->
        let chi_vs, phi = List.assoc chi_i ans_so in
        let sb, rphi = Infer.separate_subst cmp_v uni_v phi in
        let ans_sb, _ = Infer.separate_subst cmp_v uni_v ans_res in
        let sb = update_sb ~more_sb:ans_sb sb in
        let sb = List.map
          (function
          | v, (TVar v2, lc) when v2=delta || v2=delta' -> v2, (TVar v, lc)
          | sv -> sv) sb in
        let vs = List.map
          (fun v ->
            try fst (List.assoc v sb) with Not_found -> TVar v) chi_vs in
        let vs = VarSet.elements (fvs_typ (TCons (CNam "", vs))) in
        let rty = subst_typ sb ty
        and rphi = subst_formula sb rphi in
        Format.printf
          "solve-ex_types: ex_i=%d@ t1=%a@ t2=%a@ ty=%a@ chi_vs=%a@ rty=%a@ vs=%a@ rphi=%a@\nphi=%a@\n%!"
          ex_i (pr_ty false) t1 (pr_ty false) t2 (pr_ty false) ty
          pr_vars (vars_of_list chi_vs) (pr_ty false) rty
          pr_vars (vars_of_list vs)
          pr_formula rphi pr_formula phi;
        (* *)
        ex_i, ((vs, rphi, rty), loc)
      | ex_i, _ as ex_ty ->
        Format.printf "solve-ex_types: unchanged %d@\n%!" ex_i;
        ex_ty
    ) !ex_types;
    Format.printf "solve: returning@\n%!"; (* *)
    cmp_v, uni_v, sol
