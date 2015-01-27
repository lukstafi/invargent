(** Disjunction elimination for InvarGenT.

    Released under the GNU General Public Licence (version 2 or
    higher), NO WARRANTY of correctness etc. (C) Lukasz Stafiniak 2013
    @author Lukasz Stafiniak lukstafi (AT) gmail.com
    @since Mar 2013
*)

let more_existential = ref false
let preserve_all_typ = ref false
let drop_csts = ref true(* false *)

open Defs
open Terms
open Aux

let antiunif q ~bvs ts =
  let is_uni =
    if !more_existential then q.uni_v
    else (fun v -> q.uni_v v && not (VarSet.mem v bvs)) in
  let rec aux usb gsb = function
    | [] -> assert false
    | t::ts when List.for_all ((=) t) ts-> [], t, usb, gsb
    | TCons (n, t1s)::ts when List.for_all
          (function TCons (n2, _) when n2=n -> true | _ -> false) ts ->
      (*[* Format.printf "antiunif: tcons=%s@ ts=@ %a@\n%!"
        (cns_str n) (pr_sep_list " |" pr_ty) ts; *]*)
      let vs, ss, usb, gsb = auxn usb gsb
          (t1s::List.map
               (function TCons (_, tks) -> tks | _ -> assert false) ts) in
      vs, TCons (n, ss), usb, gsb
    | Fun (t1, t2)::ts when List.for_all
          (function Fun _ -> true | _ -> false) ts ->
      (*[* Format.printf "antiunif: tfun@ ts=@ %a@\n%!"
        (pr_sep_list " |" pr_ty) ts; *]*)
      let vs1, s1, usb, gsb = aux usb gsb
          (t1::List.map
               (function Fun (tk1, _) -> tk1 | _ -> assert false) ts) in
      let vs2, s2, usb, gsb = aux usb gsb
          (t2::List.map
               (function Fun (_, tk2) -> tk2 | _ -> assert false) ts) in
      vs1 @ vs2, Fun (s1, s2), usb, gsb
    | t::_ as ts when typ_sort t <> Type_sort ->
      let x = fresh_var (typ_sort t) in
      (*[* Format.printf "antiunif: num x=%s@ ts=@ %a@\n%!"
        (var_str x) (pr_sep_list " |" pr_ty) ts; *]*)
      [x], TVar x, usb, (ts, x)::gsb
    | t::_ as ts ->
      (*[* Format.printf "antiunif: other@ ts=@ %a@\n%!"
        (pr_sep_list " |" pr_ty) ts; *]*)
      try [], TVar (List.assoc ts gsb), usb, gsb
      with Not_found ->
        let n =
          find_map (function TCons (n, _) -> Some n | _ -> None) ts in
        let tn =
          try Some (List.find (function TCons _ -> true | _ -> false) ts)
          with Not_found -> None in
        let b = find_map
            (function TVar v when is_uni v -> Some v | _ -> None)
            ts in
        if n <> None && List.for_all
             (function TCons _ as t2 when Some t2=tn -> true
                     | TVar v -> not (is_uni v) | _ -> false) ts
        then
          let t = unsome tn in
          let more_sb = map_some
            (function
              | TVar v -> Some (v, (t, dummy_loc))
              | _ -> None)
            ts in
          let usb = update_sb ~more_sb usb in
          [], t, usb, gsb
        else if n <> None && List.for_all
             (function TCons (n2, _) when Some n2=n -> true
                     | TVar v -> not (is_uni v) | _ -> false) ts
        then
          let n, args = unsome
              (find_map (function TCons (n, a) -> Some (n,a)
                                | _ -> None) ts) in
          (*[* Format.printf "antiunif: abduct n=@ %s@\n%!"
            (cns_str n); *]*)
          let usb, avs = List.fold_left
              (fun (sb, avs as acc) -> function
                 | TVar v ->
                   let vs = List.map
                       (fun t -> fresh_var (typ_sort t)) args in
                   let t = TCons (n, List.map (fun v->TVar v) vs) in
                   let usb =
                     update_sb ~more_sb:[v, (t, dummy_loc)] usb in
                   let avs = vs @ avs in
                   usb, avs
                 | _ -> acc)
              (usb, []) ts in
          let ts = List.map (subst_typ usb) ts in
          let vs', g, usb, gsb = aux usb gsb ts in
          avs @ vs', g, usb, gsb
        else if n = None && not !more_existential &&
                (b = None && List.for_all
                  (function TVar v -> not (is_uni v) | _ -> false) ts
                 || List.for_all
                  (function TVar v -> Some v = b || not (q.uni_v v)
                          | _ -> false) ts)
        then
          let vars = List.map
              (function TVar v -> v | _ -> assert false) ts in
          let b = match b with
            | Some b -> b
            | None ->
              (* get the leftmost variable *)
              maximum ~leq:(fun v w -> q.cmp_v v w <> Left_of) vars in
          (*[* Format.printf "antiunif: abduct b=@ %s@\n%!"
            (var_str b); *]*)
          let tb = TVar b in
          let more_sb = map_some
            (fun v -> if v=b then None else Some (v, (tb, dummy_loc)))
            vars in
          let usb = update_sb ~more_sb usb in
          let ts = List.map (subst_typ usb) ts in
          aux usb gsb ts
        else(* *)
          let x = fresh_var (typ_sort t) in
          (*[* Format.printf "antiunif: abduct x=@ %s@\n%!"
            (var_str x);
          if n = None then (List.iter
              (function TVar v -> Format.printf "uni(%s)=%b; "
                                    (var_str v) (is_uni v);
                          | t -> Format.printf "non-v %a; " pr_ty t)
              ts; Format.printf "@\n%!");
          *]*)
          [x], TVar x, usb, (ts, x)::gsb

  and auxn usb gsb = function
    | [] -> [], [], usb, gsb
    | []::_ -> [], [], usb, gsb
    | (t1::t1s)::ts ->
      let v1s, s, usb, gsb = aux usb gsb (t1::List.map List.hd ts) in
      let vs, ss, usb, gsb = auxn usb gsb (t1s::List.map List.tl ts) in
      v1s @ vs, s::ss, usb, gsb in

  aux [] [] ts

type a = var_name * (typ list * loc list)
type b = var_name * (typ * loc)

module EqsSet =
    Set.Make (struct type t = b
                     let compare (v1,(t1,_)) (v2,(t2,_)) =
                       Pervasives.compare (v1,t1) (v2,t2) end)
let eqs_of_list l =
  List.fold_right EqsSet.add l EqsSet.empty

let pr_ty_brs ppf brs =
  pr_line_list "|  " pr_subst ppf brs

(* TODO: filter according to [preserve] variables. *)
let disjelim_typ q ~bvs ~target (* ~preserve *) brs =
  let cmp_k (v1,_) (v2,_) = compare v1 v2 in
  let brs = List.map (List.sort cmp_k) brs in
  (*[* Format.printf "disjelim_typ: bvs=%a@ target=%s@\nbrs=@ %a@\n%!"
    pr_vars bvs (var_str target) (pr_line_list "| " pr_subst) brs; *]*)
  let empty_brs = List.map (fun _ -> []) brs in
  let empty_eqs =
    {at_typ=empty_brs; at_num=empty_brs; at_ord=empty_brs; at_so=()} in
  match brs with
  | [] -> assert false
  | [br] ->
    let br = List.filter (fun (v,_) -> v = target) br in
    [], [], br, empty_eqs
  | br::more_brs ->
    (* (a) V *)
    let br =
      if !preserve_all_typ then br
      else List.filter (fun (v,_) -> v = target) br in
    let gs = List.map (fun (v,(t,lc)) -> v,([t],[lc])) br in
    let aux =
      inter_merge
        cmp_k (fun (_,(ts,lcs)) (v,(t,lc)) -> v, (t::ts,lc::lcs)) in
    let gs = List.fold_left aux gs more_brs in
    if gs = [] then [], [], [], empty_eqs
    else
      let gs = List.map
        (fun (v,(ts,lcs)) -> v, (List.rev ts, List.rev lcs)) gs in
      (* (b) G *)
      let usb, gs = fold_map
        (fun usb (v,(ts,lcs)) ->
          let ts = List.map (subst_typ usb) ts in
          let gvs,gt,usb',tss = antiunif q ~bvs ts in
          update_sb ~more_sb:usb' usb, (v, gvs, gt, tss, lcs))
        [] gs in
      let avs = concat_map (fun (_,vs,_,_, _) -> vs) gs in
      (* A set of sequences position-matched with branches. *)
      (* (c) D^u_i *)
      (*[* Format.printf "disjelim_typ: #brs=%d #gs=%d avs=%a@\n%!"
        (List.length brs) (List.length gs)
        pr_vars (vars_of_list avs);
      List.iter
        (fun (v,gvs,gt,tss,lcs) ->
          Format.printf
            "disjelim_typ: v=%s@ gvs=%a@ gt=%a@ #tss=%d@ #tss[0]=%d@ #lcs=%d@\n%!"
            (var_str v) pr_vars (vars_of_list gvs) pr_ty gt
            (List.length tss)
            (if tss=[] then -1 else (List.length (fst (List.hd tss))))
            (List.length lcs);
        ) gs;
      *]*)
      let eqs = 
        List.map
          (fun (_,_,_,tss,lcs) ->
            let brs =
              if tss=[] then empty_brs
              else transpose_lists
                (List.map (fun (ts, v) -> List.map (fun t->v,t) ts) tss) in
            List.map (fun (eqs,lc) -> List.map (fun (v,t)->v,(t,lc)) eqs)
              (List.combine brs lcs))
          gs in
      let eqs = List.map List.concat (transpose_lists eqs) in
      (* (c) D^g_i *)
      let vbrs = List.map
        (fun br ->
          map_some                  (* allow reversed equation *)
            (function (_,(TVar v as t,lc)) -> Some (v,(t,lc))
            | _ -> None) br
          @ br) brs in
      let vbrs = List.map2 (@) eqs vbrs in
      (* (d) D^v_i *)
      let eqvs = List.map
        (fun br ->
          let eqs = collect
            (List.map (fun (v,(t,lc)) -> t,(v,lc)) br) in
          concat_map
            (fun (_,vs) -> List.map
              (fun ((v1,lc1),(v2,lc2)) -> v1, (TVar v2, loc_union lc1 lc2))
              (triangle vs)) eqs)
        vbrs in
      (* (e) A_s_ty *)
      let ty_ans = List.map
        (fun (v,vs,u,_, lcs) ->
          v, (u, List.fold_left loc_union dummy_loc lcs)) gs in
      let ty_ans = List.map
          (function
            | v1, (TVar v2, lc) as sv ->
              if q.cmp_v v1 v2 = Left_of then v2, (TVar v1, lc)
              else sv
            | sv -> sv) ty_ans in
      let eqvs = List.map eqs_of_list eqvs in
      let eqv_ans = EqsSet.elements
        (List.fold_left EqsSet.inter (List.hd eqvs) (List.tl eqvs)) in
      (* (f) *)
      let ty_eqs, eqs = List.split
        (List.map (List.partition
                     (fun (_,(t,_)) -> typ_sort t = Type_sort)) eqs) in
      let num_eqs, eqs = List.split
        (List.map (List.partition
                     (fun (_,(t,_)) -> typ_sort t = Num_sort)) eqs) in
      let ord_eqs, eqs = List.split
        (List.map (List.partition
                     (fun (_,(t,_)) -> typ_sort t = Order_sort)) eqs) in
      assert (List.for_all (fun br -> br=[]) eqs);
      let eqs = {
        at_typ = ty_eqs;
        at_num = List.map NumS.sort_of_subst num_eqs;
        at_ord = List.map OrderS.sort_of_subst ord_eqs;
        at_so = ()} in
      usb, avs, ty_ans @ eqv_ans, eqs


(* FIXME: too much mess together with [disjelim] *)
let simplify_dsjelim q initstep ~target ~param_bvs vs ans =
  let target_rhs = map_some
      (fun (v,(t,_)) -> if v = target then Some t else None) ans.at_typ in
  let target_vs =
    VarSet.add target (fvs_typs target_rhs) in
  (*[* Format.printf
    "disjelim-simplify: initial@ target=%s@ target_vs=%a@ \
     ty_ans=%a@ num_ans=%a@\n%!"
    (var_str target) pr_vars target_vs pr_subst ans.at_typ
    NumDefs.pr_formula ans.at_num;  *]*)
  let ty_ans = List.map
      (function
        | v, (TVar v2, lc)
          when VarSet.mem v param_bvs && not (VarSet.mem v2 param_bvs) ->
          v2, (TVar v, lc)
        | sv -> sv)
      ans.at_typ in
  let ty_sb, ty_ans = List.partition
      (fun (v,_) -> not (VarSet.mem v target_vs) || List.mem v vs)
      ty_ans in
  let ty_ans = to_formula ty_ans in
  (* Opti atoms are privileged because, like equations, they are
     functional relations. *)
  (* let minmax_vs = map_some
      (function
        | NumDefs.Opti (t1, t2, _) ->
          map_opt (NumDefs.direct_opti t1 t2) (fun (v,_,_,_) -> v)
        | _ -> None)
      ans.at_num in
     let keep_more = VarSet.inter (vars_of_list minmax_vs) target_vs in
     let target_vs = VarSet.union keep_more target_vs in *)
  let num_ans = NumS.transitive_cl q ans.at_num in
  let bvs = VarSet.union target_vs param_bvs in
  let num_sb, num_nsb, num_ans =
    (* The target variables should be in the substitution. *)
    NumS.separate_subst q ~no_csts:true
      ~keep:(VarSet.diff param_bvs target_vs) ~bvs ~apply:false num_ans in
  let non_sb_vs = NumDefs.fvs_formula num_ans in
  (*[* Format.printf "disjelim-simplify:@ non_sb_vs=%a@ num_sb=%a@ \
                       num_ans=%a@\n%!"
    pr_vars non_sb_vs pr_subst num_sb NumDefs.pr_formula num_ans; *]*)
  let num_sb = List.filter
      (fun (v, (t, _)) ->
         not !drop_csts ||
         not (VarSet.is_empty (fvs_typ t)) ||
         not (VarSet.mem v non_sb_vs))
      num_sb
  and num_nsb = List.filter
      (fun (v, t) ->
         not !drop_csts ||
         not (VarSet.is_empty (NumDefs.fvs_term t)) ||
         not (VarSet.mem v non_sb_vs))
      num_nsb in
  let num_ans = List.map (NumDefs.nsubst_atom num_nsb) num_ans in
  let sb = update_sb ~more_sb:num_sb ty_sb in
  let target_vs =
    VarSet.add target
      (vars_of_map (fvs_typ % subst_typ sb) target_rhs) in
  let num_ans = List.filter
      (fun a -> not (NumDefs.taut_atom_or_undir_opti a))
      num_ans in
  let ty_ans =
    List.filter
      (function Eqty (t1, t2, _) when t1 = t2 -> false | _ -> true)
      (subst_formula sb ty_ans) in
  (*[* Format.printf
    "disjelim-simplify: parts@ sb=%a@ ty_ans=%a@ num_ans=%a@\n%!"
    pr_subst sb pr_formula ty_ans NumDefs.pr_formula num_ans;  *]*)
  let ans = List.filter
      (fun c ->
         let cvs = fvs_atom c in
         (*[* Format.printf
           "dsj-simpl: c=%a@ cvs=%a@\n%!" pr_atom c pr_vars cvs; *]*)
         VarSet.exists (fun v -> VarSet.mem v cvs) target_vs)
      (ty_ans @ NumS.formula_of_sort num_ans) in
  let ans_vs = fvs_formula ans in
  let vs = List.filter
      (fun v -> VarSet.mem v ans_vs && not (List.mem_assoc v ty_sb))
      vs in
  (*[* Format.printf
    "disjelim-simplify: result@ target_vs=%a@ vs=%a@ ans=%a@\n%!"
    pr_vars target_vs pr_vars (vars_of_list vs) pr_formula ans;  *]*)
  vs, ans

(* FIXME: introduce existential type variables for escaping parameters *)
let disjelim q ?target ~bvs ~param_bvs (* ~preserve *) (* ~old_local *)
    ~up_of_anchor ~do_num ~guess ~initstep ~residuum brs =
  let target = match target with None -> delta | Some v -> v in
  (* (1) D_i,s *)
  (*[* Format.printf
    "disjelim:@ target=%s@ bvs=%a;@ param=%a@\n%!"
    (var_str target) pr_vars bvs pr_vars param_bvs; *]*)
  let brs = map_some
      (fun (prem, br) ->
         try Some (solve ~use_quants:false q prem,
                   solve ~use_quants:false q br)
         with Contradiction _ -> None) brs in
  if brs = [] then [], ([], [])
  else
    let residuum =
      solve ~use_quants:false q residuum in
    (*[* Format.printf
      "disjelim:@ residuum.cnj_num=%a@\n%!"
      NumDefs.pr_formula residuum.cnj_num; *]*)
    (* [avs] contains variables introduced by anti-unification, also
       of sorts other than "type" *)
    (* (2) *)
    let usb, avs, ty_ans, eqs =
      disjelim_typ q ~bvs ~target (* ~preserve *)
        (List.map (fun (_, br) -> br.cnj_typ) brs) in
    let target_vs =
      try fvs_typ (fst (List.assoc target ty_ans))
      with Not_found -> VarSet.empty in
    let lift_vs = VarSet.filter
        (fun v -> not (List.mem v avs) && not (up_of_anchor v))
        target_vs in
    let lift_rn = List.map
        (fun v -> v, fresh_var (var_sort v))
        (VarSet.elements lift_vs) in
    (*[* Format.printf "disjelim: lift_rn=%a@\n%!" pr_hvsubst lift_rn; *]*)
    let avs = map_append snd lift_rn avs in
    let ty_ans = List.map
      (fun (v, (t, lc)) ->
        (try List.assoc v lift_rn with Not_found -> v),
        (hvsubst_typ lift_rn t, lc)) ty_ans in
    if do_num
    then
      let eqs_num =
        List.map (List.map (NumDefs.hvsubst_atom lift_rn))
          eqs.at_num in
      let eqs_ord =
        List.map (List.map (OrderDefs.hvsubst_atom lift_rn))
          eqs.at_ord in
      let residuum_num =
        List.map (NumDefs.hvsubst_atom lift_rn)
          residuum.cnj_num in
      let residuum_ord =
        List.map (OrderDefs.hvsubst_atom lift_rn)
          residuum.cnj_ord in
      let brs_num = List.map
          (fun (prem, br) ->
             List.map (NumDefs.hvsubst_atom lift_rn) prem.cnj_num,
             List.map (NumDefs.hvsubst_atom lift_rn) br.cnj_num)
          brs in
      let brs_ord = List.map
          (fun (prem, br) ->
             List.map (OrderDefs.hvsubst_atom lift_rn) prem.cnj_ord,
             List.map (OrderDefs.hvsubst_atom lift_rn) br.cnj_ord)
          brs in
      (* Variables not in [q] will behave as rightmost. *)
      (* (3) *)
      let preserved = map_some
          (fun (v,(t,_)) -> if v = target then Some t else None)
          ty_ans in
      let target_vs = fvs_typs preserved in
      let keep_for_simpl =
        VarSet.union target_vs (VarSet.filter up_of_anchor param_bvs) in
      let keep_for_simpl =
        (* VarSet.filter (fun v -> not (List.mem_assoc v restore_sb)) *)
        keep_for_simpl in
      (*[* Format.printf "disjelim:@ keep_for_simpl=%a@\n%!"
        pr_vars keep_for_simpl; *]*)
      let num_brs = List.map2
          (fun (prem, a) b -> prem, residuum_num @ a @ b) brs_num eqs_num in
      let ord_brs = List.map2
          (fun (prem, a) b -> prem, residuum_ord @ a @ b) brs_ord eqs_ord in
      let num_avs, (num_abd, num_ans) = NumS.disjelim q ~target_vs
          ~preserve:keep_for_simpl ~bvs ~param_bvs
          ~guess ~initstep num_brs in
      let ord_avs, ord_ans = OrderS.disjelim q ~target_vs
          ~preserve:keep_for_simpl ~initstep ord_brs in
      (*[* Format.printf
        "disjelim: before simpl@ vs=%a@ ty_ans=%a@ num_ans=%a@\n\
         initstep=%b num_abd=@ %a@\n%!"
        pr_vars (vars_of_list (num_avs @ avs))
        pr_subst ty_ans NumDefs.pr_formula num_ans
        initstep NumDefs.pr_formula num_abd; *]*)
      (* (4) *)
      (* Dooes not simplify redundancy. *)
      to_formula usb (* @
        (if initstep then [] else NumS.formula_of_sort num_abd) *),
      simplify_dsjelim q initstep ~target ~param_bvs (num_avs @ avs)
        {at_typ=ty_ans; at_num=num_ans; at_ord=ord_ans; at_so=()}
    else
      to_formula usb,
      simplify_dsjelim q initstep ~target ~param_bvs avs
        {at_typ=ty_ans; at_num=[]; at_ord=[]; at_so=()}

