(** Disjunction elimination for InvarGenT.

    Released under the GNU General Public Licence (version 2 or
    higher), NO WARRANTY of correctness etc. (C) Lukasz Stafiniak 2013
    @author Lukasz Stafiniak lukstafi (AT) gmail.com
    @since Mar 2013
*)

open Defs
open Terms
open Aux

let antiunif q ts =
  let rec aux usb gsb = function
    | [] -> assert false
    | t::ts when List.for_all ((=) t) ts-> [], t, usb, gsb
    | TCons (n, t1s)::ts when List.for_all
          (function TCons (n2, _) when n2=n -> true | _ -> false) ts ->
      let vs, ss, usb, gsb = auxn usb gsb
          (t1s::List.map
               (function TCons (_, tks) -> tks | _ -> assert false) ts) in
      vs, TCons (n, ss), usb, gsb
    | Fun (t1, t2)::ts when List.for_all
          (function Fun _ -> true | _ -> false) ts ->
      let vs1, s1, usb, gsb = aux usb gsb
          (t1::List.map
               (function Fun (tk1, _) -> tk1 | _ -> assert false) ts) in
      let vs2, s2, usb, gsb = aux usb gsb
          (t2::List.map
               (function Fun (_, tk2) -> tk2 | _ -> assert false) ts) in
      vs1 @ vs2, Fun (s1, s2), usb, gsb
    | t::_ as ts when typ_sort t <> Type_sort ->
          let x = fresh_var (typ_sort t) in
          [x], TVar x, usb, (ts, x)::gsb
    | t::_ as ts ->
      try [], TVar (List.assoc ts gsb), usb, gsb
      with Not_found ->
        let n =
          find_map (function TCons (n, _) -> Some n | _ -> None) ts in
        let b = find_map
            (function TVar v when q.uni_v v -> Some v | _ -> None)
            ts in
        (* *)if n <> None && List.for_all
             (function TCons (n2, _) when Some n2=n -> true
                     | TVar v -> not (q.uni_v v) | _ -> false) ts
        then
          let n, args = unsome
              (find_map (function TCons (n, a) -> Some (n,a)
                                | _ -> None) ts) in
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
        else if n = None && List.for_all
                  (function TVar v -> Some v = b || not (q.uni_v v)
                          | _ -> false) ts
        then
          let vars = List.map
              (function TVar v -> v | _ -> assert false) ts in
          let b = match b with
            | Some b -> b
            | None ->
              (* get the leftmost variable *)
              maximum ~leq:(fun v w -> q.cmp_v v w <> Left_of) vars in
          let tb = TVar b in
          let more_sb = map_some
            (fun v -> if v=b then None else Some (v, (tb, dummy_loc)))
            vars in
          let usb = update_sb ~more_sb usb in
          let ts = List.map (subst_typ usb) ts in
          aux usb gsb ts
        else(* *)
          let x = fresh_var (typ_sort t) in
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
let disjelim_typ q ~preserve brs =
  let cmp_k (v1,_) (v2,_) = compare v1 v2 in
  let brs = List.map (List.sort cmp_k) brs in
  (*[* Format.printf "disjelim_typ: preserve=%a@\nbrs=@ %a@\n%!"
    pr_vars preserve (pr_line_list "| " pr_subst) brs; *]*)
  let empty_brs = List.map (fun _ -> []) brs in
  let empty_eqs = {at_typ=empty_brs; at_num=empty_brs; at_so=()} in
  match brs with
  | [] -> assert false
  | [br] -> [], br, empty_eqs
  | br::more_brs ->
    (* (a) V *)
    let gs = List.map (fun (v,(t,lc)) -> v,([t],[lc])) br in
    let aux =
      inter_merge
        cmp_k (fun (_,(ts,lcs)) (v,(t,lc)) -> v, (t::ts,lc::lcs)) in
    let gs = List.fold_left aux gs more_brs in
    if gs = [] then [], [], empty_eqs
    else
      let gs = List.map
        (fun (v,(ts,lcs)) -> v, (List.rev ts, List.rev lcs)) gs in
      (* (b) G *)
      let gs = List.map
        (fun (v,(ts,lcs)) ->
          let gvs,gt,_,tss = antiunif q ts in
          (* [usb] not used currently *)
          v, gvs, gt, tss, lcs)
        gs in
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
      let num_eqs, ty_eqs = List.split
        (List.map (List.partition
                     (fun (_,(t,_)) -> typ_sort t = Num_sort)) eqs) in
      let eqs = {
        at_typ = ty_eqs;
        at_num = List.map NumS.sort_of_subst num_eqs;
        at_so = ()} in
      avs, ty_ans @ eqv_ans, eqs

(* Do not simplify redundancy! Just remove spurious introduced variables. *)
(* FIXME: too much mess together with [disjelim] *)
let simplify_dsjelim q ~keep ~preserve vs ans =
  (*[* Format.printf
    "disjelim-simplify: initial@ keep=%a@ preserve=%a@ ty_ans=%a@ num_ans=%a@\n%!"
    pr_vars keep pr_vars preserve pr_subst ans.at_typ
    NumDefs.pr_formula ans.at_num;  *]*)
  let ty_sb, ty_ans = List.partition
    (fun (v,_) -> not (VarSet.mem v preserve) || List.mem v vs)
    ans.at_typ in
  let ty_ans = to_formula ty_ans in
  let num_ans = NumS.transitive_cl ans.at_num in
  let num_sb, num_ans = NumS.separate_subst q ~keep num_ans in
  let num_sb, more_num_ans = List.partition
    (fun (v,_) -> not (VarSet.mem v preserve) || List.mem v vs)
    num_sb in
  let sb = update_sb ~more_sb:num_sb ty_sb in
  let ty_ans =
    List.filter
      (function Eqty (t1, t2, _) when t1 = t2 -> false | _ -> true)
      (subst_formula sb ty_ans) in
  (*[* Format.printf
    "disjelim-simplify: parts@ ty_sb=%a@ ty_ans=%a@\n%!"
    pr_subst ty_sb pr_formula ty_ans;  *]*)
  let vs = List.filter (fun v -> not (List.mem_assoc v ty_sb)) vs in
  vs, to_formula more_num_ans @ NumS.formula_of_sort num_ans @ ty_ans

let disjelim q ~bvs ~preserve ~do_num brs =
  (* (1) D_i,s *)
  let brs = map_some
      (fun br ->
         try Some (unify ~use_quants:false q br)
         with Contradiction _ -> None) brs in
  (* [avs] contains variables introduced by anti-unification, also
     of sorts other than "type" *)
  (* (2) *)
  let avs, ty_ans, eqs =
    disjelim_typ q ~preserve (List.map (fun br->br.cnj_typ) brs) in
  let keep = fvs_typs
      (map_some
         (fun (v,(t,_)) -> if VarSet.mem v bvs then Some t else None)
         ty_ans) in
  if do_num
  then
    (* Variables not in [q] will behave as rightmost. *)
    (* (3) *)
    let preserved = map_some
        (fun (v,(t,_)) -> if VarSet.mem v preserve then Some t else None)
        ty_ans in
    let keep_for_simpl =
      VarSet.union (fvs_typs preserved) preserve in
    let num_brs = List.map (fun (a,b)->a@b)
        (List.combine (List.map (fun br->br.cnj_num) brs) eqs.at_num) in
    let num_avs, num_ans = NumS.disjelim q
        ~preserve:keep_for_simpl
        num_brs in
    (*[* Format.printf "disjelim: before simpl@ vs=%a@ ty_ans=%a@ num_ans=%a@\n%!"
      pr_vars (vars_of_list (num_avs @ avs))
      pr_subst ty_ans NumDefs.pr_formula num_ans; *]*)
    (* (4) *)
    (* Dooes not simplify redundancy. *)
    simplify_dsjelim q ~keep ~preserve (num_avs @ avs)
      {at_typ=ty_ans; at_num=num_ans; at_so=()}
  else
    simplify_dsjelim q ~keep ~preserve avs
      {at_typ=ty_ans; at_num=[]; at_so=()}
    
let transitive_cl cnj =
  let {cnj_typ=_; cnj_num; cnj_so=_} = sep_formulas cnj in
  let cnj_typ = concat_map
    (function
      | Eqty (t1, t2, loc) ->
        [t1, t2, loc; t2, t1, loc]
      | _ -> [])
    cnj in
  let cnj_typ = Hashtbl.fold
      (fun (i,j) lc cnj -> if i<j then Eqty (i, j, lc)::cnj else cnj)
      (Joint.transitive_cl cnj_typ) [] in
  let cnj_num = NumS.transitive_cl cnj_num in
  cnj_typ @ NumS.formula_of_sort cnj_num

let initstep_heur q ~preserve cnj =
  (*[* let init_cnj = cnj in *]*)
  (* FIXME *)
  (* let cnj = NumS.cleanup_formula cnj in *)
  let preserve = add_vars [delta; delta'] preserve in
  let preserve = List.fold_left
      (fun preserve a ->
         let vs = fvs_atom a in
         if VarSet.mem delta vs then VarSet.union vs preserve else preserve)
      preserve cnj in
  let cnj = transitive_cl cnj in
  let cst_eqs, cnj =
    partition_choice
      (map_some
         (fun c ->
            let vs = fvs_atom c in
            (*[* Format.printf "testing c=%a@ vs=%a@ diff=%a..." pr_atom c
              pr_vars vs pr_vars (VarSet.diff vs preserve); *]*)
            if VarSet.is_empty (VarSet.diff vs preserve)
            then match VarSet.elements vs with
              | [v] -> (*[* Format.printf "cst@\n%!"; *]*) Some (Left (v, c))
              | _ -> (*[* Format.printf "cnj@\n%!"; *]*) Some (Right c)
            else ((*[* Format.printf "none@\n%!"; *]*) None))
         cnj) in
  let cvs = fvs_formula cnj in
  let cst_eqs = map_some
      (fun (v,c) -> if VarSet.mem v cvs then None else Some c) cst_eqs in
  (*[* Format.printf
    "DisjElim.initstep_heur: preserve=%a@\ninit_cnj=%a@\ncst_eqs=%a@ cnj=%a@\n%!"
    pr_vars preserve pr_formula init_cnj pr_formula cst_eqs pr_formula cnj; *]*)
  cst_eqs @ cnj
