(** Disjunction elimination for InvarGenT.

    Released under the GNU General Public Licence (version 2 or
    higher), NO WARRANTY of correctness etc. (C) Lukasz Stafiniak 2013
    @author Lukasz Stafiniak lukstafi (AT) gmail.com
    @since Mar 2013
*)

open Terms

let antiunif ts =
  let rec aux gsb = function
    | [] -> assert false
    | t::ts when List.for_all ((=) t) ts-> [], t, gsb
    | TCons (n, t1s)::ts when List.for_all
        (function TCons (n2, _) when n2=n -> true | _ -> false) ts ->
      let vs, ss, gsb = auxn gsb
        (t1s::List.map
           (function TCons (_, tks) -> tks | _ -> assert false) ts) in
      vs, TCons (n, ss), gsb
    | Fun (t1, t2)::ts when List.for_all
        (function Fun _ -> true | _ -> false) ts ->
      let vs1, s1, gsb = aux gsb
        (t1::List.map
           (function Fun (tk1, _) -> tk1 | _ -> assert false) ts) in
      let vs2, s2, gsb = aux gsb
        (t2::List.map
           (function Fun (_, tk2) -> tk2 | _ -> assert false) ts) in
      vs1 @ vs2, Fun (s1, s2), gsb
    | Nadd t1s::ts when List.for_all
        (function Nadd _ -> true | _ -> false) ts ->
      (* FIXME: why handling numbers? *)
      let vs, ss, gsb = auxn gsb
        (t1s::List.map
           (function Nadd tks -> tks | _ -> assert false) ts) in
      vs, Nadd ss, gsb
    | ts ->
      try [], TVar (List.assoc ts gsb), gsb
      with Not_found ->
        let x =
          if List.for_all typ_sort_typ ts
          then Infer.fresh_typ_var ()
          else if List.for_all num_sort_typ ts
          then Infer.fresh_num_var ()
          else assert false in
        [x], TVar x, (ts, x)::gsb

  and auxn gsb = function
    | [] -> [], [], gsb
    | []::_ -> [], [], gsb
    | (t1::t1s)::ts ->
      let v1s, s, gsb = aux gsb (t1::List.map List.hd ts) in
      let vs, ss, gsb = auxn gsb (t1s::List.map List.tl ts) in
      v1s @ vs, s::ss, gsb in

  aux [] ts

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

open Aux

let disjelim_typ q brs =
  let cmp_k (v1,_) (v2,_) = compare v1 v2 in
  let brs = List.map (List.sort cmp_k) brs in
  Format.printf "disjelim_typ: brs=@ %a@\n%!"
    (pr_line_list "| " pr_subst) brs; (* *)
  let empty_brs = List.map (fun _ -> []) brs in
  match brs with
  | [] -> assert false
  | [br] -> [], br, empty_brs, empty_brs
  | br::more_brs ->
    (* (a) V *)
    let gs = List.map (fun (v,(t,lc)) -> v,([t],[lc])) br in
    let aux =
      Aux.inter_merge
        cmp_k (fun (_,(ts,lcs)) (v,(t,lc)) -> v, (t::ts,lc::lcs)) in
    let gs = List.fold_left aux gs more_brs in
    if gs = [] then [], [], empty_brs, empty_brs
    else
      let gs = List.map
        (fun (v,(ts,lcs)) -> v, (List.rev ts, List.rev lcs)) gs in
      (* (b) G *)
      let gs = List.map
        (fun (v,(ts,lcs)) ->
          let gvs,gt,tss = antiunif ts in
          v, gvs, gt, tss, lcs)
        gs in
      let avs = Aux.concat_map (fun (_,vs,_,_, _) -> vs) gs in
      (* A set of sequences position-matched with branches. *)
      (* (c) D^u_i *)
      Format.printf "disjelim_typ: #brs=%d #gs=%d avs=%a@\n%!"
        (List.length brs) (List.length gs)
        pr_vars (vars_of_list avs);
      List.iter
        (fun (v,gvs,gt,tss,lcs) ->
          Format.printf
            "disjelim_typ: v=%s@ gvs=%a@ gt=%a@ #tss=%d@ #tss[0]=%d@ #lcs=%d@\n%!"
            (var_str v) pr_vars (vars_of_list gvs) (pr_ty false) gt
            (List.length tss)
            (if tss=[] then -1 else (List.length (fst (List.hd tss))))
            (List.length lcs);
        ) gs;
      (* *)
      let eqs = 
        List.map
          (fun (_,_,_,tss,lcs) ->
            let brs =
              if tss=[] then empty_brs
              else Aux.transpose_lists
                (List.map (fun (ts, v) -> List.map (fun t->v,t) ts) tss) in
            List.map (fun (eqs,lc) -> List.map (fun (v,t)->v,(t,lc)) eqs)
              (List.combine brs lcs))
          gs in
      let eqs = List.map List.concat (Aux.transpose_lists eqs) in
      (* (c) D^g_i *)
      let vbrs = List.map
        (fun br ->
          Aux.map_some                  (* allow reversed equation *)
            (function (_,(TVar v as t,lc)) -> Some (v,(t,lc))
            | _ -> None) br
          @ br) brs in
      let vbrs = List.map2 (@) eqs vbrs in
      (* (d) D^v_i *)
      let eqvs = List.map
        (fun br ->
          let eqs = Aux.collect
            (List.map (fun (v,(t,lc)) -> t,(v,lc)) br) in
          Aux.concat_map
            (fun (_,vs) -> List.map
              (fun ((v1,lc1),(v2,lc2)) -> v1, (TVar v2, loc_union lc1 lc2))
              (Aux.triangle vs)) eqs)
        vbrs in
      (* (e) A_s_ty *)
      let ty_ans = List.map
        (fun (v,vs,u,_, lcs) ->
          v, (u, List.fold_left loc_union dummy_loc lcs)) gs in
      let eqvs = List.map eqs_of_list eqvs in
      let eqv_ans = EqsSet.elements
        (List.fold_left EqsSet.inter (List.hd eqvs) (List.tl eqvs)) in
      (* (f) *)
      let num_eqs, ty_eqs = List.split
        (List.map (List.partition (fun (_,(t,_)) -> num_sort_typ t)) eqs) in
      avs, ty_ans @ eqv_ans, ty_eqs, List.map to_formula num_eqs

(* Do not simplify redundancy! Just remove spurious introduced variables. *)
let simplify (vs, ty_ans, num_ans) =
  let ty_sb, ty_ans = List.partition
    (fun (v,_) -> List.mem v vs) ty_ans in
  let ty_ans =
    List.filter
      (function Eqty (t1, t2, _) when t1 = t2 -> false | _ -> true)
      (subst_formula ty_sb (to_formula ty_ans)) in
  Format.printf
    "disjelim-simplify: parts@ ty_sb=%a@ ty_ans=%a@\n%!"
    pr_subst ty_sb pr_formula ty_ans;  (* *)
  let vs = List.filter (fun v -> not (List.mem_assoc v ty_sb)) vs in
  vs, num_ans @ ty_ans

let disjelim q ~do_num brs =
  (* (1) D_i,s *)
  let brs = Aux.map_some
      (fun br ->
         try Some (unify q br)
         with Contradiction _ -> None) brs in
  (* [avs] contains variables introduced by anti-unification, also
     of sorts other than "type" *)
  (* (2) *)
  let avs, ty_ans, ty_eqs, num_eqs =
    disjelim_typ q (List.map Aux.fst3 brs) in
  if do_num
  then
    (* Variables not in [q] will behave as rightmost. *)
    (* (3) *)
    let num_brs = List.map (fun (a,b)->a@b)
        (List.combine (List.map Aux.snd3 brs) num_eqs) in
    let num_avs, num_ans = NumS.disjelim q num_brs in
    Format.printf "disjelim: before simpl@ vs=%a@ ty_ans=%a@ num_ans=%a@\n%!"
      pr_vars (vars_of_list (num_avs @ avs))
      pr_subst ty_ans pr_formula num_ans; (* *)
    (* (4) *)
    (* Dooes not simplify redundancy. *)
    simplify (num_avs @ avs, ty_ans, num_ans)
  else
    simplify (avs, ty_ans, [])
    
