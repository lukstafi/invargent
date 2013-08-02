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
      let vs, ss, gsb = auxn gsb
        (t1s::List.map
           (function Nadd tks -> tks | _ -> assert false) ts) in
      vs, Nadd ss, gsb
    | ts ->
      try [], TVar (List.assoc ts gsb), gsb
      with Not_found ->
        let x = Infer.fresh_typ_var () in
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

let disjelim_typ cmp_v uni_v brs =
  let cmp_k (v1,_) (v2,_) = compare v1 v2 in
  let brs = List.map (List.sort cmp_k) brs in
  let empty_brs = List.map (fun _ -> []) brs in
  match brs with
  | [] -> assert false
  | [br] -> [], br, empty_brs, empty_brs
  | br::more_brs ->
    (* (a) V *)
    let gs = List.map (fun (v,(t,lc)) -> v,([t],[lc])) br in
    let aux =
      (Aux.inter_merge : (a -> b -> int) ->
       (a -> b -> a) -> a list -> b list -> a list)
        cmp_k (fun (_,(ts,lcs)) (v,(t,lc)) -> v, (t::ts,lc::lcs)) in
    let gs = List.fold_left aux gs more_brs in
    if gs = [] then [], [], empty_brs, empty_brs
    else
      let gs = List.map
        (fun (v,(ts,lcs)) -> v, (List.rev ts, List.rev lcs)) gs in
      (* (b) G *)
      let gs = List.map
        (fun (v,(ts,lcs)) -> v, antiunif ts, lcs) gs in
      let avs = Aux.concat_map (fun (_,(vs,_,_), _) -> vs) gs in
      (* A set of sequences position-matched with branches. *)
      (* (c) D^u_i *)
      let eqs = 
        List.map
          (fun (_,(_,_,tss),lcs) ->
            let brs = Aux.transpose_lists
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
        (fun (v,(vs,u,_), lcs) ->
          v, (u, List.fold_left loc_union dummy_loc lcs)) gs in
      let eqvs = List.map eqs_of_list eqvs in
      let eqv_ans = EqsSet.elements
        (List.fold_left EqsSet.inter (List.hd eqvs) (List.tl eqvs)) in
      (* (f) *)
      let num_eqs, ty_eqs = List.split
        (List.map (List.partition (fun (_,(t,_)) -> num_sort_typ t)) eqs) in
      avs, ty_ans @ eqv_ans, ty_eqs, List.map to_formula num_eqs

let simplify cmp_v (vs, ty_ans, num_ans) =
  let params = vars_of_list vs in
  let cmp_v v1 v2 =
    let c1 = VarSet.mem v1 params and c2 = VarSet.mem v2 params in
    if c1 && c2 then Same_quant
    else if c1 then Downstream
    else if c2 then Upstream
    else cmp_v v1 v2 in
  let ty_ans, ty_num, _ =
    unify cmp_v (fun _ -> false) (to_formula ty_ans) in
  assert (ty_num = []);
  let ty_sb, ty_ans = List.partition
    (fun (v,_) -> List.mem v vs) ty_ans in
  let vs = List.filter (fun v -> not (List.mem_assoc v ty_sb)) vs in
  vs, subst_formula ty_sb (to_formula ty_ans) @ num_ans

let disjelim cmp_v uni_v brs =
  (* (1) D_i,s *)
  let brs = Aux.map_some
    (fun br ->
      try Some (unify cmp_v uni_v br)
      with Contradiction _ -> None) brs in
  (* [avs] contains variables introduced by anti-unification, also
  of sorts other than "type" *)
  (* (2) *)
  let avs, ty_ans, ty_eqs, num_eqs =
    disjelim_typ cmp_v uni_v (List.map Aux.fst3 brs) in
  let cmp_v v1 v2 =
    let av1 = List.mem v1 avs and av2 = List.mem v2 avs in
    if av1 && av2 then Same_quant
    else if av1 then Downstream
    else if av2 then Upstream
    else cmp_v v1 v2 in
  (* (3) *)
  let num_brs = List.map (fun (a,b)->a@b)
    (List.combine (List.map Aux.snd3 brs) num_eqs) in
  let num_avs, num_ans = NumS.disjelim cmp_v uni_v num_brs in
  (* (4) *)
  simplify cmp_v (num_avs @ avs, ty_ans, num_ans)
