(** Numeric sort operations for InvarGenT.

    Released under the GNU General Public Licence (version 2 or
    higher), NO WARRANTY of correctness etc. (C) Lukasz Stafiniak 2013
    @author Lukasz Stafiniak lukstafi (AT) gmail.com
    @since Mar 2013
*)

open Terms
open Num
let (!/) i = num_of_int i

type w = (var_name * num) list * num * loc
type w_subst = (var_name * w) list

let mult c (vars, cst, loc) =
  List.map (fun (v,k) -> v, c */ k) vars, c */ cst, loc

let diff cmp (vars1, cst1, loc1) w2 =
  let (vars2, cst2, loc2) = mult !/(-1) w2 in
  let loc = loc_union loc1 loc2 in
  let vars = Aux.map_reduce (+/) (!/0) (vars1 @ vars2) in
  let vars = List.sort cmp
    (List.filter (fun (_,k) -> k <>/ !/0) vars) in
  vars, cst1 +/ cst2, loc

let flatten cmp a : (w, w) Aux.choice =
  let rec flat (vars, cst, loc as acc) = function
    | Nadd sum ->
      List.fold_left flat acc sum
    | NCst i -> vars, cst +/ !/i, loc
    | TVar v -> (v, !/1)::vars, cst, loc
    | TCons _ | Fun _ -> assert false in
  let collect t1 t2 loc =
    let zero = [], !/0, loc in
    let w1 = flat zero t1 in
    let w2 = flat zero t2 in
    diff cmp w1 w2 in
  match a with
  | Eqty (t1, t2, loc) ->
    Aux.Left (collect t1 t2 loc)
  | Leq (t1, t2, loc) ->
    Aux.Right (collect t1 t2 loc)
  | _ -> assert false

let subst cmp (eqs : w_subst) (vars, cst, loc : w) : w =
  let sums = List.map
    (fun (v,k) ->
      try let vars, cst, _ = mult k (List.assoc v eqs) in vars, cst
      with Not_found -> [v,k], !/0)
    vars in
  let vars, csts = List.split sums in
  let vars = Aux.map_reduce (+/) (!/0) (List.concat vars) in
  let vars = List.sort cmp
    (List.filter (fun (_,k) -> k <>/ !/0) vars) in
  let cst = List.fold_left (+/) (!/0) csts in
  vars, cst, loc

let subst_one cmp (v, w) (vars, cst, loc as arg) =
  try
    let k, vars = Aux.pop_assoc v vars in
    let w_vs, w_cst, w_loc = mult k w in
    let vars = Aux.map_reduce (+/) (!/0) (w_vs @ vars) in
    let vars = List.sort cmp
      (List.filter (fun (_,k) -> k <>/ !/0) vars) in
    let cst = w_cst +/ cst in
    vars, cst, loc
  with Not_found -> arg

let subst_one_sb cmp w_sb sb =
  List.map (fun (v, w) -> v, subst_one cmp w_sb w) sb

let expand_atom equ (vars, cst, loc) =
  let vars = List.map (fun (v,k) -> v, ratio_of_num k) vars in
  let cst = ratio_of_num cst in
  let denoms =
    List.map (fun (_,k) -> Ratio.denominator_ratio k) vars in
  let denoms = Ratio.denominator_ratio cst :: denoms in
  let sc = List.fold_left Big_int.mult_big_int
    (Big_int.big_int_of_int 1) denoms in
  let vars = List.map
    (fun (v,k) -> v, Ratio.int_of_ratio (Ratio.mult_big_int_ratio sc k))
    vars in
  let cst = Ratio.int_of_ratio (Ratio.mult_big_int_ratio sc cst) in
  let left, right = List.partition (fun (_,k) -> k > 0) vars in
  let right = List.map (fun (v,k) -> v, ~-k) right in
  let expand (v,k) = Array.to_list (Array.make k (TVar v)) in
  let left = (if cst > 0 then [NCst cst] else [])
    @ Aux.concat_map expand left in
  let right = (if cst < 0 then [NCst (~-cst)] else [])
    @ Aux.concat_map expand right in
  let left = match left with [t] -> t | _ -> Nadd left in
  let right = match right with [t] -> t | _ -> Nadd right in
  if equ then Eqty (left, right, loc) else Leq (left, right, loc)

let solve ~use_quants ?(strict=false) cmp_v uni_v ?(eqs=[]) ?(ineqs=[]) cnj =
  let cmp_v v1 v2 =
    match cmp_v v1 v2 with
    | Upstream -> 1
    | Downstream -> -1
    | _ -> compare v1 v2 in
  let cmp (v1,_) (v2,_) = cmp_v v1 v2 in
  let cmp_w (vars1,_,_) (vars2,_,_) =
    match vars1, vars2 with
    | [], [] -> 0
    | _, [] -> -1
    | [], _ -> 1
    | (v1,_)::_, (v2,_)::_ -> cmp_v v1 v2 in
  let eqn, ineqn = Aux.partition_map (flatten cmp) cnj in
  assert (not strict || eqn = []);
  let eqn = if eqs=[] then eqn else List.map (subst cmp eqs) eqn in
  let ineqn = if eqs=[] then ineqn else List.map (subst cmp eqs) ineqn in
  let eqn = List.map
    (fun (vars, cst, loc) ->
      List.filter (fun (v,k)->k <>/ !/0) vars, cst, loc) eqn in
  let eqn = List.sort cmp_w eqn in
  let rec elim acc = function
    | [] -> List.rev acc
    | ((v, k)::vars, cst, loc)::eqn ->
      let w_sb = v, mult (!/(-1) // k) (vars, cst, loc) in
      let acc = subst_one_sb cmp w_sb acc in
      let eqn = List.map (subst_one cmp w_sb) eqn in
      elim (w_sb::acc) eqn
    | ([], cst, loc)::eqn when cst =/ !/0 -> elim acc eqn
    | ([], cst, loc)::eqn ->
      raise (Contradiction ("Failed numeric equation", None, loc)) in
  let eqn = List.rev (elim [] eqn) in
  let ineqn = if eqn=[] then ineqn else List.map (subst cmp eqn) ineqn in
  let eqs = if eqn=[] then eqs else List.map
      (fun (v,eq) -> v, subst cmp eqn eq) eqs in
  (* inequalities [left <= v] and [v <= right] *)
  let ineqs = if eqn=[] then ineqs else
      List.map (fun (v, (left, right)) ->
        v,
        (List.map (subst cmp eqn) left,
         List.map (subst cmp eqn) right)) ineqs in
  let more_ineqn =
    Aux.concat_map
      (fun (v, w) ->
        try
          let left, right = List.assoc v ineqs in
          List.map (fun lhs -> diff cmp lhs w) left @
            List.map (fun rhs -> diff cmp w rhs) right
        with Not_found -> [])
      eqn in
  let ineqn = List.sort cmp_w (more_ineqn @ ineqn) in
  let project v lhs rhs =
    if lhs = rhs
    then if strict
      then
        let vars, cst, loc = lhs in
        let a = expand_atom false ((v, !/(-1))::vars, cst, loc) in
        let t1, t2 = match a with
          | Leq (t1, t2, _) -> t1, t2 | _ -> assert false in
        raise (Contradiction ("Failed numeric strict inequality",
                              Some (t1, t2), loc))
      else Aux.Right lhs
    else Aux.Left (diff cmp lhs rhs) in
  let rec proj ineqs implicits ineqn =
    match ineqn with
    | [] -> ineqs, implicits
    | ([], cst, _)::ineqn
        when (strict && cst </ !/0) || (not strict && cst <=/ !/0) ->
      proj ineqs implicits ineqn
    | ([], cst, loc)::_ ->
      raise (Contradiction ("Failed numeric inequality", None, loc))
    | ((v,k)::vars, cst, loc)::ineqn ->
      let (left, right), ineqs =
        try Aux.pop_assoc v ineqs with Not_found -> ([], []), ineqs in
      let ineq_l, ineq_r, (more_ineqn, more_implicits) = 
        if k >/ !/0
        then
          let rhs = mult (!/(-1) // k) (vars, cst, loc) in
          [], [rhs],
          Aux.partition_map (fun lhs -> project v lhs rhs) left
        else
          let lhs = mult (!/1 // k) (vars, cst, loc) in
          [lhs], [],
          Aux.partition_map (fun rhs -> project v lhs rhs) right in
      let more_ineqn = List.filter
        (function
        | [], cst, _
          when (strict && cst </ !/0) || (not strict && cst <=/ !/0) ->
          false
        | [], cst, loc ->
          let a = expand_atom false ([v, !/(-1)], cst, loc) in
          let t1, t2 = match a with
            | Leq (t1, t2, _) -> t1, t2 | _ -> assert false in
          raise (Contradiction ("Failed numeric inequality",
                                Some (t1, t2), loc))
        | _ -> true)
        more_ineqn in
      let ineqn =
        Aux.merge cmp_w (List.sort cmp_w more_ineqn) ineqn in
      let ineqs = (v, (ineq_l @ left, ineq_r @ right))::ineqs in
      proj ineqs (more_implicits @ implicits) ineqn in
  eqn @ eqs, proj ineqs [] ineqn

let satisfiable cnj =
  let cmp_v _ _ = Same_quant in
  let uni_v _ = false in
  try ignore (solve ~use_quants:false cmp_v uni_v cnj); true
  with Contradiction _ -> false

(*
let abd_simple cmp_v uni_v validate skip eqs ineqs (prem, concl) =
  let skip = ref skip in
  let skipped = ref [] in
  try
    let d_eqs, (d_ineqs, d_implicits) =
      solve ~use_quants:false cmp_v uni_v ~eqs ~ineqs prem in
    let dc_eqs, (dc_ineqs, dc_implicits) =
      solve ~use_quants:false cmp_v uni_v ~eqs ~ineqs (prem @ concl) in
    

    let prem_and vs ans =
      (* TODO: optimize, don't redo work *)
      combine_sbs ~use_quants:false ~params:vs cmp_v uni_v [prem; ans] in
    let implies_concl vs ans =
      let cnj_typ, cnj_num = prem_and vs ans in
      let res_ty, res_num = residuum cmp_v uni_v vs cnj_typ concl in
      let num = res_num @ cnj_num in
      res_ty = [] && NumS.satisfiable num in
    let rec abstract repls vs ans cur_ans = function
      | [] ->
        if implies_concl vs ans then
          let ans = List.sort compare ans in
          allvs := List.fold_right VarSet.add vs !allvs;
          if List.exists (fun xs ->
            List.for_all (fun (y,_) -> VarSet.mem y !allvs)
              (Aux.sorted_diff xs ans)) !skipped
          then ()
          else if !skip > 0 then (
            skipped := ans :: !skipped;
            decr skip)
          else raise (Result (vs, ans))
      | (x, (t, lc))::cand ->
        if implies_concl vs (ans @ cand) then (
          (* Choice 1: drop premise/conclusion atom from answer *)
          abstract repls vs ans cur_ans cand);
        step x lc {typ_sub=t; typ_ctx=[]} repls vs ans cur_ans cand
    and step x lc loc repls vs ans cur_ans cand =
      (* Choice 2: preserve current premise/conclusion subterm for answer *)
      (match typ_next loc with
        | None ->
          let ans =
            try
              let ans, _, so =
                unify ~use_quants:true ~params:vs ~sb:ans
                  cmp_v uni_v [Eqty (TVar x, typ_out loc, lc)] in
              validate vs ans;
              assert (so = []); Some ans
            with Contradiction _ -> None in
          (match ans with None -> ()
          | Some ans ->
            abstract repls vs ans cur_ans cand)
        | Some loc ->
          step x lc loc repls vs ans cur_ans cand);
      if not (num_sort_typ loc.typ_sub)
      then
        (* Choice 3: remove subterm from answer *)
        let a = Infer.fresh_typ_var () in
        let repls' = (loc.typ_sub, a)::repls in
        let vs' = a::vs in
        let loc' = {loc with typ_sub = TVar a} in
        let t' = typ_out loc' in
        let cur_ans' = (x, (t', lc))::cur_ans in
        (match typ_next loc' with (* x bound when leaving step *)
        | None ->
          (try
             let ans', _, so =
               unify ~use_quants:true ~params:vs' ~sb:ans
                 cmp_v uni_v [Eqty (TVar x, t', lc)] in
             validate vs' ans';
             assert (so = []);
             abstract repls' vs' ans' cur_ans' cand
           with Contradiction _ ->
             ())
        | Some loc' ->
          step x lc loc' repls' vs' ans cur_ans cand);
        (* Choice 4: match subterm with an earlier occurrence *)
        if not (implies_concl vs' (cur_ans' @ cand))
        then (
          let repl = Aux.assoc_all loc.typ_sub repls in
          List.iter
            (fun b ->
              let loc' = {loc with typ_sub = TVar b} in
              let t' = typ_out loc' in
              let cur_ans' = (x, (t', lc))::cur_ans in
              match typ_next loc' with
              | None ->
                (try
                   let ans', _, so =
                     unify ~use_quants:true ~params:vs' ~sb:ans
                       cmp_v uni_v [Eqty (TVar x, t', lc)] in
                   validate vs ans';
                   assert (so = []);
                   abstract repls vs ans' cur_ans' cand
                 with Contradiction _ ->
                   ())
              | Some loc' ->
                step x lc loc' repls vs ans cur_ans cand)
            repl;
          (* Choice 5: try subterms of the subterm *)
          (match typ_up loc with
          | None ->
            ()        
          | Some loc ->
            step x lc loc repls vs ans cur_ans cand);
        )
    in
    let cleanup vs ans =
      let ans = List.filter (fun (x,_) -> not (List.mem x vs)) ans in
      let ansvs = fvs_sb ans in
      List.filter (Aux.flip VarSet.mem ansvs) vs, ans in
    if implies_concl vs ans then Some (vs, ans)
    else
      let cnj_typ, _ = prem_and vs concl in
      try abstract [] vs ans [] cnj_typ; None
      with Result (vs, ans) -> Some (cleanup vs ans)
  with Contradiction _ -> None          (* subst_solved or implies_concl *)

let abd_typ cmp_v uni_v brs =
  let br0 = 0, List.hd brs in
  let more_brs = List.map (fun br -> -1, br) (List.tl brs) in
  let validate vs ans = List.iter
    (fun (prem, _) ->
      ignore (combine_sbs ~use_quants:false ~params:vs cmp_v uni_v
                [prem; ans]))
    brs in
  (* let time = ref (Sys.time ()) in *)
  let rec loop first acc done_brs = function
    | [] -> Some acc
    | (skip, br as obr)::more_brs ->
      (*Format.printf "abd_typ-loop:@ @[<2>%a@ ⟹@ %a@]@\n"
        pr_subst (fst br) pr_subst (snd br);*)
      match abd_simple cmp_v uni_v validate skip acc br with
      | Some acc ->
        (*let ntime = Sys.time () in
        Format.printf "ans: (%.2fs)@ @[<2>%a@]@\n" (ntime -. !time)
          pr_subst (snd acc); time := ntime;*)
        loop false acc (obr::done_brs) more_brs
      | None ->
        (* Format.printf "reset@\n"; *)
        if first then None
        else loop true ([], []) []
          ((skip+1, br)::List.rev_append done_brs more_brs) in
  Aux.bind_opt (loop true ([], []) [] (br0::more_brs))
    (fun (vs, ans) ->
      let num = List.map
        (fun (prem, concl) ->
          try
            let cnj_ty, cnj_num =
              combine_sbs ~use_quants:false ~params:vs cmp_v uni_v
                [prem; ans] in
            let res_ty, res_num =
              residuum cmp_v uni_v vs cnj_ty concl in
            assert (res_ty = []);
            cnj_num @ res_num
          with Contradiction _ -> assert false)
        brs in
      Some (vs, ans, num))

let abd_simple = ()
*)
let abd cmp_v uni_v brs =
  Some ([],[])
