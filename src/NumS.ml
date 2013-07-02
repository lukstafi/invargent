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
type ineqs = (var_name * (w list * w list)) list

let mult c (vars, cst, loc) =
  List.map (fun (v,k) -> v, c */ k) vars, c */ cst, loc

let sum_w cmp (vars1, cst1, loc1) (vars2, cst2, loc2) =
  let loc = loc_union loc1 loc2 in
  let vars = Aux.map_reduce (+/) (!/0) (vars1 @ vars2) in
  let vars = List.sort cmp
    (List.filter (fun (_,k) -> k <>/ !/0) vars) in
  vars, cst1 +/ cst2, loc

let diff cmp w1 w2 = sum_w cmp w1 (mult !/(-1) w2)

let zero_p (vars, cst, _) = vars = [] && cst = !/0

let equal_w cmp w1 w2 = zero_p (diff cmp w1 w2)

let unsubst sb =
  List.map (fun (v, (vars, cst, loc)) -> (v, !/(-1))::vars, cst, loc) sb

let unsolve (ineqs : ineqs) : w list = Aux.concat_map
  (fun (v, (left, right)) ->
    List.map (fun (vars, cst, loc) -> (v, !/(-1))::vars, cst, loc)
      left @
      List.map (fun rhs ->
        let vars, cst, loc = mult !/(-1) rhs in
        (v, !/1)::vars, cst, loc)
      right)
  ineqs
  

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

let subst_w cmp (eqs : w_subst) (vars, cst, loc : w) : w =
  let sums = List.map
    (fun (v,k) ->
      try let vars, cst, _ = mult k (List.assoc v eqs) in vars, cst
      with Not_found -> [v,k], !/0)
    vars in
  let vars, csts = List.split sums in
  let vars = Aux.map_reduce (+/) (!/0) (List.concat vars) in
  let vars = List.sort cmp
    (List.filter (fun (_,k) -> k <>/ !/0) vars) in
  let cst = List.fold_left (+/) cst csts in
  vars, cst, loc

let subst_ineqs cmp eqs ineqs = List.map
  (fun (v, (left, right)) ->
    v, (List.map (subst_w cmp eqs) left, List.map (subst_w cmp eqs) right))
  ineqs

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

(* TODO: quantifier violations not possible? *)
let solve ?(use_quants=false) ?(strict=false)
    ?(eqs=[]) ?(ineqs=[]) ?(eqn=[]) ?(ineqn=[]) ?(cnj=[])
    cmp cmp_w uni_v =
  (* FIXME: use uni_v when use_quants. *)
  let more_eqn, more_ineqn = Aux.partition_map (flatten cmp) cnj in
  let eqn = eqn @ more_eqn in
  let ineqn = ineqn @ more_ineqn in
  assert (not strict || eqn = []);
  let eqn = if eqs=[] then eqn else List.map (subst_w cmp eqs) eqn in
  let ineqn = if eqs=[] then ineqn else List.map (subst_w cmp eqs) ineqn in
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
  let ineqn = if eqn=[] then ineqn else List.map (subst_w cmp eqn) ineqn in
  let eqs = if eqn=[] then eqs else List.map
      (fun (v,eq) -> v, subst_w cmp eqn eq) eqs in
  (* inequalities [left <= v] and [v <= right] *)
  let ineqs = if eqn=[] then ineqs else
      List.map (fun (v, (left, right)) ->
        v,
        (List.map (subst_w cmp eqn) left,
         List.map (subst_w cmp eqn) right)) ineqs in
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
  let project v (vars, cst, loc as lhs) rhs =
    if equal_w cmp lhs rhs
    then
      let w = (v, !/(-1))::vars, cst, loc in
      if strict then
        let a = expand_atom false w in
        let t1, t2 = match a with
          | Leq (t1, t2, _) -> t1, t2 | _ -> assert false in
        raise (Contradiction ("Failed numeric strict inequality",
                              Some (t1, t2), loc))
      else Aux.Right w
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
        let ohs = mult (!/(-1) // k) (vars, cst, loc) in
        if k >/ !/0
        then
          [], [ohs],
          Aux.partition_map (fun lhs -> project v lhs ohs) left
        else
          [ohs], [],
          Aux.partition_map (fun rhs -> project v ohs rhs) right in
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

let fvs_w (vars, _, _) = vars_of_list (List.map fst vars)

exception Result of w_subst * ineqs

let abd_simple cmp cmp_w uni_v ~init_params validate
    skip eqs ineqs (prem, concl) =
  let skip = ref skip in
  try
    let d_eqs, (d_ineqs, d_implicits) =
      solve ~eqs ~ineqs ~cnj:prem cmp cmp_w uni_v in
    (* let c_eqs, (c_ineqs, c_implicits) =
      solve ~eqs ~ineqs ~cnj:prem cmp cmp_w uni_v in *)
    let dc_eqs, (dc_ineqs, dc_implicits) =
      solve ~eqs ~ineqs ~cnj:(prem @ concl) cmp cmp_w uni_v in
    let theta = unsubst dc_eqs @ dc_implicits in
    let theta_sb, _ = solve ~eqs:dc_eqs ~eqn:dc_implicits cmp cmp_w uni_v in
    let concl' = subst_ineqs cmp theta_sb dc_ineqs in
    let prem' =  subst_ineqs cmp theta_sb d_ineqs in
    let des = unsubst d_eqs @ d_implicits in
    let d_sb, _ = solve ~eqs:d_eqs ~eqn:d_implicits cmp cmp_w uni_v in
    let ans_eqs = List.map (subst_w cmp d_sb) theta in
    (* Algorithm in reverse order: *)
    (* We need to normalize the answer again after substitutions. *)
    let return eqn ineqn =
      try
        let eqs, (ans_ineqs, implicits) =
          solve ~use_quants:true ~eqn ~ineqn cmp cmp_w uni_v in
        let ans_eqs, _ =
          solve ~eqs ~eqn:implicits cmp cmp_w uni_v in
        validate ans_eqs ans_ineqs;
        if !skip <= 0 then raise (Result (ans_eqs, ans_ineqs))
        else decr skip
      with Contradiction _ -> () in
    let prepare ans_ineqs sb_cand =
      return
        (List.map (subst_w cmp sb_cand) ans_eqs)
        (List.map (subst_w cmp sb_cand) ans_ineqs) in
    (* Choice point 2. *)
    (* Iterate through all substitutions (as a product of equations
       for variables occurring in the answer, from premises [des] plus
       "identity equation"). *)
    let rename ans_ineqs =
      (* possible optimization:
         if !skip = 0 then (return ans_eqs ans_ineqs; incr skip); *)
      let allvs = List.fold_left VarSet.union VarSet.empty
        (List.map fvs_w ans_eqs) in
      let allvs = VarSet.union allvs
        (List.fold_left VarSet.union VarSet.empty
           (List.map fvs_w ans_ineqs)) in
      let repls = List.map
        (fun v -> (v, ([v,!/1], !/0, dummy_loc))::Aux.map_some
          (fun (vars, cst, loc) ->
            try
              let k, vars = Aux.pop_assoc v vars in
              Some (v, mult k (vars, cst, loc))
            with Not_found -> None)
          des)
        (VarSet.elements allvs) in
      Aux.product_iter (prepare ans_ineqs) repls in
    (* Compute the core by checking in turn whether conclusion atoms
       are implied by the premise and the partial answer so far. *)
    let rec core_fin ans_ineqs = function
      | [] -> rename ans_ineqs
      | w::concl ->
        (try
           ignore (solve ~strict:true
                      ~eqs:theta_sb ~ineqs:prem'
                      ~ineqn:(mult !/(-1) w::ans_ineqs)
                      cmp cmp_w uni_v);
           (* does not imply w *)
           core_fin (w::ans_ineqs) concl
         with Contradiction _ ->
           (* implies w *)
           core_fin ans_ineqs concl) in
    (* Choice point 1. *)
    let rec core untried partial = function
      | [] -> core_fin partial untried
      | w::concl ->
        (try
           ignore (solve ~strict:true
                      ~eqs:theta_sb ~ineqs:prem'
                      ~ineqn:(mult !/(-1) w::partial)
                      cmp cmp_w uni_v);
           (* prem' does not imply w *)
           core untried (w::partial) concl; (* choice 1a *)
           core (w::untried) partial concl  (* choice 1b *)
         with Contradiction _ ->
           (* prem' implies w *)
           core untried partial concl) in
    try core [] [] (unsolve concl'); None
    with Result (ans_eqs, ans_ineqs) -> Some (ans_eqs, ans_ineqs)
  with Contradiction _ -> None

let abd cmp_v uni_v ?(init_params=VarSet.empty) brs =
  let cmp_v v1 v2 =
    match cmp_v v1 v2 with
    | Upstream -> 1
    | Downstream -> -1
    | _ -> compare v1 v2 in
  let cmp (v1,_) (v2,_) = cmp_v v1 v2 in
  let cmp_w (vars1,cst1,_) (vars2,cst2,_) =
    match vars1, vars2 with
    | [], [] -> 0
    | _, [] -> -1
    | [], _ -> 1
    | (v1,_)::_, (v2,_)::_ -> cmp_v v1 v2 in
  let br0 = 0, List.hd brs in
  let more_brs = List.map (fun br -> -1, br) (List.tl brs) in
  let validate eqs (ineqs : ineqs) = List.iter
    (fun (prem, _) ->
      ignore (solve ~eqs ~ineqs ~cnj:prem
                cmp cmp_w uni_v))
    brs in
  let rec loop first ans_eqs ans_ineqs done_brs = function
    | [] ->
      let ans = List.map (expand_atom true) (unsubst ans_eqs) in
      let ans = ans @ List.map (expand_atom false) (unsolve ans_ineqs) in
      [], ans
    | (skip, br as obr)::more_brs ->
      match abd_simple cmp cmp_w uni_v init_params validate
        skip ans_eqs ans_ineqs br with
      | Some (ans_eqs, ans_ineqs) ->
        loop false ans_eqs ans_ineqs (obr::done_brs) more_brs
      | None ->
        if first then
          let ans = List.map (expand_atom true) (unsubst ans_eqs) in
          let ans = ans @ List.map (expand_atom false) (unsolve ans_ineqs) in
          raise (Suspect ([], ans @ snd br))
        else loop true [] [] []
          ((skip+1, br)::List.rev_append done_brs more_brs) in
  loop true [] [] [] (br0::more_brs)

let abd_s cmp_v uni_v ?(init_params=VarSet.empty) prem concl =
  let cmp_v v1 v2 =
    match cmp_v v1 v2 with
    | Upstream -> 1
    | Downstream -> -1
    | _ -> compare v1 v2 in
  let cmp (v1,_) (v2,_) = cmp_v v1 v2 in
  let cmp_w (vars1,cst1,_) (vars2,cst2,_) =
    match vars1, vars2 with
    | [], [] -> 0
    | _, [] -> -1
    | [], _ -> 1
    | (v1,_)::_, (v2,_)::_ -> cmp_v v1 v2 in
  let validate eqs (ineqs : ineqs) = () in
  match abd_simple cmp cmp_w uni_v ~init_params validate
    0 [] [] (prem, concl) with
  | Some (ans_eqs, ans_ineqs) ->
    let ans = List.map (expand_atom true) (unsubst ans_eqs) in
    let ans = ans @ List.map (expand_atom false) (unsolve ans_ineqs) in
    Some ([], ans)
  | None -> None

let disjelim_rotations = ref 3

let i2f = float_of_int
let expand_eqineqs eqs ineqs =
  let ans = List.map (expand_atom true) (unsubst eqs) in
  ans @ List.map (expand_atom false) (unsolve ineqs)

let disjelim cmp_v uni_v brs =
  let vars = List.map fvs_formula brs in
  let common =
    match vars with [] -> assert false
    | [vars] -> vars
    | hd::tl -> List.fold_left VarSet.inter hd tl in
  let cmp_v v1 v2 =
    let v1c = VarSet.mem v1 common and v2c = VarSet.mem v2 common in
    if v1c && not v2c then 1
    else if v2c && not v1c then -1
    else match cmp_v v1 v2 with
    | Upstream -> 1
    | Downstream -> -1
    | _ -> compare v1 v2 in
  let cmp (v1,_) (v2,_) = cmp_v v1 v2 in
  let cmp_w (vars1,cst1,_) (vars2,cst2,_) =
    match vars1, vars2 with
    | [], [] -> 0
    | _, [] -> -1
    | [], _ -> 1
    | (v1,_)::_, (v2,_)::_ -> cmp_v v1 v2 in
  let compare_w (vars1,cst1,_) (vars2,cst2,_) =
    let c = compare vars1 vars2 in
    if c = 0 then compare_num cst1 cst2 else c in
  let polytopes, elim_eqs = List.split
    (List.map
       (fun cnj ->
         let eqs, (ineqs, implicits) = solve ~cnj cmp cmp_w uni_v in
         let eqs, _ = solve ~eqs ~eqn:implicits cmp cmp_w uni_v in
         let eqs, elim_eqs = List.partition
           (fun (v, _) -> VarSet.mem v common) eqs in
         (eqs, ineqs), elim_eqs)
       brs) in
  let polytopes = List.map2
    (fun (eqs, ineqs) esb ->
      List.map (fun (v,w) -> v, subst_w cmp esb w) eqs,
      subst_ineqs cmp esb ineqs)
    polytopes elim_eqs in
  let faces : w list list = List.map2
    (fun br esb -> Aux.concat_map
       (fun a -> match (flatten cmp a) with
       | Aux.Right w -> [subst_w cmp esb w]
       | Aux.Left w -> let w = subst_w cmp esb w in [w; mult !/(-1) w]) br)
    brs elim_eqs in
  let check face =
    let ineqn = [mult !/(-1) face] in
    List.for_all
      (fun (eqs, ineqs) ->
        try ignore
              (solve ~strict:true ~eqs ~ineqs ~ineqn cmp cmp_w uni_v);
            false
        with Contradiction _ -> true)
      polytopes in
  let selected : (w list * w list) list =
    List.map (List.partition check) faces in
  let ridges : (w * w) list = Aux.concat_map
    (fun (sel, ptope) ->
      Aux.concat_map (fun p -> List.map (fun s->s, p) sel) ptope)
    selected in
  let angle i j = i2f (i+1) /. i2f (j+1) in
  let cands = List.map
    (fun (s, p) ->
      let l = Array.init
        !disjelim_rotations (fun i ->
          if i <= 1 then [||]
          else Array.init (i-1) (fun j ->
            angle j i, sum_w cmp (mult !/(j+1) s) (mult !/(i+1) p))) in
      let r = Array.init
        !disjelim_rotations (fun i ->
          if i <= 1 then [||]
          else Array.init (i-1) (fun j ->
            angle i j, sum_w cmp (mult !/(i+1) s) (mult !/(j+1) p))) in
      (1., sum_w cmp s p) ::
        Array.to_list (Array.concat (Array.to_list l)) @
        Array.to_list (Array.concat (Array.to_list r)))
    ridges in
  let cands = List.map (fun angles ->
    List.map snd
      (List.sort (fun (a,_) (b,_) -> compare a b) angles)) cands in
  let result = Aux.concat_map fst selected in
  let result = Aux.map_some
    (fun cands -> try Some (List.find check cands)
      with Not_found -> None) cands
    @ result in
  let sort_w (vars, cst, loc) =
    let vars = Aux.map_reduce (+/) (!/0) vars in
    let vars = List.sort cmp
      (List.filter (fun (_,k) -> k <>/ !/0) vars) in
    vars, cst, loc in
  let result = List.map sort_w result in
  let rec idemp eqn ineqn = function
    | e1::(e2::_ as tl) when compare_w e1 e2 = 0 -> idemp eqn ineqn tl
    | e::tl when List.exists (fun w -> zero_p (sum_w cmp e w)) tl ->
      idemp (e::eqn) ineqn
        (List.filter (fun w -> not (zero_p (sum_w cmp e w))) tl)
    | e::tl -> idemp eqn (e::ineqn) tl
    | [] -> eqn, ineqn in
  let eqn, ineqn =
    idemp [] [] (List.sort compare result) in
  let check face ptope =
    let eqs, (ineqs, implicits) =
      solve ~eqn ~ineqn:ptope cmp cmp_w uni_v in
    let eqs, _ = solve ~eqs ~eqn:implicits cmp cmp_w uni_v in
    let ineqn = [mult !/(-1) face] in
    try ignore (solve ~strict:true ~eqs ~ineqs ~ineqn cmp cmp_w uni_v);
        false
    with Contradiction _ -> true in
  let rec redundant p1 = function
    | face::p2 ->
      if check face (p1 @ p2) then redundant p1 p2
      else redundant (face::p1) p2
    | [] -> p1 in
  [], List.map (expand_atom true) eqn
    @ List.map (expand_atom false) (redundant [] ineqn)

(* TODO *)
let simplify cmp_v vs cnj =
  if vs = [] then [], cnj
  else failwith "simplify: not implemented yet"

let satisfiable cnj =
  let cmp_v _ _ = Same_quant in
  let uni_v _ = false in
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
  try ignore (solve ~cnj cmp cmp_w uni_v); true
  with Contradiction _ -> false

type state = w_subst * ineqs
let empty_state = [], []

let formula_of_state (eqs, ineqs) = expand_eqineqs eqs ineqs
  

let holds cmp_v uni_v (eqs, ineqs : state) cnj : state =
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
  let eqs, (ineqs, implicits) =
    solve ~eqs ~ineqs ~cnj cmp cmp_w uni_v in
  let eqs, _ = solve ~eqs ~eqn:implicits cmp cmp_w uni_v in
  eqs, ineqs
