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

let solve ~use_quants cmp_v uni_v ?(eqs=[]) ?(ineqs=[]) cnj =
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
  let eqn_vs = List.map fst eqn in
  let ineqs, more_ineqn = if eqn=[] then ineqs, [] else
      let ineqs, more_ineqn = List.split
        (List.map (fun (v, (left, right)) ->
          let more_l, left =
            List.partition (fun (vars,_,_) ->
              List.exists (Aux.flip List.mem_assoc vars) eqn_vs) left in
          let more_r, right =
            List.partition (fun (vars,_,_) ->
              List.exists (Aux.flip List.mem_assoc vars) eqn_vs) right in
          let more_l = List.map
            (fun ineq ->
              let vars, cst, loc = subst cmp eqn ineq in
              Aux.sorted_put cmp (v,!/(-1)) vars, cst, loc)
            more_l in
          let more_r = List.map
            (fun ineq ->
              let vars, cst, loc = mult !/(-1) (subst cmp eqn ineq) in
              Aux.sorted_put cmp (v,!/1) vars, cst, loc)
            more_r in
          let ineq =
            if left <> [] || right <> []
            then Some (v, (left, right)) else None in
          ineq, more_l @ more_r) ineqs) in
      Aux.map_some (fun x->x) ineqs, more_ineqn in
  let ineqn = List.sort cmp_w (List.concat (more_ineqn @ [ineqn])) in
  let rec proj ineqs implicits ineqn =
    match ineqn with
    | [] -> ineqs, implicits
    | ([], cst, _)::ineqn when cst <=/ !/0 -> proj ineqs implicits ineqn
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
          Aux.partition_map
            (fun lhs ->
              if lhs = rhs then Aux.Right lhs
              else Aux.Left (diff cmp lhs rhs))
            left
        else
          let lhs = mult (!/1 // k) (vars, cst, loc) in
          [lhs], [],
          Aux.partition_map
            (fun rhs ->
              if lhs = rhs then Aux.Right lhs
              else Aux.Left (diff cmp lhs rhs))
            right in
      let more_ineqn = List.filter
        (function
        | [], cst, _ when cst <=/ !/0 -> false
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

let abd cmp_v uni_v brs =
  Some ([],[])
