(** Numeric sort operations for InvarGenT.

    Released under the GNU General Public Licence (version 2 or
    higher), NO WARRANTY of correctness etc. (C) Lukasz Stafiniak 2013
    @author Lukasz Stafiniak lukstafi (AT) gmail.com
    @since Mar 2013
*)

let early_num_abduction = ref (* false *)true
let abd_rotations = ref (* 2 *)3(* 4 *)
let abd_prune_at = ref (* 4 *)6(* 10 *)
let abd_timeout_count = ref (* 500 *)1000(* 5000 *)
let abd_discard_param_only = ref (* false *)true
let abd_fail_timeout_count = ref 20
let aggressive_discard = ref (* false *)true
let disjelim_rotations = ref 3
let abductive_disjelim = ref false(* true *)
let int_pruning = ref false(* true *)
let strong_int_pruning = ref false
let passing_ineq_trs = ref false
let subopti_of_cst = ref `No_sides
let revert_csts = ref true(* false *)
let discard_penalty = ref 2
let more_general = ref (* true *)false
let general_reward = ref 2
let affine_penalty = ref (* 4 *)3
let affine_threshold = ref 2
let affine_thresh_penalty = ref 3
let reward_constrn = ref 2 (* (-1) *)
let complexity_penalty = ref 2.5
let reward_locality = ref 3
let multi_levels_penalty = ref 4
let escaping_var_penalty = ref 4
let locality_vars_penalty = ref 6
let nonparam_vars_penalty = ref 6
let no_prem_var_penalty = ref 6
let no_prem_penalty_derived_only = ref true
let abduct_source_bonus = ref 0
(* special_source_bonus is used only when prefer_bound_to_local is true. *)
let special_source_bonus = ref 7
(* uplevel_penalty is used only when prefer_bound_to_outer is true. *)
let uplevel_penalty = ref 9
let prefer_bound_to_local = ref false
let prefer_bound_to_outer = ref false
let only_off_by_1 = ref false
let concl_abd_penalty = ref 4
let discourage_upper_bound = ref 6
let discourage_already_bounded = ref 4
let upper_bound_outer_penalty = ref 5
let implied_by_prem_penalty = ref 0
let implicit_eq_penalty = ref 10
let encourage_not_yet_bounded = ref 2
let discourage_equations_1 = ref 4
let discourage_equations_2 = ref 4
let implied_ineqn_compensation = ref 1
let abd_scoring = ref `Sum
let complexity_scale = ref (`LinThres (2.0, 2.0)) (* (`Pow 2.0) *)
let preserve_params = ref false(* true *)
let preserve_only_target = ref false(* true *)
let max_opti_postcond = ref 5
let max_subopti_postcond = ref 5
let opti_postcond_reward = ref 5
let primary_only_target = ref true
let excuse_case_by_common = ref (* true *)false
let verif_all_brs = ref false(* true *)
let verif_incremental = ref (* true *)false

let abd_fail_flag = ref false
let abd_timeout_flag = ref false

open Defs
open NumDefs
(* open Terms *)
open Num
open Aux

let num_of = function
  | Terms.Alien (Terms.Num_term t) -> t
  | Terms.TVar v when var_sort v = Num_sort -> Lin (1, 1, v)
  | _ -> assert false

let sort_formula = List.map
    Terms.(function
        | Eqty (t1, t2, loc) ->
          Eq (num_of t1, num_of t2, loc)
        | A (Num_atom a) -> a
        | _ -> assert false)

let formula_of_sort = List.map Terms.(fun a -> A (Num_atom a))

let sort_of_assoc sb =
  List.map
    (fun (v, (t, lc)) -> Eq (Lin (1,1,v), num_of t, lc))
    sb
let sort_of_subst sb = sort_of_assoc (varmap_to_assoc sb)

(* FIXME: or *)
    (*Terms.(function
        | Eq (t1, t2, loc) ->
          Eqty (Alien (Num_term t1), Alien (Num_term t2), loc)
        | a -> A (Num_atom a))*)

let (!/) i = num_of_int i
type w = (var_name * num) list * num * loc
type w_subst = w VarMap.t

let w_size (vars, cst, _) =
  (if cst =/ !/0 then 0 else 1) +
    List.fold_left
      (fun acc (_, coef) -> if coef =/ !/0 then acc else acc + 1) 0 vars

let w_complexity1 bvs vars =
  let update =
    match !complexity_scale with
    | `Pow pow_scale ->
      fun kk -> kk ** pow_scale *. !complexity_penalty
    | `LinThres (thres, step) ->
      fun kk ->
        if kk < thres then kk *. !complexity_penalty
        else kk *. !complexity_penalty +. step in
  int_of_float
    (List.fold_left
       (fun acc (v, k) ->
          if VarSet.mem v bvs && k <>/ !/0 then
            let r = Ratio.float_of_ratio (Num.ratio_of_num k) in
            let r' =
              Ratio.float_of_ratio (Num.ratio_of_num (!/1 // k)) in
            let kk = max (abs_float r) (abs_float r') in
            acc -. update kk
          else acc)
       0. vars)

let w_complexity2 bvs (vars, cst, _) =
  let rcst = Num.ratio_of_num cst in
  let cc =
    abs (Big_int.int_of_big_int (Ratio.numerator_ratio rcst)) +
      abs (Big_int.int_of_big_int
             (Ratio.denominator_ratio rcst)) - 1 in
  List.fold_left
    (fun acc (v, k) ->
       if VarSet.mem v bvs then
         let r = Num.ratio_of_num k in
         let kk =
           abs (Big_int.int_of_big_int (Ratio.numerator_ratio r)) +
             abs (Big_int.int_of_big_int
                    (Ratio.denominator_ratio r)) - 1 in
         acc - kk
       else acc + !opti_postcond_reward)
    cc vars

let compare_comb vars1 vars2 =
  let rec loop = function
    | [], [] -> 0
    | [], _ -> -1
    | _, [] -> 1
    | (v1, k1)::vars1, (v2, k2)::vars2 ->
      let c = compare v1 v2 in
      if c <> 0 then c
      else
        let c = compare_num k1 k2 in
        if c <> 0 then c
        else loop (vars1, vars2) in
  loop (vars1, vars2)

(* Assumes [vars1] and [vars2] are in the same order. *)
let compare_w (vars1, cst1, _) (vars2, cst2, _) =
  let c = compare_num cst1 cst2 in
  if c <> 0 then c
  else compare_comb vars1 vars2

module WSet = Set.Make (struct type t = w let compare = compare_w end)
let add_to_wset l ws = List.fold_right WSet.add l ws
let wset_of_list l = List.fold_right WSet.add l WSet.empty
let wset_of_map f l =
  List.fold_left (fun acc x -> WSet.union acc (f x)) WSet.empty l  
let wset_map f ws =
  WSet.fold (fun w ws -> WSet.add (f w) ws) ws WSet.empty
let wset_map_to_list f ws =
  WSet.fold (fun w ws -> f w :: ws) ws []
let wset_partition_map f ws =
  WSet.fold (fun w (wl, wr) ->
      match f w with
      | Left l -> l::wl, wr
      | Right r -> wl, r::wr)
    ws ([], [])

module CombMap = Map.Make (struct type t = (var_name * num) list
                           let compare = compare_comb end)
type affine = (num * loc) CombMap.t
let affine_to_ineqn af =
  CombMap.fold (fun vars (cst, lc) acc -> (vars, cst, lc)::acc)
    af []
let affine_add ~is_lhs (vars, cst, lc) af =
  try
    let cst', _ = CombMap.find vars af in
    let cmp = if is_lhs then (</) else (>/) in
    if cmp cst' cst then CombMap.add vars (cst, lc) af else af
  with Not_found -> CombMap.add vars (cst, lc) af
let affine_mem ~is_lhs (vars, cst, _) af =
  try
    let cst', _ = CombMap.find vars af in
    if is_lhs then cst' >=/ cst else cst' <=/ cst
  with Not_found -> false
let affine_empty = CombMap.empty
let affine_partition_map f af =
  CombMap.fold (fun vars (cst, lc) (wl, wr) ->
      match f (vars, cst, lc) with
      | Left l -> l::wl, wr
      | Right r -> wl, r::wr)
    af ([], [])
let affine_union ~is_lhs af1 af2 =
  let cmp = if is_lhs then (</) else (>/) in
  CombMap.merge
    (fun vars b1 b2 ->
       match b1, b2 with
       | None, None -> None
       | Some _, None -> b1
       | None, Some _ -> b2
       | Some (cst1, _), Some (cst2, _) ->
         if cmp cst1 cst2 then b2 else b1)
    af1 af2
let affine_of_list ~is_lhs ineqn =
  List.fold_left (fun acc w -> affine_add ~is_lhs w acc) affine_empty ineqn
let affine_map ~is_lhs f af =
  let ineqn = affine_to_ineqn af in
  affine_of_list ~is_lhs (List.map f ineqn)
let affine_map_to_list f af =
  CombMap.fold (fun vars (cst, lc) ws -> f (vars, cst, lc) :: ws) af []
let add_to_affine ~is_lhs l af =
  List.fold_right (affine_add ~is_lhs) l af
let affine_exists f af =
  CombMap.exists (fun vars (cst, lc) -> f (vars, cst, lc)) af

type ineqs = (affine * affine) VarMap.t
type optis = (w * w) list
type suboptis = (w * w) list

let pr_vnum ppf (v, n) =
  Format.fprintf ppf "%s*%s" (string_of_num n) (var_str v)

let pr_w ppf (vs, cst, _ : w) =
  if vs = [] then Format.fprintf ppf "%s" (string_of_num cst)
  else Format.fprintf ppf "@[<2>%a@ +@ %s@]"
    (pr_sep_list "+" pr_vnum) vs (string_of_num cst)

let pr_sw ppf (v, w) =
  Format.fprintf ppf "@[<2>%s@ =@ %a@]" (var_str v) pr_w w

let pr_w_subst ppf sb =
  Format.fprintf ppf "@[<2>%a@]" (pr_sep_list "," pr_sw)
    (varmap_to_assoc sb)

let pr_ineq ppf (v, (wl, wr)) =
  let wl = affine_to_ineqn wl
  and wr = affine_to_ineqn wr in
  Format.fprintf ppf "@[<2>[%a]@ ≤@ %s@ ≤@ [%a]@]"
    (pr_sep_list ";" pr_w) wl (var_str v)
    (pr_sep_list ";" pr_w) wr

let pr_ineqs ppf (ineqs : ineqs) =
  pr_sep_list "," pr_ineq ppf (varmap_to_assoc ineqs)

let pr_hineqs ppf ineqs =
  pr_sep_list "," pr_ineq ppf (hashtbl_to_assoc ineqs)

let pr_opti ppf (w1, w2) =
  Format.fprintf ppf "@[<2>opti(%a,@ %a)@]" pr_w w1 pr_w w2

let pr_optis ppf (optis : optis) =
  pr_sep_list "," pr_opti ppf optis

let pr_subopti ppf (w1, w2) =
  Format.fprintf ppf "@[<2>subopti(%a,@ %a)@]" pr_w w1 pr_w w2

let pr_suboptis ppf (suboptis : suboptis) =
  pr_sep_list "," pr_subopti ppf suboptis

let pr_ans ppf (eqs, ineqs) =
  Format.fprintf ppf "%a@ ∧@ %a" pr_w_subst eqs pr_ineqs ineqs

let pr_state ppf (eqs, ineqs, optis, suboptis) =
  Format.fprintf ppf "%a@ ∧@ %a@ ∧@ %a@ ∧@ %a" pr_w_subst eqs
    pr_ineqs ineqs pr_optis optis pr_suboptis suboptis

let pr_eq ppf w = Format.fprintf ppf "%a@ = 0" pr_w w
let pr_ineq ppf w = Format.fprintf ppf "%a@ ≤ 0" pr_w w
let pr_eqn ppf eqn =
  pr_sep_list "," pr_eq ppf eqn
let pr_ineqn ppf ineqn =
  pr_sep_list "," pr_ineq ppf ineqn
let pr_eqnineqn ppf (eqn, ineqn) =
  Format.fprintf ppf "%a@ ∧@ %a" pr_eqn eqn pr_ineqn ineqn
let pr_sep_br ppf (_, (d_eqn, d_ineqn), (c_eqn, c_ineqn, c_optis, c_suboptis)) =
    Format.fprintf ppf "@[<2>%a,@ %a@ ⟹@ %a,@ %a,@ %a,@ %a@]"
    pr_eqn d_eqn pr_ineqn d_ineqn
    pr_eqn c_eqn pr_ineqn c_ineqn
    pr_optis c_optis pr_suboptis c_suboptis

let pr_br2 ppf (prem, concl) =
    Format.fprintf ppf "@[<2>%a@ ⟹@ %a@]"
    pr_formula prem pr_formula concl
let pr_br4 ppf (_, _, prem, concl) =
    Format.fprintf ppf "@[<2>%a@ ⟹@ %a@]"
    pr_formula prem pr_formula concl

type w_atom =
    Eq_w of w | Leq_w of w | Opti_w of (w * w) | Subopti_w of (w * w)  

let pr_w_atom ppf = function
  | Eq_w w -> Format.fprintf ppf "%a=0" pr_w w
  | Leq_w w -> Format.fprintf ppf "%a≤0" pr_w w
  | Opti_w (w1, w2) -> Format.fprintf ppf "opti(%a,%a)" pr_w w1 pr_w w2
  | Subopti_w (w1, w2) -> Format.fprintf ppf "subopti(%a,%a)" pr_w w1 pr_w w2

let pr_w_formula ppf atoms =
  pr_sep_list " ∧" pr_w_atom ppf atoms


let mult c (vars, cst, loc) =
  List.map (fun (v,k) -> v, c */ k) vars, c */ cst, loc

let sum_w ~cmp_v (vars1, cst1, loc1 as w1) (vars2, cst2, loc2 as w2) =
  let loc = loc_union loc1 loc2 in
  (* Alternative in case arguments were not normalized:  *)
  (* let vars = map_reduce ~cmp_k:cmp_v (+/) (!/0) (vars1 @ vars2) in *)
  (* We normalize [w] combinations prior to operating on them. *)
  (* FIXME: recover normalization guarantee. *)
  let cmp (x,_) (y,_) = cmp_v x y in
  let vars = union_merge cmp
      (fun (v1,k1) (v2,k2) ->
         if v1<>v2 then Format.printf
             "sum_w: order mism:@ w1=%a@ w2=%a@\n%!" pr_w w1 pr_w w2;
         assert (v1=v2); v1, k1+/k2)
      vars1 vars2 in
  let vars =
    List.filter (fun (_,k) -> k <>/ !/0) vars in
  vars, cst1 +/ cst2, loc

let norm_w ~cmp_v (vars, cst, loc) =
  let vars = map_reduce ~cmp_k:cmp_v (+/) (!/0) vars in
  let vars =
    List.filter (fun (_,k) -> k <>/ !/0) vars in
  vars, cst, loc

let diff ~cmp_v w1 w2 = sum_w ~cmp_v w1 (mult !/(-1) w2)

let norm_by_gcd (vars, _, _ as w) =
  match vars with
  | [] -> w
  | (_, k)::_ when k =/ !/1 || k =/ !/(-1) -> w
  | (_, k)::vars1 ->
    let denom k =
      Big_int.abs_big_int (Ratio.denominator_ratio (ratio_of_num k)) in
    let norm_d = List.fold_left
        (fun acc (_, k) -> Big_int.gcd_big_int acc (denom k))
        (denom k) vars1 in
    let nom k =
      Big_int.abs_big_int (Ratio.numerator_ratio (ratio_of_num k)) in
    let norm_n = List.fold_left
        (fun acc (_, k) -> Big_int.gcd_big_int acc (nom k))
        (nom k) vars1 in
    mult (num_of_big_int norm_d // num_of_big_int norm_n) w

let norm_by_lcd (vars, cst, _ as w) =
  let denom k =
    Big_int.abs_big_int (Ratio.denominator_ratio (ratio_of_num k)) in
  let norm = List.fold_left
      (fun acc (_, k) ->
         let d = denom k in
         Big_int.(div_big_int (mult_big_int acc d)
                    (gcd_big_int acc d)))
      (denom cst) vars in
  mult (num_of_big_int norm) w

let zero_p (vars, cst, _) = vars = [] && cst =/ !/0
let taut_w iseq (vars, cst, _) =
  vars = [] && ((iseq && cst =/ !/0) || (not iseq && cst <=/ !/0))
let contr_w iseq (vars, cst, _) =
  vars = [] && ((iseq && cst <>/ !/0) || (not iseq && cst >/ !/0))
let nonneg_cst_w (vars, cst, _) =
  vars = [] && (cst >=/ !/0)

(* TODO: a bit wasteful, simply compare. *)
let equal_w ~cmp_v w1 w2 = zero_p (diff ~cmp_v w1 w2)
let equal_2w ~cmp_v (w1, w2) (w3, w4) =
  equal_w ~cmp_v w1 w3 && equal_w ~cmp_v w2 w4

let compare_w ~cmp_v w1 w2 =
  match diff ~cmp_v w1 w2 with
  | [], cst, _ -> Num.compare_num cst !/0
  | (_, k)::_, _, _ -> Num.compare_num k !/0

(* Comparison disregarding the order of variables in the quantifier. *)
let nonq_cmp_w (vars1,cst1,_) (vars2,cst2,_) =
  let rec aux = function
    | [], [] -> Num.compare_num cst1 cst2
    | _, [] -> -1
    | [], _ -> 1
    | (v1,k1)::vs1, (v2,k2)::vs2 ->
      let c = Pervasives.compare v1 v2 in
      if c <> 0 then c
      else let c = Num.compare_num k1 k2 in
        if c <> 0 then c
        else aux (vs1, vs2) in
  aux (vars1, vars2)

let unsubst sb =
  VarMap.fold
    (fun v (vars, cst, loc) acc -> ((v, !/(-1))::vars, cst, loc)::acc)
    sb []

(* FIXME: no need to sort the variables? *)
let unsolve (ineqs : ineqs) : w list = concat_varmap
  (fun v (left, right) ->
    let left = affine_to_ineqn left
    and right = affine_to_ineqn right in
    List.map (fun (vars, cst, loc) -> (v, !/(-1))::vars, cst, loc)
      left @
      List.map (fun rhs ->
          let vars, cst, loc = mult !/(-1) rhs in
          (v, !/1)::vars, cst, loc)
        right)
  ineqs

let w_atom_loc = function
  | Eq_w (_, _, loc)
  | Leq_w (_, _, loc) -> loc
  | Opti_w ((_, _, lc1), (_, _, lc2))
  | Subopti_w ((_, _, lc1), (_, _, lc2)) -> loc_union lc1 lc2

let flatten ~cmp_v a : w_atom =
  (* We no longer have min/max subterms *)
  let rec flat (vars, cst, loc as acc) = function
    | Add sum ->
      List.fold_left flat acc sum
    | Cst (j,k) -> (vars, cst +/ (!/j // !/k), loc)
    | Lin (j,k,v) -> ((v, !/j // !/k)::vars, cst, loc) in
  let collect t1 t2 loc =
    let zero = [], !/0, loc in
    let w1 = flat zero t1 in
    let w2 = flat zero t2 in
    diff ~cmp_v (norm_w ~cmp_v w1) (norm_w ~cmp_v w2) in
  match a with
  | Eq (t1, t2, loc) ->
    Eq_w (collect t1 t2 loc)
  | Leq (t1, t2, loc) ->
    Leq_w (collect t1 t2 loc)
  | Opti (t1, t2, loc) ->
    let zero = [], !/0, loc in
    let w1 = flat zero t1 in
    let w2 = flat zero t2 in
    Opti_w (norm_w ~cmp_v w1, norm_w ~cmp_v w2)
  | Subopti (t1, t2, loc) ->
    let zero = [], !/0, loc in
    let w1 = flat zero t1 in
    let w2 = flat zero t2 in
    Subopti_w (norm_w ~cmp_v w1, norm_w ~cmp_v w2)

let flatten_formula ~cmp_v cnj = List.map (flatten ~cmp_v) cnj

let subst_w ~cmp_v (eqs : w_subst) (vars, cst, loc : w) : w =
  let sums = List.map
    (fun (v,k) ->
      try let vars, cst, _ = mult k (VarMap.find v eqs) in vars, cst
      with Not_found -> [v,k], !/0)
    vars in
  let vars, csts = List.split sums in
  let vars = map_reduce ~cmp_k:cmp_v (+/) (!/0) (List.concat vars) in
  let vars =
    List.filter (fun (_,k) -> k <>/ !/0) vars in
  let cst = List.fold_left (+/) cst csts in
  vars, cst, loc

let subst_2w ~cmp_v (eqs : w_subst) (w1, w2) =
  subst_w ~cmp_v eqs w1, subst_w ~cmp_v eqs w2

(* FIXME: can we assume normalized form, i.e. that the rightmost
   variable is first? *)
let subst_if_qv ~uni_v ~bvs ~cmp_v (eqs : w_subst) (vars, _, _ as w) =
  if vars=[] then w
  else
    let v, _ = maximum
        (* Order is increasing from right to left, we want the rightmost. *)
        ~leq:(fun (v1, _) (v2, _) -> cmp_v v1 v2 >= 0) vars in
    (* FIXME: [uni_v v] implies [mem v bvs], right? *)
    if uni_v v || VarSet.mem v bvs
    then subst_w ~cmp_v eqs w
    else w

let subst_if_qv_2w ~uni_v ~bvs ~cmp_v (eqs : w_subst) (w1, w2) =
  subst_if_qv ~uni_v ~bvs ~cmp_v eqs w1,
  subst_if_qv ~uni_v ~bvs ~cmp_v eqs w2

let subst_ineqs ~cmp_v eqs ineqs = List.map
  (fun (v, (left, right)) ->
    v, (wset_map (subst_w ~cmp_v eqs) left,
        wset_map (subst_w ~cmp_v eqs) right))
  ineqs

let subst_eqs ~cmp_v ~sb eqs = VarMap.map
  (fun eq -> subst_w ~cmp_v sb eq) eqs

let subst_one ~cmp_v (v, w) (vars, cst, loc as arg) =
  try
    let k, vars = pop_assoc v vars in
    let w_vs, w_cst, w_loc = mult k w in
    let vars = map_reduce ~cmp_k:cmp_v (+/) (!/0) (w_vs @ vars) in
    let vars =
      List.filter (fun (_,k) -> k <>/ !/0) vars in
    let cst = w_cst +/ cst in
    vars, cst, loc
  with Not_found -> arg

let subst_one_sb ~cmp_v w_sb sb =
  List.map (fun (v, w) -> v, subst_one ~cmp_v w_sb w) sb

let subst_w_atom ~cmp_v eqs =
  function
  | Eq_w w -> Eq_w (subst_w ~cmp_v eqs w)
  | Leq_w w -> Leq_w (subst_w ~cmp_v eqs w)
  | Opti_w w12 -> Opti_w (subst_2w ~cmp_v eqs w12)
  | Subopti_w w12 -> Subopti_w (subst_2w ~cmp_v eqs w12)

let subst_w_formula ~cmp_v eqs = List.map (subst_w_atom ~cmp_v eqs)

let frac_of_num k =
  let k = ratio_of_num k in
  Big_int.int_of_big_int (Ratio.numerator_ratio k),
  Big_int.int_of_big_int (Ratio.denominator_ratio k)

let denom_of_num k =
  let k = ratio_of_num k in
  Ratio.denominator_ratio k

let denom_w (vars,cst,_) =
  let k = List.fold_left
      (fun acc (_,k) ->
         lcm_big_int acc (denom_of_num k))
      (denom_of_num cst) vars in
  num_of_big_int k

let expand_w (vars, cst, loc) =
  let vars = List.map
      (fun (v,c) ->
         let j, k = frac_of_num c in
         Lin (j, k, v)) vars in
  let cst =
    let j, k = frac_of_num cst in
    if j=0 then [] else [Cst (j, k)] in
  match List.rev (cst @ vars) with
  | [] -> Cst (0,1)
  | [t] -> t
  | ts -> Add ts

let expand_sides_cst (vars, cst, loc) =
  let left_vars, right_vars = partition_map
      (fun (v,c) ->
         let j, k = frac_of_num c in
         assert (k > 0);
         if j>0 then Left (Lin (j, k, v))
         else Right (Lin ((-1)*j, k, v))) vars in
  let pack vars =
    match List.rev vars with
    | [] -> Cst (0,1)
    | [t] -> t
    | ts -> Add ts in
  pack left_vars, pack right_vars, cst, loc

let expand_sides (vars, cst, _) =
  let left_vars, right_vars = partition_map
      (fun (v,c) ->
         let j, k = frac_of_num c in
         assert (k > 0);
         if j>0 then Left (Lin (j, k, v))
         else Right (Lin ((-1)*j, k, v))) vars in
  let left_cst, right_cst =
    let j, k = frac_of_num cst in
    assert (k > 0);
    if j>0 then [Cst (j, k)], []
    else if j<0 then [], [Cst ((-1)*j, k)]
    else [], [] in
  let pack cst vars =
    match List.rev (cst @ vars) with
    | [] -> Cst (0,1)
    | [t] -> t
    | ts -> Add ts in
  pack left_cst left_vars, pack right_cst right_vars

let expand_cst cst =
  let j, k = frac_of_num cst in Cst (j, k)

let unexpand_sides_cst ~cmp_v ((lhs, rhs), cst, lc) =
  let unlin = function
    | Lin (i, j, v) -> v, !/i // !/j
    | _ -> assert false in
  let unpack = function
    | Cst (i, j) -> [], !/i // !/j, lc
    | Lin (i, j, v) -> [v, !/i // !/j], !/0, lc
    | Add ts ->
      match List.rev ts with
      | Cst (i, j) :: vars -> List.map unlin vars, !/i // !/j, lc
      | vars -> List.map unlin vars, !/0, lc in
  let lhs_vars, lhs_cst, _ = unpack lhs in
  diff ~cmp_v (norm_w ~cmp_v (lhs_vars, cst +/ lhs_cst, lc))
    (norm_w ~cmp_v (unpack rhs))

let unexpand_sides ~cmp_v ((lhs, rhs), lc) =
  let unlin = function
    | Lin (i, j, v) -> v, !/i // !/j
    | _ -> assert false in
  let unpack = function
    | Cst (i, j) -> [], !/i // !/j, lc
    | Lin (i, j, v) -> [v, !/i // !/j], !/0, lc
    | Add ts ->
      match List.rev ts with
      | Cst (i, j) :: vars -> List.map unlin vars, !/i // !/j, lc
      | vars -> List.map unlin vars, !/0, lc in
  diff ~cmp_v (norm_w ~cmp_v (unpack lhs)) (norm_w ~cmp_v (unpack rhs))

let expand_atom equ (_,_,loc as w) =
  let left, right = expand_sides (norm_by_gcd w) in
  if equ then Eq (left, right, loc) else Leq (left, right, loc)

let expand_opti ((_,_,lc1) as w1, (_,_,lc2 as w2)) =
  Opti (expand_w (norm_by_gcd w1), expand_w (norm_by_gcd w2),
        loc_union lc1 lc2)
let expand_subopti ((_,_,lc1) as w1, (_,_,lc2 as w2)) =
  Subopti (expand_w (norm_by_gcd w1), expand_w (norm_by_gcd w2),
           loc_union lc1 lc2)

let extract_v_subst v (vars, cst, loc) =
  let j, vars = pop_assoc v vars in
  v, mult (!/(-1) // j) (vars, cst, loc)

let expand_subst ~keep ~bvs eqs =
  let sb, sb' =
    List.split
      (List.map
         (fun (v, (vars, cst, loc as w) as sw) ->
            let w' = (v, !/(-1))::vars, cst, loc in
            (*[* Format.printf "expand_subst: v=%s w=%a@ norm=%a@\n%!"
              (var_str v) pr_w w pr_w
              (norm_by_lcd ((v, !/(-1))::vars, cst, loc)); *]*)
            if not (VarSet.mem v bvs) then (v, (expand_w w, loc)), sw
            else match expand_sides
                         (norm_by_lcd ((v, !/(-1))::vars, cst, loc)) with
            | Lin (1, 1, v), t when not (VarSet.mem v keep) ->
              (*[* Format.printf
                "expand_subst: [1] v=%s t=%a@\n%!" (var_str v) pr_term t; *]*)
              (v, (t, loc)), extract_v_subst v w'
            | t, Lin (1, 1, v) when not (VarSet.mem v keep) ->
              (*[* Format.printf
                "expand_subst: [2] v=%s t=%a@\n%!" (var_str v) pr_term t; *]*)
              (v, (t, loc)), extract_v_subst v w'
            | _ when not (VarSet.mem v keep) ->
              (*[* Format.printf
                "expand_subst: [3] v=%s t=%a@\n%!" (var_str v)
                pr_term (expand_w w); *]*)
              (v, (expand_w w, loc)), sw
            | _ ->
              (*[* Format.printf
                "expand_subst: [3] orig_v=%s orig_t=%a@\n%!" (var_str v)
                pr_term (expand_w w); *]*)
              let keep_vars, cands = List.partition
                  (fun (v, _) -> VarSet.mem v keep) vars in
              match cands with
              | [] -> (v, (expand_w w, loc)), sw
              | (v, j)::vars ->
                let w = mult (!/1 // j) (vars @ cands, cst, loc) in
                (*[* Format.printf
                  "expand_subst: [3] v=%s t=%a@\n%!" (var_str v)
                  pr_term (expand_w w); *]*)
                (v, (expand_w w, loc)), extract_v_subst v w')
         (varmap_to_assoc eqs)) in
  varmap_of_assoc sb, varmap_of_assoc sb'

let expand_formula = List.map
    (function
      | Eq_w w -> expand_atom true w
      | Leq_w w -> expand_atom false w
      | Opti_w w12 -> expand_opti w12
      | Subopti_w w12 -> expand_subopti w12)

let ans_to_num_formula (eqs, ineqs, optis, suboptis) =
  List.map (expand_atom true) (unsubst eqs)
  @ List.map (expand_atom false) (unsolve ineqs)
  @ List.map expand_opti optis
  @ List.map expand_subopti suboptis

let eqineq_to_num_formula (eqn, ineqn) =
  List.map (expand_atom true) eqn
  @ List.map (expand_atom false) ineqn

let cnj_to_num_formula (eqn, ineqn, optis, suboptis) =
  List.map (expand_atom true) eqn
  @ List.map (expand_atom false) ineqn
  @ List.map expand_opti optis
  @ List.map expand_subopti suboptis

let cnj_to_w_formula (eqn, ineqn, optis, suboptis) =
  List.map (fun w -> Eq_w w) eqn
  @ List.map (fun w -> Leq_w w) ineqn
  @ List.map (fun (w1,w2) -> Opti_w (w1, w2)) optis
  @ List.map (fun (w1,w2) -> Subopti_w (w1, w2)) suboptis

let num_to_formula phi = List.map (fun a -> Terms.A (Terms.Num_atom a)) phi

let eqn_of_eqs eqs =
  VarMap.fold
    (fun v (vars,cst,loc) acc -> ((v,!/(-1))::vars,cst,loc)::acc) eqs []

let eqineq_loc_union (eqn, ineqn) =
  List.fold_left loc_union dummy_loc
    (List.map (fun (_,_,lc) -> lc) (eqn @ ineqn))

let un_ans (eqs, ineqs) = unsubst eqs, unsolve ineqs

(* TODO: make wider use of [clean] pruning. *)
let clean_ws preserve iseq eqs = List.filter
    (fun (vars,_,_ as w) ->
       let res =
         List.for_all (fun (v,_) -> VarSet.mem v preserve) vars &&
         not (taut_w iseq w) in
       (*[* if not (taut_w iseq w) && not res then
         Format.printf "clean_ws: dropping w=%a@\n%!"
           pr_w w; *]*)
       res)
    eqs
let clean_ws' iseq eqs = List.filter
    (fun (vars,_,_ as w) -> not (taut_w iseq w))
    eqs

let taut_ineq (vars, cst, _) = vars = [] && cst <=/ !/0
let taut_strict_ineq (vars, cst, _) = vars = [] && cst </ !/0

(* Transitive closure modulo constants. *)
let ineq_transitive_cl ~cmp_v edge_l =
  let edges = Hashtbl.create 8 in
  let nodes = Hashtbl.create 8 in
  List.iter
    (fun (t1, t2, cst, loc) ->
       Hashtbl.replace nodes t1 (cst, loc);
       Hashtbl.replace nodes t2 (!/0, dummy_loc);
       Hashtbl.replace edges (t1, t2) (cst, loc))
    edge_l;
  (* More edges by affine displacement. *)
  Hashtbl.iter
    (fun i (c1, lc1) ->
       Hashtbl.iter
         (fun j (c2, lc2) ->
            let vars, _, _ =
              unexpand_sides ~cmp_v ((i, j), dummy_loc) in
            let cst = c1 -/ c2 in
            let w = vars, cst, dummy_loc in
            if taut_w false w
            then Hashtbl.add edges (i, j) (cst, loc_union lc1 lc2))
         nodes) nodes;
  (* Floyd-Warshall algo *)
  let add i j k =
    if not (Hashtbl.mem edges (i, j)) then
      let c1, lc1 = Hashtbl.find edges (i, k)
      and c2, lc2 = Hashtbl.find edges (k, j) in
      let lc = loc_union lc1 lc2 in
      Hashtbl.add edges (i, j) (c1 +/ c2, lc) in
  Hashtbl.iter
    (fun k _ ->
       Hashtbl.iter
         (fun i _ ->
            Hashtbl.iter
              (fun j _ -> try add i j k with Not_found -> ())
              nodes) nodes) nodes;
  edges

let pr_transitive_cl ~cmp_v ppf edges =
  let ineqn = Hashtbl.fold
    (fun key (cst, lc) ineqn ->
      unexpand_sides_cst ~cmp_v (key, cst, lc)::ineqn)
    edges [] in
  pr_ineqn ppf ineqn

let check_one_redund ~cmp_v ineqn a =
  (* A result [0=0] may represent a violation of strict inequality. *)
  taut_strict_ineq a ||
  List.exists (fun b -> taut_ineq (diff ~cmp_v a b)) ineqn

(* Checks redundancy only with respect to a single other atom. *)
let keep_one_nonredund ~cmp_v ~acc l =
  let rec loop acc = function
    | [] -> List.rev acc
    | a::l ->
      if check_one_redund ~cmp_v acc a then loop acc l
      else loop (a::acc) l in
  loop acc l

let merge_one_nonredund ~cmp_v ~cmp_w l1 l2 = (* merge cmp_w l1 l2 *)
  let l2 = List.filter
      (fun e -> not (check_one_redund ~cmp_v l1 e)) l2 in
  let l1 = List.filter
      (fun e -> not (check_one_redund ~cmp_v l2 e)) l1 in
  let rec aux acc = function
    | [], l -> List.rev_append acc l
    | l, [] -> keep_one_nonredund ~cmp_v ~acc l
    | e1::tl1, (e2::_ as l2) when cmp_w e1 e2 <= 0 ->
      if check_one_redund ~cmp_v acc e1
      then aux acc (tl1, l2)
      else aux (e1::acc) (tl1, l2)
    | l1, e2::tl2 ->
      aux (e2::acc) (l1, tl2) in
  aux [] (l1, l2)

(* FIXME: should we assume order? *)
let no_scope_viol ~cmp_v ~upward_of ~bvs (vars, _, _) =
  let vs = map_some
      (fun (v, _) -> if VarSet.mem v bvs then Some v else None) vars in
  let leq v1 v2 = cmp_v v1 v2 <> Right_of in
  if vs = [] then true
  else
    let v = maximum ~leq vs in
    (*[* Format.printf "no_scope_viol: v=%s@ " (var_str v);
    let res = *]*)
    List.for_all
      (fun (u, _) ->
         (*[* Format.printf "u=%s bvs=%b cmp=%s up=%b@ " (var_str u)
           (VarSet.mem u bvs) (var_scope_str (cmp_v v u))
           (upward_of u v); *]*)
         (* Case of a parameter candidate. *)
         not (VarSet.mem u bvs) && cmp_v v u = Left_of ||
         u == v || upward_of u v || cmp_v v u = Same_params)
      vars
      (*[* in Format.printf "@\n%!"; res *]*)

let no_scope_viol_atom ~cmp_v ~upward_of ~bvs = function
  | Leq_w w -> no_scope_viol ~cmp_v ~upward_of ~bvs w
  | Eq_w w -> no_scope_viol ~cmp_v ~upward_of ~bvs w
  | Opti_w ((vars1, cst1, lc1), (vars2, _, _)) ->
    no_scope_viol ~cmp_v ~upward_of ~bvs (vars1 @ vars2, cst1, lc1)
  | Subopti_w ((vars1, cst1, lc1), (vars2, _, _)) ->
    no_scope_viol ~cmp_v ~upward_of ~bvs (vars1 @ vars2, cst1, lc1)

(* Assumption: [v] is downstream of all [vars] *)
(* TODO: understand why the equivalent of [Terms.quant_viol] utterly
   fails here. *)
(* FIXME: fail on out-of-scope parameters. *)
let quant_viol uni_v cmp_v ~storeable bvs v0 vars =
  (* FIXME: v should already be to the right of vars. *)
  let leq v1 v2 = cmp_v v1 v2 >= 0 in
  let v = maximum ~leq (v0::List.map fst vars) in
  let res = uni_v v &&
            if storeable then VarSet.mem v bvs
            else not (VarSet.mem v bvs) in
  (*[* let v1 = match vars with (v1,_)::_ -> v1 | _ -> v0 in
  if res then
   Format.printf
     "NumS.quant_viol: v=%s; v0=%s; v1=%s; cmp0=%d; cmp1=%d; \
      uni(v)=%b; bvs(v)=%b@\n%!"
    (var_str v) (var_str v0) (var_str v1) (cmp_v v v0) (cmp_v v v1)
    (uni_v v) (VarSet.mem v bvs);
  *]*)
  res

let split_formula cnj =
  List.fold_left (fun (eqn, ineqn, optis, suboptis) ->
      function
      | Eq_w w -> w::eqn, ineqn, optis, suboptis
      | Leq_w w -> eqn, w::ineqn, optis, suboptis
      | Opti_w w12 -> eqn, ineqn, w12::optis, suboptis
      | Subopti_w w12 -> eqn, ineqn, optis, w12::suboptis)
    ([],[],[],[]) cnj

let split_flatten ~cmp_v cnj = split_formula (flatten_formula ~cmp_v cnj)

(* Note: w1 and w2 are just passed without change, unlike what
   [NumDefs.direct_opti] does. *)
let direct_opti ((vars1,cst1,lc1 as w1), (vars2,cst2,lc2 as w2)) =
  let vs1 = vars_of_list (List.map fst vars1)
  and vs2 = vars_of_list (List.map fst vars2) in
  let cand = VarSet.inter vs1 vs2 in
  let cand = VarSet.filter
      (fun v -> Num.sign_num (List.assoc v vars1) =
                Num.sign_num (List.assoc v vars2)) cand in
  try
    let v = VarSet.choose cand in
    let s = Num.sign_num (List.assoc v vars1) in
    Some (v, cand, s>0, w1, w2)
  with Not_found -> None

(* Transitive closure of one sides of inequalities. If [is_left=true],
   then find all smaller expressions, otherwise find all larger
   expressions. *)
let trans_wset ~cmp_v ineqs is_left wn =
  let rec proj acc wn =
    match wn with
    | [] -> acc
    | ([], _, _ as w)::wn -> proj (WSet.add w acc) wn
    | ((v,k)::vars, cst, loc as w)::wn ->
      let left, right =
        try List.assoc v ineqs
        with Not_found -> WSet.empty, WSet.empty in
      let is_left = if k </ !/0 then not is_left else is_left in
      let more = if is_left then left else right in
      let w1 = vars, cst, loc in
      let more =
        List.map (fun w2 -> sum_w ~cmp_v (mult k w2) w1)
          (WSet.elements more) in
      proj (WSet.add w acc) (more @ wn) in
  proj WSet.empty wn

let trans_affine ~cmp_v (ineqs : ineqs) ~is_lhs wn =
  let rec proj acc wn =
    match wn with
    | [] -> acc
    | ([], _, _ as w)::wn -> proj (affine_add ~is_lhs w acc) wn
    | ((v,k)::vars, cst, loc as w)::wn ->
      let left, right =
        try VarMap.find v ineqs
        with Not_found -> affine_empty, affine_empty in
      let is_left = if k </ !/0 then not is_lhs else is_lhs in
      let more = if is_left then left else right in
      let w1 = vars, cst, loc in
      let more =
        List.map (fun w2 -> sum_w ~cmp_v (mult k w2) w1)
          (affine_to_ineqn more) in
      proj (affine_add ~is_lhs w acc) (more @ wn) in
  proj affine_empty wn

type quant_viol_response =
    Store_viol of VarSet.t | Fail_viol of VarSet.t | Ignore_viol

let solve_aux ~use_quants ?(strict=false)
    ~eqs ~ineqs ~eqs' ~optis ~suboptis ~eqn ~ineqn ~cnj ~cnj'
    ~cmp_v ~cmp_w uni_v =
  let storeable, use_quants, bvs = match use_quants with
    | Ignore_viol -> false, false, VarSet.empty
    | Store_viol bvs -> true, true, bvs
    | Fail_viol bvs -> false, true, bvs in
  let eqs =
    if VarMap.is_empty eqs' then eqs
    else varmap_merge (subst_eqs ~cmp_v ~sb:eqs' eqs) eqs' in
  let eqs_implicits = ref [] in
  let subst_side_ineq ~is_lhs v sb ohs w =
    let vars, cst, lc as w' = subst_w ~cmp_v sb w in
    if affine_mem ~is_lhs:(not is_lhs) w' ohs
    then eqs_implicits := ((v,!/(-1))::vars,cst,lc) :: !eqs_implicits;
    w' in
  let ineqs = if VarMap.is_empty eqs' then ineqs else VarMap.mapi
      (fun v (wl,wr) ->
        affine_map ~is_lhs:true
          (subst_side_ineq ~is_lhs:true v eqs' wr) wl,
        affine_map ~is_lhs:false
          (subst_side_ineq ~is_lhs:false v eqs' wl) wr)
      ineqs in
  let more_eqn, more_ineqn, more_optis, more_suboptis =
    split_flatten ~cmp_v cnj in
  let more_eqn', more_ineqn', more_optis', more_suboptis' =
    split_formula cnj' in
  let more_eqn = more_eqn' @ more_eqn
  and more_ineqn = more_ineqn' @ more_ineqn
  and more_optis = more_optis' @ more_optis
  and more_suboptis = more_suboptis' @ more_suboptis in
  let eqn = eqn @ more_eqn in
  let optis = optis @ more_optis in
  let suboptis = suboptis @ more_suboptis in
  let ineqn0 = if more_ineqn = [] then ineqn else ineqn @ more_ineqn in
  (*[* Format.printf "NumS.solve: start ineqn0=@ %a@\n%!"
    pr_ineqn ineqn0; *]*)
  assert (not strict || eqn = []);
  let eqn =
    if VarMap.is_empty eqs then eqn
    else List.map (subst_w ~cmp_v eqs) eqn in
  let ineqn0 =
    if VarMap.is_empty eqs then ineqn0
    else List.map (subst_w ~cmp_v eqs) ineqn0 in
  let optis1 = List.map (subst_w ~cmp_v eqs) (flat2 optis) in
  let ineqn = ineqn0 @ optis1 in
  (*[* Format.printf "NumS.solve: subst1 ineqn0=@ %a@\n%!"
    pr_ineqn ineqn0; *]*)
  let eqn = List.map
    (fun (vars, cst, loc) ->
      List.filter (fun (v,k)->k <>/ !/0) vars, cst, loc) eqn in
  let eqn = List.sort cmp_w eqn in
  (*[* Format.printf "NumS.solve: start@ eqn=@ %a@ ineqn=@ %a@\n%!"
    pr_eqn eqn pr_ineqn ineqn; *]*)
  let quant_viol_cnj = ref [] in
  let rec elim acc = function
    | [] -> List.rev acc
    | ((v, k)::vars, cst, loc as w)::eqn
        when storeable && quant_viol uni_v cmp_v ~storeable bvs v vars ->
      quant_viol_cnj := Eq_w w :: !quant_viol_cnj;
      let w_sb = v, mult (!/(-1) // k) (vars, cst, loc) in
      let acc = subst_one_sb ~cmp_v w_sb acc in
      let eqn = List.map (subst_one ~cmp_v w_sb) eqn in
      elim (w_sb::acc) eqn
    | ((v, k)::vars, cst, loc)::eqn
        when use_quants &&
             quant_viol uni_v cmp_v ~storeable:false bvs v vars ->
      (*[* Format.printf "NumS.solve: fail--quant viol eq=@ %a@\n%!"
        pr_w ((v, k)::vars, cst, loc); *]*)
      let t1, t2 =
        match expand_atom true ((v, k)::vars, cst, loc) with
        | Eq (t1, t2, _) -> t1, t2
        | _ -> assert false in
      raise (Terms.Contradiction
               (Num_sort,
                "Quantifier violation (numeric equation)",
                Some (Terms.num t1, Terms.num t2), loc))
    | ((v, k)::vars, cst, loc)::eqn ->
      let w_sb = v, mult (!/(-1) // k) (vars, cst, loc) in
      let acc = subst_one_sb ~cmp_v w_sb acc in
      let eqn = List.map (subst_one ~cmp_v w_sb) eqn in
      elim (w_sb::acc) eqn
    | ([], cst, loc)::eqn when cst =/ !/0 -> elim acc eqn
    | ([], cst, loc)::eqn ->
      (*[* Format.printf "NumS.solve: fail-- eq=@ %a@\n%!"
        pr_w ([], cst, loc); *]*)
      let msg =
        "Failed numeric equation ("^Num.string_of_num cst^"=0)" in
      raise (Terms.Contradiction (Num_sort, msg, None, loc)) in
  (*[* Format.printf "NumS.solve: solving eqs...@\n%!"; *]*)
  (* [eqn0] and [ineqn0] store the unprocessed but substituted new
     equations and inequalities. *)
  let eqn0 = eqn in
  let eqn = varmap_of_assoc (elim [] eqn) in
  let new_eqvars =
    VarSet.union (varmap_domain eqn) (varmap_domain eqs') in
  (*[* Format.printf "NumS.solve: solved eqn=@ %a@\n%!"
    pr_w_subst eqn; *]*)
  let ineqn = if VarMap.is_empty eqn then ineqn
    else List.map (subst_w ~cmp_v eqn) ineqn in
  (*[* Format.printf "NumS.solve: subst2 ineqn=@ %a@\n%!"
    pr_ineqn ineqn; *]*)
  let eqs = if VarMap.is_empty eqn then eqs
    else subst_eqs ~cmp_v ~sb:eqn eqs in
  (* inequalities [left <= v] and [v <= right] *)
  let ineqs = if VarMap.is_empty eqn then ineqs else
      VarMap.mapi (fun v (wl, wr) ->
        affine_map ~is_lhs:true
          (subst_side_ineq ~is_lhs:true v eqn wr) wl,
        affine_map ~is_lhs:false
          (subst_side_ineq ~is_lhs:false v eqn wl) wr) ineqs in
  (*[* Format.printf "NumS.solve: simplified eqn=@ %a@\n%!"
    pr_w_subst eqn; *]*)
  let more_ineqn =
    concat_varmap
      (fun v w ->
        try
          let left, right = VarMap.find v ineqs in
          affine_map_to_list (fun lhs -> diff ~cmp_v lhs w) left @
            affine_map_to_list (fun rhs -> diff ~cmp_v w rhs) right
        with Not_found -> [])
      eqn in
  let ineqs = VarMap.filter
      (fun v _ -> not (VarSet.mem v new_eqvars)) ineqs in
  let ineqn = List.sort cmp_w (more_ineqn @ ineqn) in
  (*[* Format.printf "NumS.solve:@\neqs=%a@\nsimplified ineqn=@ %a@\n%!"
    pr_w_subst (varmap_merge eqn eqs) pr_ineqn ineqn; *]*)
  let project v (vars, cst, loc as lhs) rhs =
    if equal_w ~cmp_v lhs rhs
    then
      let w = (v, !/(-1))::vars, cst, loc in
      if strict then
        let a = expand_atom false w in
        (*[* Format.printf "NumS.solve: fail-- strict ineq=@ %a@\n%!"
          pr_w w; *]*)
        let t1, t2 = match a with
          | Leq (t1, t2, _) -> t1, t2 | _ -> assert false in
        raise (Terms.Contradiction
                 (Num_sort, "Failed numeric strict inequality",
                  Some (Terms.num t1, Terms.num t2), loc))
      else Right (norm_w ~cmp_v w)
    else Left (diff ~cmp_v lhs rhs) in
  let rec proj (ineqs : ineqs) implicits ineqn0 =
    (*[* Format.printf
      "NumS.solve-project:@\nineqs=%a@\nimplicits=%a@\nineqn0=@ %a@\n%!"
      pr_ineqs ineqs pr_eqn implicits pr_ineqn ineqn0; *]*)  
    let handle_proj v k vars cst loc ineqn =
      let trans_affine = trans_affine ~cmp_v ineqs in
      let left, right =
        try VarMap.find v ineqs
        with Not_found -> affine_empty, affine_empty in
      let ineq_l, ineq_r, (more_ineqn, more_implicits) =
        (* Change sides wrt. to variable [v]. *)
        let ohs = mult (!/(-1) // k) (vars, cst, loc) in
        if k >/ !/0
        then
          (if not strict && affine_mem ~is_lhs:false ohs right
           then [], [], ([], [])
           else [], [ohs],
                affine_partition_map (fun lhs -> project v lhs ohs) left)
        else
          (if not strict && affine_mem ~is_lhs:true ohs left
           then [], [], ([], [])
           else [ohs], [],
                affine_partition_map (fun rhs -> project v ohs rhs) right) in
      (*[* Format.printf
        "NumS.solve-project: try v=%s@\nmore_ineqn=@ %a@\nmore_impl=@ %a@\n%!"
        (var_str v) pr_ineqn more_ineqn pr_eqn more_implicits; *]*)  
      let more_ineqn = List.filter
        (function
        | [], cst, _
          when (strict && cst </ !/0) || (not strict && cst <=/ !/0) ->
          false
        | [], cst, loc ->
          let a = expand_atom false ([v, !/(-1)], cst, loc) in
          (*[* Format.printf "NumS.solve: fail-- ineq.2=@ %a@\n%!"
            pr_w ([], cst, loc); *]*)
          let t1, t2 = match a with
            | Leq (t1, t2, _) -> t1, t2 | _ -> assert false in
          raise (Terms.Contradiction
                   (Num_sort, "Failed numeric inequality",
                    Some (Terms.num t1, Terms.num t2), loc))
        | _ -> true)
        more_ineqn in
      let ineqn =
        merge_one_nonredund ~cmp_v ~cmp_w (List.sort cmp_w more_ineqn) ineqn in
      let more_ineqs =
        affine_union ~is_lhs:true
          (trans_affine ~is_lhs:true ineq_l) left,
        affine_union ~is_lhs:false
          (trans_affine ~is_lhs:false ineq_r) right in
      (*[* Format.printf
        "NumS.solve-project: res v=%s@\nmore_ineqn=@ %a@\nineqs_v=@ %a@\n%!"
        (var_str v) pr_ineqn more_ineqn
        pr_ineqs (VarMap.singleton v more_ineqs); *]*)  
      let ineqs = VarMap.add v more_ineqs ineqs in
      proj ineqs (more_implicits @ implicits) ineqn in
    match ineqn0 with
    | [] -> ineqs, implicits
    | ([], cst, _)::ineqn
        when (strict && cst </ !/0) || (not strict && cst <=/ !/0) ->
      proj ineqs implicits ineqn
    | ([], cst, loc)::_ ->
        (*[* Format.printf "NumS.solve: fail-- ineq=@ %a@\n%!"
          pr_w ([], cst, loc); *]*)
      raise (Terms.Contradiction
               (Num_sort,
                "Failed numeric inequality (cst="^
                  Num.string_of_num cst^")",
                None, loc))
    | ((v, k)::vars, cst, loc as w)::ineqn
        when storeable && quant_viol uni_v cmp_v ~storeable bvs v vars ->
      let old_ineq =
        try
          let lhs, rhs = VarMap.find v ineqs in
          let ohs = mult (!/(-1) // k) (vars, cst, loc) in
          if k >/ !/0 then affine_mem ~is_lhs:false ohs rhs
          else affine_mem ~is_lhs:true ohs lhs
        with Not_found -> false in
      if not old_ineq then
        quant_viol_cnj := Leq_w w :: !quant_viol_cnj;
      handle_proj v k vars cst loc ineqn
    | ((v, k)::vars, cst, loc)::ineqn
        when use_quants &&
             quant_viol uni_v cmp_v ~storeable:false bvs v vars ->
        (*[* Format.printf "NumS.solve: fail--quant viol ineq=@ %a@\n%!"
          pr_w ((v, k)::vars, cst, loc); *]*)
      let t1, t2 =
        match expand_atom false ((v, k)::vars, cst, loc) with
        | Leq (t1, t2, _) -> t1, t2
        | _ -> assert false in
      raise (Terms.Contradiction
               (Num_sort,
                "Quantifier violation (numeric inequality)",
                Some (Terms.num t1, Terms.num t2), loc))
    | ((v,k)::vars, cst, loc)::ineqn ->
      handle_proj v k vars cst loc ineqn in
  let propagate (m, n) =
    let (m_vars, m_cst, _ as m) = subst_w ~cmp_v eqn m
    and (n_vars, n_cst, _ as n) = subst_w ~cmp_v eqn n in
    if m_vars=[] && m_cst =/ !/0 || n_vars=[] && n_cst =/ !/0
    then None
    (* Possible contradiction will be recognized from the implicit
       equality on next iteration. *)
    else if m_vars=[] && m_cst <>/ !/0 then Some (Right n)
    else if n_vars=[] && n_cst <>/ !/0 then Some (Right m)
    else if equal_w ~cmp_v m n then Some (Right m)
    else Some (Left (m, n)) in
  (*[* Format.printf "NumS.solve: solving optis...@\n%!"; *]*)
  let optis, more_implicits =
    if VarMap.is_empty eqn then optis, []
    else partition_choice (map_some propagate optis) in
  (*[* Format.printf "NumS.solve: solving suboptis...@\n%!"; *]*)
  let suboptis, more_ineqn =
    if VarMap.is_empty eqn then suboptis, []
    else partition_choice (map_some propagate suboptis) in
  (*[* Format.printf "NumS.solve: solving ineqs...@\nineqn=%a@\n%!"
    pr_ineqn ineqn; *]*)
  let ineqs, implicits = proj ineqs (more_implicits @ !eqs_implicits)
      (keep_one_nonredund ~cmp_v ~acc:[] (more_ineqn @ ineqn)) in
  (*[* Format.printf "NumS.solve: done@\nineqs=@ %a@\n%!"
    pr_ineqs ineqs; *]*)
  
  (varmap_merge eqn eqs, ineqs,
   optis, suboptis), eqn0, ineqn0, WSet.elements (wset_of_list implicits),
  !quant_viol_cnj

type num_solution = w_subst * ineqs * optis * suboptis

let solve_get_eqn ~use_quants ?strict
    ?(eqs=VarMap.empty) ?(ineqs=VarMap.empty) ?(eqs'=VarMap.empty)
    ?(optis=[]) ?(suboptis=[]) ?(eqn=[]) ?(ineqn=[]) ?(cnj=[]) ?(cnj'=[])
    ~cmp_v ~cmp_w uni_v =
  (*[* Format.printf
    "NumS.main-solve: start@\ninit_st=@ %a@\neqn=%a@\nineqn=%a@\n\
     cnj=%a@\ncnj'=%a@\n%!"
    pr_state (eqs, ineqs, optis, suboptis) pr_eqn eqn pr_ineqn ineqn
    pr_formula cnj pr_w_formula cnj'; *]*)
  let all_implicit = ref [] in
  let all_eqn = ref [] in
  let all_ineqn = ref [] in
  let all_quant_viol_cnj = ref [] in
  let rec loop ((eqs, ineqs, optis, suboptis),
                eqn0, ineqn0, implicits, quant_viol_cnj) =
    if implicits=[] then (
      all_eqn := eqn0 @ !all_eqn;
      all_ineqn := ineqn0 @ !all_ineqn;
      all_quant_viol_cnj := quant_viol_cnj @ !all_quant_viol_cnj;
      (eqs, ineqs, optis, suboptis))
    else (
      (*[* Format.printf "solve: implicits=%a@\n%!"
        pr_eqn implicits; *]*)
      all_implicit := implicits @ !all_implicit;
      all_eqn := eqn0 @ !all_eqn;
      all_ineqn := ineqn0 @ !all_ineqn;
      all_quant_viol_cnj := quant_viol_cnj @ !all_quant_viol_cnj;
      loop
        (solve_aux ~use_quants ?strict ~eqs ~ineqs ~optis ~suboptis
           ~eqn:implicits
           ~eqs':VarMap.empty
           ~ineqn:[] ~cnj:[] ~cnj':[] ~cmp_v ~cmp_w uni_v)) in
  if eqn=[] && (VarMap.is_empty eqs || VarMap.is_empty eqs') &&
     ineqn=[] && optis=[] &&
     suboptis=[] && cnj=[] && cnj'=[]
  then (varmap_merge eqs eqs', ineqs, [], []), [], [], [], []
  else
    let (eqs,ineqs,optis,suboptis as res) =
      loop (solve_aux ~use_quants ?strict ~eqs ~ineqs ~eqs' ~optis ~suboptis
              ~eqn ~ineqn ~cnj ~cnj' ~cmp_v ~cmp_w uni_v) in
    (*[* Format.printf "NumS.main-solve: done@\n%a@\n@\n%!"
      pr_state res; *]*)
    res, !all_eqn, !all_ineqn, !all_implicit, !all_quant_viol_cnj

let solve ?(use_quants=Ignore_viol) ?strict
    ?eqs ?ineqs ?eqs' ?optis ?suboptis ?eqn ?ineqn ?cnj ?cnj'
    ~cmp_v ~cmp_w uni_v =
  let res, _, _, implicits, _ =
    solve_get_eqn ~use_quants ?strict
      ?eqs ?ineqs ?eqs' ?optis ?suboptis ?eqn ?ineqn ?cnj ?cnj'
      ~cmp_v ~cmp_w uni_v in
  (*[* if implicits <> []
  then Format.printf "NumS.main-solve: implicits=@ %a@\n%!"
      pr_ineqn implicits; *]*)
  res

let fvs_w (vars, _, _) = vars_of_list (List.map fst vars)
let fvs_2w (w1, w2) = VarSet.union (fvs_w w1) (fvs_w w2)
let fvs_w_atom = function
  | Eq_w w
  | Leq_w w -> fvs_w w
  | Opti_w (w1, w2)
  | Subopti_w (w1, w2) -> VarSet.union (fvs_w w1) (fvs_w w2)
let fvs_w_formula = List.fold_left
    (fun acc a -> VarSet.union (fvs_w_atom a) acc) VarSet.empty

type t_br_state = (int ref * int) * (int * Terms.hvsubst) list *
                num_solution * num_solution
type t_validation = (VarSet.t * t_br_state) list
exception Result of w_subst * ineqs * optis * suboptis * t_validation

let debug_dep = ref 0
let no_pass_msg = "Could not solve numeric SCA (algorithm step 5b)"

let implies_case ~cmp_v ~cmp_w uni_v eqs ineqs c_eqn c_ineqn
    c_optis c_suboptis =
  (*[* Format.printf "implies_case: prem=@ %a@\nconcl=@ %a@\n%!"
    pr_ans (eqs, ineqs) pr_eqnineqn (c_eqn, c_ineqn); *]*)
  List.for_all
    (fun w ->
       match subst_w ~cmp_v eqs w with
       | [], cst, _ -> cst =/ !/0
       | w' ->
         (*[* Format.printf "implies: false eq w=%a@ w'=%a@\n%!"
           pr_w w pr_w w'; *]*)
         false)
    c_eqn
  && List.for_all
    (fun (w1, w2) ->
       match subst_w ~cmp_v eqs w1, subst_w ~cmp_v eqs w2 with
       | ([], cst1, _), ([], cst2, _) -> cst1 =/ !/0 || cst2 =/ !/0
       | ([], cst1, _), _ -> cst1 =/ !/0
       | _, ([], cst2, _) -> cst2 =/ !/0
       | w1', w2' ->
         (*[* Format.printf "implies: false eq w1'=%a@ w2'=%a@\n%!"
           pr_w w1' pr_w w2'; *]*)
         false)
    c_optis
  && List.for_all
    (fun w ->
       let ineqn = [mult !/(-1) w] in
       try ignore
             (solve ~strict:true ~eqs ~ineqs ~ineqn ~cmp_v ~cmp_w uni_v);
         (*[* Format.printf "implies: false ineq w=%a@\n%!"
           pr_w w; *]*)        
         false
       with Terms.Contradiction _ -> true)
    c_ineqn
  && List.for_all
    (fun (w1, w2) ->
       try
         let ineqn = [mult !/(-1) w1] in
         ignore
           (solve ~strict:true ~eqs ~ineqs ~ineqn ~cmp_v ~cmp_w uni_v);
         let ineqn = [mult !/(-1) w2] in
         ignore
           (solve ~strict:true ~eqs ~ineqs ~ineqn ~cmp_v ~cmp_w uni_v);
         (*[* Format.printf "implies: false subopti w1=%a w2=%a@\n%!"
           pr_w w1 pr_w w2; *]*)        
         false
       with Terms.Contradiction _ -> true)
    c_suboptis

(* Simultaneous case split on several opti and subopti
   disjunctions. Also include inequalities implied by opti atoms, in
   each choice. *)
let choices ~cmp_v ~intro_cho_ineq optis suboptis =
  (*[* Format.printf "NumS.choices: optis=%d suboptis=%d@\n%!"
    (List.length optis) (List.length suboptis); *]*)
  let disjs =
      List.map
         (fun (w1,w2) -> [Left (w1, w2); Left (w2, w1)]) optis @
      List.map
         (fun (w1,w2) -> [Right (w1, w2); Right (w2, w1)]) suboptis in
  let res = product disjs in
  (*[* Format.printf "NumS.choices: optis/suboptis %d cases@\n%!"
    (List.length res); *]*)  
  List.map (fun cho ->  
      let ch_opt, ch_sub = partition_choice cho in
      concat_map
        (* The last inequality is deducible, but sometimes doesn't get
           reconstructed. *)
          (fun (w1, w2) ->
            if intro_cho_ineq
            then [Eq_w w1; Leq_w w2; Leq_w (diff ~cmp_v w2 w1)]
            else [Eq_w w1; Leq_w w2])
          ch_opt @
        concat_map
          (* As above. *)
          (fun (w1, w2) ->
             if intro_cho_ineq
             then [Leq_w w1; Leq_w (diff ~cmp_v w1 w2)]
             else [Leq_w w1])
          ch_sub)
    res

let implies ~cmp_v ~cmp_w uni_v eqs ineqs optis suboptis c_eqn c_ineqn
    c_optis c_suboptis =
  (*[* Format.printf "NumS.implies: prem=@\n%a@\nconcl=@ %a@\n%a;@ %a@\n%!"
    pr_state (eqs, ineqs, optis, suboptis)
    pr_eqnineqn (c_eqn, c_ineqn) pr_optis c_optis pr_suboptis c_suboptis; *]*)
  if c_optis=[] && c_suboptis=[]
  then
    implies_case ~cmp_v ~cmp_w uni_v eqs ineqs c_eqn c_ineqn
      c_optis c_suboptis
  else List.for_all
      (fun cho ->
         let o_eqn, o_ineqn, _, _ = split_formula cho in
         (* FIXME: do we need try-with here? *)
         try
           let eqs, ineqs, _, _ = solve ~eqs ~ineqs
               ~eqn:o_eqn ~ineqn:o_ineqn ~cmp_v ~cmp_w uni_v in
           implies_case ~cmp_v ~cmp_w uni_v eqs ineqs c_eqn c_ineqn
             c_optis c_suboptis
         with Terms.Contradiction _ -> true)
      (choices ~cmp_v ~intro_cho_ineq:true optis suboptis)

let implies_discard ~cmp_v ~cmp_w uni_v ~bvs (eqs, ineqs, optis, suboptis)
    (c_eqn, c_ineqn, c_optis, c_suboptis) =
  let eqs' =
    if !abd_discard_param_only
    then VarMap.filter (fun v _ -> VarSet.mem v bvs) eqs
    else eqs in
  let ineqs' =
    if !abd_discard_param_only
    then VarMap.filter (fun v _ -> VarSet.mem v bvs) ineqs
    else ineqs in
  let c_eqn' =
    if !abd_discard_param_only
    then List.filter
        (function
          | (v, _)::_, _, _ -> VarSet.mem v bvs
          | _ -> false) c_eqn
    else c_eqn in
  let c_ineqn' =
    if !abd_discard_param_only
    then List.filter
        (function
          | (v, _)::_, _, _ -> VarSet.mem v bvs
          | _ -> false) c_ineqn
    else c_ineqn in
  (* TODO: also for optis, suboptis *)
  if c_eqn' = [] && c_ineqn' = [] then (
    (*[* Format.printf "NumS.implies_discard: empty@\n%!"; *]*)
    (* *)
    (*[*let res =*]*)implies ~cmp_v ~cmp_w uni_v eqs ineqs optis suboptis
      c_eqn c_ineqn c_optis c_suboptis
      (*[* in Format.printf "NumS.implies_discard: implied? %b@\n%!" res;
    res *]*)
    (* *)
    (* false *))
  else
    (*[*let res =*]*)implies ~cmp_v ~cmp_w uni_v eqs' ineqs' optis suboptis
      c_eqn' c_ineqn' c_optis c_suboptis 
      (*[* in Format.printf "NumS.implies_discard: implied? %b@\n%!" res;
    res *]*)

(* A streamlined portion of the [solve] algorithm dealing with
   inequalities. *)
let implies_ineq ~cmp_v ~cmp_w ineqs ineq =
  let project v (vars, cst, loc as lhs) rhs =
    if equal_w ~cmp_v lhs rhs
    then
      (*[* let w = (v, !/(-1))::vars, cst, loc in
        Format.printf "NumS.implies_ineq: fail-- strict ineq=@ %a@\n%!"
        pr_w w; *]*)
      raise (Terms.Contradiction
               (Num_sort, "Failed numeric strict inequality",
                None, loc))
    else diff ~cmp_v lhs rhs in
  let rec proj (ineqs : ineqs) ineqn0 =
    let handle_proj v k vars cst loc ineqn =
      let trans_affine = trans_affine ~cmp_v ineqs in
      let left, right =
        try VarMap.find v ineqs
        with Not_found -> affine_empty, affine_empty in
      let ineq_l, ineq_r, more_ineqn =
        (* Change sides wrt. to variable [v]. *)
        let ohs = mult (!/(-1) // k) (vars, cst, loc) in
        if k >/ !/0
        then
          [], [ohs], affine_map ~is_lhs:true
            (fun lhs -> project v lhs ohs) left
        else
          [ohs], [], affine_map ~is_lhs:false
            (fun rhs -> project v ohs rhs) right in
      let more_ineqn = affine_to_ineqn more_ineqn in
      (*[* Format.printf
        "NumS.impl-project: try v=%s@\nmore_ineqn=@ %a@\n%!"
        (var_str v) pr_ineqn more_ineqn; *]*)  
      let more_ineqn = List.filter
          (function
            | [], cst, _ when cst </ !/0 ->
              false
            | [], cst, loc ->
              (*[* Format.printf "NumS.implies_ineq: fail-- ineq.2=@ %a@\n%!"
                pr_w ([], cst, loc); *]*)
              raise (Terms.Contradiction
                       (Num_sort, "Failed numeric inequality",
                        None, loc))
            | _ -> true)
          more_ineqn in
      let ineqn =
        merge_one_nonredund ~cmp_v ~cmp_w (List.sort cmp_w more_ineqn) ineqn in
      let more_ineqs =
        affine_union ~is_lhs:true
          (trans_affine ~is_lhs:true ineq_l) left,
        affine_union ~is_lhs:false
          (trans_affine ~is_lhs:false ineq_r) right in
      (*[* Format.printf
        "NumS.impl-project: res v=%s@\nmore_ineqn=@ %a@\nineqs_v=@ %a@\n%!"
        (var_str v) pr_ineqn more_ineqn
        pr_ineqs (VarMap.singleton v more_ineqs); *]*)  
      let ineqs = VarMap.add v more_ineqs ineqs in
      proj ineqs ineqn in
    match ineqn0 with
    | [] -> ()
    | ([], cst, _)::ineqn when cst </ !/0 ->
      proj ineqs ineqn
    | ([], cst, loc)::_ ->
      (*[* Format.printf "NumS.implies_ineq: fail-- ineq=@ %a@\n%!"
        pr_w ([], cst, loc); *]*)
      raise (Terms.Contradiction
               (Num_sort,
                "Failed numeric inequality (cst="^
                  Num.string_of_num cst^")",
                None, loc))
    | ((v,k)::vars, cst, loc)::ineqn ->
      handle_proj v k vars cst loc ineqn in
  try proj ineqs [mult !/(-1) ineq];
    (*[* Format.printf "NumS.implies_ineq: false@ ineq=%a@\n%!"
      pr_w ineq; *]*)
    false
  with Terms.Contradiction _ ->
    (*[* Format.printf "NumS.implies_ineq: true@ ineq=%a@\n%!"
      pr_w ineq; *]*)
    true

exception Timeout

let rec taut = function
  | Eq_w (vars, cst, _) -> vars=[] && cst =/ !/0
  | Leq_w (vars, cst, _) -> vars=[] && cst <=/ !/0
  | Opti_w (w1, w2) ->
    taut (Leq_w w1) && taut (Leq_w w2) &&
    (taut (Eq_w w1) || taut (Eq_w w2))
  | Subopti_w (w1, w2) ->
    taut (Leq_w w1) || taut (Leq_w w2)

(* Equality-like atoms cannot be weakened using transitivity with an
   inequality while remaining in the same class of atoms. *)
let iseq_w_atom = function
  | Eq_w _ -> true
  | Leq_w _ -> false
  | Opti_w _ -> false
  | Subopti_w _ -> false

let split_w_atom = function
  | Eq_w w -> [w], [], [], []
  | Leq_w w -> [], [w], [], []
  | Opti_w w12 -> [], [], [w12], []
  | Subopti_w w12 -> [], [], [], [w12]

let trans_w_atom ~cmp_v tr = function
  | Eq_w w -> Eq_w (sum_w ~cmp_v tr w)
  | Leq_w w -> Leq_w (sum_w ~cmp_v tr w)
  | Opti_w (w1, w2) -> Opti_w (sum_w ~cmp_v tr w1, sum_w ~cmp_v tr w2)
  | Subopti_w (w1, w2) -> Subopti_w (sum_w ~cmp_v tr w1, sum_w ~cmp_v tr w2)

(* Introduce indexes for missing variables. E.g. inupt: [[a] <= b <=
   [c]], output [[] <= a <= [b]; [a] <= b <= [c]; [b] <= c <= []]. *)
let complete_ineqs ~cmp_v ineqs =
  let ineqn = unsolve ineqs in
  let res = Hashtbl.create (VarMap.cardinal ineqs) in
  VarMap.iter (fun v v_ineqs -> Hashtbl.add res v v_ineqs) ineqs;
  List.iter
    (fun (vars, cst, lc) ->
       List.iter
         (fun ((v, coef), vars1) ->
            let c = mult (!/(-1) // coef) (vars1, cst, lc) in
            let lhs, rhs =
              try Hashtbl.find res v
              with Not_found -> affine_empty, affine_empty in
            if coef </ !/0 then
              Hashtbl.replace res v (affine_add ~is_lhs:true c lhs, rhs)
            else
              Hashtbl.replace res v (lhs, affine_add ~is_lhs:false c rhs))
         (one_out vars))
    ineqn;
  res

let revert_uni ~cmp_v ~cmp_w ~uni_v ~bvs eqn =
  let cmp_v v1 v2 =
    let c1 = uni_v v1 && not (VarSet.mem v1 bvs)
    and c2 = uni_v v2 && not (VarSet.mem v2 bvs) in
    if c1 && c2 then cmp_v v1 v2
    else if c1 then -1
    else if c2 then 1
    else cmp_v v1 v2 in
  let eqn = List.map (norm_w ~cmp_v) eqn in
  let rev_sb, _, _, _ =
    (* Do not use quantifiers. *)
    solve ~eqn ~cmp_v ~cmp_w uni_v in
  VarMap.filter (fun v (vars, _, _) ->
      uni_v v && not (VarSet.mem v bvs) &&
      not (List.exists (fun (v', _) ->
          uni_v v' && not (VarSet.mem v' bvs)) vars)) rev_sb

let revert_cst cmp_v uni_v eqn =
  let c_eqn, eqn = partition_map
      (function
        | [v, coef], cst, lc -> Left (cst // coef, (v, lc))
        | eq -> Right eq)
      eqn in
  let c_eqn =
    collect ~cmp_k:Num.compare_num c_eqn in
  let leq (v1, _) (v2, _) = not (cmp_v v1 v2 = Left_of) || uni_v v1 in
  let c_eqn =
    concat_map
      (fun (cst, vars) ->
         let ov, olc = maximum ~leq vars in
         let o = [ov, !/1] in
         map_some
           (fun (cv, lc) ->
              if cv=ov then None else Some ((cv, !/(-1))::o, !/0, lc))
           vars
         @ [(o, cst, olc)]) c_eqn in
  c_eqn @ eqn

exception Omit_trans

(* TODO: perhaps include other branches in finding which variables are
   bounded by a constant. [d_ineqn] and [d_ineqs] represent the same
   inequalities, but [d_ineqs] is normalized and completed
   wrt. transitivity. *)
let abd_cands ~cmp_v ~qcmp_v ~cmp_w ~uni_v ~orig_ren ~b_of_v ~upward_of
    ~bvs ~nonparam_vars ~discard_ineqs
    ~eqs_acc0 ~ineqs_acc0 ~optis_acc ~suboptis_acc
    ~b_ineqs ~bh_ineqs ~d_ineqn ~d_ineqs
    (vars, cst, lc as w) =
  (*[* Format.printf
    "NumS.abd_cands: w=%a@ bvs=%a@\nnonparam_vars=%a@\n\
     d_ineqs=%a@ d_ineqn=%a@\nbh_ineqs=@ %a@\n%!"
    pr_w w pr_vars bvs pr_vars nonparam_vars
    pr_hineqs d_ineqs pr_ineqn d_ineqn
    pr_hineqs bh_ineqs; *]*)
  let cands_vs =
    concat_map
      (fun ((v, coef), vars1) ->
         (*[* Format.printf
           "NumS.abd_cands: trying v=%s@\n%!" (var_str v); *]*)
         try
           let lhs, rhs = Hashtbl.find d_ineqs v in
           (* No change of sign for c because it stays on the same side. *)
           let c = mult (!/1 // abs_num coef) (vars1, cst, lc) in
           let ohs = if coef </ !/0 then lhs else rhs in
           (*[* Format.printf "NumS.abd_cands: c=%a@\n%!"
             pr_w c; *]*)
           List.map (fun d ->
               let from_d =
                 if !concl_abd_penalty > 0 then
                   (* TODO: this can be optimized: e.g. compute the
                      d_ineqn abductions directly. *)
                   let v_w = [v, !/1], !/0, dummy_loc in
                   let d_w =
                     if coef </ !/0 then diff ~cmp_v d v_w
                     else  diff ~cmp_v v_w d in
                   List.exists (equal_w ~cmp_v d_w) d_ineqn
                 else true (* here we don't care *) in
               (* Change of sign for d only when it moves to right side. *)
               let res =
                 if coef </ !/0
                 then Some from_d, norm_by_gcd (diff ~cmp_v c d)
                 else Some from_d, norm_by_gcd (sum_w ~cmp_v c d) in
               (*[* Format.printf
                 "NumS.abd_cands: from_d=%b@ res=%a@\n%!"
                 from_d pr_w (snd res); *]*)
               res)
             (affine_to_ineqn ohs)
         with Not_found -> [])
      (one_out vars) in
  let cands_cst =
    if cst =/ !/0 then []
    else map_some
        (fun (vars2, cst2, lc2) ->
           let s = sign_num cst in
           if sign_num cst2 <> s then None
           else
             let c = mult (!/(-1) // cst) (vars, !/0, lc) in
             let d = mult (!/(-1) // cst2) (vars2, !/0, lc2) in
             (*[* Format.printf
               "NumS.abd_cands: trying s=%d@ c=%a;@ d=%a;@ res=%a@\n%!"
               s pr_w c pr_w d pr_w (if s > 0 then diff ~cmp_v d c
                                     else diff ~cmp_v c d); *]*)
             if s > 0
             then Some (Some true, norm_by_gcd (diff ~cmp_v d c))
             else Some (Some true, norm_by_gcd (diff ~cmp_v c d)))
        d_ineqn in
  let cands = List.filter
      (no_scope_viol ~cmp_v:qcmp_v ~upward_of ~bvs % snd)
      (* Remember whether [w] is the source (None) or an abduced inequality. *)
      ((None, w) :: cands_cst @ cands_vs) in
  (*[* Format.printf "abd_cands: filtered@ %a@\n%!" pr_ineqn
    (List.map snd cands); *]*)
  let less (x_ineqs, (_, x)) (y_ineqs, (_, y)) =
    (*[* let res = *]*)
    implies_ineq ~cmp_v ~cmp_w y_ineqs x &&
    not (implies_ineq ~cmp_v ~cmp_w x_ineqs y)
    (*[* in Format.printf "less: x=%a@ y=%a@ res=%b@\n%!"
      pr_w x pr_w y res;
      res *]*) in
  let minimal_cands =
    if !more_general
    then
      let cands = List.map
          (fun (_, w as sw) ->
             let (_, ineqs, _, _), _, _, _, _ =
               solve_get_eqn ~use_quants:Ignore_viol
                 ~ineqs:b_ineqs ~ineqn:[w] ~cmp_v ~cmp_w uni_v in
             ineqs, sw) cands in
      List.map snd (minimal ~less cands)
    else [] in
  let prem_vars = vars_of_map fvs_w d_ineqn in
  let down_v, skip_uplevel =
    match vars with
    | [v, _; v2, _] -> v, upward_of v2 v &&
                          (not !only_off_by_1 || cst =/ !/1)
    | (v, _)::_ -> v, false
    | _ -> assert false in
  (*[* if !more_general
    then Format.printf "abd_cands: minimal@ %a@\n%!"
      pr_ineqn (List.map snd minimal_cands); *]*)
  (* Promote candidates introducing constraints on unconstrained
     variables. Otherwise, penalize for size. *)
  let w_value is_orig orig_w (vars, cst, lc as w) =
    let cst_value =
      if cst =/ !/0 then 0
      else ~- !affine_penalty -
             (if abs_num cst </ !/ !affine_threshold then 0
              else !affine_thresh_penalty) in
    let discard_value =
      if WSet.mem w discard_ineqs then ~- !discard_penalty else 0 in
    let minimal =
      (* FIXME: not sure if physical comparison works. *)
      if List.exists (fun (_, w') -> w' == orig_w) minimal_cands
      then
        if !more_general && equal_w ~cmp_v orig_w w
        then !general_reward else 0
      else 0 in
    let locality =
      (* Do not reward locality multiple times. *)
      if not is_orig then 0
      else
        match vars with
        | [] -> 0
        | (v, _)::tl ->
          if List.for_all (fun (v2, _) -> qcmp_v v v2 = Same_params) tl
          then !reward_locality
          else
            let v_orig =
              try Hashtbl.find orig_ren v with Not_found -> v in
            (if List.exists
                (fun (v2, _) ->
                   upward_of v2 v && List.exists
                     (fun (v3, _) -> upward_of v3 v2) tl) tl
             then ~- !multi_levels_penalty
             else 0) +
              (if List.exists
                  (* Here we use the "original" of v *)
                  (fun (v2, _) ->
                     (*[*
                       let b1 = try b_of_v v_orig
                       with Not_found -> v_orig in
                       let b2 = try b_of_v v2 with Not_found -> v2 in
                       Format.printf
                       "w_val_cmp: v=%s o=%s p=%s -- v2=%s p2=%s is upw=%b \
                        cmp(v2,v)=%s@\n%!"
                       (var_str v) (var_str v_orig) (var_str b1)
                       (var_str v2) (var_str b2)
                       (upward_of v2 v_orig)
                       (var_scope_str (qcmp_v v2 v_orig)); *]*)
                     not (upward_of v2 v_orig) &&
                     qcmp_v v2 v_orig <> Same_params) tl
               then ~- !escaping_var_penalty
               else 0) +
              !locality_vars_penalty *
                List.fold_left
                  (fun acc (v2, _) ->
                     if qcmp_v v v2 <> Same_params then acc - 1
                     else acc)
                  1 tl +
              !upper_bound_outer_penalty *
                List.fold_left
                  (fun acc (v2, k2) ->
                     if upward_of v2 v_orig && k2 >/ !/0 then acc - 1
                     else acc)
                  0 tl +
              !nonparam_vars_penalty *
                List.fold_left
                  (fun acc (v2, _) ->
                     if VarSet.mem v2 nonparam_vars then acc - 1
                     else acc)
                  (* We exclude the head variable from contributing. *)
                  0 tl in
    let bound =
      match vars with
      | [v, k] ->
        (* A single variable bounded by a constant -- deprioritize
           if the variable is already bounded. *)
        let bounded =
          try
            let lhs, rhs = Hashtbl.find bh_ineqs v in
            k >/ !/0 && CombMap.exists (fun vars _ -> vars=[]) lhs ||
            k </ !/0 && CombMap.exists (fun vars _ -> vars=[]) rhs
          with Not_found -> false in
        if bounded then ~- !discourage_already_bounded
        else !encourage_not_yet_bounded
      | (v, k)::vars1 ->
        (* Check whether the inequality is an implicit equality. *)
        let w' = vars1, cst, lc in
        let bounded =
          try
            let lhs, rhs = Hashtbl.find bh_ineqs v in
            k >/ !/0 &&
            affine_exists (equal_w ~cmp_v w') lhs ||
            k </ !/0 &&
            affine_exists (equal_w ~cmp_v w') rhs
          with Not_found -> false in
        if bounded then ~- !discourage_equations_1 else 0
      | _ -> 0 in
    let upper_bound =
      if List.for_all (fun (_, k) -> k >/ !/0) vars
      then ~- !discourage_upper_bound else 0 in
    let complexity = w_complexity1 bvs vars in
    let constraining =
      List.fold_left
        (fun acc (v, k) ->
           try
             let lhs, rhs = Hashtbl.find bh_ineqs v in
             if VarSet.mem v bvs &&
                (k >/ !/0 && CombMap.is_empty rhs ||
                 k </ !/0 && CombMap.is_empty lhs)
             then acc + !reward_constrn
             else acc
           with Not_found -> acc)
        0 vars in
    (*[* Format.printf
      "w_value:@ is_orig=%b@ orig=%a@ w=%a;@ cst_val=%i@ \
       discard_val=%i@ locality=%i@ \
       bound=%i@ upper_bound=%i@ complexity=%i@ constraining=%i@ \
       minimal=%i@\n%!"
      is_orig pr_w orig_w pr_w w cst_value
      discard_value locality bound upper_bound
      complexity constraining minimal; *]*)
    cst_value + discard_value + locality + bound + upper_bound +
      complexity + constraining + minimal in
  let cands =
    map_some
      (fun (prem_abduced, (vars, cst, _ as w)) ->
         try
           (* This should be filtered out by verification! But
              anyway, checking here is faster. *)
           if (* contradicting premise *)
             List.exists
               (fun d_w -> contr_w false (sum_w ~cmp_v w d_w)) d_ineqn
           then raise Omit_trans;
           (* [new_eqn, new_ineqn] are used to determine the variables
              contributed to the answer and evaluate the candidate. *)
           let _, new_eqn, new_ineqn, _, new_viol as acc =
             solve_get_eqn ~use_quants:(Store_viol bvs)
               ~eqs:eqs_acc0 ~ineqs:ineqs_acc0
               ~optis:optis_acc ~suboptis:suboptis_acc
               ~ineqn:[w] ~cmp_v ~cmp_w uni_v in
           let score_ineqn =
             concat_map
               (function
                 | Leq_w w -> if List.memq w new_ineqn then [] else [w]
                 | Eq_w w -> [w; mult !/(-1) w]
                 | Opti_w (w1, w2) | Subopti_w (w1, w2)-> [w1; w2])
               new_viol @
               new_eqn @ List.map (mult !/(-1)) new_eqn @
               new_ineqn in
           (* The last one above is equal to [w], list reversed below. *)
           let score_ineqn = List.fold_left
               (fun acc w ->
                  if taut_w false w || List.exists (equal_w ~cmp_v w) acc
                  then acc else w::acc)
               [] score_ineqn in
           let scores =
             match score_ineqn with
             | hd::tl ->
               w_value true w hd :: List.map (w_value false w) tl
             | [] -> assert false in
           let i2f = float_of_int and f2i = int_of_float in
           let special_bonus () =
             if prem_abduced = None &&
                (not !only_off_by_1 || cst =/ !/1) &&
                List.tl score_ineqn = [] then
               let nonlocal_pair =
                 match vars with
                 | (v, _)::(v2, _)::[] -> upward_of v2 v
                 | _ -> false in
               if nonlocal_pair then !special_source_bonus else 0
             else 0 in
           let implied_ineqn_correction =
             !implied_ineqn_compensation *
               (List.length score_ineqn - 1) in
           let uplevel_score =
             if !prefer_bound_to_outer && skip_uplevel
             then match vars with
               | [v, _; _] ->
                 (*[* Format.printf "uplevel: down_v=%s v=%s up=%b@\n%!"
                   (var_str down_v) (var_str v) (upward_of v down_v); *]*)
                 if upward_of v down_v then ~- !uplevel_penalty else 0
               | [] -> ~- !uplevel_penalty
               (* Three variables or more: interestingness bonus. *)
               | _ -> 0
             else 0 in
           let implied_by_prem_score =
             if List.exists
                 (fun d_w -> taut_w false (diff ~cmp_v w d_w)) d_ineqn
             then ~- !implied_by_prem_penalty else 0 in
           let implicit_eq_score =
             if List.exists
                 (fun d_w -> taut_w true (sum_w ~cmp_v w d_w)) d_ineqn
             then ~- !implicit_eq_penalty else 0 in
           let concl_abd_score =
             if prem_abduced = Some false then ~- !concl_abd_penalty
             else 0 in
           let no_prem_vars_score =
             if !no_prem_penalty_derived_only && prem_abduced = None
             then 0
             else if
               List.exists (fun (v, _) -> VarSet.mem v prem_vars) vars
             then 0 else ~- !no_prem_var_penalty in
           let bound_vs_local =
             if !prefer_bound_to_local then special_bonus () else 0 in
           let score =
             concl_abd_score + bound_vs_local +
               uplevel_score + implied_by_prem_score +
               implicit_eq_score + no_prem_vars_score +
               (if prem_abduced = None then !abduct_source_bonus else 0) +
               (if new_eqn = [] then 0 else ~- !discourage_equations_2) +
               (if !abd_scoring = `Sum then List.fold_left (+) 0 scores
                else if !abd_scoring = `Min then maximum ~leq:(>=) scores
                else if !abd_scoring = `Max then maximum ~leq:(<=) scores
                else if !abd_scoring = `Avg then
                  f2i (i2f (List.fold_left (+) 0 scores) /.
                         i2f (List.length new_ineqn))
                else assert false)
             + implied_ineqn_correction in
           (*[* Format.printf
             "abd_cands:@ w=%a@ source=%b prem_abduced=%b@ new_eqn=%a@ \
              new_ineqn=%a@\nconcl_abd_score=%i@ \
              no_prem_vars_score=%i@ \
              implied correction=%i@ uplevel score=%i@ \
              bound vs local=%d@ implied ineq penalty=%d@ \
              implicit eq penalty=%d@\n\
              total score=%i@\n%!"
             pr_w w (prem_abduced = None) (prem_abduced = Some true)
             pr_eqn new_eqn pr_ineqn new_ineqn concl_abd_score
             no_prem_vars_score
             implied_ineqn_correction uplevel_score
             bound_vs_local implied_by_prem_score implicit_eq_score
             score; *]*)
           Some (score, (acc, w))
         with
         | Terms.Contradiction _ (*[* as e *]*)->
           (*[* Format.printf
             "abd_cands: skipping@ w=%a@\nreason=@ %a@\n%!"
             pr_w w Terms.pr_exception e; *]*)
           None
         | Omit_trans ->
           (*[* Format.printf
             "abd_cands:@ w=%a contradicts premise@\n%!"
             pr_w w; *]*)
           None)
      cands in
  (* TODO: optimize, do not score if there is a tautology *)
  try [snd (List.find (fun (_, (_, w)) -> taut_w false w) cands)]
  with Not_found ->
    List.map snd
      (List.sort (fun (x, _) (y, _) -> compare y x) cands)

let rename_w sb (vars, cst, lc) =
  List.map
    (fun (v, k as sv) ->
       try VarMap.find v sb, k
       with Not_found -> sv)
    vars,
  cst, lc

let rename_w_atom sb = function
  | Eq_w w -> Eq_w (rename_w sb w)
  | Leq_w w -> Leq_w (rename_w sb w)
  | Opti_w (w1, w2) -> Opti_w (rename_w sb w1, rename_w sb w2)
  | Subopti_w (w1, w2) -> Subopti_w (rename_w sb w1, rename_w sb w2)

let local_split ~cmp_v ~bvs ~xbvs eqn ineqn optis suboptis =
  let leq x y =
    let c = cmp_v x y in
    if c = Same_quant then VarSet.mem x bvs else c <> Right_of in
  let pick_var vs =
    let res =
      maximum ~leq (VarSet.elements vs) in
    (*[* Format.printf "pick_var: vs=%a; res=%s@\n%!" pr_vars vs
      (var_str res); *]*)
    res in
  let eqn = List.map
      (fun w -> pick_var (fvs_w w), w) eqn
  and ineqn = List.map
      (fun w -> pick_var (fvs_w w), w) ineqn
  and optis = List.map
      (fun o -> pick_var (fvs_2w o), o) optis
  and suboptis = List.map
      (fun o -> pick_var (fvs_2w o), o) suboptis in
  let split xvs = map_some
      (fun (v, a) -> if VarSet.mem v xvs then Some a else None) in
  List.map
    (fun (x, xvs) ->
       let x_eqn = split xvs eqn in
       let x_ineqn = split xvs ineqn in
       (*[* Format.printf
         "local_split: x=%d; xvs=%a@\nx_eqn=%a@\nx_ineqn=%a@\n%!"
       x pr_vars xvs pr_eqn x_eqn pr_ineqn x_ineqn; *]*)
       x, (x_eqn, x_ineqn, split xvs optis, split xvs suboptis))
    xbvs

let subst_chi chi_sb pos_chi =
  List.fold_left
    (fun (acc_eqn, acc_ineqn, acc_optis, acc_suboptis)
      (i, renaming) ->
      let (eqn, ineqn, optis, suboptis) =
        try List.assoc i chi_sb
        with Not_found -> [], [], [], [] in
      let eqn = List.map (rename_w renaming) eqn
      and ineqn = List.map (rename_w renaming) ineqn
      and optis = List.map
          (fun (w1, w2) -> rename_w renaming w1, rename_w renaming w2)
          optis
      and suboptis = List.map
          (fun (w1, w2) -> rename_w renaming w1, rename_w renaming w2)
          suboptis in
      eqn @ acc_eqn, ineqn @ acc_ineqn,
      optis @ acc_optis, suboptis @ acc_suboptis)
    ([], [], [], []) pos_chi

let subst_chi_incr ~cmp_v ~bvs ~xbvs pos_chi a =
  let leq x y =
    (* let c = cmp_v x y in
       if c = Same_quant then VarSet.mem x bvs else c <> Right_of *)
    cmp_v x y >= 0 in
  let v = maximum ~leq (VarSet.elements (fvs_w_atom a)) in
  (*[* Format.printf
    "subst_chi: v=%s pos_chi=%a@ xbvs=@ %a@\n%!" (var_str v)
    pr_ints (ints_of_list (List.map fst pos_chi))
    (pr_sep_list
       "| " (fun ppf (i, vs) -> Format.fprintf ppf "%d->%a" i pr_vars vs))
    xbvs; *]*)
  List.fold_left
    (fun acc (i, renaming) ->
       if List.exists (fun (j, xvs) -> i=j && VarSet.mem v xvs) xbvs
       then rename_w_atom renaming a::acc
       else acc)
    [] pos_chi

let validate_incr ~cmp_v ~cmp_w uni_v ~bvs ~xbvs validation a =
  let added_vs = fvs_w_atom a in
  (*[* Format.printf
    "NumS.abd-validate-incr:@ a=%a@\n%!" pr_w_atom a; *]*)
  (* TODO: introduce use-site substitutions *)
  try
    let validation =
      List.map
        (* We do not use [br_vs], to keep all branches updated with
           the whole partial answer. *)
        (fun (br_vs, ((brs_r, brs_n),
                      chi_pos, (d_eqs, d_ineqs, d_optis, d_suboptis),
                      (dc_eqs, dc_ineqs, dc_optis, dc_suboptis)) as br) ->
          let prem_state =
            (*[* Format.printf
              "NumS.abd-validate-incr: brs_r=%d; brs_n=%d\
               @\nv-d_eqs=%a@\nv-d_ineqs=%a\
               @\nv-d_optis=%a@\nv-d_suboptis=%a@\n%!" !brs_r brs_n
              pr_w_subst d_eqs pr_ineqs d_ineqs
              pr_optis d_optis pr_suboptis d_suboptis; *]*)
            try
              Right (solve ~eqs:d_eqs ~ineqs:d_ineqs
                       ~optis:d_optis ~suboptis:d_suboptis
                       ~cnj':[a]
                       ~cmp_v ~cmp_w uni_v)
            with Terms.Contradiction _ as e -> Left e in
          match prem_state with
          | Right (d_eqs, d_ineqs, d_optis, d_suboptis) ->
            (*[* Format.printf
              "v-d_eqs'=%a@\nv-d_ineqs'=%a@\n\
               v-d_optis'=%a@\nv-d_suboptis'=%a@\n%!"
              pr_w_subst d_eqs pr_ineqs d_ineqs pr_optis d_optis
              pr_suboptis d_suboptis; *]*)
            let u = subst_chi_incr ~cmp_v ~bvs ~xbvs chi_pos a in
            (*[* Format.printf
              "v-dc_eqs=%a@\nv-dc_ineqs=%a@\n\
               v-dc_optis=%a@\nv-dc_suboptis=%a@\n%!"
              pr_w_subst dc_eqs pr_ineqs dc_ineqs pr_optis dc_optis
              pr_suboptis dc_suboptis; *]*)
            (*[* Format.printf
              "NumS.abd-validate-incr: trying u=%a@\n%!"
              pr_w_formula u; *]*)
            let dc_eqs, dc_ineqs, dc_optis, dc_suboptis =
              solve ~eqs:dc_eqs ~ineqs:dc_ineqs
                ~optis:dc_optis ~suboptis:dc_suboptis
                ~cnj':(a::u)
                ~cmp_v ~cmp_w uni_v in
            (*[* Format.printf
              "v-dc_eqs'=%a@\nv-dc_ineqs'=%a@\n\
               v-dc_optis'=%a@\nv-dc_suboptis'=%a@\n%!"
              pr_w_subst dc_eqs pr_ineqs dc_ineqs pr_optis dc_optis
              pr_suboptis dc_suboptis; *]*)
            (VarSet.union added_vs br_vs,
             ((brs_r, brs_n),
              chi_pos, (d_eqs, d_ineqs, d_optis, d_suboptis),
              (dc_eqs, dc_ineqs, dc_optis, dc_suboptis)))
          | Left e ->
            (*[* Format.printf
              "NumS.abd-validate-incr: dead premise, brs_r=%d nodead=%b@\n%!"
              !brs_r !nodeadcode; *]*)
            if !nodeadcode then (
              decr brs_r;
              if !brs_r <= 0 then (deadcode_flag := true; raise e)
              else br)
            else br)
        validation in
    (*[* Format.printf "NumS.abd-validate-incr: passed@\n%!"; *]*)
    List.iter (fun (_, ((brs_r, brs_n), _, _, _)) -> brs_r := brs_n)
      validation;
    validation
  with e ->
    List.iter (fun (_, ((brs_r, brs_n), _, _, _)) -> brs_r := brs_n)
      validation;
    raise e

(* We currently do not measure satisfiability of negative constraints. *)
(* TODO: guess equalities between parameters. *)
let abd_simple ~qcmp_v ~cmp_w
    ~orig_ren ~b_of_v ~upward_of cmp_v uni_v
    ~bvs ~xbvs ~nonparam_vars ~discard ~validation ~validate
    ~neg_validate:_
    skip (eqs_i, ineqs_i, optis_i, suboptis_i)
    (opti_lhs, (d_eqn, d_ineqn), (c_eqn, c_ineqn, c_optis, c_suboptis)) =
  let skip = ref skip in
  let counter = ref 0 in
  (* 1 *)
  let d_eqn' = List.map (subst_w ~cmp_v eqs_i) d_eqn
  and c_eqn' = List.map (subst_w ~cmp_v eqs_i) c_eqn in
  let d_ineqn' = List.map (subst_w ~cmp_v eqs_i) d_ineqn
  and c_ineqn' = List.map (subst_w ~cmp_v eqs_i) c_ineqn
  and c_optis' = List.map (subst_2w ~cmp_v eqs_i) c_optis
  and c_suboptis' = List.map (subst_2w ~cmp_v eqs_i) c_suboptis in
  try
    (* Extract more equations implied by premise and earlier answer. *)
    (* A contradiction in premise here means the answer so far
       conflicts with a live-code branch, should be discarded. *)
    let (d_eqs0, d_ineqs0, _, _), _, _, d_implicits, _ =
      (* TODO: could we speed up abduction by using Store_viol? *)
      solve_get_eqn ~use_quants:Ignore_viol ~eqs:eqs_i ~eqs':VarMap.empty
        ~ineqs:ineqs_i ~eqn:d_eqn' ~ineqn:d_ineqn'
        ~optis:[] ~suboptis:[] ~cnj:[] ~cmp_v ~cmp_w uni_v in
    (*[* Format.printf
      "NumS.abd_simple:@ d_ineqn'=@ %a@\nd_ineqs0=@ %a@\nd_implicits=@ %a@\n%!"
      pr_ineqn d_ineqn' pr_ineqs d_ineqs0 pr_eqn d_implicits;
    *]*)
    let d_ineqs = complete_ineqs ~cmp_v d_ineqs0 in
    let d_eqn' = d_implicits @ d_eqn' in
    (* 1a *)
    let zero = [], !/0, dummy_loc in
    let rev_sb = revert_uni ~cmp_v ~cmp_w ~uni_v ~bvs d_eqn' in
    (*[* Format.printf "NumS.abd_simple: rev_sb=@ %a@\n%!"
      pr_w_subst rev_sb; *]*)
    let c_eqn0 = List.map
        (subst_if_qv ~uni_v ~bvs ~cmp_v rev_sb) c_eqn'
    and c_ineqn0 = List.map
        (* FIXME: unnecessary? We do elimination later, before solving. *)
        (subst_if_qv ~uni_v ~bvs ~cmp_v rev_sb) c_ineqn'
    and c_optis0 = List.map
        (subst_if_qv_2w ~uni_v ~bvs ~cmp_v rev_sb) c_optis'
    and c_suboptis0 = List.map
        (subst_if_qv_2w ~uni_v ~bvs ~cmp_v rev_sb) c_suboptis' in
    (*[* Format.printf
      "NumS.abd_simple:@ c_eqn0=@ %a@\nc_ineqn0=@ %a@\n%!"
      pr_eqn c_eqn0 pr_ineqn c_ineqn0;
    *]*)
    (* Test if there is a fully maximal answer at all. *)
    let b_eqs, b_ineqs, b_optis, b_suboptis =
      solve ~eqs:eqs_i ~ineqs:ineqs_i
        ~eqn:(c_eqn0 @ d_eqn) ~ineqn:(c_ineqn0 @ d_ineqn)
        ~optis:(optis_i @ c_optis0)
        ~suboptis:(suboptis_i @ c_suboptis0)
        ~cmp_v ~cmp_w uni_v in
    (*[* Format.printf
      "NumS.abd_simple: initial test@\nb_eqs=@ %a@\nb_ineqs=@ %a@\n%!"
      pr_w_subst b_eqs pr_ineqs b_ineqs;
    *]*)

    if not
        (implies ~cmp_v ~cmp_w uni_v b_eqs b_ineqs b_optis b_suboptis
           c_eqn c_ineqn c_optis c_suboptis)
    then (
      (*[* Format.printf
        "NumS.abd_simple: no fully maximal answer for@\nc_eqn0=%a@\n\
         c_ineqn0=%a@\nc_optis0=%a@\nc_suboptis0=%a@\n%!"
        pr_eqn c_eqn0 pr_ineqn c_ineqn0 pr_optis c_optis0
        pr_suboptis c_suboptis0;
      *]*)
      raise
        (Terms.Contradiction (Num_sort,
                              "No fully maximal abduction answer",
                              None, dummy_loc)));
    let prune (vars, _, _ as w) =
      if List.length vars < !abd_prune_at then Some w else None in
    let add_tr ks_eq eq_trs (vars,_,_ as a) =
      if vars=[] then eq_trs
      else (
        (* TODO: the transformations repeat, optimize *)
        (*[* Format.printf "add_eq/ineq_tr: a=%a@\n%!" pr_w a; *]*)
        let kas = lazmap (fun k -> mult k a) ks_eq in
        let add_kas tr =
          lazmap_some (fun ka -> prune (sum_w ~cmp_v ka tr)) kas in
        lazconcat_map add_kas eq_trs) in
    (*[* Format.printf
      "NumS.abd_simple: 2.@\neqs_i=@ %a@\nineqs_i=@ %a@\noptis_i=@ \
       %a@\nsuboptis_i=@ %a@\nd_eqn=@ %a@ d_ineqn=@ %a@\nc_eqn=@ \
       %a@\nc_ineqn=@ %a@\nd_ineqn'=@ %a@\nc_ineqn'=@ %a@\nd_eqn'=@ \
       %a@\n%!"
      pr_w_subst eqs_i pr_ineqs ineqs_i pr_optis optis_i pr_suboptis
      suboptis_i pr_eqn d_eqn pr_ineqn d_ineqn
      pr_eqn c_eqn pr_ineqn c_ineqn pr_ineqn d_ineqn'
      pr_ineqn c_ineqn' pr_eqn d_eqn';
    List.iter
      (fun (r_eqn, r_ineqn, r_optin, r_suboptin) ->
         Format.printf "discard:@ eqn:@ %a@ ineqn:@ %a" pr_eqn r_eqn
           pr_ineqn r_ineqn) discard;
    *]*)
    (* 3 *)
    let c_eqn0 =
      if !revert_csts then revert_cst qcmp_v uni_v c_eqn0 else c_eqn0 in
    (*[* Format.printf
      "NumS.abd_simple: reverted c_eqn0=@ %a@\n%!"
      pr_eqn c_eqn0; *]*)
    (* 4 *)
    let rec loop validation eq_trs
        eqs_acc0 ineqs_acc0 optis_acc suboptis_acc
        c0eqn c0ineqn c0optis c0suboptis =
      (*[* let ddepth = incr debug_dep; !debug_dep in *]*)
      incr counter; if !counter > !abd_timeout_count then raise Timeout;
      let a, c0eqn, c0ineqn, c0optis, c0suboptis =
        match c0eqn, c0ineqn, c0optis, c0suboptis with
        | a::c0eqn, c0ineqn, c0optis, c0suboptis ->
          Eq_w a, c0eqn, c0ineqn, c0optis, c0suboptis
        | [], a::c0ineqn, c0optis, c0suboptis ->
          Leq_w a, [], c0ineqn, c0optis, c0suboptis
        | [], [], a::c0optis, c0suboptis ->
          Opti_w a, [], [], c0optis, c0suboptis
        | [], [], [], a::c0suboptis ->
          Subopti_w a, [], [], [], c0suboptis
        | [], [], [], [] ->
          if (!skip > 0 && (decr skip; true))
          || List.exists
               (implies_discard ~cmp_v ~cmp_w uni_v ~bvs
                  (eqs_acc0, ineqs_acc0, optis_acc, suboptis_acc))
               (discard : (w list * w list * optis * suboptis) list)
          then
            (raise
               (Terms.Contradiction
                  (Num_sort,
                   "Numeric SCA: skipping", None, dummy_loc)))
          else raise
              (Result (eqs_acc0, ineqs_acc0, optis_acc, suboptis_acc,
                       validation)) in
      (* 5 *)
      (* We get a substitution in [~eqs:(eqs_acc0 @ c0eqs)]
         because initial equations [c0eqs] are a solved form with
         [eqs_i], and all transformations are through equations
         absent from [eqs_acc0]. *)
      (*[* Format.printf
        "NumS.abd_simple: [%d] 5.@ a=%a @\nd_eqn=@ %a@\nineqn=@ %a@\n%!"
        ddepth pr_w_atom a pr_eqn d_eqn pr_ineqn (c0ineqn @ d_ineqn);
      *]*)
      (*[* Format.printf
        "NumS.abd_simple: loop-validation-prems:@\n%a@\n%!"
        (pr_line_list "| "
           (fun ppf (_, (_, _, s, _)) -> pr_state ppf s)) validation; *]*)
      let b_eqs, b_ineqs, b_optis, b_suboptis =
        solve ~eqs:eqs_acc0 ~ineqs:ineqs_acc0
          ~eqn:(c0eqn @ d_eqn) ~ineqn:(c0ineqn @ d_ineqn)
          ~optis:(optis_acc @ c0optis)
          ~suboptis:(suboptis_acc @ c0suboptis)
          ~cmp_v ~cmp_w uni_v in
      (*[* Format.printf
        "NumS.abd_simple: [%d] 5.@\nb_eqs=@ %a@\nb_ineqs=@ %a@\n%!"
        ddepth pr_w_subst b_eqs pr_ineqs b_ineqs;
      *]*)
      let discard_ineqs = wset_of_map
          (fun (_, ineqn, _, suboptis) ->
             wset_of_list
               (List.map fst suboptis @ List.map snd suboptis @ ineqn))
          discard in

      if taut a
      || implies ~cmp_v ~cmp_w uni_v b_eqs b_ineqs b_optis b_suboptis
           c_eqn c_ineqn c_optis c_suboptis
      then (
        (* 6 *)
        (*[* Format.printf
          "NumS.abd_simple: [%d] STEP 6. skip a=@ %a@\nc0remain=%a@\n%!"
          ddepth pr_w_atom a pr_eqn c0eqn;
        *]*)
        (*[* Format.printf
          "NumS.abd_simple: [%d] loop at:@\neqs=@ %a@\nineqs=@ %a@\n%!"
          ddepth pr_w_subst eqs_acc0 pr_ineqs ineqs_acc0;
        *]*)
        loop validation eq_trs eqs_acc0
          ineqs_acc0 optis_acc suboptis_acc c0eqn c0ineqn
          c0optis c0suboptis)
      else
        (* 7 *)
        (*[* Format.printf
          "NumS.abd_simple: [%d] STEP 7. a=@ %a@\nc0remain=%a@\n%!"
          ddepth pr_w_atom a pr_eqn c0eqn;
      *]*)
      let passes = ref false in
      let bh_ineqs = complete_ineqs ~cmp_v b_ineqs in
      (* FIXME: do opti or subopti atoms make it to here? *)
      let try_trans validation
          (((eqs_acc, ineqs_acc, optis_acc, suboptis_acc),
            new_eqn, new_ineqn, _, _), optin, suboptin) =
        (*[* Format.printf
          "NumS.abd_simple: trans-validation-prems:@\n%a@\n%!"
          (pr_line_list "| "
             (fun ppf (_, (_, _, s, _)) -> pr_state ppf s)) validation; *]*)
        if !aggressive_discard &&
           List.exists
             (fun (r_eqn, r_ineqn, r_optin, r_suboptin) ->
                List.exists (fun eqn ->
                    let a'vs = fvs_w eqn in
                    VarSet.cardinal a'vs > 1 &&
                    VarSet.is_empty (VarSet.diff a'vs bvs) &&
                    List.exists (equal_w ~cmp_v eqn) r_eqn)
                  new_eqn ||
                List.exists (fun ineqn ->
                    let a'vs = fvs_w ineqn in
                    VarSet.cardinal a'vs > 1 &&
                    VarSet.is_empty (VarSet.diff a'vs bvs) &&
                    List.exists (equal_w ~cmp_v ineqn) r_ineqn)
                  new_ineqn ||
                List.exists (fun optin ->
                    let a'vs = fvs_2w optin in
                    VarSet.cardinal a'vs > 1 &&
                    VarSet.is_empty (VarSet.diff a'vs bvs) &&
                    List.exists (equal_2w ~cmp_v optin) r_optin)
                  optin ||
                List.exists (fun suboptin ->
                    let a'vs = fvs_2w suboptin in
                    VarSet.cardinal a'vs > 1 &&
                    VarSet.is_empty (VarSet.diff a'vs bvs) &&
                    List.exists (equal_2w ~cmp_v suboptin) r_suboptin)
                  suboptin)
             discard
        then raise Omit_trans;
        (*[* Format.printf
          "NumS.abd_simple: [%d] 7a. validating=%b a'=@ %a@ ...@\n%!"
          ddepth (not !verif_incremental) pr_formula
          (ans_to_num_formula
             (eqs_acc, ineqs_acc, optis_acc, suboptis_acc));
        *]*)
        let all_new_vs =
          VarSet.union (vars_of_map fvs_w new_eqn)
            ((* VarSet.union *) (vars_of_map fvs_w new_ineqn)
            (* (VarSet.union (vars_of_map fvs_2w optin) *)
            (*    (vars_of_map fvs_2w suboptin)) *)) in
        let new_vs = VarSet.inter bvs all_new_vs in
        (*[* Format.printf
          "NumS.abd_simple: [%d] approaching 7. new_vs=@ %a\
           @ crosses=%b@\n%!"
          ddepth pr_vars new_vs (crosses_xparams ~cmp_v:qcmp_v ~bvs new_vs);
        *]*)
        (* 7b *)
        if crosses_xparams ~cmp_v:qcmp_v ~bvs new_vs then raise Omit_trans;
        if not !verif_incremental then
          ignore (validate all_new_vs
                    (eqs_acc, ineqs_acc, optis_acc, suboptis_acc));
        passes := true;
        (*[* Format.printf
          "NumS.abd_simple: [%d] 7a. validated@\n%!" ddepth; *]*)
        (* 7d *)
        (*[* Format.printf
          "NumS.abd_simple: [%d] 7 OK@\n%!" ddepth; *]*)
        (*[* Format.printf
          "NumS.abd_simple: [%d] loop at:\
           @\neqs=@ %a@\nineqs=@ %a@\n%!"
          ddepth pr_w_subst eqs_acc pr_ineqs ineqs_acc;
        *]*)
        (* (try                         *)
        loop validation eq_trs eqs_acc ineqs_acc optis_acc suboptis_acc
          c0eqn c0ineqn c0optis c0suboptis in
      let try_trans_a a' =
        try
          (* 7a *)
          (*[* Format.printf
            "NumS.abd_simple: [%d] 7a. trying a'=@ %a@ ...@\n%!"
            ddepth pr_w_atom a';
          *]*)
          if not (no_scope_viol_atom ~cmp_v:qcmp_v ~upward_of ~bvs a')
          then raise Omit_trans;
          let validation =
            if !verif_incremental
            then validate_incr
                ~cmp_v ~cmp_w uni_v ~bvs ~xbvs validation a'
            else validation in
          let eqn, ineqn, optin, suboptin = split_w_atom a' in
          (* [new_eqn, new_ineqn] are only used to determine the
             variables contributed to the answer. *)
          let acc =
            solve_get_eqn ~use_quants:(Fail_viol bvs)
              ~eqs:eqs_acc0 ~ineqs:ineqs_acc0
              ~optis:(optin @ optis_acc) ~suboptis:(suboptin @ suboptis_acc)
              ~eqn ~ineqn ~cmp_v ~cmp_w uni_v in
          try_trans validation (acc, optin, suboptin)
        (* with Contradiction _ -> ()) *)
        with
        | Terms.Contradiction (_,msg,tys,_) (*[* as e *]*) ->
          (*[* Format.printf
            "NumS.abd_simple: A [%d] 7. invalid, error=@\n%a@\n%!"
            ddepth Terms.pr_exception e;
          *]*)
          ()
        | Omit_trans ->
          (*[* Format.printf
            "NumS.abd_simple: A [%d] 7. too weak or crossing params@\n%!"
            ddepth;
          *]*)
          () in
      let try_trans_ineq (acc', w') =
        try
          (* 7a *)
          (*[* Format.printf
            "NumS.abd_simple: IN [%d] 7a. trying a'=@ %a@ ...@\n%!"
            ddepth pr_ineq w';
          *]*)
          if not (no_scope_viol ~cmp_v:qcmp_v ~upward_of ~bvs w')
          then raise Omit_trans;
          let validation =
            if !verif_incremental
            then validate_incr
                ~cmp_v ~cmp_w uni_v ~bvs ~xbvs validation (Leq_w w')
            else validation in
          try_trans validation (acc', [], [])
        (* with Contradiction _ -> ()) *)
        with
        | Terms.Contradiction (_,msg,tys,_) (*[* as e *]*) ->
          (*[* Format.printf
            "NumS.abd_simple: IN [%d] 7. invalid, error=@\n%a@\n%!"
            ddepth Terms.pr_exception e;
          *]*)
          ()
        | Omit_trans ->
          (*[* Format.printf
            "NumS.abd_simple: IN [%d] 7. too weak or crossing params@\n%!"
            ddepth;
          *]*)
          () in
      let a0 = subst_w_atom ~cmp_v eqs_acc0 a in
      (*[* Format.printf
        "NumS.abd_simple: [%d]@ a0=%a@\n%!" ddepth pr_w_atom a0; *]*)
      (match a0 with
       | Leq_w w ->
         let w = subst_if_qv ~uni_v ~bvs ~cmp_v rev_sb w in
         let cands =
           abd_cands ~cmp_v ~qcmp_v ~cmp_w ~uni_v ~orig_ren ~b_of_v ~upward_of
             ~bvs ~nonparam_vars
             ~discard_ineqs ~eqs_acc0 ~ineqs_acc0 ~optis_acc ~suboptis_acc
             ~b_ineqs ~bh_ineqs ~d_ineqn:d_ineqn' ~d_ineqs w in
         (*[* Format.printf
           "NumS.abd_simple: [%d] 7. choice=%b \
            c0s=@ %a@\na=%a@\neqs_acc0=%a@\n\
            rev_sb=%a@\n%!"
           ddepth (List.length cands > 1)
           pr_ineqn (List.map snd cands) pr_w_atom a
           pr_w_subst eqs_acc0 pr_w_subst rev_sb; *]*)
         List.iter try_trans_ineq cands
       | _ ->
         try_trans_a a0;
         laziter
           (fun tr ->
              (*[* Format.printf
                "NumS.abd_simple: [%d] 7. performing tr=@ %a@ \
                 on a0=@ %a@ ...@\n%!"
                ddepth pr_w tr pr_w_atom a0;
              *]*)
              try_trans_a (trans_w_atom ~cmp_v tr a0)) eq_trs);
      if not !passes then (
        (* 7c *)
        (*[* Format.printf
          "NumS.abd_simple: [%d] 7b. failed a0=@ %a@ ...@\n%!"
          ddepth pr_w_atom a0;
        *]*)
        raise (Terms.Contradiction
                 (Num_sort, no_pass_msg, None, dummy_loc))) in

    (* 2 *)
    (*[* Format.printf
      "NumS.abd_simple: init-validation-prems:@\n%a@\n%!"
      (pr_line_list "| "
         (fun ppf (_, (_, _, s, _)) -> pr_state ppf s)) validation; *]*)
    try
      for rot = 1 to !abd_rotations do
        let big_k = Array.init (rot - 1) (fun k -> !/(k+2)) in
        let big_k =
          Array.append big_k (Array.map (fun k-> !/1 // k) big_k) in
        let ks_eq =
          Array.to_list
            (Array.append [|!/1; !/(-1); !/0|]
               (Array.append
                  big_k
                  (Array.map (fun k -> !/(-1) */ k) big_k))) in
        let ks_eq = laz_of_list ks_eq in
        let eq_trs = laz_single zero in
        let add_eq_tr = add_tr ks_eq in
        let eq_trs = List.fold_left add_eq_tr eq_trs d_eqn' in
        try
          loop validation eq_trs eqs_i ineqs_i optis_i suboptis_i
            c_eqn0 c_ineqn0 c_optis0 c_suboptis0
        with Terms.Contradiction _ (*[* as e *]*) ->
          (*[* Format.printf
            "NumS.abd_simple: trying more rotations because:@\n%a@\n%!"
            Terms.pr_exception e;
          *]*)
          ()
      done; None
    with Result (ans_eqs, ans_ineqs, ans_optis, ans_suboptis, validation) ->
      (*[* Format.printf "NumS.abd_simple: result:\
                           @\neqs=@ %a@\nineqs=@ %a@\n%!"
        pr_w_subst ans_eqs pr_ineqs ans_ineqs; *]*)
      (*[* Format.printf
        "NumS.abd_simple: result-validation-prems:@\n%a@\n%!"
        (pr_line_list "| "
           (fun ppf (_, (_, _, s, _)) -> pr_state ppf s)) validation; *]*)
      Some ((ans_eqs, ans_ineqs, ans_optis, ans_suboptis), validation)
  with (* failed premise/\conclusion *)
  | Terms.Contradiction _ -> None
  | Timeout ->
    abd_timeout_flag := true;
    (*[* Format.printf
      "NumS.abd_simple: TIMEOUT@\neqs_i=@ %a@\nineqs_i=@ \
       %a@\noptis_i=@ %a@\nsuboptis_i=@ %a@\nd_eqn=@ %a@ d_ineqn=@ %a@\nc_eqn=@ %a@\nc_ineqn=@ %a@\n%!"
      pr_w_subst eqs_i pr_ineqs ineqs_i pr_optis optis_i
      pr_suboptis suboptis_i pr_eqn d_eqn pr_ineqn d_ineqn
      pr_eqn c_eqn pr_ineqn c_ineqn;
    *]*)
    None

let make_cmp q v1 v2 =
  (* Order: variables more to the right in the quantifier should be more
     to the left in the sum. *)
  match q.cmp_v v1 v2 with
  | Left_of -> 1
  | Right_of -> -1
  | Same_params -> compare v2 v1
  | Same_quant -> compare v2 v1


module NumAbd = struct
  type accu = w_subst * ineqs * optis * suboptis
  type args = {
    cmp_v : (var_name -> var_name -> int);
    cmp_w : (w -> w -> int);
    qcmp_v : (var_name -> var_name -> var_scope);
    b_of_v : var_name -> var_name;
    upward_of : var_name -> var_name -> bool;
    orig_ren : (var_name, var_name) Hashtbl.t;
    uni_v : (var_name -> bool);
    bvs : VarSet.t;
    xbvs : (int * VarSet.t) list;
    nonparam_vars : VarSet.t}
  type answer = accu
  type br_state = t_br_state
  type validation = t_validation
  type discarded = w list * w list * optis * suboptis
  (** "LHS" variables of opti atoms, premise, conclusion. *)
  type branch =
      VarSet.t * (w list * w list) * (w list * w list * optis * suboptis)

  let abd_fail_timeout = abd_fail_timeout_count
  let abd_fail_flag = abd_fail_flag

  let abd_simple
      {qcmp_v; cmp_w; cmp_v; uni_v; bvs; xbvs; nonparam_vars;
       b_of_v; orig_ren; upward_of}
      ~discard ~validation ~validate ~neg_validate acc br =
    abd_simple ~qcmp_v ~cmp_w cmp_v ~orig_ren ~b_of_v ~upward_of
      uni_v ~bvs ~xbvs ~nonparam_vars
      ~discard ~validation ~validate ~neg_validate 0 acc br

  let extract_ans ans = ans

  (* FIXME *)
  let discard_ans (eqs, ineqs, optis, suboptis) =
    unsubst eqs, unsolve ineqs, optis, suboptis

  let concl_of_br ((_, _, concl) : branch) =
    num_to_formula (cnj_to_num_formula concl)

  let is_taut (eqs, ineqs, optis, suboptis) =
    VarMap.is_empty eqs && VarMap.is_empty ineqs && optis=[] && suboptis=[]

  let pr_branch pp (_, (d_eqn, d_ineqn),
                    (c_eqn, c_ineqn, c_optis, c_suboptis)) =
    Format.fprintf pp
      "@[<2>d_eqn=%a@\nd_ineqn=%a@\n⟹@\nc_eqn=%a@\nc_ineqn=%a@\nc_optis=%a@\nc_suboptis=%a@\n@]"
      pr_eqn d_eqn pr_ineqn d_ineqn
      pr_eqn c_eqn pr_ineqn c_ineqn pr_optis c_optis pr_suboptis c_suboptis

  let pr_ans pp (eqs, ineqs, optis, suboptis) =
    Format.fprintf pp "eqs=%a@\nineqs=%a@\noptis=%a@\nsuboptis=%a@\n%!"
      pr_w_subst eqs pr_ineqs ineqs
      pr_optis optis pr_suboptis suboptis
end

module JCA = Joint.JointAbduction (NumAbd)

let empty_renaming = Hashtbl.create 0
let empty_b_of_v v = v

let fvs_br_concl (_, _, _, _,
            (c_eqn, c_ineqn, c_optis, c_suboptis)) =
  VarSet.union
    (vars_of_map (vars_of_map fvs_w) [c_eqn; c_ineqn])
    (vars_of_map (vars_of_map fvs_2w) [c_optis; c_suboptis])

let fvs_sep_w_formula (c_eqn, c_ineqn, c_optis, c_suboptis) =
  VarSet.union
    (vars_of_map (vars_of_map fvs_w) [c_eqn; c_ineqn])
    (vars_of_map (vars_of_map fvs_2w) [c_optis; c_suboptis])

(* FIXME: eliminate optis from premise, but first try simplifying
   them with both premise and conclusion of a branch. *)
let abd q ~bvs ~xbvs ?(orig_ren=empty_renaming) ?(b_of_v=empty_b_of_v)
    ~upward_of ~nonparam_vars
    ~discard ?(iter_no=2) brs =
  abd_timeout_flag := false;
  let cmp_v = make_cmp q in
  let cmp_w (vars1,cst1,_) (vars2,cst2,_) =
    match vars1, vars2 with
    | [], [] -> 0
    | _, [] -> -1
    | [], _ -> 1
    | (v1,_)::_, (v2,_)::_ -> cmp_v v1 v2 in
  (*[* Format.printf "NumS.abd: iter_no=%d@ bvs=%s@\n%!"
    iter_no
    (String.concat "," (List.map var_str (VarSet.elements bvs))); *]*)
  (*[* Format.printf "NumS.abd: brs=@\n| %a@\n%!"
    (pr_line_list "| " pr_br4) brs;
   *]*)
  let brs = List.map
      (fun (nonrec, chi_pos, prem, concl) ->
         (*[* Format.printf "NumS.abd: splitting premise=@\n%a@\n%!"
           pr_formula prem; *]*)
         let d_eqn, d_ineqn, d_optis, d_suboptis =
           split_flatten ~cmp_v prem in
         (* We normalize to reduce the number of opti and subopti
            disjunctions. Also recovers implicit equalities
            due to optis. *)
         try
           let (d_eqs,d_ineqs,d_optis,d_suboptis), _, _, d_opti_eqn, _ =
             solve_aux ~cmp_v ~cmp_w q.uni_v ~use_quants:Ignore_viol
               ~eqs:VarMap.empty ~ineqs:VarMap.empty
               ~eqs':VarMap.empty ~cnj:[] ~cnj':[]
               ~eqn:d_eqn ~ineqn:d_ineqn
               ~optis:d_optis ~suboptis:d_suboptis in
           (*[* Format.printf
             "NumS.abd: premise has %d optis, %d suboptis@\n%!"
             (List.length d_optis) (List.length d_suboptis); *]*)
           (* FIXME: [choices] now adds these inequalities, remove *)
           (* let d_ineqn = flat2 d_optis @ d_ineqn in *)
           let opti_lhs = List.fold_left
               (fun lhs ((vars1,_,_),(vars2,_,_)) ->
                  let vs1 = vars_of_list (List.map fst vars1)
                  and vs2 = vars_of_list (List.map fst vars2) in
                  let cand = VarSet.inter vs1 vs2 in
                  let cand = VarSet.filter
                      (fun v -> Num.sign_num (List.assoc v vars1) =
                                Num.sign_num (List.assoc v vars2)) cand in
                  VarSet.union cand lhs)
               VarSet.empty d_optis in
           let concl = split_flatten ~cmp_v concl in
           let contr_exc = ref None in
           let res = map_some
               (fun opti_subopti ->
                  (* eqs come from opti, ineqs from both *)
                  let o_eqn, o_ineqn, _, _ = split_formula opti_subopti in
                  (*[* Format.printf
                    "NumS.abd-split: case@\no_eqn=%a@\no_ineqn=%a@\n%!"
                    pr_eqn o_eqn pr_ineqn o_ineqn; *]*)
                  try
                    let d_eqs,d_ineqs,_,_ =
                      solve ~cmp_v ~cmp_w q.uni_v
                        ~eqs:d_eqs ~ineqs:d_ineqs
                        ~eqn:o_eqn ~ineqn:o_ineqn in
                    (*[* Format.printf
                      "NumS.abd-split: case@\nd_eqs=%a@\nd_ineqs=%a@\n%!"
                      pr_w_subst d_eqs pr_ineqs d_ineqs; *]*)
                    Some (nonrec, chi_pos, opti_lhs, d_eqs, d_ineqs,
                          (d_opti_eqn @ o_eqn @ d_eqn, o_ineqn @ d_ineqn),
                          concl)
                  with Terms.Contradiction _ as e ->
                    if !nodeadcode && !contr_exc=None
                    then contr_exc := Some e;
                    None)
               (choices ~cmp_v ~intro_cho_ineq:true d_optis d_suboptis) in
           if !nodeadcode && res=[] && !contr_exc<>None
           then (deadcode_flag := true; raise (unsome !contr_exc))
           else (
             (*[* Format.printf "NumS.abd: done splitting #=%d of=@\n%a@\n%!"
               (List.length res) pr_formula prem; *]*)
             res)
         with Terms.Contradiction _ as e ->
           if !nodeadcode then (deadcode_flag := true; raise e)
           else [])
      brs in
  (* Raise [Contradiction] from [abd] when constraints are not
     satisfiable. *)
  (* TODO: optimize -- don't redo work. *)
  let guard_brs = List.concat brs in
  (*[* Format.printf "NumS.abd: brs processing past splitting@\n%!"; *]*)
  let brs = concat_map
      (fun obrs ->
         let contr_exc = ref None in
         let res = map_some
             (fun ((nonrec, chi_pos, opti_lhs,
                    d_eqs, d_ineqs, (d_eqn, d_ineqn),
                    (c_eqn, c_ineqn, c_optis, c_suboptis)) as br) ->
               let br =
                 try
                   (* Some equations from case splitting can lead to
                      contradictory branches. We collect the context to
                      detect all such cases. *)
                   let (g_eqn, g_ineqn, g_optis, g_suboptis) =
                     List.fold_left
                       (fun (g_eqn, g_ineqn, g_optis, g_suboptis as g_acc)
                         ((_, _, _, _, _, (d2_eqn, d2_ineqn),
                           (c2_eqn, c2_ineqn, c2_optis, c2_suboptis)) as br2) ->
                         if br == br2 then g_acc
                         else if implies_case ~cmp_v ~cmp_w q.uni_v
                             d_eqs d_ineqs
                             d2_eqn d2_ineqn [] []
                         then (
                           (*[* Format.printf
                             "implies-guard:@\nd_eqs=%a@\nd_ineqs=%a\
                             @\nd2_eqn=%a@\nc2_eqn=%a@\nd2_ineqn=%a\
                             @\nc2_ineqn=%a@\nc2_optis=%a\
                             @\nc2_suboptis=%a@\n%!"
                             pr_w_subst d_eqs pr_ineqs d_ineqs
                             pr_eqn d2_eqn pr_eqn c2_eqn pr_ineqn
                             d2_ineqn pr_ineqn c2_ineqn
                             pr_optis c2_optis pr_suboptis c2_suboptis; *]*)

                           c2_eqn @ g_eqn, c2_ineqn @ g_ineqn,
                           c2_optis @ g_optis, c2_suboptis @ g_suboptis)
                         else g_acc)
                       ([], [], [], []) guard_brs in
                   ignore (solve (* or: ~eqs:d_eqs ~ineqs:d_ineqs *)
                             ~eqn:(g_eqn @ d_eqn) ~ineqn:(g_ineqn @ d_ineqn)
                             ~cmp_v ~cmp_w q.uni_v);
                   Some (nonrec, chi_pos, opti_lhs, (d_eqn, d_ineqn),
                         (c_eqn, c_ineqn, c_optis, c_suboptis))
                 with Terms.Contradiction _ as e ->
                   if !nodeadcode then contr_exc := Some e;
                   None in
               (*if br = None then br
                 else (ignore (solve
                               ~eqn:(d_eqn @ c_eqn) ~ineqn:(d_ineqn @ c_ineqn)
                               ~cmp_v ~cmp_w q.uni_v); )*)
               br)
             obrs in
         if res=[] && !nodeadcode && !force_nodeadcode && !contr_exc<>None
         then (deadcode_flag := true; raise (unsome !contr_exc))
         else
           let brs_n = List.length res in
           let brs_r = ref brs_n in
           List.map (fun br -> br, (fvs_br_concl br, brs_r, brs_n, br)) res)
      brs in
  let brs, validate_brs = List.split brs in
  (*[* Format.printf "NumS.abd: brs processing past merging@\n%!"; *]*)
  let validate added_vs (eqs, ineqs, optis, suboptis) =
    let chi_sb = local_split ~cmp_v:q.cmp_v ~bvs ~xbvs
        (unsubst eqs) (unsolve ineqs) optis suboptis in
    (*[* Format.printf
      "NumS.abd-validate:@ eqs=%a@ ineqs=%a@ optis=%a@ suboptis=%a@ \
       @\n%!"
      pr_w_subst eqs pr_ineqs ineqs pr_optis optis pr_suboptis suboptis; *]*)
    (* TODO: introduce use-site substitutions *)
    try
      List.iter
        (fun (br_vs, brs_r, (_ (*[* as brs_n *]*)),
              (_, chi_pos, _, (d_eqn, d_ineqn),
               (c_eqn, c_ineqn, c_optis, c_suboptis))) ->
          if !verif_all_brs || chi_pos <> [] ||
             VarSet.exists (fun v -> VarSet.mem v br_vs) added_vs
          then
            let prem_state =
              (*[* Format.printf
                "NumS.abd-validate: brs_r=%d; brs_n=%d\
                 @\nd_eqn=%a@\nc_eqn=%a@\nd_ineqn=%a@\nc_ineqn=%a\
                 @\nc_optis=%a@\nc_suboptis=%a@\n%!" !brs_r brs_n
                pr_eqn d_eqn pr_eqn c_eqn pr_ineqn d_ineqn pr_ineqn c_ineqn
                pr_optis c_optis pr_suboptis c_suboptis; *]*)
              try
                Right (solve ~eqs ~ineqs ~optis ~suboptis
                         ~eqn:d_eqn ~ineqn:d_ineqn ~cmp_v ~cmp_w q.uni_v)
              with Terms.Contradiction _ as e -> Left e in
            match prem_state with
            | Right (eqs,ineqs,optis,suboptis) ->
                (*[* Format.printf
                  "v_eqs=%a@\nv_ineqs=%a@\nv_optis=%a@\nv_suboptis=%a@\n%!"
                  pr_w_subst eqs pr_ineqs ineqs pr_optis optis
                  pr_suboptis suboptis; *]*)
              let u_eqn, u_ineqn, u_optis, u_suboptis as u =
                subst_chi chi_sb chi_pos in
              (*[* Format.printf
                "brc_eqn=%a@\nbrc_ineqn=%a@\nbrc_optis=%a@\n\
                 brc_suboptis=%a@\n%!"
                pr_eqn (u_eqn @ c_eqn) pr_ineqn (u_ineqn @ c_ineqn)
                pr_optis (u_optis @ c_optis)
                pr_suboptis (suboptis @ u_suboptis @ c_suboptis); *]*)
              if !verif_all_brs ||
                 VarSet.exists (fun v -> VarSet.mem v br_vs) added_vs ||
                 VarSet.exists (fun v -> VarSet.mem v br_vs)
                   (fvs_sep_w_formula u)
              then
                let (*[* br_eqs,br_ineqs,br_optis,br_suboptis *]*) _ =
                  solve ~eqs ~ineqs
                    ~eqn:(u_eqn @ c_eqn) ~ineqn:(u_ineqn @ c_ineqn)
                    ~optis:(optis @ u_optis @ c_optis)
                    ~suboptis:(suboptis @ u_suboptis @ c_suboptis)
                    ~cmp_v ~cmp_w q.uni_v in
                (*[* Format.printf
                  "br_eqs=%a@\nbr_ineqs=%a@\nbr_optis=%a@\nbr_suboptis=%a@\n%!"
                  pr_w_subst br_eqs pr_ineqs br_ineqs pr_optis br_optis
                  pr_suboptis br_suboptis; *]*)
                ()
            | Left e ->
              if !nodeadcode then (
                decr brs_r;
                if !brs_r <= 0 then (deadcode_flag := true; raise e)))
        validate_brs;
      (*[* Format.printf "NumS.abd-validate: passed@\n%!"; *]*)
      List.iter (fun (_, brs_r, brs_n, _) -> brs_r := brs_n) validate_brs
    with e ->
      List.iter (fun (_, brs_r, brs_n, _) -> brs_r := brs_n) validate_brs;
      raise e in
  let validation =
    map_some
      (fun (br_vs, brs_r, brs_n,
            (_, chi_pos, _,
             (d_eqn, d_ineqn),
             (c_eqn, c_ineqn, c_optis, c_suboptis))) ->
         try
           let (eqs, ineqs, _, _ as prem) = solve
             ~eqn:d_eqn ~ineqn:d_ineqn
             ~cmp_v ~cmp_w q.uni_v in
           let prem_n_concl = solve
               ~eqs ~ineqs
               ~eqn:c_eqn ~ineqn:c_ineqn ~optis:c_optis ~suboptis:c_suboptis
               ~cmp_v ~cmp_w q.uni_v in
           Some (br_vs, ((brs_r, brs_n), chi_pos, prem, prem_n_concl))
         with Terms.Contradiction _ -> None)
      validate_brs in
  (*[* Format.printf
    "validation:@ %a@\n%!"
    (pr_line_list "| "
       (fun ppf (_, (_, _, _, s)) -> pr_state ppf s)) validation; *]*)
  (* We currently do not make use of negative constraints. *)
  let neg_validate _ = 0 in
  let brs, unproc_brs =
    if iter_no > 1 || !early_num_abduction
    then brs, []
    else List.partition
        (fun (nonrec, chi_pos, opti_lhs, prem, concl) -> nonrec) brs in
  let brs = List.map
      (fun (_, chi_pos, opti_lhs,  prem, concl) -> opti_lhs, prem, concl)
      brs in
  let brs = List.stable_sort
      (fun (_,(pe1,pi1),_) (_,(pe2,pi2),_) ->
         (List.length pe1 + List.length pi1) -
           (List.length pe2 + List.length pi2))
      brs in
  (*[* Format.printf "NumS.abd: split-brs=@\n| %a@\n%!"
    (pr_line_list "| " pr_sep_br) brs;
   *]*)
  (*[* Format.printf "NumS.abd: unproc_brs=@\n| %a@\n%!"
    (pr_line_list "| " pr_sep_br)
    (List.map
       (fun (_, _, opti_lhs,  prem, concl) -> opti_lhs, prem, concl)
       unproc_brs);
   *]*)
  let discard =
    List.map (split_flatten ~cmp_v) discard in
  let elim_uni =
    (* FIXME: rethink *)
    concat_map
      (fun (_,_,_,_,(concl_eqs, _, _, _)) ->
         List.filter
           (function
             | Eq (Lin (_,_,v), Lin (_,_,w), lc)
               when q.uni_v v && q.uni_v w -> false
             | Eq (Lin (_,_,b), t, lc)
               when q.uni_v b &&
                    Terms.var_not_left_of q b (Terms.num t) -> true
             | Eq (t, Lin (_,_,b), lc)
               when q.uni_v b &&
                    Terms.var_not_left_of q b (Terms.num t) -> true
             | _ -> false)
           (List.map (expand_atom true) concl_eqs))
      unproc_brs in
  let ans = JCA.abd
      {cmp_v; cmp_w; NumAbd.qcmp_v = q.cmp_v; orig_ren; b_of_v;
       upward_of; uni_v = q.uni_v; bvs; xbvs; nonparam_vars}
      ~discard validation ~validate ~neg_validate
      (VarMap.empty, VarMap.empty, [], []) brs in
  [], elim_uni @ ans_to_num_formula ans


let i2f = float_of_int

let expand_eqineqs eqs ineqs =
  let ans = List.map (expand_atom true) (unsubst eqs) in
  ans @ List.map (expand_atom false) (unsolve ineqs)



(* [atomic_impl a b] means [a] is stronger than [b], or equal in
   strength unless [a] is [Opti_w] -- prune opti atoms as side effect. *)
let atomic_impl ~cmp_v a b =
  match a, b with
  | Eq_w w1, Eq_w w2
    -> equal_w ~cmp_v w1 w2
  | Leq_w _, Eq_w _ -> false
  | (Eq_w w1 | Leq_w w1), Leq_w w2 ->
    taut_w false (diff ~cmp_v w2 w1)
  | (Eq_w w3 | Leq_w w3), Opti_w (w1, w2) when zero_p w2 ->
    taut_w false (diff ~cmp_v w1 w3)
  | (Eq_w w3 | Leq_w w3), Opti_w (w1, w2) when zero_p w1 ->
    taut_w false (diff ~cmp_v w2 w3)
  | Eq_w w3, Opti_w (w1, w2) ->
    (* We cannot actually eliminate `opti` of distinct arguments -- it
       requires more than just an equality. *)
    equal_w ~cmp_v w1 w2 && equal_w ~cmp_v w1 w3
  | Opti_w (w1, w2), Leq_w w3 ->
    taut_w false (diff ~cmp_v w3 w1) || taut_w false (diff ~cmp_v w3 w2) ||
    (* Below, just one of the things that can be done with two equations,
       but even this is seldom useful. *)
    taut_w false (diff ~cmp_v w3 (sum_w ~cmp_v w1 w2))
  | Leq_w _, Opti_w _ -> false
  | Opti_w _, Eq_w _ -> false
  | Opti_w (w1, w2), Opti_w (w3, w4) ->
    (equal_w ~cmp_v w1 w3 && equal_w ~cmp_v w2 w4) ||
    (equal_w ~cmp_v w2 w3 && equal_w ~cmp_v w1 w4)
  | Leq_w w1, Subopti_w (w2, w3) ->
    taut_w false (diff ~cmp_v w2 w1) ||
    taut_w false (diff ~cmp_v w3 w1)
  | Eq_w w1, Subopti_w (w2, w3) ->
    taut_w false (diff ~cmp_v w2 w1) ||
    taut_w false (diff ~cmp_v w3 w1) ||
    (nonneg_cst_w (sum_w ~cmp_v w1 w2) &&
     nonneg_cst_w (sum_w ~cmp_v w1 w3))
  | Opti_w (w1, w2), Subopti_w (w3, w4) ->
    let res =
      taut_w false (diff ~cmp_v w3 w1) ||
      taut_w false (diff ~cmp_v w4 w1) ||
      taut_w false (diff ~cmp_v w3 w2) ||
      taut_w false (diff ~cmp_v w4 w2) ||
      (nonneg_cst_w (sum_w ~cmp_v w1 w3) &&
       nonneg_cst_w (sum_w ~cmp_v w2 w4)) ||
      (nonneg_cst_w (sum_w ~cmp_v w2 w3) &&
       nonneg_cst_w (sum_w ~cmp_v w1 w4)) in
    (*[* Format.printf
      "implies-opt-subopti: w1=%a;@ w1=%a;@ w1=%a;@ w1=%a;@ \
       w3-w1=%a;@ w4-w1=%a;@ w3-w2=%a;@ w4-w2=%a@ res=%b@\n%!"
      pr_w w1 pr_w w2 pr_w w3 pr_w w4
      pr_w (diff ~cmp_v w3 w1) pr_w (diff ~cmp_v w4 w1)
      pr_w (diff ~cmp_v w3 w2) pr_w (diff ~cmp_v w4 w2) res; *]*)
    res
  | Subopti_w (w1, w2), Subopti_w (w3, w4) ->
    (taut_w false (diff ~cmp_v w3 w1) ||
     taut_w false (diff ~cmp_v w4 w1)) &&
    (taut_w false (diff ~cmp_v w3 w2) ||
     taut_w false (diff ~cmp_v w4 w2))
  | Subopti_w _, (Eq_w _ | Leq_w _ | Opti_w _) -> false

(* Prune atoms implied by other atoms -- only single
   other atoms are considered. *)
let prune_single_redund ~cmp_v guard_cnj cnj =
  let rec aux pareto = function
    | [] -> pareto
    | a::cnj ->
      let cnj = List.filter (not % atomic_impl ~cmp_v a) cnj in
      if List.exists (fun b -> atomic_impl ~cmp_v b a) cnj
          || List.exists (fun b -> atomic_impl ~cmp_v b a) guard_cnj
      then aux pareto cnj
      else aux (a::pareto) cnj in
  aux [] cnj

(* Dismisses contradictions. FIXME: should? *)
let project ~cmp_v ~cmp_w ineqs ineqn =
  let rec proj ineqs ineqn =
    match ineqn with
    | [] -> ineqs
    | ([], cst, _)::ineqn (* when cst <=/ !/0 *) -> proj ineqs ineqn
    | ((v,k)::vars, cst, loc)::ineqn ->
      let left, right =
        try VarMap.find v ineqs
        with Not_found -> affine_empty, affine_empty in
      let ineq_l, ineq_r, more_ineqn = 
        let ohs = mult (!/(-1) // k) (vars, cst, loc) in
        if k >/ !/0
        then
          [], [ohs],
          affine_map_to_list (fun lhs -> diff ~cmp_v lhs ohs) left
        else
          [ohs], [],
          affine_map_to_list (fun rhs -> diff ~cmp_v ohs rhs) right
      in
      let more_ineqn = List.filter
        (function
        | [], cst, _ (* when cst <=/ !/0 *) -> false
        | _ -> true)
        more_ineqn in
      (*[* Format.printf
        "NumS.project: v=%s@\nmore_ineqn=@ %a@\n%!"
        (var_str v) pr_ineqn more_ineqn; *]*)  
      let ineqn =
        merge cmp_w (List.sort cmp_w more_ineqn) ineqn in
      let ineqs =
        VarMap.add v
          (add_to_affine ~is_lhs:true ineq_l left,
           add_to_affine ~is_lhs:false ineq_r right) ineqs in
      proj ineqs ineqn in
  proj ineqs ineqn

exception Not_satisfiable

let strict_sat ~cmp_v ~cmp_w (ineqs : ineqs)
    ~strict:(vars,cst,lc as ineq) ineqn =
  (*[* Format.printf
    "NumS.strict-sat: test strict=%a@\nineqs=@ %a@\nineqn=@ %a@\n%!"
     pr_ineq ineq pr_ineqs ineqs pr_ineqn ineqn; *]*)  
  let rec proj strict ineqs ineqn =
    match ineqn with
    | [] -> ineqs
    | ([], cst, _)::ineqn when strict && cst </ !/0 ->
      proj true ineqs ineqn
    | ([], cst, _)::ineqn when not strict && cst <=/ !/0 ->
      proj false ineqs ineqn
    | ([], cst, loc)::_ ->
      raise Not_satisfiable
    | ((v,k)::vars, cst, loc)::ineqn ->
      let left, right =
        try VarMap.find v ineqs
        with Not_found -> affine_empty, affine_empty in
      let ohs = mult (!/(-1) // k) (vars, cst, loc) in
      let ineq_l, ineq_r, more_ineqn = 
        if k >/ !/0
        then
          (if not strict && affine_mem ~is_lhs:false ohs right
           then [], [], []
           else [], [ohs],
                affine_map_to_list (fun lhs -> diff ~cmp_v lhs ohs) left)
        else
          (if not strict && affine_mem ~is_lhs:true ohs left
           then [], [], []
           else [ohs], [],
                affine_map_to_list (fun rhs -> diff ~cmp_v ohs rhs) right)
      in
      (*[* Format.printf
        "NumS.strict-sat-proj: v=%s k=%s@ ohs=%a@\nleft=@ \
         %a@\nright=@ %a@\nmore_ineqn=@ %a@\nrem_ineqn=@ %a@\n%!"
        (var_str v) (string_of_num k) pr_w ohs pr_eqn
        (affine_to_ineqn left) pr_eqn (affine_to_ineqn right)
        pr_ineqn more_ineqn pr_ineqn ineqn; *]*)  
      let more_ineqn = List.filter
        (function
          | ([], cst, _) when strict && cst </ !/0 ->
            false
          | ([], cst, _) when not strict && cst <=/ !/0 ->
            false
          | [], cst, loc -> raise Not_satisfiable
          | w -> true)
        more_ineqn in
      let ineqn =
        merge cmp_w (List.sort cmp_w more_ineqn) ineqn in
      let ineqs =
        VarMap.add v
          (add_to_affine ~is_lhs:true ineq_l left,
           add_to_affine ~is_lhs:false ineq_r right)
          ineqs in
      proj strict ineqs ineqn in
  let res =
    try
      if not (!int_pruning || !strong_int_pruning)
      then ignore (proj true (proj false ineqs ineqn) [ineq])
      (* TODO: consider pruning by margin of 1/rotations instead of 1. *)
      else ignore (proj !strong_int_pruning (proj false ineqs ineqn)
                     [vars, cst +/ !/1, lc]);
      true
    with Not_satisfiable -> false in
  (*[* Format.printf
    "NumS.strict-sat: result %b@\n%!" res; *]*)
  res

(* Checks redundancy with respect to all past and remaining inequalities. *)
let keep_nonredund ~cmp_v ~cmp_w ineqs l =
  (*[* Format.printf
    "NumS.keep_nonredund: ineqs=@ %a@\nl=@ %a@\n%!"
     pr_ineqs ineqs pr_ineqn l; *]*)    
  let rec loop ineqs acc drop = function
    | [] -> ineqs, acc, drop
    | a::l ->
      (*[* Format.printf
        "NumS.keep_nonredund: a=@ %a@\nacc=@ %a@\ndrop=@ %a@\n%!"
        pr_ineq a pr_ineqn acc pr_ineqn drop; *]*)    
      if strict_sat ~cmp_v ~cmp_w ineqs ~strict:(mult !/(-1) a) l
      then loop (project ~cmp_v ~cmp_w ineqs [a]) (a::acc) drop l
      else loop ineqs acc (a::drop) l in
  (*[* let (_, ineq_res, _ as res) = *]*) loop ineqs [] [] l (*[* in
  Format.printf
    "NumS.keep_nonredund: res=@ %a@\n%!" pr_ineqn ineq_res;
  res *]*)

(* Checks redundancy of suboptis with respect to optis and all past
   and remaining suboptis. Returns implicit inequalities and remaining
   suboptis. *)
let keep_nonredund_subopti ~cmp_v ~cmp_w ineqs optis suboptis =
  (*[* Format.printf
    "NumS.keep_nonredund-subopti: ineqs=@ %a@\noptis=@ %a@\nsuboptis=@ %a@\n%!"
    pr_ineqs ineqs pr_optis optis pr_suboptis suboptis; *]*)    
  let opti_subopti = choices ~cmp_v ~intro_cho_ineq:false optis suboptis in
  let rec loop cho acc implicit drop =
    function
    | [] -> acc, implicit, drop
    | (w1, w2 as a)::suboptis
      when List.memq a acc ||
           List.mem_assq w1 implicit || List.mem_assq w2 implicit ->
      loop cho acc implicit drop suboptis
    | (([], _, _), _)::suboptis
    | (_, ([], _, _))::suboptis ->
      loop cho acc implicit drop suboptis
    | (w1, w2 as a)::suboptis ->
      let o_ineqn, dsj_pair = partition_map
          (function
            | Leq_w w when w == w1 -> Right (w1, w2)
            | Leq_w w when w == w2 -> Right (w2, w1)
            | Leq_w w when List.memq w drop -> Left []
            | Leq_w w -> Left [w]
            | Eq_w w -> Left [w; mult !/(-1) w]
            | _ -> Left [])
          cho in
      let dsj1, dsj2 as dsj_pair =
        match dsj_pair with [dsj1, dsj2] -> dsj1, dsj2 | _ -> assert false in
      let o_ineqn = List.concat o_ineqn in
      let o_case = diff ~cmp_v dsj1 dsj2 in
      let o_ineqn = o_case::o_ineqn in
      let res =
        strict_sat ~cmp_v ~cmp_w ineqs ~strict:(mult !/(-1) dsj1) o_ineqn in
      (*[* Format.printf
        "NumS.keep_nonredund-subopti: a=%a@ keep=%b@ strict=%a@ \
         +ineqn=%a@\n%!"
        pr_subopti a res pr_ineq dsj1 pr_ineqn o_ineqn; *]*)
      if not res
      then
        loop cho acc implicit (w1::w2::drop) suboptis
      else if not (strict_sat ~cmp_v ~cmp_w ineqs
                     ~strict:(mult !/(-1) o_case) o_ineqn)
      then (* dsj1 <= dsj2, so: *)
        let s =
          match direct_opti dsj_pair with
          | Some (_, _, s, _, _) -> s
          | None -> assert false in
        let dsj = if s then dsj2 else dsj1 in
        loop cho acc ((dsj, a)::implicit) drop suboptis
      else
        loop cho (a::acc) implicit drop suboptis in

  let subopti_res, implicit_res, _ =
    List.fold_left
      (fun (acc, implicit, drop) cho ->
         let acc, implicit', drop =
           loop cho acc [] drop suboptis in
         let implicit, more = List.partition
             (fun (d, a) -> List.mem_assq d implicit)
             implicit' in
         map_append snd more acc, implicit, drop)
      (loop (List.hd opti_subopti) [] [] [] suboptis)
      (List.tl opti_subopti) in
  let implicit = List.map fst implicit_res in
  (*[* Format.printf
    "NumS.keep_nonredund-subopti: subopti_res=@ %a@\nimplicit=@ %a@\n%!"
    pr_suboptis subopti_res pr_eqn implicit; *]*)
  subopti_res, implicit

let ineqn_of_eqineq_w = concat_map
    (function
      | Leq_w w -> [w]
      | Eq_w w -> [w; mult !/(-1) w]
      | _ -> [])

(* Checks redundancy of optis with respect to past and remaining
   optis. Returns implicit equations and remaining optis. *)
let keep_nonredund_opti ~cmp_v ~cmp_w ineqs optis suboptis =
  (*[* Format.printf
    "NumS.keep_nonredund-opti: ineqs=@ %a@\noptis=@ %a@\nsuboptis=@ %a@\n%!"
    pr_ineqs ineqs pr_optis optis pr_suboptis suboptis; *]*)    
  let opti_subopti = choices ~cmp_v ~intro_cho_ineq:false optis suboptis in
  let rec loop cho acc implicit drop =
    function
    | [] -> acc, implicit, drop
    | (w1, w2 as a)::optis
      when List.memq a acc ||
           List.mem_assq w1 implicit || List.mem_assq w2 implicit ->
      loop cho acc implicit drop optis
    | (([], _, _), _)::optis
    | (_, ([], _, _))::optis ->
      loop cho acc implicit drop optis
    | (w1, w2 as a)::optis ->
      let o_ineqn, dsj_pair = partition_map
          (function
            | Leq_w w when w == w1 -> Right (w1, w2)
            | Leq_w w when w == w2 -> Right (w2, w1)
            | Eq_w w when List.memq w drop -> Left []
            | Leq_w w -> Left [w]
            | Eq_w w -> Left [w; mult !/(-1) w]
            | _ -> Left [])
          cho in
      let dsj1, dsj2 as dsj_pair =
        match dsj_pair with [dsj1, dsj2] -> dsj1, dsj2 | _ -> assert false in
      let o_ineqn = List.concat o_ineqn in
      let o_case = diff ~cmp_v dsj1 dsj2 in
      (*[* Format.printf
        "NumS.keep_nonredund-opti:@ w1=%a@ w2=%a@ dsj1=%a@ dsj2=%a@ \
         cho=%a@ o_ineqn=%a@ o_case=%a@\n%!"
        pr_ineq w1 pr_ineq w2 pr_ineq dsj1 pr_ineq dsj2
        pr_w_formula cho pr_ineqn o_ineqn pr_ineq o_case; *]*)
      let o_ineqn' = o_case::o_ineqn in
      let res = (* disequality: both strict inequalities fail *)
        strict_sat ~cmp_v ~cmp_w ineqs ~strict:(mult !/(-1) dsj1)
          o_ineqn' ||
        strict_sat ~cmp_v ~cmp_w ineqs ~strict:dsj1
          o_ineqn' in
      (*[* Format.printf
        "NumS.keep_nonredund-opti: a=%a@ keep=%b@ strict=%a@ +ineqn'=%a@\n%!"
        pr_subopti a res pr_ineq dsj1 pr_ineqn o_ineqn'; *]*)
      if not res
      then
        loop cho acc implicit (w1::w2::drop) optis
      else if not (strict_sat ~cmp_v ~cmp_w ineqs
                     ~strict:(mult !/(-1) o_case) o_ineqn)
      then (* dsj1 <= dsj2, so: *)
        let s =
          match direct_opti dsj_pair with
          | Some (_, _, s, _, _) -> s
          | None -> assert false in
        let dsj = if s then dsj2 else dsj1 in
        loop cho acc ((dsj, a)::implicit) drop optis
      else
        loop cho (a::acc) implicit drop optis in

  let opti_res, implicit_res, _ =
    List.fold_left
      (fun (acc, implicit, drop) cho ->
         let acc, implicit', drop =
           loop cho acc [] drop optis in
         let implicit, more = List.partition
             (fun (d, a) -> List.mem_assq d implicit)
             implicit' in
         map_append snd more acc, implicit, drop)
      (loop (List.hd opti_subopti) [] [] [] optis)
      (List.tl opti_subopti) in
  let implicit = List.map fst implicit_res in
  (*[* Format.printf
    "NumS.keep_nonredund-opti: opti_res=@ %a@\nimplicit=@ %a@\n%!"
    pr_optis opti_res pr_eqn implicit; *]*)
  opti_res, implicit

let ineqn_of_eqineq_w = concat_map
    (function
      | Leq_w w -> [w]
      | Eq_w w -> [w; mult !/(-1) w]
      | _ -> [])

(* Prune atoms implied by other atoms. *)
let prune_redund ~cmp_v ~cmp_w guard_cnj cnj =
  (*[* Format.printf "NumS.prune_redund:@\nguard=@ %a@\ncnj=@ %a@\n%!"
    pr_formula guard_cnj pr_formula cnj; *]*)
  (* First prune opti and subopti atoms, to avoid convoluted result
     instead of straightforward inequalities. *)
  let cnj = split_flatten ~cmp_v cnj in
  let g_eqn, g_ineqn, g_optis, g_suboptis as guard_cnj =
    split_flatten ~cmp_v guard_cnj in
  let cnj = prune_single_redund ~cmp_v
      (cnj_to_w_formula guard_cnj) (cnj_to_w_formula cnj) in
  let eqn, ineqn, optis, suboptis = split_formula cnj in
  (* The initial state against which to check redundancy -- mild pruning *)
  (*let init_ineqn = List.concat
      (map_append
         (fun (w1, w2) -> [w1; w2])
         (g_optis @ optis)
         [g_ineqn]) in*)
  (* More agressive -- split choices *)
  let init_ineqn = List.concat
      (map_append
         (fun w -> [w; mult !/(-1) w])
         (g_eqn @ eqn)
         [g_ineqn]) in
  (*[* Format.printf "NumS.prune_redund:@\ninit_ineqn=@ %a@\n%!"
    pr_ineqn init_ineqn; *]*)
  let init_ineqs = project ~cmp_v ~cmp_w VarMap.empty
      (List.sort cmp_w init_ineqn) in
  let init_ineqs_for_subopti = project ~cmp_v ~cmp_w init_ineqs
      (List.sort cmp_w ineqn) in
  let suboptis, more_ineqn =
    (* FIXME: change as in the opti case *)
    if suboptis = [] then [], []
    else
      keep_nonredund_subopti ~cmp_v ~cmp_w
        init_ineqs_for_subopti optis suboptis in
  let init_ineqs_for_opti = project ~cmp_v ~cmp_w init_ineqs_for_subopti
      (List.sort cmp_w more_ineqn) in
  (*[* Format.printf "NumS.prune_redund:@\ninit_ineqs_for_opti=@ %a@\n%!"
    pr_ineqs init_ineqs_for_opti; *]*)
  let optis, more_eqn =
    if optis = [] then [], []
    else
      keep_nonredund_opti ~cmp_v ~cmp_w
        init_ineqs_for_opti optis suboptis in
  let more_eq_ineqn =
    List.sort cmp_w (more_eqn @ List.map (mult !/(-1)) more_eqn) in
  let ineqs = project ~cmp_v ~cmp_w init_ineqs
      (more_ineqn @ more_eq_ineqn) in
  (* FIXME:  ~intro_cho_ineq:true? *)
  let opti_subopti = choices ~cmp_v ~intro_cho_ineq:true
      (g_optis @ optis) (g_suboptis @ suboptis) in
  (* Keep the union of atoms kept for each disjunct. *)
  let ineqn, _ = List.fold_left
      (fun (ineqn, cands) cho ->
         let o_ineqn = ineqn_of_eqineq_w cho in
         let ineqs = project ~cmp_v ~cmp_w ineqs o_ineqn in
         let _, more_ineqn, dropped =
           keep_nonredund ~cmp_v ~cmp_w ineqs cands in
         more_ineqn @ ineqn, dropped)
      ([], more_ineqn @ ineqn) opti_subopti in
  (* For now, optis and suboptis are filtered only in
     [prune_single_redund] at the beginning. *)
  (*[* Format.printf "NumS.prune_redund: result@\nineqn=@ %a@\n%!"
    pr_ineqn ineqn; *]*)
  cnj_to_num_formula (more_eqn @ eqn, ineqn, optis, suboptis)

let prune_redundant q ?localvs ?(guard=[]) ~initstep cnj =
  (*[* Format.printf
    "NumS.prune_redundant: initstep=%b localvs=%a@\ncnj=@ %a@\n%!"
    initstep pr_vars (match localvs with Some vs->vs|None->VarSet.empty)
    pr_formula cnj; *]*)
  let cmp_v = make_cmp q in
  let cmp_w (vars1,_,_) (vars2,_,_) =
    match vars1, vars2 with
    | [], [] -> 0
    | _, [] -> -1
    | [], _ -> 1
    | (v1,_)::_, (v2,_)::_ -> cmp_v v1 v2 in
  let more_guard, cnj =
    match localvs with
      | Some localvs when not initstep ->
        List.partition
          (fun c -> VarSet.is_empty (VarSet.inter localvs (fvs_atom c)))
          cnj
      | _ -> [], cnj in
  (*[* Format.printf
    "NumS.prune_redundant: guard=%a@ more_guard=%a@ res=%a@\n%!"
    pr_formula guard pr_formula more_guard pr_formula cnj; *]*)
  prune_redund ~cmp_v ~cmp_w (more_guard @ guard) cnj


let ptope_mem ptope w_key w_c =
  try w_c <=/ fst (Hashtbl.find ptope w_key)
  with Not_found -> false

(* Currently, [initstep] is only used to generate more -- redundant --
   [subopti] atoms. *)
let disjelim_aux q ~target_vs ~preserve ~bvs ~param_bvs
    ~guess ~initstep brs =
  let cmp_v = make_cmp q in
  (* Move preserved variables to the front of parameters but behind
     variables that should be eliminated. *)
  let cmp_v v1 v2 =
    let v1p = VarSet.mem v1 preserve and v2p = VarSet.mem v2 preserve
    and v1b = VarSet.mem v1 param_bvs and v2b = VarSet.mem v2 param_bvs in
    (* Preserved in front of parameters. *)
    (* v1p && v2p -> else branch *)
    if      v1p && not v2p && v2b then -1
    else if v1p && not (v2p || v2b) then 1
    else if not v1p && v1b && v2p then 1
    (* not v1p && v1b && not v2p && v2b -> else branch *)
    else if not v1p && v1b && not (v2p || v2b) then 1
    else if not (v1p || v1b) && (v2p || v2b) then -1
    (* not (v1p || v1b) && not (v2p || v2b) -> else branch *)
    else cmp_v v1 v2 in
  let cmp_w (vars1,cst1,_) (vars2,cst2,_) =
    match vars1, vars2 with
    | [], [] -> 0
    | _, [] -> -1
    | [], _ -> 1
    | (v1,_)::_, (v2,_)::_ -> cmp_v v1 v2 in
  (*[* Format.printf
    "NumS.disjelim_aux:@ target_vs=%a@ preserve=%a@ initstep=%b@\n%!"
    pr_vars target_vs pr_vars preserve initstep; *]*)
  let preserved =
    if !preserve_params then VarSet.union preserve param_bvs
    else if !preserve_only_target then target_vs
    else preserve in
  (* Case-split on [optis]. *)
  (* Discard empty disjuncts. *)
  let polytopes = concat_map
      (fun (prem, br) ->
         try
           let prem = flatten_formula ~cmp_v prem in
           (*[* Format.printf
             "NumS.disjelim: try polytope prem=@ %a@ br=@ %a@\n%!"
             pr_w_formula prem pr_formula br; *]*)
           let eqs, ineqs, optis, suboptis =
             solve ~cnj:br ~cmp_v ~cmp_w q.uni_v in
           (*[* Format.printf
             "NumS.disjelim: try polytope eqs=@ %a@\n\
              ineqs=@\n%a@\n%!"
             pr_w_subst eqs pr_ineqs ineqs; *]*)
           (* FIXME: [choices] now adds these inequalities, remove *)
           (* let opti_ineqs = flat2 optis in *)
           map_some
             (fun opti_subopti ->
                try
                  let o_eqn, o_ineqn, _, _ = split_formula opti_subopti in
                  (*[* Format.printf
                    "NumS.disjelim: opti_eqn=@ %a@ opti_ineqn=@ %a@\n%!"
                    pr_eqn o_eqn pr_ineqn o_ineqn; *]*)
                  let eqs, ineqs, _, _ =
                    solve ~eqs ~ineqs ~eqn:o_eqn
                      ~ineqn:o_ineqn
                      ~cmp_v ~cmp_w q.uni_v in
                  let cnj' = subst_w_formula ~cmp_v eqs prem in
                  (*[* Format.printf
                    "NumS.disjelim: polytope case@\neqs=@ %a@\n\
                     ineqs=@ %a@\nsubst prem=@ %a@\n%!"
                    pr_w_subst eqs pr_ineqs ineqs pr_w_formula cnj'; *]*)
                  let p_eqs, p_ineqs, p_optis, p_suboptis =
                    solve ~cnj' ~cmp_v ~cmp_w q.uni_v in
                  (*[* Format.printf
                    "NumS.disjelim: substituted p_ineqs=@\n%a@\n%!"
                    pr_ineqs p_ineqs; *]*)
                  (* Simplify downto preserved variables. *)
                  let eqs = VarMap.filter
                      (fun v _ -> VarSet.mem v preserved) eqs in
                  let ineqs = VarMap.filter
                      (fun v _ -> VarSet.mem v preserved) ineqs in
                  let p_eqs = VarMap.filter
                      (fun v _ -> VarSet.mem v preserved) p_eqs in
                  let p_ineqs = VarMap.filter
                      (fun v _ -> VarSet.mem v preserved) p_ineqs in
                  (*[* Format.printf
                    "NumS.disjelim: success opti_choice=@\n%a@\n%!"
                    pr_w_formula opti_subopti; *]*)
                  Some ((p_eqs, p_ineqs, p_optis, p_suboptis), (eqs, ineqs))
                with Terms.Contradiction _ ->
                  (*[* Format.printf
                    "NumS.disjelim: failed opti_choice=@\n%a@\n%!"
                    pr_w_formula opti_subopti; *]*)
                  None)
             (choices ~cmp_v ~intro_cho_ineq:true optis suboptis)
         with Terms.Contradiction _ -> [])
      brs in
  let verif_polytopes, polytopes = List.split polytopes in
  let validate common_eqn common_ineqn (w1, w2 as o) =
    (* let g = !guess_from_postcond && guess in *)
    let ineq = diff ~cmp_v w1 w2 in
    let n_ineq = mult !/(-1) ineq in
    let verif is_n is_p eqs ineqs optis suboptis =
      if is_p && not !excuse_case_by_common then true
      else
        let ineqn =
          (if is_n then n_ineq else ineq)::
            (if is_p then common_ineqn else []) in
        (*[* Format.printf
          "verif: n=%b prem=%b@ ineq=%a@ ineqs=%a@\n%!" is_n is_p
          pr_ineqn ineqn pr_ineqs ineqs; *]*)
        try
          ignore (solve ~eqs ~ineqs ~optis ~suboptis ~eqn:common_eqn ~ineqn
                    ~cmp_v ~cmp_w q.uni_v);
          true
        with Terms.Contradiction _ -> false in

    (*[* Format.printf
      "NumS.disjelim-validate: testing ineq=%a@ o=%a@\ncommon=%a@\n%!"
      pr_ineqn [ineq] pr_subopti o pr_ineqn common_ineqn; *]*)
    let prefer_left, weak_left, holds_left, fails_left =
      let pn, fn =
        List.fold_left2
          (fun (pn, fn) (p_eqs, p_ineqs, p_optis, p_suboptis) (eqs, ineqs) ->
             if
               not (verif false true p_eqs p_ineqs p_optis p_suboptis) ||
               verif false false eqs ineqs [] []
             then pn+1, fn else pn, fn+1)
          (0, 0) verif_polytopes polytopes in
      (*[* Format.printf "holds_left: pn=%d fn=%d@\n%!" pn fn; *]*)
      pn > fn, pn >= fn, fn = 0, pn = 0 in
    let prefer_right, weak_right, holds_right, fails_right =
      let pn, fn =
        List.fold_left2
        (fun (pn, fn) (p_eqs, p_ineqs, p_optis, p_suboptis) (eqs, ineqs) ->
             if
               not (verif true true p_eqs p_ineqs p_optis p_suboptis) ||
               verif true false eqs ineqs [] []
             then pn+1, fn else pn, fn+1)
        (0, 0) verif_polytopes polytopes in
      (*[* Format.printf "holds_right: pn=%d fn=%d@\n%!" pn fn; *]*)
      pn > fn, pn >= fn, fn = 0, pn = 0 in
    (*[* Format.printf
      "NumS.disjelim-validate: left=%b right=%b ineq=%a@\n%!"
      holds_left holds_right pr_ineqn [ineq];
     *]*)
    (* If w1 <= w2 and (w1 <= 0 \/ w2 <= 0), then w1 <= 0 *)
    if weak_left && weak_right then Some (Left o)
    else if holds_left then Some (Right (ineq, w1))
    else if holds_right then Some (Right (n_ineq, w2))
    else None in
  (* Now restore non-redundancy needed for convex hull algo. *)
  let faces, equations = split_map
      (fun (eqs, ineqs) ->
         let eq_classes = collect ~cmp_k:(compare_w ~cmp_v)
             (List.map (fun (v, rhs) -> rhs, v)
                (varmap_to_assoc eqs)) in
         let eq_sides = concat_map
             (fun (rhs, lvs) ->
                let ws =
                  rhs::List.map
                      (fun v -> [v, !/1], !/0, dummy_loc) lvs in
                (*[* Format.printf "eq_class:@ %a@\n%!" pr_eqn ws; *]*)
                let pairs = triangle ws in
                map_some (fun (w1, w2) ->
                    let w = diff ~cmp_v w1 w2 in
                    match w with
                    | [], _, _ -> None
                    | (v, k)::_, _, _ when k </ !/0 -> Some (mult !/(-1) w)
                    | _ -> Some w)
                  pairs)
             eq_classes in
         let ineqs = unsolve ineqs in
         let faces =
           ineqs @ eq_sides @ List.map (mult !/(-1)) eq_sides in
         let _, res, _ = keep_nonredund ~cmp_v ~cmp_w VarMap.empty faces in
         (*[* Format.printf
           "ptop-ineqs=%a@\nptop-faces=%a@\nptop-res=%a@\n%!"
           pr_ineqn ineqs pr_ineqn faces pr_ineqn res; *]*)
         res, wset_of_list eq_sides)
      polytopes in
  let common_faces =
    match faces with
    | hd::tl when !abductive_disjelim ->
      List.fold_left WSet.inter (wset_of_list hd) (List.map wset_of_list tl)
    | _ -> WSet.empty in
  let common_equations =
    match equations with
    | hd::tl -> WSet.elements (List.fold_left WSet.inter hd tl)
    | _ -> [] in
  (*[* Format.printf
    "NumS.disjelim: polytope-ineqs=@\n%a@\nfaces=@\n%a@\nequations=@\n%a@\n%!"
    (pr_line_list "| " pr_ineqs) (List.map snd polytopes)
    (pr_line_list "| " pr_ineqn) faces
    (pr_line_list "| " pr_eqn) (List.map WSet.elements equations); *]*)
  let ptopes =
    if !abductive_disjelim
    then List.map2
        (fun ptope ptope_faces ->
           let ptope_specific = List.filter
               (fun w -> not (WSet.mem w common_faces)) ptope_faces in
           let specif_vs = List.fold_left
               (fun vs w -> VarSet.union vs (fvs_w w))
               VarSet.empty ptope_specific in
           let common_vs =
             VarSet.diff (vars_of_map fvs_w ptope_faces) specif_vs in
           (*[* Format.printf
             "NumS.disjelim: polytope specif_vs=%a;@ common_vs=%a;@ \
              faces=@\n%a@\n%!"
             pr_vars specif_vs pr_vars common_vs pr_ineqn ptope_faces; *]*)
           specif_vs, common_vs, ptope)
        polytopes faces
    else List.map
        (fun ptope -> VarSet.empty, VarSet.empty, ptope) polytopes in
  (* Check if a polytope face is also a face of resulting convex hull
     -- its outside does not contain any piece of any polytope (that
     contains all its variables, if abductive_disjelim is on). *)
  let check prefer face =
    let ineqn = [mult !/(-1) face] in
    let face_vs = fvs_w face in
    let res = List.for_all
        (fun (specif_vs, common_vs, (eqs, ineqs)) ->
           (* If intersects both specif_vs and common_vs, accept without
              checking. *)
           (!abductive_disjelim && prefer &&
            not (VarSet.is_empty (VarSet.diff face_vs specif_vs)) &&
            not (VarSet.is_empty (VarSet.diff face_vs common_vs))) ||
           try ignore
                 (solve ~strict:true ~eqs ~ineqs ~ineqn ~cmp_v ~cmp_w q.uni_v);
             false
           with Terms.Contradiction _ -> true)
        ptopes in
    (*[* Format.printf "NumS.disjelim-check: res=%b face=%a@\n%!"
      res pr_w face; *]*)
    res in
  let selected =
    List.map (List.partition (check true)) faces in
  (*[* Format.printf "NumS.disjelim: selected=%a@\n%!"
    (pr_line_list "| " pr_ineqn) (List.map fst selected); *]*)
  let ridges : (w * w) list = concat_map
      (fun (sel, ptope) ->
         (*[* Format.printf
           "NumS.disjelim: ridges between sel=%a;@ ptope=%a@\n%!"
           pr_ineqn sel pr_ineqn ptope; *]*)
         concat_map (fun p -> List.map (fun s->s, p) sel) ptope)
      selected in
  let angle i j = i2f (i+1) /. i2f (j+1) in
  let cands = List.map
      (fun (s, p) ->
         let pre_size = w_size s + w_size p in
         let l = Array.init
             (!disjelim_rotations + 1) (fun i ->
                 if i <= 1 then [||]
                 else Array.init (i-1) (fun j ->
                     (*[* Format.printf
                       "NumS.disjelim: ridge j+1=%d i=%d angle=%.2f@ \
                        cand=%a@\n%!" (j+1) i (angle j i) pr_w
                       (sum_w ~cmp_v (mult !/(j+1) s) (mult !/i p)); *]*)
                     angle (j+1) i,
                     (pre_size,
                      sum_w ~cmp_v (mult !/(j+1) s) (mult !/i p)))) in
         let r = Array.init
             (!disjelim_rotations + 1) (fun i ->
                 if i <= 1 then [||]
                 else Array.init (i-1) (fun j ->
                     (*[* Format.printf
                       "NumS.disjelim: ridge i=%d j+1=%d angle=%.2f@ \
                        cand=%a@\n%!" i (j+1) (angle i j) pr_w
                       (sum_w ~cmp_v (mult !/i s) (mult !/(j+1) p)); *]*)
                     angle i (j+1),
                     (pre_size,
                      sum_w ~cmp_v (mult !/i s) (mult !/(j+1) p)))) in
         (*[* Format.printf
           "NumS.disjelim: cands for ridge@ s=%a;@ p=%a@\n%a@\n%!"
           pr_w s pr_w p pr_ineqn
           (List.map (snd % snd)
              ((1., (pre_size, sum_w ~cmp_v s p)) ::
                 Array.to_list (Array.concat (Array.to_list l)) @
                 Array.to_list (Array.concat (Array.to_list r)))); *]*)
         (1., (pre_size, sum_w ~cmp_v s p)) ::
           Array.to_list (Array.concat (Array.to_list l)) @
           Array.to_list (Array.concat (Array.to_list r)))
      ridges in
  let cands = List.map (fun angles ->
      List.map snd
        (* Select the smallest value -- less [s], more [p] in [cands] *)
        (List.sort (fun (a,_) (b,_) -> compare a b) angles)) cands in
  let result = concat_map fst selected in
  let check_res (pre_size, face) = check (w_size face < pre_size) face in
  let result = map_some
      (fun cands ->
         try Some (snd (List.find check_res cands))
         with Not_found -> None) cands
               @ result in (* *)
  let sort_w (vars, cst, loc) =
    let vars = map_reduce ~cmp_k:cmp_v (+/) (!/0) vars in
    let vars =
      List.filter (fun (_,k) -> k <>/ !/0) vars in
    vars, cst, loc in
  let result = List.map sort_w result in
  (*[* Format.printf "NumS.disjelim: result=%a@\n%!"
    pr_ineqn result; *]*)
  let rec idemp ineqn = function
    | e1::(e2::_ as tl) when (* nonq_cmp_w e1 e2 = 0 *)
        equal_w ~cmp_v e1 e2 -> idemp ineqn tl
    | e::tl when List.exists (fun w -> zero_p (sum_w ~cmp_v e w)) tl ->
      (* Two inequalities forming an equation. *)
      idemp ineqn
        (List.filter (fun w -> not (zero_p (sum_w ~cmp_v e w))) tl)
    | e::tl -> idemp (e::ineqn) tl
    | [] -> ineqn in
  (* Rather than using convex hull, we get the common equations directly. *)
  let ineqn = idemp [] (List.sort nonq_cmp_w result) in
  (*[* Format.printf "NumS.disjelim: solution@\neqn=%a@\nineqn=%a@\n%!"
    pr_eqn common_equations pr_ineqn ineqn; *]*)
  let check_redund face ptope =
    (*[* Format.printf
      "NumS.disjelim-check_redund: face=%a@\nptope=%a@\n%!" pr_w face
      pr_ineqn ptope; *]*)
    let eqs, ineqs, _, _ =
      solve ~eqn:common_equations ~ineqn:ptope ~cmp_v ~cmp_w q.uni_v in
    let ineqn = [mult !/(-1) face] in
    (*[* Format.printf
      "NumS.disjelim-check_redund: neg-face %a \
       solved ptope@\neqs=%a@\nineqs=%a@\n%!"
      pr_ineqn ineqn pr_w_subst eqs pr_ineqs ineqs; *]*)
    try ignore
          (solve ~strict:true ~eqs ~ineqs ~ineqn ~cmp_v ~cmp_w q.uni_v);
      (*[* Format.printf
        "NumS.disjelim-check_redund: false face=%a@\n%!" pr_w face; *]*)
      false
    with Terms.Contradiction _ ->
      (*[* Format.printf
        "NumS.disjelim-check_redund: true face=%a@\n%!" pr_w face; *]*)
      true in
  let rec nonredundant p1 = function
    | face::p2 ->
      if check_redund face (p1 @ p2) then nonredundant p1 p2
      else nonredundant (face::p1) p2
    | [] -> p1 in
  let ineqn = nonredundant [] ineqn in
  (*[* Format.printf "NumS.disjelim: nonredundant@\nineqn=%a@\n%!"
    pr_ineqn ineqn; *]*)
  (* Generating opti atoms. *)
  let brs_eqs = List.map
      (fun (_, _, (eqs, _)) ->
         let eqn = eqn_of_eqs eqs in
         let eqn = eqn @ List.map (mult !/(-1)) eqn in
         ineq_transitive_cl ~cmp_v (List.map expand_sides_cst eqn))
      ptopes in
  (*[* let pr_hasheqs ppf h =
    let eqs = Hashtbl.fold
        (fun (lhs, rhs) (cst, lc) eqs ->
           Eq (Add [lhs; expand_cst cst], rhs, lc)::eqs) h [] in
    pr_formula ppf eqs in
    Format.printf "NumS.disjelim: brs_eqs=@\n%a@\n%!"
    (pr_line_list "| " pr_hasheqs) brs_eqs; *]*)
  (* Transitive closure of resulting equations and inequalities. *)
  let result = List.map expand_sides_cst result in
  let result = ineq_transitive_cl ~cmp_v result in
  let result = Hashtbl.fold
      (fun w_key (cst, loc) cnj -> (w_key, cst, loc)::cnj) result [] in
  let opt_cands = map_some
      (fun ((w_lhs, w_rhs as w_key), w_cst, w_lc as w) ->
         let inds = mapi_some
             (fun i eqs ->
                try
                  let e_cst, e_lc = Hashtbl.find eqs w_key in
                  if e_cst = w_cst then Some i else None
                with Not_found -> None)
             brs_eqs in
         if inds=[] then None
         else Some (w, ints_of_list inds))
      result in
  (*[* let pr_opt_cand ppf (((w_lhs, w_rhs), w_cst, w_lc), inds) =
    Format.fprintf ppf "%a:@ %s" pr_atom (Eq (w_lhs, w_rhs, w_lc))
      (String.concat "," (List.map string_of_int
                            (Ints.elements inds))) in
    Format.printf "NumS.disjelim: opt_cands=@\n%a@\n%!"
    (pr_line_list "| " pr_opt_cand) opt_cands; *]*)  
  let allbrs =
    ints_of_list (List.mapi (fun i _ -> i) brs_eqs) in
  let optis = map_some
      (fun ((w1,inds1),(w2,inds2)) ->
         if Ints.is_empty (Ints.diff allbrs (Ints.union inds1 inds2))
         then Some (w1, w2) else None)
      (triangle opt_cands) in
  (*[* let unexpand_opti (dsj1, dsj2) =
    unexpand_sides_cst ~cmp_v dsj1, unexpand_sides_cst ~cmp_v dsj2 in
  Format.printf "NumS.disjelim: initial optis=@\n%a@\n%!"
    pr_optis (List.map unexpand_opti optis); *]*)
  let optis = List.map
      (fun (dsj1, dsj2) ->
         unexpand_sides_cst ~cmp_v dsj1,
         unexpand_sides_cst ~cmp_v dsj2)
      optis in
  (* TODO: redundant conversion, remove [unexpand_sides] and
     [expand_opti] and implement [is_directed]? *)
  let optis =
    map_some (fun (_, ovs, _, w1, w2) ->
        if !primary_only_target &&
           VarSet.is_empty (VarSet.inter ovs target_vs)
        then None
        else Some (w1, w2))
      (map_some direct_opti optis) in
  (*[* Format.printf "NumS.disjelim: optis=@\n%a@\n%!"
    pr_optis optis; *]*)
  let optis, opt_eqn =
    partition_map_some
        (validate common_equations ineqn) optis in
  let abd_eqn, more_eqn = List.split opt_eqn in
  (*[* Format.printf "NumS.disjelim: case-filtered optis=@\n%a@\n%!"
    pr_optis optis; *]*)
  let optis =
    List.map snd
      (List.sort (fun (x, _) (y, _) -> y - x)
         (List.map
            (fun (w1, w2 as c) ->
               w_complexity2 bvs w1 + w_complexity2 bvs w2, c)
            optis)) in
  let optis = list_take !max_opti_postcond optis in
  (*[* Format.printf "NumS.disjelim: filtered optis=@\n%a@\n%!"
    pr_optis optis; *]*)
  (* Generating subopti atoms. *)
  let ptopes_ineqs = List.map
      (fun ptope ->
         let p_ineqs = List.map expand_sides_cst ptope in
         ineq_transitive_cl ~cmp_v p_ineqs)
      faces in
  let add_subopti_cand c suboptis =
    (*[*
      let wf_of_choice = function
      | Left (w,_,_)->Leq_w w
      | Right (w1,w2,_,_,_) -> Subopti_w (w1,w2) in
      Format.printf "add_subopti: c=%a@\nsuboptis=%a@\n%!"
      pr_w_atom (wf_of_choice c)
      pr_w_formula (List.map wf_of_choice suboptis); *]*)      
    match c with
    | Left (([], _, _), _, _) -> suboptis
    | Left (([_], _, _), _, _)
      when initstep || !subopti_of_cst = `No_sides -> suboptis
    | Left (([_, s], _, _), _, _)
      when !subopti_of_cst = `Left_side && s >=/ !/0 -> suboptis
    | Left (w, _, _) ->
      if List.exists
          (function
            | Left (w2, _, _) ->
              atomic_impl ~cmp_v (Leq_w w2) (Leq_w w)
            | _ -> false) suboptis
      then suboptis
      else
        c::List.filter
            (function
              | Left (w2, _, _) ->
                not (atomic_impl ~cmp_v (Leq_w w) (Leq_w w2))
              | Right (w2, w3, _, _, _) ->
                not (atomic_impl ~cmp_v (Leq_w w) (Subopti_w (w2, w3))))
            suboptis
    | Right (([_], _, _), _, _, _, _)
      when initstep || !subopti_of_cst = `No_sides -> suboptis
    | Right (_, ([_], _, _), _, _, _)
      when initstep || !subopti_of_cst = `No_sides -> suboptis
    | Right (([_, s], _, _), _, _, _, _)
      when !subopti_of_cst = `Left_side && s >=/ !/0 -> suboptis
    | Right (_, ([_, s], _, _), _, _, _)
      when !subopti_of_cst = `Left_side && s >=/ !/0 -> suboptis
    | Right (w1, w2, _, _, _) ->
      if List.exists
          (function
            | Left (w3, _, _) ->
              atomic_impl ~cmp_v (Leq_w w3) (Subopti_w (w1, w2))
            | Right (w3, w4, _, _, _) ->
              atomic_impl ~cmp_v (Subopti_w (w3, w4)) (Subopti_w (w1, w2)))
          suboptis
      then suboptis
      else
        c::List.filter
            (function
              | Left _ -> true
              | Right (w3, w4, _, _, _) ->
                not (atomic_impl ~cmp_v (Subopti_w (w1, w2))
                       (Subopti_w (w3, w4))))
            suboptis in               
  let suboptis =
    if ptopes_ineqs = [] then []
    else Hashtbl.fold
        (fun w_key (cst, lc) suboptis ->
           add_subopti_cand
             (Left (unexpand_sides_cst ~cmp_v (w_key, cst, lc),
                    w_key, lc))
             suboptis)
        (List.hd ptopes_ineqs) [] in
  let suboptis =
    if ptopes_ineqs = [] then []
    else
      List.fold_left
        (fun suboptis ptope ->
           (*[* let left, right = partition_choice suboptis in
             let left = List.map fst3 left in
             let right = List.map
               (fun (w1, w2, _, _, lc) -> w1, w2) right in
             Format.printf
             "NumS.disjelim: subopti step@\nleft=%a;@ right=%a@\nptope=%a@\n%!"
             pr_ineqn left pr_suboptis right
             (pr_transitive_cl ~cmp_v) ptope; *]*)
           List.fold_left (fun suboptis ->
               function
               | Left (_, w_c, _ as w, w_key, lc) as cand ->
                 if ptope_mem ptope w_key w_c then cand::suboptis
                 else Hashtbl.fold
                     (fun w2_key (cst2, lc2) suboptis ->
                        let w2 =
                          unexpand_sides_cst ~cmp_v (w2_key, cst2, lc2) in
                        match direct_opti (w, w2) with
                        | Some (_, ovs, _, _, _)
                          when not (!primary_only_target &&
                                    VarSet.is_empty
                                      (VarSet.inter ovs target_vs)) ->
                          (*[* Format.printf
                            "subopti: w1=%a;@ w2=%a@\n%!"
                            pr_w w pr_w w2; *]*)
                          (* Pick the weaker inequality. *)
                          (match diff ~cmp_v w w2 with
                           | [], cst, _ when cst <=/ !/0 ->
                             add_subopti_cand (Left (w, w_key, lc2)) suboptis
                           | [], cst, _ ->
                             add_subopti_cand (Left (w2, w2_key, lc)) suboptis
                           | _ ->
                             add_subopti_cand
                               (Right (w, w2, w_key, w2_key,
                                       loc_union lc lc2))
                               suboptis)
                        | _ -> suboptis) ptope suboptis
               | Right ((_, w1_c, _ as w1),
                        (_, w2_c, _ as w2), w1_key, w2_key, lc) as cand ->
                 let aux w w_key w' w'_key
                     w3_key (cst3, lc3) suboptis =
                   let w3 =
                     unexpand_sides_cst ~cmp_v (w3_key, cst3, lc3) in
                   match direct_opti (w, w3) with
                   | Some (_, ovs, _, _, _)
                     when not (!primary_only_target &&
                               VarSet.is_empty (VarSet.inter ovs target_vs)) ->
                     (*[* Format.printf
                       "subopti-aux: w=%a;@ w'=%a@\n%!"
                       pr_w w pr_w w'; *]*)
                     (* Pick the weaker inequality. *)
                     (match diff ~cmp_v w w3 with
                      | [], cst, _ when cst <=/ !/0 ->
                        add_subopti_cand
                          (Right (w, w', w_key, w'_key, lc3)) suboptis
                      | [], cst, _ ->
                        add_subopti_cand
                          (Right (w3, w', w3_key, w'_key, lc)) suboptis
                      | _ -> suboptis)
                   | _ -> suboptis in
                 if ptope_mem ptope w1_key w1_c ||
                    ptope_mem ptope w2_key w2_c
                 then cand::suboptis
                 else Hashtbl.fold (aux w1 w1_key w2 w2_key) ptope
                     (Hashtbl.fold (aux w2 w2_key w1 w1_key) ptope
                        suboptis))
             [] suboptis)
        suboptis (List.tl ptopes_ineqs) in
  let suboptis = map_some
      (function
        | Left _ -> None
        | Right (w1, w2, w1_key, w2_key, lc) -> Some (w1, w2))
      suboptis in
  (*[* Format.printf "NumS.disjelim: initial suboptis=@\n%a@\n%!"
    pr_suboptis suboptis; *]*)
  let suboptis, opt_ineqn =
    partition_map_some
        (validate common_equations ineqn) suboptis in
  (*[* Format.printf "NumS.disjelim: case-filtered suboptis=@\n%a@\n%!"
    pr_suboptis suboptis; *]*)  
  let abd_ineqn, more_ineqn = List.split opt_ineqn in
  let suboptis =
    List.map snd
      (List.sort (fun (x, _) (y, _) -> y - x)
         (List.map
            (fun (w1, w2 as c) ->
               w_complexity2 bvs w1 + w_complexity2 bvs w2, c)
            suboptis)) in
  let suboptis = list_take !max_subopti_postcond suboptis in
  (*[* Format.printf "NumS.disjelim: filtered suboptis=@\n%a@\n%!"
    pr_suboptis suboptis; *]*)
  List.map (expand_atom true) abd_eqn @
    List.map (expand_atom false) abd_ineqn,
  List.map expand_opti optis @
    List.map expand_subopti suboptis @
    List.map (expand_atom true) (more_eqn @ common_equations)
  @ List.map (expand_atom false) (more_ineqn @ ineqn),
  List.map (eqineq_to_num_formula % un_ans) polytopes

let cleanup ~preserve cnj =
  List.filter
    (fun c ->
       VarSet.exists (fun p -> VarSet.mem p preserve) (fvs_atom c))
    cnj

let disjelim q ~target_vs ~preserve ~bvs ~param_bvs ~guess ~initstep brs =
  (*[* Format.printf "NumS.disjelim: preserve=%a #brs=%d@ params=%a@ bvs=%a\
                       @\ninit brs=@\n%a@\n%!"
    pr_vars preserve (List.length brs) pr_vars param_bvs pr_vars bvs
    (pr_line_list "| " pr_br2) brs; *]*)
  match brs with
  | [] -> assert false
  | [br] ->
    let abd_cnj, cnj, dsj_brs =
      disjelim_aux q ~target_vs ~preserve ~bvs ~param_bvs
         ~guess ~initstep [br; br] in
    [], abd_cnj, cleanup ~preserve cnj, dsj_brs
  | _ ->
    let abd_cnj, cnj, dsj_brs =
      disjelim_aux q ~target_vs ~preserve ~bvs ~param_bvs
         ~guess ~initstep brs in
    [], abd_cnj, cleanup ~preserve cnj, dsj_brs

let simplify q ?(keepvs=VarSet.empty) ?localvs ?(guard=[]) elimvs cnj =
  (*[* Format.printf "NumS.simplify: elimvs=%s;@\ncnj=@ %a@\n%!"
    (String.concat "," (List.map var_str (VarSet.elements elimvs)))
    pr_formula cnj; *]*)
  (* FIXME: does [elimvs] give correct order of vars? Write test. *)
  let cmp_v = make_cmp q in
  let cmp_w (vars1,_,_) (vars2,_,_) =
    match vars1, vars2 with
    | [], [] -> 0
    | _, [] -> -1
    | [], _ -> 1
    | (v1,_)::_, (v2,_)::_ -> cmp_v v1 v2 in
  let eqs, ineqs, optis, suboptis =
    solve ~cnj ~cmp_v ~cmp_w q.uni_v in
  let eqs =
    VarMap.filter (fun v _ ->
        VarSet.mem v keepvs || not (VarSet.mem v elimvs)) eqs in
  (*let ineqs =
    List.filter (fun (v,_) ->
    VarSet.mem v keepvs || not (VarSet.mem v elimvs)) ineqs in*)
  let ans = ans_to_num_formula (eqs, ineqs, optis, suboptis) in
  let ans =
    match localvs with
    | None -> prune_redund ~cmp_v ~cmp_w guard ans
    | Some localvs ->                   (* FIXME: when not initstep *)
      let more_guard, res = List.partition
          (fun c -> VarSet.is_empty (VarSet.inter localvs (fvs_atom c)))
          ans in
      prune_redund ~cmp_v ~cmp_w (more_guard @ guard) res in
  let vs = VarSet.inter elimvs (fvs_formula ans) in
  (*[* Format.printf "NumS.simplify:@\nres=%a@\n%!" pr_formula ans; *]*)
  VarSet.elements vs, ans

let converge q ?localvs ?(guard=[]) ~initstep cnj1 cnj2 =
  (*[* Format.printf
    "NumS.converge: initstep=%b localvs=%a@\ncnj1=@ %a@\ncnj2=@ %a@\n%!"
    initstep pr_vars (match localvs with Some vs->vs|None->VarSet.empty)
    pr_formula cnj1 pr_formula cnj2; *]*)
  let cmp_v = make_cmp q in
  let cmp_w (vars1,_,_) (vars2,_,_) =
    match vars1, vars2 with
    | [], [] -> 0
    | _, [] -> -1
    | [], _ -> 1
    | (v1,_)::_, (v2,_)::_ -> cmp_v v1 v2 in
  (*let params = map_opt params
    (List.fold_left
    (fun acc (_,ps) -> VarSet.union acc ps) VarSet.empty) in*)
  let eqs1, ineqs1, optis1, suboptis1 =
    solve ~cnj:cnj1 ~cmp_v ~cmp_w q.uni_v in
  let eqs2, ineqs2, optis2, suboptis2 =
    solve ~cnj:cnj2 ~cmp_v ~cmp_w q.uni_v in
  let ans1 = ans_to_num_formula (eqs1, ineqs1, optis1, suboptis1) in
  let ans2 = ans_to_num_formula (eqs2, ineqs2, optis2, suboptis2) in
  let eq2ineq = function
    | Eq (t1, t2, lc) -> [Leq (t1, t2, lc); Leq (t2, t1, lc)]
    | a -> [a] in
  let ans1 = concat_map eq2ineq ans1
  and ans2 = concat_map eq2ineq ans2 in
  (* FIXME: Actually, include transitivity! *)
  (* FIXME: where are equations recovered? *)
  let res = formula_inter (cnj1 @ ans1) (cnj2 @ ans2) in
  let more_guard, res =
    match localvs with
      | Some localvs when not initstep ->
        List.partition
          (fun c -> VarSet.is_empty (VarSet.inter localvs (fvs_atom c)))
          res
      | _ -> [], res in
  (*[* Format.printf "NumS.converge:@\nans1=@ %a@\nans2=@ %a@\nres=@ %a@\n%!"
    pr_formula ans1 pr_formula ans2 pr_formula res; *]*)
  prune_redund ~cmp_v ~cmp_w (more_guard @ guard) res


type state = w_subst * ineqs * optis * suboptis
let empty_state = VarMap.empty, VarMap.empty, [], []

let formula_of_state (eqs, ineqs, optis, suboptis) =
  let cnj = expand_eqineqs eqs ineqs in
  map_append (fun ((_,_,lc as w1), w2) ->
      let t1 = expand_w w1 and t2 = expand_w w2 in
      Opti (t1, t2, lc)) optis
    (map_append (fun ((_,_,lc as w1), w2) ->
      let t1 = expand_w w1 and t2 = expand_w w2 in
      Subopti (t1, t2, lc))
    suboptis cnj)

let satisfiable ?state cnj =
  let eqs, ineqs, optis, suboptis = match state with
    | None -> None, None, None, None
    | Some (eqs, ineqs, optis, suboptis) ->
      Some eqs, Some ineqs, Some optis, Some suboptis in
  let uni_v _ = false in
  (* The same order as in make_cmp *)
  let cmp_v v1 v2 = compare v2 v1 in
  let cmp_w (vars1,_,_) (vars2,_,_) =
    match vars1, vars2 with
    | [], [] -> 0
    | _, [] -> -1
    | [], _ -> 1
    | (v1,_)::_, (v2,_)::_ -> cmp_v v1 v2 in
  try
    let eqs, ineqs, optis, suboptis =
      solve ?eqs ?ineqs ?optis ?suboptis ~cnj ~cmp_v ~cmp_w uni_v in
    Right (eqs, ineqs, optis, suboptis)
  with Terms.Contradiction _ as e -> Left e

let satisfiable_exn ?state cnj =
  let eqs, ineqs, optis, suboptis = match state with
    | None -> None, None, None, None
    | Some (eqs, ineqs, optis, suboptis) ->
      Some eqs, Some ineqs, Some optis, Some suboptis in
  let uni_v _ = false in
  (* The same order as in make_cmp *)
  let cmp_v v1 v2 = compare v2 v1 in
  let cmp_w (vars1,_,_) (vars2,_,_) =
    match vars1, vars2 with
    | [], [] -> 0
    | _, [] -> -1
    | [], _ -> 1
    | (v1,_)::_, (v2,_)::_ -> cmp_v v1 v2 in
  let eqs, ineqs, optis, suboptis =
    solve ?eqs ?ineqs ?optis ?suboptis ~cnj ~cmp_v ~cmp_w uni_v in
  eqs, ineqs, optis, suboptis

let implies_cnj (eqs, ineqs, optis, suboptis) cnj =
  let uni_v _ = false in
  (* The same order as in make_cmp *)
  let cmp_v v1 v2 = compare v2 v1 in
  let cmp_w (vars1,_,_) (vars2,_,_) =
    match vars1, vars2 with
    | [], [] -> 0
    | _, [] -> -1
    | [], _ -> 1
    | (v1,_)::_, (v2,_)::_ -> cmp_v v1 v2 in
  let c_eqn, c_ineqn, c_optis, c_suboptis = split_flatten ~cmp_v cnj in
  implies ~cmp_v ~cmp_w uni_v eqs ineqs optis suboptis c_eqn c_ineqn
    c_optis c_suboptis 

let holds q avs (eqs, ineqs, optis, suboptis : state) cnj : state =
  let cmp_v = make_cmp q in
  let cmp_w (vars1,_,_) (vars2,_,_) =
    match vars1, vars2 with
    | [], [] -> 0
    | _, [] -> -1
    | [], _ -> 1
    | (v1,_)::_, (v2,_)::_ -> cmp_v v1 v2 in
  solve ~use_quants:(Fail_viol avs)
      ~eqs ~ineqs ~optis ~suboptis ~cnj ~cmp_v ~cmp_w q.uni_v

let abductive_holds q ~bvs (eqs, ineqs, optis, suboptis : state) cnj =
  let cmp_v = make_cmp q in
  let cmp_w (vars1,_,_) (vars2,_,_) =
    match vars1, vars2 with
    | [], [] -> 0
    | _, [] -> -1
    | [], _ -> 1
    | (v1,_)::_, (v2,_)::_ -> cmp_v v1 v2 in
  let state, _, _, _, quant_viol_cnj =
    solve_get_eqn ~use_quants:(Store_viol bvs)
      ~eqs ~ineqs ~optis ~suboptis ~cnj ~cmp_v ~cmp_w q.uni_v in
  state, expand_formula quant_viol_cnj

let negation_elim q ~bvs ~verif_cns neg_cns =
  (*[* Format.printf "NumS.negation_elim:@\nneg_cns=@ %a@\n%!"
    (pr_line_list "| " pr_formula) (List.map fst neg_cns); *]*)
  (*[* Format.printf "verif_cns=@ %a@\n%!"
    (pr_line_list "| " pr_state) verif_cns; *]*)
  let validated_num d =
    List.fold_left
      (fun count state ->
         try ignore (satisfiable_exn ~state d); count
         with Terms.Contradiction _ -> count + 1)
      0 verif_cns in
  let cmp_v = make_cmp q in
  let cmp_w (vars1,_,_) (vars2,_,_) =
    match vars1, vars2 with
    | [], [] -> 0
    | _, [] -> -1
    | [], _ -> 1
    | (v1,_)::_, (v2,_)::_ -> cmp_v v1 v2 in
  let cmp_v v1 v2 =
    let c1 = q.uni_v v1 && not (VarSet.mem v1 bvs)
    and c2 = q.uni_v v2 && not (VarSet.mem v2 bvs) in
    if c1 && c2 then cmp_v v1 v2
    else if c1 then -1
    else if c2 then 1
    else cmp_v v1 v2 in
  let uni_v v = q.uni_v v && not (VarSet.mem v bvs) in
  let revert cnj =
    let rev_sb, _, _, _ =
      (* Do not use quantifiers. *)
      solve ~cnj ~cmp_v ~cmp_w q.uni_v in
    VarMap.map expand_w
      (VarMap.filter (fun v _ -> uni_v v) rev_sb) in
  (* The formula will be conjoined to the branches. Note that the
          branch will be non-recursive.  *)
  let res = concat_map
      (fun (cnj, loc) ->
         let rev_sb = revert cnj in
         let cnj = List.map (nsubst_atom rev_sb) cnj in
         (*[* Format.printf
           "NumS.negation_elim: rev_sb=%a@\nneg-cnj=%a@\n%!"
           pr_nsubst rev_sb pr_formula cnj; *]*)
         let guard_cnj, cnj = List.partition
             (fun a -> VarSet.exists uni_v (fvs_atom a)) cnj in
         let cnj = prune_redund ~cmp_v ~cmp_w guard_cnj cnj in
         let d, _, _ = List.fold_left
             (fun (sel, selN, selS as acc) c ->
                (*[* Format.printf "NumS.negation_elim: try c=@ %a@\n%!"
                  pr_atom c; *]*)
                match c with
                  | Leq (lhs, rhs, lc) ->
                    let w = NumDefs.diff lhs rhs in
                    let k = denom w in
                    let lhs = NumDefs.scale_term ~-k 1 w in
                    let d = [Leq (lhs, Cst (-1, 1), loc)] in
                    let dN = validated_num d
                    and dS = formula_size d in
                    if dN < selN ||
                       dN=selN && dS > selS
                    then (d, dN, dS) else acc
                  | Eq (lhs, rhs, lc) ->
                    let w = NumDefs.diff lhs rhs in
                    let k = denom w in
                    let lhs1 = NumDefs.scale_term ~-k 1 w in
                    let d1 = [Leq (lhs1, Cst (-1, 1), loc)] in
                    let d1N = validated_num d1
                    and d1S = formula_size d1 in
                    let _, selN, selS as acc =
                      if d1N < selN ||
                       d1N=selN && d1S > selS
                      then (d1, d1N, d1S) else acc in
                    if d1N=0 then acc
                    else
                      let lhs2 = NumDefs.scale_term k 1 w in
                      let d2 = [Leq (lhs2, Cst (-1, 1), loc)] in
                      let d2N = validated_num d2
                      and d2S = formula_size d2 in
                      if d2N < selN ||
                       d2N=selN && d2S > selS
                      then (d2, d2N, d2S) else acc
                  | Opti _ -> acc
                  | Subopti (t1, t2, lc) ->
                    let k1 = denom t1 in
                    let lhs1 = NumDefs.scale_term ~-k1 1 t1 in
                    let k2 = denom t2 in
                    let lhs2 = NumDefs.scale_term ~-k2 1 t2 in
                    let d =
                      [Leq (lhs1, Cst (-1, 1), loc);
                       Leq (lhs2, Cst (-1, 1), loc)] in
                    let dN = validated_num d
                    and dS = formula_size d in
                    if dN < selN ||
                       dN=selN && dS > selS
                    then (d, dN, dS) else acc)
             ([], List.length verif_cns, 0) cnj in
         (*[* Format.printf "NumS.negation_elim: selected d=@ %a@\n%!"
           pr_formula d; *]*)
         d)
      neg_cns in
  (*[* Format.printf "NumS.negation_elim:@\nres=@ %a@\n%!"
    pr_formula res; *]*)
  res

type subst = (term * loc) VarMap.t

let subst_num_formula sb phi =
  if VarMap.is_empty sb then phi
  else List.map (subst_atom (fun _ _ x->x) sb) phi

let subst_formula sb phi =
  if VarMap.is_empty sb then phi
  else List.map (subst_atom Terms.num_v_unbox sb) phi

(* match q.cmp_v v1 v2 with
  | Left_of -> 1
  | Right_of -> -1
  | Same_params -> compare v2 v1
  | Same_quant -> compare v2 v1
 *)
let separate_subst_aux q ~no_csts ~keep ~bvs ~apply cnj =
  let cmp_v = make_cmp q in
  let cmp_v v1 v2 =
    let c1 = VarSet.mem v1 keep and c2 = VarSet.mem v2 keep in
    if c1 && c2 then cmp_v v1 v2
    else if c1 then 1
    else if c2 then -1
    else cmp_v v1 v2 in
  let cmp_w (vars1,_,_) (vars2,_,_) =
    match vars1, vars2 with
    | [], [] -> 0
    | _, [] -> -1
    | [], _ -> 1
    | (v1,_)::_, (v2,_)::_ -> cmp_v v1 v2 in
  let eqs, _, _, _ =
    solve ~cnj ~cmp_v ~cmp_w q.uni_v in
  let c_eqn, eqs =
    if no_csts
    then partition_map
        (function
          | v, ([], cst, lc) -> Left (cst, (v, lc))
          | eq -> Right eq)
        (varmap_to_assoc eqs)
    else [], varmap_to_assoc eqs in
  let c_eqn =
    collect ~cmp_k:Num.compare_num c_eqn in
  let leq (v1, _) (v2, _) = cmp_v v1 v2 >= 0 in
  let c_eqs =
    concat_map
      (fun (cst, vars) ->
         let ov, olc = maximum ~leq vars in
         let o = [ov, !/1] in
         map_some
           (fun (cv, lc) ->
              if cv=ov then None else Some (cv, (o, !/0, lc)))
           vars
         @ [ov, ([], cst, olc)])
      c_eqn in
  let c_eqs = List.map
      (function
        | v1, ((v2, k)::vars, cst, lc)
          when VarSet.mem v1 keep && not (VarSet.mem v2 keep) ->
          v2, mult (!/(-1) // k) ((v1, !/(-1))::vars, cst, lc)
        | sv -> sv)
      c_eqs in
  let eqs, more_eqs = List.partition
      (fun (v,_) -> not (VarSet.mem v keep)) (c_eqs @ eqs) in
  let eqs = varmap_of_assoc eqs in
  let sb, eqs = expand_subst ~keep ~bvs eqs in
  (*[* Format.printf
    "NumS.separate_subst: no_csts=%b@ eq-keys=%a@ sb=%a@\n%!"
    no_csts pr_vars (varmap_domain eqs)
    pr_num_subst sb; *]*)
  if not apply
  then
    sb, List.filter (function Eq _ -> false | _ -> true) cnj
  else
    let _, ineqn, optis, suboptis = split_flatten ~cmp_v cnj in
    (* FIXME: drop [keep] variables before substituting? *)
    let ineqn = List.map (norm_by_lcd % subst_w ~cmp_v eqs) ineqn in
    let optis = List.map (subst_2w ~cmp_v eqs) optis in
    let suboptis = List.map (subst_2w ~cmp_v eqs) suboptis in
    let ineqn = List.filter
        (function [], cst, _ when cst <=/ !/0 -> false | _ -> true)
        ineqn in
    let phi_num = cnj_to_num_formula ([], ineqn, optis, suboptis) in
    (*[* Format.printf "NumS.separate_subst: bvs=%a@ phi=%a@\n%!"
      pr_vars bvs pr_formula phi_num; *]*)
    let more_sb, _ =
      expand_subst ~keep ~bvs (varmap_of_assoc more_eqs) in
    let more = List.map
        (fun (v,(t,lc)) -> Eq (Lin (1,1,v), t, lc))
        (varmap_to_assoc more_sb) in
    sb, more @ phi_num
         
(* TODO: move to VarMap-based solutions? *)
let separate_subst q ?(no_csts=false)
    ?(keep=VarSet.empty) ?(bvs=VarSet.empty) ~apply cnj =
  (*[* Format.printf "NumS.separate_subst: keep=%a@ bvs=%a@ cnj=%a@\n%!"
    pr_vars keep pr_vars bvs pr_formula cnj; *]*)
  let sb, phi = (* separate_num_subst *)
    separate_subst_aux q ~no_csts ~keep ~bvs ~apply cnj in
  (*[* Format.printf "NumS.separate_subst: res phi=%a@\n%!"
    pr_formula phi; *]*)
  VarMap.map (fun (t, lc) -> Terms.num t, lc) sb,
  VarMap.map (fun (t,lc) -> t) sb,
  phi

let unexpand_cst lhs rhs loc =
  let unpack = function
    | Cst (i, j) -> [], !/i // !/j
    | Lin _ as t -> [t], !/0
    | Add ts ->
      match List.rev ts with
      | Cst (i, j) :: vars -> vars, !/i // !/j
      | vars -> vars, !/0 in
  let lhs_vars, lhs_cst = unpack lhs in
  let rhs_vars, rhs_cst = unpack rhs in
  let lhs = if lhs_vars = [] then Cst (0, 1) else Add lhs_vars in
  let rhs = if rhs_vars = [] then Cst (0, 1) else Add rhs_vars in
  lhs, rhs, lhs_cst -/ rhs_cst, loc

let expand_of_cst lhs rhs cst =
  let j, k = frac_of_num cst in
  assert (k > 0);
  if j>0 then
    match lhs with
    | Add ts -> Add (ts @ [Cst (j, k)]), rhs
    | t -> Add ([t; Cst (j, k)]), rhs
  else if j<0 then
    match rhs with
    | Add ts -> lhs, Add (ts @ [Cst ((-1)*j, k)])
    | t -> lhs, Add ([t; Cst ((-1)*j, k)])
  else lhs, rhs

let transitive_cl q cnj =
  let cmp_v = make_cmp q in
  let eqs = concat_map
    (function
      | Eq (t1, t2, loc) ->
        [unexpand_cst t1 t2 loc; unexpand_cst t2 t1 loc]
      | _ -> [])
    cnj in
  let ineqs = concat_map
    (function
      | Leq (t1, t2, loc) ->
        [unexpand_cst t1 t2 loc]
      | _ -> [])
    cnj in
  let other = map_some
    (function Eq _ | Leq _ -> None | a -> Some a)
    cnj in
  let eqs = ineq_transitive_cl ~cmp_v eqs in
  let cmp_v v1 v2 = Pervasives.compare v1 v2 in
  let ineqs = ineq_transitive_cl ~cmp_v ineqs in
  let cnj = Hashtbl.fold
      (fun (i,j) (cst, lc) cnj ->
         if i<j then
           let lhs, rhs = expand_of_cst i j cst in
           Eq (lhs, rhs, lc)::cnj else cnj)
      eqs [] in
  let cnj = Hashtbl.fold
      (fun (i,j) (cst, lc) cnj ->
         let lhs, rhs = expand_of_cst i j cst in
         Leq (lhs, rhs, lc)::cnj)
      ineqs cnj in
  other @ cnj
