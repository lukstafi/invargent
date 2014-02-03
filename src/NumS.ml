(** Numeric sort operations for InvarGenT.

    Released under the GNU General Public Licence (version 2 or
    higher), NO WARRANTY of correctness etc. (C) Lukasz Stafiniak 2013
    @author Lukasz Stafiniak lukstafi (AT) gmail.com
    @since Mar 2013
*)

let early_num_abduction = ref false(* true *)
let abd_rotations = ref (* 2 *)3
let abd_prune_at = ref (* 4 *)6(* 10 *)
let abd_timeout_count = ref (* 500 *)1000(* 5000 *)(* 50000 *)
let abd_fail_timeout_count = ref 10
let disjelim_rotations = ref 3
let abd_int_negation = ref true
let passing_ineq_trs = ref false
let no_subopti_of_cst = ref true

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

let sort_of_subst = List.map
    (fun (v, (t, lc)) -> Eq (Lin (1,1,v), num_of t, lc))

(* FIXME: or *)
    (*Terms.(function
        | Eq (t1, t2, loc) ->
          Eqty (Alien (Num_term t1), Alien (Num_term t2), loc)
        | a -> A (Num_atom a))*)

let (!/) i = num_of_int i
type w = (var_name * num) list * num * loc
type w_subst = (var_name * w) list
type cw_subst = ((var_name, bool) choice * w) list

(* Assumes [vars1] and [vars2] are in the same order. *)
let compare_w (vars1, cst1, _) (vars2, cst2, _) =
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
  let c = compare_num cst1 cst2 in
  if c <> 0 then c
  else loop (vars1, vars2)

module WSet = Set.Make (struct type t = w let compare = compare_w end)
let add_to_wset l ws = List.fold_right WSet.add l ws
let wset_of_list l = List.fold_right WSet.add l WSet.empty
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

type ineqs = (var_name * (WSet.t * WSet.t)) list
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
  Format.fprintf ppf "@[<2>%a@]" (pr_sep_list "," pr_sw) sb

let pr_cw ppf (v, w) =
  match v with
  | Left v ->
    Format.fprintf ppf "@[<2>%s@ =@ %a@]" (var_str v) pr_w w
  | Right false ->
    Format.fprintf ppf "@[<2>0 =@ %a@]" pr_w w
  | Right true ->
    Format.fprintf ppf "@[<2>1 =@ %a@]" pr_w w

let pr_cw_subst ppf sb =
  Format.fprintf ppf "@[<2>%a@]" (pr_sep_list "," pr_cw) sb

let pr_ineq ppf (v, (wl, wr)) =
  Format.fprintf ppf "@[<2>[%a]@ ≤@ %s@ ≤@ [%a]@]"
    (pr_sep_list ";" pr_w) (WSet.elements wl) (var_str v)
    (pr_sep_list ";" pr_w) (WSet.elements wr)

let pr_ineqs ppf (ineqs : ineqs) =
  pr_sep_list "," pr_ineq ppf ineqs

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

let pr_br3 ppf (_, prem, concl) =
    Format.fprintf ppf "@[<2>%a@ ⟹@ %a@]"
    pr_formula prem pr_formula concl


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

let zero_p (vars, cst, _) = vars = [] && cst =/ !/0
let taut_w iseq (vars, cst, _) =
  vars = [] && ((iseq && cst =/ !/0) || (not iseq && cst <=/ !/0))
let nonneg_cst_w (vars, cst, _) =
  vars = [] && (cst >=/ !/0)

let equal_w ~cmp_v w1 w2 = zero_p (diff ~cmp_v w1 w2)

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
  List.map (fun (v, (vars, cst, loc)) -> (v, !/(-1))::vars, cst, loc) sb

let unsolve (ineqs : ineqs) : w list = concat_map
  (fun (v, (left, right)) ->
    wset_map_to_list (fun (vars, cst, loc) -> (v, !/(-1))::vars, cst, loc)
      left @
      wset_map_to_list (fun rhs ->
          let vars, cst, loc = mult !/(-1) rhs in
          (v, !/1)::vars, cst, loc)
        right)
  ineqs

type w_atom =
    Eq_w of w | Leq_w of w | Opti_w of (w * w) | Subopti_w of (w * w)

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
      try let vars, cst, _ = mult k (List.assoc v eqs) in vars, cst
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

let subst_ineqs ~cmp_v eqs ineqs = List.map
  (fun (v, (left, right)) ->
    v, (wset_map (subst_w ~cmp_v eqs) left,
        wset_map (subst_w ~cmp_v eqs) right))
  ineqs

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
  let left, right = expand_sides w in
  if equ then Eq (left, right, loc) else Leq (left, right, loc)

let expand_opti ((_,_,lc1) as w1, (_,_,lc2 as w2)) =
  Opti (expand_w w1, expand_w w2, loc_union lc1 lc2)
let expand_subopti ((_,_,lc1) as w1, (_,_,lc2 as w2)) =
  Subopti (expand_w w1, expand_w w2, loc_union lc1 lc2)

let expand_subst eqs =
  List.map (fun (v, (_,_,loc as w)) -> v, (expand_w w, loc)) eqs    

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
  List.map (fun (v,(vars,cst,loc)) -> (v,!/(-1))::vars,cst,loc) eqs

let eqineq_loc_union (eqn, ineqn) =
  List.fold_left loc_union dummy_loc
    (List.map (fun (_,_,lc) -> lc) (eqn @ ineqn))

let un_ans (eqs, ineqs) = unsubst eqs, unsolve ineqs

(* TODO: make wider use of [clean] pruning. *)
let clean_ws preserve iseq eqs = List.filter
    (fun (vars,_,_ as w) ->
       List.for_all (fun (v,_) -> VarSet.mem v preserve) vars &&
       not (taut_w iseq w))
    eqs

let taut_ineq (vars, cst, _) = vars = [] && cst <=/ !/0
let taut_strict_ineq (vars, cst, _) = vars = [] && cst </ !/0

let ineq_transitive_cl ~cmp_v edge_l =
  let edges = Hashtbl.create 8 in
  let nodes = Hashtbl.create 8 in
  List.iter
    (fun (t1, t2, loc) ->
       Hashtbl.replace nodes t1 (); Hashtbl.replace nodes t2 ();
       Hashtbl.replace edges (t1, t2) loc)
    edge_l;
  (* More edges by affine displacement. *)
  Hashtbl.iter
    (fun i _ ->
       Hashtbl.iter
         (fun j _ ->
            let w = unexpand_sides ~cmp_v ((i, j), dummy_loc) in
            if taut_w false w
            then Hashtbl.add edges (i, j) dummy_loc)
         nodes) nodes;
  (* Floyd-Warshall algo *)
  let add i j k =
    if not (Hashtbl.mem edges (i, j)) then
      let lc1 = Hashtbl.find edges (i, k)
      and lc2 = Hashtbl.find edges (k, j) in
      let lc = loc_union lc1 lc2 in
      Hashtbl.add edges (i, j) lc in
  Hashtbl.iter
    (fun k _ ->
       Hashtbl.iter
         (fun i _ ->
            Hashtbl.iter
              (fun j _ -> try add i j k with Not_found -> ())
              nodes) nodes) nodes;
  edges

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

(* Assumption: [v] is downstream of all [vars] *)
(* TODO: understand why the equivalent of [Terms.quant_viol] utterly
   fails here. *)
let quant_viol uni_v bvs v vars =
  let res = uni_v v && not (VarSet.mem v bvs) in
  (*[* if res then
   Format.printf "NumS.quant_viol: v=%s; uni(v)=%b; bvs(v)=%b@\n%!"
    (var_str v) (uni_v v) (VarSet.mem v bvs);
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
    Some (v, s>0, w1, w2)
  with Not_found -> None

let solve_aux ?use_quants ?(strict=false)
    ~eqs ~ineqs ~eqs' ~optis ~suboptis ~eqn ~ineqn ~cnj
    ~cmp_v ~cmp_w uni_v =
  let use_quants, bvs = match use_quants with
    | None -> false, VarSet.empty
    | Some bvs -> true, bvs in
  let eqs = if eqs' = [] then eqs else List.map
      (fun (v,eq) -> v, subst_w ~cmp_v eqs' eq) eqs @ eqs' in
  let ineqs = if eqs' = [] then ineqs else List.map
      (fun (v,(wl,wr)) -> v,
        (wset_map (subst_w ~cmp_v eqs') wl,
         wset_map (subst_w ~cmp_v eqs') wr)) ineqs in
  let more_eqn, more_ineqn, more_optis, more_suboptis =
    split_flatten ~cmp_v cnj in
  let eqn = eqn @ more_eqn in
  let optis = optis @ more_optis in
  let suboptis = suboptis @ more_suboptis in
  let ineqn = ineqn @ more_ineqn @ flat2 optis in
  assert (not strict || eqn = []);
  let eqn = if eqs=[] then eqn else List.map (subst_w ~cmp_v eqs) eqn in
  let ineqn = if eqs=[] then ineqn else List.map (subst_w ~cmp_v eqs) ineqn in
  let eqn = List.map
    (fun (vars, cst, loc) ->
      List.filter (fun (v,k)->k <>/ !/0) vars, cst, loc) eqn in
  let eqn = List.sort cmp_w eqn in
  (*[* Format.printf "NumS.solve: start@ eqn=@ %a@ ineqn=@ %a@\n%!"
    pr_eqn eqn pr_ineqn ineqn; *]*)
  let rec elim acc = function
    | [] -> List.rev acc
    | ((v, k)::vars, cst, loc)::eqn
        when use_quants && quant_viol uni_v bvs v vars ->
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
      let msg =
        "Failed numeric equation ("^Num.string_of_num cst^"=0)" in
      raise (Terms.Contradiction (Num_sort, msg, None, loc)) in
  (*[* Format.printf "NumS.solve: solving eqs...@\n%!"; *]*)
  let eqn = List.rev (elim [] eqn) in
  let ineqn = if eqn=[] then ineqn else List.map (subst_w ~cmp_v eqn) ineqn in
  let eqs = if eqn=[] then eqs else List.map
      (fun (v,eq) -> v, subst_w ~cmp_v eqn eq) eqs in
  (* inequalities [left <= v] and [v <= right] *)
  let ineqs = if eqn=[] then ineqs else
      List.map (fun (v, (left, right)) ->
        v,
        (wset_map (subst_w ~cmp_v eqn) left,
         wset_map (subst_w ~cmp_v eqn) right)) ineqs in
  let more_ineqn =
    concat_map
      (fun (v, w) ->
        try
          let left, right = List.assoc v ineqs in
          wset_map_to_list (fun lhs -> diff ~cmp_v lhs w) left @
            wset_map_to_list (fun rhs -> diff ~cmp_v w rhs) right
        with Not_found -> [])
      eqn in
  let ineqn = List.sort cmp_w (more_ineqn @ ineqn) in
  (*[* Format.printf "NumS.solve:@\neqs=%a@\nsimplified ineqn=@ %a@\n%!"
    pr_w_subst (eqn @ eqs) pr_ineqn ineqn; *]*)
  let project v (vars, cst, loc as lhs) rhs =
    if equal_w ~cmp_v lhs rhs
    then
      let w = (v, !/(-1))::vars, cst, loc in
      if strict then
        let a = expand_atom false w in
        let t1, t2 = match a with
          | Leq (t1, t2, _) -> t1, t2 | _ -> assert false in
        raise (Terms.Contradiction
                 (Num_sort, "Failed numeric strict inequality",
                  Some (Terms.num t1, Terms.num t2), loc))
      else Right (norm_w ~cmp_v w)
    else Left (diff ~cmp_v lhs rhs) in
  let rec proj (ineqs : ineqs) implicits ineqn =
    match ineqn with
    | [] -> ineqs, implicits
    | ([], cst, _)::ineqn
        when (strict && cst </ !/0) || (not strict && cst <=/ !/0) ->
      proj ineqs implicits ineqn
    | ([], cst, loc)::_ ->
      raise (Terms.Contradiction
               (Num_sort,
                "Failed numeric inequality (cst="^
                  Num.string_of_num cst^")",
                None, loc))
    | ((v, k)::vars, cst, loc)::ineqn
        when use_quants && quant_viol uni_v bvs v vars ->
      let t1, t2 =
        match expand_atom false ((v, k)::vars, cst, loc) with
        | Leq (t1, t2, _) -> t1, t2
        | _ -> assert false in
      raise (Terms.Contradiction
               (Num_sort,
                "Quantifier violation (numeric inequality)",
                Some (Terms.num t1, Terms.num t2), loc))
    | ((v,k)::vars, cst, loc)::ineqn ->
      let (left, right), ineqs =
        try pop_assoc v ineqs
        with Not_found -> (WSet.empty, WSet.empty), ineqs in
      let ineq_l, ineq_r, (more_ineqn, more_implicits) = 
        let ohs = mult (!/(-1) // k) (vars, cst, loc) in
        if k >/ !/0
        then
          [], [ohs],
          wset_partition_map (fun lhs -> project v lhs ohs) left
        else
          [ohs], [],
          wset_partition_map (fun rhs -> project v ohs rhs) right in
      let more_ineqn = List.filter
        (function
        | [], cst, _
          when (strict && cst </ !/0) || (not strict && cst <=/ !/0) ->
          false
        | [], cst, loc ->
          let a = expand_atom false ([v, !/(-1)], cst, loc) in
          let t1, t2 = match a with
            | Leq (t1, t2, _) -> t1, t2 | _ -> assert false in
          raise (Terms.Contradiction
                   (Num_sort, "Failed numeric inequality",
                    Some (Terms.num t1, Terms.num t2), loc))
        | _ -> true)
        more_ineqn in
      (*[* Format.printf
        "NumS.solve-project: v=%s@\nmore_ineqn=@ %a@\nmore_impl=@ %a@\n%!"
        (var_str v) pr_ineqn more_ineqn pr_eqn more_implicits; *]*)  
      let ineqn =
        merge_one_nonredund ~cmp_v ~cmp_w (List.sort cmp_w more_ineqn) ineqn in
      let ineqs =
        (v, (add_to_wset ineq_l left, add_to_wset ineq_r right))::ineqs in
      proj ineqs (more_implicits @ implicits) ineqn in
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
  let optis =
    if eqn = [] then optis, []
    else partition_choice (map_some propagate optis) in
  (*[* Format.printf "NumS.solve: solving suboptis...@\n%!"; *]*)
  let suboptis, more_ineqn =
    if eqn = [] then suboptis, []
    else partition_choice (map_some propagate suboptis) in
  (*[* Format.printf "NumS.solve: solving ineqs...@\nineqn=%a@\n%!"
    pr_ineqn ineqn; *]*)
  let ineqs = proj ineqs []
      (keep_one_nonredund ~cmp_v ~acc:[] (more_ineqn @ ineqn)) in
  (*[* Format.printf "NumS.solve: done@\nineqs=@ %a@\n%!"
    pr_ineqs (fst ineqs); *]*)
  eqn @ eqs, ineqs, optis, suboptis

type num_solution = w_subst * ineqs * optis * suboptis

let solve ?use_quants ?strict
    ?(eqs=[]) ?(ineqs=[]) ?(eqs'=[])
    ?(optis=[]) ?(suboptis=[]) ?(eqn=[]) ?(ineqn=[]) ?(cnj=[])
    ~cmp_v ~cmp_w uni_v =
  (*[* Format.printf
    "NumS.main-solve: start@\ninit_st=@ %a@\neqn=%a@\nineqn=%a@\ncnj=%a@\n%!"
    pr_state (eqs, ineqs, optis, suboptis) pr_eqn eqn pr_ineqn ineqn
    pr_formula cnj; *]*)
  let rec loop (eqs,(ineqs,implicits1),(optis,implicits2),suboptis) =
    let implicits = implicits2 @ implicits1 in
    if implicits=[] then eqs, ineqs, optis, suboptis
    else (
      (*[* Format.printf "solve: implicits=%a@\n%!"
        pr_eqn implicits; *]*)
      loop
        (solve_aux ?use_quants ?strict ~eqs ~ineqs ~optis ~suboptis
           ~eqn:implicits
           ~eqs':[] ~ineqn:[] ~cnj:[] ~cmp_v ~cmp_w uni_v)) in
  if eqn=[] && (eqs=[] || eqs'=[]) && ineqn=[] && optis=[] &&
     suboptis=[] && cnj=[]
  then eqs @ eqs', ineqs, [], []
  else
    let res =
      loop (solve_aux ?use_quants ?strict ~eqs ~ineqs ~eqs' ~optis ~suboptis
              ~eqn ~ineqn ~cnj ~cmp_v ~cmp_w uni_v) in
    (*[* Format.printf "NumS.main-solve: done@\n%a@\n@\n%!"
      pr_state res; *]*)
    res

let fvs_w (vars, _, _) = vars_of_list (List.map fst vars)


exception Result of w_subst * ineqs * optis * suboptis

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

(* Simultaneous case split on several opti and subopti disjunctions. *)
let choices optis suboptis =
  (*[* Format.printf "NumS.choices: optis=%d suboptis=%d@\n%!"
    (List.length optis) (List.length suboptis); *]*)
  let disjs =
      List.map
         (fun (w1,w2) -> [Eq_w w1; Eq_w w2]) optis @
      List.map
         (fun (w1,w2) -> [Leq_w w1; Leq_w w2]) suboptis in
  let res = product disjs in
  (*[* Format.printf "NumS.choices: optis/suboptis %d cases@\n%!"
    (List.length res); *]*)
  res

let implies ~cmp_v ~cmp_w uni_v eqs ineqs optis suboptis c_eqn c_ineqn
    c_optis c_suboptis =
  (*[* Format.printf "implies: prem=@\n%a@\nconcl=@ %a@\n%a;@ %a@\n%!"
    pr_state (eqs, ineqs, optis, suboptis)
    pr_eqnineqn (c_eqn, c_ineqn) pr_optis c_optis pr_suboptis c_suboptis; *]*)
  if c_optis=[] && c_suboptis=[]
  then
    implies_case ~cmp_v ~cmp_w uni_v eqs ineqs c_eqn c_ineqn
      c_optis c_suboptis
  else List.for_all
      (fun cho ->
         let o_eqn, o_ineqn, _, _ = split_formula cho in
         let eqs, ineqs, _, _ = solve ~eqs ~ineqs
             ~eqn:o_eqn ~ineqn:o_ineqn ~cmp_v ~cmp_w uni_v in
         implies_case ~cmp_v ~cmp_w uni_v eqs ineqs c_eqn c_ineqn
           c_optis c_suboptis)
      (choices optis suboptis)

let implies_ans ~cmp_v ~cmp_w uni_v (eqs, ineqs, optis, suboptis)
    (c_eqn, c_ineqn, c_optis, c_suboptis) =
  implies ~cmp_v ~cmp_w uni_v eqs ineqs optis suboptis
    c_eqn c_ineqn c_optis c_suboptis 

(* FIXME: should [bvs] variables be considered not universal? *)
let revert_cst_n_uni ~qcmp_v cmp_v uni_v ~opti_lhs ~bvs
    eqs0 c_ineqn0 c_optis0 c_suboptis0 =
  (*[* Format.printf "revert: opti_lhs=%a@ initial eqs0=@\n%a@\n%!"
    pr_vars opti_lhs pr_w_subst eqs0; *]*)
  let opti_sb, eqs0 =
    if VarSet.is_empty opti_lhs then [], eqs0
    else partition_map
        (function
          | v1, ((v2,k2)::vars,cst,lc) when VarSet.mem v1 opti_lhs ->
            Left (v2, mult (!/(-1) // k2)
                    (norm_w ~cmp_v ((v1, !/(-1))::vars,cst,lc)))
          | sv -> Right sv)
        eqs0 in
  let eqs0 = if opti_sb=[] then eqs0
    else opti_sb @ List.map (fun (v,w)->v, subst_w ~cmp_v opti_sb w) eqs0 in
  let c_ineqn0 = if opti_sb=[] then c_ineqn0
    else List.map (subst_w ~cmp_v opti_sb) c_ineqn0 in
  let c_optis0 = if opti_sb=[] then c_optis0
    else List.map
        (fun (w1,w2) -> subst_w ~cmp_v opti_sb w1, subst_w ~cmp_v opti_sb w2)
        c_optis0 in
  let c_suboptis0 = if opti_sb=[] then c_suboptis0
    else List.map
        (fun (w1,w2) -> subst_w ~cmp_v opti_sb w1, subst_w ~cmp_v opti_sb w2)
        c_suboptis0 in
  let univar v = not (VarSet.mem v bvs) && uni_v v in
  let fresh_id = ref 0 in
  let old_sb, eqs0 = partition_map
      (function
        | v2, ([v1, k1], cst, loc) as sv
          when univar v2 && not (univar v1) ->
          incr fresh_id;
          Left (Left (v2, (v1, (!/1//k1, (!/(-1)//k1) */ cst,
                                k1,cst,
                                (loc,!fresh_id)))),
                (!fresh_id, sv))
        | v1, ([v2, k2], cst, loc) as sv
          when univar v2 && not (univar v1) ->
          incr fresh_id;
          Left (Left (v2, (v1, (k2, cst,
                                !/1//k2, (!/(-1)//k2) */ cst,
                                (loc,!fresh_id)))),
                (!fresh_id, sv))
        | v1, ([], cst, loc) as sv (* when not (uni_v v1) *) ->
          incr fresh_id;
          Left (Right (cst, (v1, (loc,!fresh_id))),
                (!fresh_id, sv))
        | sv -> Right sv)
      eqs0 in
  let c6_sb, old_sb = List.split old_sb in
  let c6u_sb, c6_cst = partition_choice c6_sb in
  let u_sb, c6u_sb =
    List.fold_left
      (fun (u_sb, c6u_sb) (b, avs) ->
         (* Maximum should be the leftmost here. *)
         let leq (v1,_) (v2,_) =
           VarSet.mem v1 opti_lhs ||
           uni_v v1 && not (VarSet.mem v2 opti_lhs) ||
           not (qcmp_v v1 v2 = Left_of) in
         let ov, (obk,obcst,bok,bocst,olc) = maximum ~leq avs in
         (b, ([ov,bok], bocst, fst olc))::u_sb,
         (ov, ([b,obk], obcst, olc)) :: map_some_append
             (fun (av, (abk,abcst,bak,bacst,alc)) ->
                if av=ov then None
                else Some (av, ([ov, abk*/bok], abcst +/ abk*/bocst, alc)))
             avs c6u_sb)
      ([], []) (collect c6u_sb) in
  let c6_cst =
    concat_map
      (fun (cst, avs) ->
         (* Maximum should be the leftmost here. *)
         let leq (v1,_) (v2,_) =
           VarSet.mem v1 opti_lhs ||
           uni_v v1 && not (VarSet.mem v2 opti_lhs) ||
           not (qcmp_v v1 v2 = Left_of) in
         let ov, olc = maximum ~leq avs in
         (ov, ([], cst, olc)) :: map_some
           (fun (av, lc) ->
             if av=ov then None else Some (av, ([ov,!/1], !/0, lc)))
           avs)
      (collect ~cmp_k:Num.compare_num c6_cst) in
  let c6eqs = c6u_sb @ c6_cst in
  let old_sb = List.map
      (fun (_, (_, _, (_,id))) -> List.assoc id old_sb)
      c6eqs in
  let c6eqs = List.map (fun (v,(vs,c,(lc,_))) -> v,(vs,c,lc)) c6eqs in
  let c6eqs = c6eqs @ List.map (fun (v,w)->v, subst_w ~cmp_v u_sb w) eqs0 in
  (*[* Format.printf "revert:@ old_sb=%a@ c6eqs=%a@\neqs0=%a@\n%!"
    pr_w_subst old_sb pr_w_subst c6eqs pr_w_subst eqs0; *]*)
  let eqs0 = old_sb @ eqs0 in
  let c6_ineqn0 =
      List.map (subst_w ~cmp_v u_sb) c_ineqn0 in
  let c6_optis0 =
      List.map (subst_2w ~cmp_v u_sb) c_optis0 in
  let c6_suboptis0 =
      List.map (subst_2w ~cmp_v u_sb) c_suboptis0 in
  c6eqs, eqs0, c6_ineqn0, c6_optis0, c6_suboptis0

exception Timeout

let rec taut = function
  | Eq_w (vars, cst, _) -> vars=[] && cst =/ !/0
  | Leq_w (vars, cst, _) -> vars=[] && cst <=/ !/0
  | Opti_w (w1, w2) ->
    taut (Leq_w w1) && taut (Leq_w w2) &&
    (taut (Eq_w w1) || taut (Eq_w w2))
  | Subopti_w (w1, w2) ->
    taut (Leq_w w1) || taut (Leq_w w2)

let pr_w_atom ppf = function
  | Eq_w w -> Format.fprintf ppf "%a=0" pr_w w
  | Leq_w w -> Format.fprintf ppf "%a≤0" pr_w w
  | Opti_w (w1, w2) -> Format.fprintf ppf "opti(%a,%a)" pr_w w1 pr_w w2
  | Subopti_w (w1, w2) -> Format.fprintf ppf "subopti(%a,%a)" pr_w w1 pr_w w2

let pr_w_formula ppf atoms =
  pr_sep_list " ∧" pr_w_atom ppf atoms

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

let abd_simple ~qcmp_v ~cmp_w cmp_v uni_v ~bvs ~discard ~validate
    skip (eqs_i, ineqs_i, optis_i, suboptis_i)
    (opti_lhs, (d_eqn, d_ineqn), (c_eqn, c_ineqn, c_optis, c_suboptis)) =
  let skip = ref skip in
  let counter = ref 0 in
  try
    (* 1 *)
    let d_eqn' = List.map (subst_w ~cmp_v eqs_i) d_eqn
    and c_eqn' = List.map (subst_w ~cmp_v eqs_i) c_eqn in
    let d_ineqn' = List.map (subst_w ~cmp_v eqs_i) d_ineqn
    and c_ineqn' = List.map (subst_w ~cmp_v eqs_i) c_ineqn
    and c_optis' = List.map (subst_2w ~cmp_v eqs_i) c_optis
    and c_suboptis' = List.map (subst_2w ~cmp_v eqs_i) c_suboptis in
    (* Extract (almost) all equations implied by premise and conclusion. *)
    let eqs0, _, _, _ =
      solve ~ineqs:ineqs_i ~eqn:(d_eqn' @ c_eqn')
        ~ineqn:(flat2 c_optis' @ d_ineqn' @ c_ineqn')
        ~cmp_v ~cmp_w uni_v in
    (* [eqs0] does not contain [eqs_i]. *)
    let d_ineqn0 = List.map (subst_w ~cmp_v eqs0) d_ineqn' in
    let c_ineqn0 = List.map (subst_w ~cmp_v eqs0) c_ineqn' in
    let c_optis0 = List.map (subst_2w ~cmp_v eqs0) c_optis' in
    let c_suboptis0 = List.map (subst_2w ~cmp_v eqs0) c_suboptis' in
    (* 2 *)
    let zero = [], !/0, dummy_loc in
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
    let add_atom_tr is_ineq ks_eq eq_trs = function
      | Eq_w ([], cst, _) when cst <>/ !/0 -> assert false
      | Eq_w a -> add_tr ks_eq eq_trs a
      | Leq_w ([], cst, _) when cst >/ !/0 -> assert false
      | Leq_w a when is_ineq -> add_tr ks_eq eq_trs a
      | Opti_w (a1, a2) when is_ineq ->
        add_tr ks_eq (add_tr ks_eq eq_trs a1) a2
      | Leq_w _ | Opti_w _ | Subopti_w _ -> eq_trs in
    (*[* Format.printf
      "NumS.abd_simple: 2.@\neqs_i=@ %a@\nineqs_i=@ %a@\nd_eqn=@ %a@ d_ineqn=@ %a@\nc_eqn=@ %a@\nc_ineqn=@ %a@\nd_ineqn0=@ %a@\nc_ineqn0=@ %a@\neqs0=@ %a@\n%!"
      pr_w_subst eqs_i pr_ineqs ineqs_i pr_eqn d_eqn pr_ineqn d_ineqn
      pr_eqn c_eqn pr_ineqn c_ineqn pr_ineqn d_ineqn0
      pr_ineqn c_ineqn0 pr_w_subst eqs0;
    *]*)
    (* 3 *)
    let eqs0, c6eqs, c6ineqn, c6optis, c6suboptis =
      revert_cst_n_uni ~qcmp_v cmp_v uni_v ~opti_lhs ~bvs
        eqs0 c_ineqn0 c_optis0 c_suboptis0 in
    (* 4 *)
    let rec loop add_eq_tr add_ineq_tr eq_trs ineq_trs
        eqs_acc ineqs_acc optis_acc suboptis_acc
        c6eqs c0eqs c6ineqn c0ineqn c6optis c0optis c6suboptis c0suboptis
      : unit =
      (*[* let ddepth = incr debug_dep; !debug_dep in *]*)
      incr counter; if !counter > !abd_timeout_count then raise Timeout;
      let a, c6a, c0eqs, c6eqs, c0ineqn, c6ineqn,
          c0optis, c6optis, c0suboptis, c6suboptis =
        match c0eqs, c6eqs, c0ineqn, c6ineqn,
              c0optis, c6optis, c0suboptis, c6suboptis with
        | (v,(vs,cst,lc))::c0eqs, (c6v,(c6vs,c6cst,c6lc))::c6eqs,
          c0ineqn, c6ineqn, c0optis, c6optis, c0suboptis, c6suboptis ->
          let a = (v,!/(-1))::vs,cst,lc
          and c6a = (c6v,!/(-1))::c6vs,c6cst,c6lc in
          Eq_w a, Eq_w c6a, c0eqs, c6eqs, c0ineqn, c6ineqn,
          c0optis, c6optis, c0suboptis, c6suboptis
        | [], [], a::c0ineqn, c6a::c6ineqn, c0optis, c6optis,
          c0suboptis, c6suboptis ->
          Leq_w a, Leq_w c6a, [], [], c0ineqn, c6ineqn,
          c0optis, c6optis, c0suboptis, c6suboptis
        | [], [], [], [], a::c0optis, c6a::c6optis, c0suboptis, c6suboptis ->
          Opti_w a, Opti_w c6a, [], [], [], [], c0optis, c6optis,
          c0suboptis, c6suboptis
        | [], [], [], [], [], [], a::c0suboptis, c6a::c6suboptis ->
          Subopti_w a, Subopti_w c6a, [], [], [], [], [], [],
          c0suboptis, c6suboptis
        | [], [], [], [], [], [], [], [] ->
          if (!skip > 0 && (decr skip; true))
          || List.exists
               (implies_ans ~cmp_v ~cmp_w uni_v
                  (eqs_acc, ineqs_acc, optis_acc, suboptis_acc))
               (discard : (w list * w list * optis * suboptis) list)
          then
            (raise
               (Terms.Contradiction
                  (Num_sort,
                   "Numeric SCA: skipping", None, dummy_loc)))
          else raise (Result (eqs_acc, ineqs_acc, optis_acc, suboptis_acc))
        | _ -> assert false in
      (* 5 *)
      (* We get a substitution in [~eqs:(eqs_acc @ c0eqs)]
         because initial equations [c0eqs] are a solved form with
         [eqs_i], and all transformations are through equations
         absent from [eqs_acc]. *)
      (*[* Format.printf
        "NumS.abd_simple: [%d] 5. @\nd_eqn=@ %a@\nineqn=@ %a@\n%!"
        ddepth pr_eqn d_eqn pr_ineqn (d_ineqn0 @ c0ineqn);
      *]*)
      let b_eqs, b_ineqs, b_optis, b_suboptis =
        solve ~eqs:(eqs_acc @ c0eqs)
          ~ineqs:ineqs_acc ~eqn:d_eqn ~ineqn:(d_ineqn0 @ c0ineqn)
          ~optis:(optis_acc @ c0optis)
          ~suboptis:(suboptis_acc @ c0suboptis)
          ~cmp_v ~cmp_w uni_v in
      (*[* Format.printf
        "NumS.abd_simple: [%d] 5. a=@ %a@\nb_eqs=@ %a@\nb_ineqs=@ %a@\n%!"
        ddepth pr_w_atom a pr_w_subst b_eqs pr_ineqs b_ineqs;
      *]*)

      if taut a
      || implies ~cmp_v ~cmp_w uni_v b_eqs b_ineqs b_optis b_suboptis
           c_eqn c_ineqn c_optis c_suboptis
      then (
        (* 6 *)
        (* [ineq_trs] include [eq_trs]. *)
        (*[* Format.printf "NumS.abd_simple: [%d] STEP 6.@\nc6remain=%a@\n%!"
          ddepth pr_w_subst c6eqs;
        *]*)
        loop add_eq_tr add_ineq_tr eq_trs ineq_trs eqs_acc
          ineqs_acc optis_acc suboptis_acc c6eqs c0eqs c6ineqn c0ineqn
          c6optis c0optis c6suboptis c0suboptis)
      else
        (* 7 *)
        let trs = if iseq_w_atom a then eq_trs else ineq_trs in
        (*[* Format.printf
          "NumS.abd_simple: [%d] 7. STEP a=@ %a@\nc6remain=%a@\n%!"
          ddepth pr_w_atom a pr_w_subst c6eqs;
        *]*)
        let passes = ref false in
        let try_trans a' =
          try
            (* 7a *)
            (*[* Format.printf
              "NumS.abd_simple: [%d] 7a. trying a'=@ %a@ ...@\n%!"
              ddepth pr_w_atom a';
            *]*)
            let eqn, ineqn, optin, suboptin = split_w_atom a' in
            let eqs_acc, ineqs_acc, optis_acc, suboptis_acc =
              solve ~use_quants:bvs
                ~eqs:eqs_acc ~ineqs:ineqs_acc
                ~optis:(optin @ optis_acc) ~suboptis:(suboptin @ suboptis_acc)
                ~eqn ~ineqn ~cmp_v ~cmp_w uni_v in
            ignore (validate (eqs_acc, ineqs_acc, optis_acc, suboptis_acc));
            passes := true;
            (*[* Format.printf "NumS.abd_simple: [%d] 7a. validated@\n%!" ddepth;
            *]*)
            (* 7c *)
            let ineq_trs =
              if not (iseq_w_atom a) && !passing_ineq_trs
              then add_ineq_tr ineq_trs a
              else ineq_trs in
            (* 7d *)
            (*[* Format.printf
              "NumS.abd_simple: [%d] 7 OK@\n%!" ddepth; *]*)
            (* (try                         *)
            loop add_eq_tr add_ineq_tr eq_trs ineq_trs
              eqs_acc ineqs_acc optis_acc suboptis_acc
              c6eqs c0eqs c6ineqn c0ineqn c6optis c0optis
              c6suboptis c0suboptis
          (* with Contradiction _ -> ()) *)
          with
          | Terms.Contradiction (_,msg,tys,_) (*[* as e *]*)
            when msg != no_pass_msg ->
            (*[* Format.printf
              "NumS.abd_simple: [%d] 7. invalid, error=@\n%a@\n%!"
              ddepth Terms.pr_exception e;
            *]*)
            () in
        try_trans c6a;
        laziter (fun tr -> try_trans (trans_w_atom ~cmp_v tr a)) trs;
        if not !passes then (
          (* 7b *)
          (*[* Format.printf
            "NumS.abd_simple: [%d] 7b. failed a=@ %a@ ...@\n%!"
            ddepth pr_w_atom a;
          *]*)
          raise (Terms.Contradiction
                   (Num_sort, no_pass_msg, None, dummy_loc))) in
    (* 2 *)
    try
      for rot = 1 to !abd_rotations do
        let big_k = Array.init (rot - 1) (fun k -> !/(k+2)) in
        let big_k =
          Array.append big_k (Array.map (fun k-> !/1 // k) big_k) in
        let ks_eq = (* 1a1 *)
          Array.to_list
            (Array.append [|!/1; !/(-1); !/0|]
               (Array.append
                  big_k
                  (Array.map (fun k -> !/(-1) */ k) big_k))) in
        let ks_ineq = (* 1b1 *)
          Array.to_list (Array.append [|!/0; !/1|] big_k) in
        let ks_eq = laz_of_list ks_eq
        and ks_ineq = laz_of_list ks_ineq in
        let eq_trs = laz_single zero in
        let add_eq_tr = add_tr ks_eq in
        let add_Eq_tr = add_atom_tr false ks_eq in
        let eq_trs = List.fold_left add_eq_tr eq_trs d_eqn' in
        let add_ineq_tr = add_tr ks_ineq in
        let add_Ineq_tr = add_atom_tr true ks_ineq in
        let ineq_trs = List.fold_left add_ineq_tr eq_trs d_ineqn0 in
        loop add_Eq_tr add_Ineq_tr eq_trs ineq_trs
          eqs_i ineqs_i optis_i suboptis_i
          c6eqs eqs0 c6ineqn c_ineqn0 c6optis c_optis0 c6suboptis c_suboptis0
      done; None
    with Result (ans_eqs, ans_ineqs, ans_optis, ans_suboptis) ->
      Some (ans_eqs, ans_ineqs, ans_optis, ans_suboptis)
  with
  | Terms.Contradiction _ -> None
  | Timeout ->
    abd_timeout_flag := true;
    (*[* Format.printf
      "NumS.abd_simple: TIMEOUT@\neqs_i=@ %a@\nineqs_i=@ %a@\nd_eqn=@ %a@ d_ineqn=@ %a@\nc_eqn=@ %a@\nc_ineqn=@ %a@\n%!"
      pr_w_subst eqs_i pr_ineqs ineqs_i pr_eqn d_eqn pr_ineqn d_ineqn
      pr_eqn c_eqn pr_ineqn c_ineqn;
    *]*)
    None

let make_cmp q v1 v2 =
  (* Order: variables more to the right in the quantifier should be more
     to the left in the sum. *)
  match q.cmp_v v1 v2 with
  | Left_of -> 1
  | Right_of -> -1
  | Same_quant -> compare v2 v1


module NumAbd = struct
  type accu = w_subst * ineqs * optis * suboptis
  type args = {
    cmp_v : (var_name -> var_name -> int);
    cmp_w : (w -> w -> int);
    qcmp_v : (var_name -> var_name -> var_scope);
    uni_v : (var_name -> bool);
    bvs : VarSet.t}
  type answer = accu
  type discarded = w list * w list * optis * suboptis
  (** "LHS" variables of opti atoms, premise, conclusion. *)
  type branch =
      VarSet.t * (w list * w list) * (w list * w list * optis * suboptis)

  let abd_fail_timeout = !abd_fail_timeout_count
  let abd_fail_flag = abd_fail_flag

  let abd_simple {qcmp_v; cmp_w; cmp_v; uni_v; bvs}
      ~discard ~validate acc br =
    abd_simple ~qcmp_v ~cmp_w cmp_v uni_v ~bvs
      ~discard ~validate 0 acc br

  let extract_ans ans = ans

  (* FIXME *)
  let discard_ans (eqs, ineqs, optis, suboptis) =
    unsubst eqs, unsolve ineqs, optis, suboptis

  let concl_of_br ((_, _, concl) : branch) =
    num_to_formula (cnj_to_num_formula concl)

  let is_taut (eqs, ineqs, optis, suboptis) =
    eqs=[] && ineqs=[] && optis=[] && suboptis=[]

  let pr_branch pp (_, (d_eqn, d_ineqn),
                    (c_eqn, c_ineqn, c_optis, c_suboptis)) =
    Format.fprintf pp
      "@[<2>d_eqn=%a@\nd_ineqn=%a@\n⟹@\nc_eqn=%a@\nc_ineqn=%a@\nc_optis=%a@\nc_suboptis=%a@\n@]"
      pr_eqn d_eqn pr_ineqn d_ineqn
      pr_eqn c_eqn pr_ineqn c_ineqn pr_optis c_optis pr_suboptis c_suboptis

  let pr_ans pp (eqs, ineqs, optis, suboptis) =
    Format.fprintf pp "eqs=%a@\nineqs=%a@\noptis=%a@\nsuboptis=%a@\n%!"
      pr_w_subst eqs pr_ineqs ineqs pr_optis optis pr_suboptis suboptis
end

module JCA = Joint.JointAbduction (NumAbd)

(* FIXME: eliminate optis from premise, but first try simplifying
   them with both premise and conclusion of a branch. *)
let abd q ~bvs ~discard ?(iter_no=2) brs =
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
    (pr_line_list "| " pr_br3) brs;
  *]*)
  let brs = concat_map
      (fun (nonrec, prem, concl) ->
         let d_eqn, d_ineqn, d_optis, d_suboptis =
           split_flatten ~cmp_v prem in
         (* We normalize to reduce the number of opti and subopti
            disjunctions. Also recovers implicit equalities
            due to optis. *)
         try
           let _,_,(d_optis,d_opti_eqn),d_suboptis =
             solve_aux ~cmp_v ~cmp_w q.uni_v
               ~eqs:[] ~ineqs:[] ~eqs':[] ~cnj:[]
               ~eqn:d_eqn ~ineqn:d_ineqn
               ~optis:d_optis ~suboptis:d_suboptis in
           let d_ineqn = flat2 d_optis @ d_ineqn in
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
           List.map
             (fun opti_subopti ->
                (* eqs come from opti, ineqs from subopti *)
                let o_eqn, o_ineqn, _, _ = split_formula opti_subopti in
                nonrec, opti_lhs,
                (d_opti_eqn @ o_eqn @ d_eqn, o_ineqn @ d_ineqn),
                concl)
             (choices d_optis d_suboptis)
         with Terms.Contradiction _ -> [])
      brs in
  (* Raise [Contradiction] from [abd] when constraints are not
     satisfiable. *)
  (* TODO: optimize -- don't redo work. *)
  let brs = map_some
    (fun ((_, _, (d_eqn, d_ineqn),
           (c_eqn, c_ineqn, c_optis, c_suboptis)) as br) ->
      let br =
        try
          (* Some equations from case splitting can be contradictory. *)
          ignore (solve ~eqn:d_eqn ~ineqn:d_ineqn ~cmp_v ~cmp_w q.uni_v);
          Some br
        with Terms.Contradiction _ -> None in
      ignore (solve
                ~eqn:(d_eqn @ c_eqn) ~ineqn:(d_ineqn @ c_ineqn)
                ~cmp_v ~cmp_w q.uni_v);
      br)
    brs in
  (* FIXME *)
  let validate (eqs, ineqs, optis, suboptis) = List.iter
      (fun (_, _, (d_eqn, d_ineqn), (c_eqn, c_ineqn, c_optis, c_suboptis)) ->
         (*[* Format.printf "validate:@\nd_eqn=%a@\nc_eqn=%a@\nd_ineqn=%a@\nc_ineqn=%a@\nc_optis=%a@\nc_suboptis=%a@\n%!"
           pr_eqn d_eqn pr_eqn c_eqn pr_ineqn d_ineqn pr_ineqn c_ineqn
           pr_optis c_optis pr_suboptis c_suboptis; *]*)
         let (*[* br_eqs,br_ineqs,br_optis,br_suboptis *]*) _ =
           solve ~eqs ~ineqs
             ~eqn:(d_eqn @ c_eqn) ~ineqn:(d_ineqn @ c_ineqn)
             ~optis:c_optis ~suboptis:c_suboptis ~cmp_v ~cmp_w q.uni_v in
         (*[* Format.printf "br_eqs=%a@\nbr_ineqs=%a@\nbr_optis=%a@\nbr_suboptis=%a@\n%!"
           pr_w_subst br_eqs pr_ineqs br_ineqs pr_optis br_optis
           pr_suboptis br_suboptis; *]*)
         ())
      brs in
  let brs, unproc_brs =
    if iter_no > 1 || !early_num_abduction
    then brs, []
    else List.partition
        (fun (nonrec, opti_lhs, prem, concl) -> nonrec) brs in
  let brs = List.map
      (fun (_, opti_lhs,  prem, concl) -> opti_lhs, prem, concl)
      brs in
  let brs = List.stable_sort
      (fun (_,(pe1,pi1),_) (_,(pe2,pi2),_) ->
         (List.length pe1 + List.length pi1) -
           (List.length pe2 + List.length pi2))
      brs in
  (*[* Format.printf "NumS.abd: split-brs=@\n| %a@\n%!"
    (pr_line_list "| " pr_sep_br) brs;
  *]*)
    let discard =
      List.map (split_flatten ~cmp_v) discard in
    let elim_uni =
      (* FIXME: rethink *)
      concat_map
        (fun (_,_,_,(concl_eqs, _, _, _)) ->
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
        {cmp_v; cmp_w; NumAbd.qcmp_v = q.cmp_v; uni_v = q.uni_v; bvs}
        ~discard ~validate ([], [], [], []) brs in
    [], elim_uni @ ans_to_num_formula ans


let i2f = float_of_int

let expand_eqineqs eqs ineqs =
  let ans = List.map (expand_atom true) (unsubst eqs) in
  ans @ List.map (expand_atom false) (unsolve ineqs)

(* Currently, [initstep] is only used to generate more -- redundant --
   [subopti] atoms. *)
let disjelim_aux q ~preserve ~initstep brs =
  let vars = List.map fvs_formula brs in
  let common = List.fold_left VarSet.inter preserve vars in
  let cmp_v = make_cmp q in
  let cmp_v v1 v2 =
    let v1c = VarSet.mem v1 common and v2c = VarSet.mem v2 common in
    if v1c && not v2c then 1
    else if v2c && not v1c then -1
    else cmp_v v1 v2 in
  let cmp_w (vars1,cst1,_) (vars2,cst2,_) =
    match vars1, vars2 with
    | [], [] -> 0
    | _, [] -> -1
    | [], _ -> 1
    | (v1,_)::_, (v2,_)::_ -> cmp_v v1 v2 in
  let polytopes_n_elim_eqs = List.map
      (fun cnj ->
         (*[* Format.printf
           "NumS.disjelim:@ solving cnj==%a@\n%!"
           pr_formula cnj; *]*)
         try
           let eqs, ineqs, optis, suboptis =
             solve ~cnj ~cmp_v ~cmp_w q.uni_v in
           let eqs, elim_eqs = List.partition
               (fun (v, _) -> VarSet.mem v common) eqs in
           Some ((eqs, ineqs, optis, suboptis), elim_eqs)
         with Terms.Contradiction _ -> None)
      brs in
  (*[* Format.printf
    "NumS.disjelim:@ preserve=%a@ common=%a@ elim_eqs=@\n%a@\n%!"
    pr_vars preserve pr_vars common
    (pr_line_list "| " pr_w_subst)
    (List.map snd polytopes_n_elim_eqs); *]*)
  (* let unpack_optis esb optis =
     concat_map (fun (w1,w2) ->
        [subst_w ~cmp_v esb w1; subst_w ~cmp_v esb w2]) optis in *)
  (* Case-split on [optis]. *)
  (* [polytopes] is only used for checking if a face intersects with
     all polytopes. Faces themselves are taken from [faces]. Discard
     empty disjuncts. *)
  let polytopes_n_faces = concat_map2
      (function
        | Some ((eqs, ineqs, optis, suboptis), esb) -> fun br ->
          let opti_ineqs = flat2 optis in
          map_some
            (fun opti_subopti ->
               try
                 let o_eqn, o_ineqn, _, _ = split_formula opti_subopti in
                 let eqs, ineqs, _, _ =
                   solve ~eqs ~ineqs ~eqn:o_eqn
                     ~ineqn:(o_ineqn @ opti_ineqs)
                     ~cmp_v ~cmp_w q.uni_v in
                 let br = List.map (flatten ~cmp_v) br in
                 (*[* Format.printf
                   "NumS.disjelim: opti_eqn=@ %a@ opti_ineqn=@ %a@\n%!"
                   pr_eqn o_eqn pr_ineqn o_ineqn; *]*)
                 Some
                   ((List.map (fun (v,w) -> v, subst_w ~cmp_v esb w) eqs,
                     subst_ineqs ~cmp_v esb ineqs),
                    (esb, opti_subopti @ br))
               with Terms.Contradiction _ ->
                 (*[* Format.printf
                   "NumS.disjelim: failed opti_choice=@\n%a@\nopti_ineqs=%a@\nbr=%a@\nesb=%a@\n%!"
                   pr_w_formula opti_subopti pr_ineqn opti_ineqs
                   pr_formula br pr_w_subst esb; *]*)
                 None)
            (choices optis suboptis)
        | None -> fun _ -> [])
      polytopes_n_elim_eqs brs in
  let polytopes, faces = List.split polytopes_n_faces in
  (* Aggressive pruning: drop faces with "unwanted" variables. *)
  let faces = List.map
      (fun (esb, br) ->
         concat_map
           (function
             | Leq_w w ->
               clean_ws common false [subst_w ~cmp_v esb w]
             | Eq_w w ->
               let w = subst_w ~cmp_v esb w in
               clean_ws common false [w; mult !/(-1) w]
             | _ -> [])
           br)
      faces in
  (*[* Format.printf "NumS.disjelim: faces=@\n%a@\n%!"
    (pr_line_list "| " pr_ineqn) faces; *]*)
  (* Check if a polytope face is also a face of resulting convex hull
     -- its outside does not contain any piece of any polytope. *)
  let check face =
    let ineqn = [mult !/(-1) face] in
    List.for_all
      (fun (eqs, ineqs) ->
         try ignore
               (solve ~strict:true ~eqs ~ineqs ~ineqn ~cmp_v ~cmp_w q.uni_v);
           false
         with Terms.Contradiction _ -> true)
      polytopes in
  let selected : (w list * w list) list =
    List.map (List.partition check) faces in
  let ridges : (w * w) list = concat_map
      (fun (sel, ptope) ->
         concat_map (fun p -> List.map (fun s->s, p) sel) ptope)
      selected in
  let angle i j = i2f (i+1) /. i2f (j+1) in
  let cands = List.map
      (fun (s, p) ->
         let l = Array.init
             !disjelim_rotations (fun i ->
                 if i <= 1 then [||]
                 else Array.init (i-1) (fun j ->
                     angle j i, sum_w ~cmp_v (mult !/(j+1) s) (mult !/(i+1) p))) in
         let r = Array.init
             !disjelim_rotations (fun i ->
                 if i <= 1 then [||]
                 else Array.init (i-1) (fun j ->
                     angle i j, sum_w ~cmp_v (mult !/(i+1) s) (mult !/(j+1) p))) in
         (1., sum_w ~cmp_v s p) ::
           Array.to_list (Array.concat (Array.to_list l)) @
           Array.to_list (Array.concat (Array.to_list r)))
      ridges in
  let cands = List.map (fun angles ->
      List.map snd
        (List.sort (fun (a,_) (b,_) -> compare a b) angles)) cands in
  let result = concat_map fst selected in
  let result = map_some
      (fun cands -> try Some (List.find check cands)
        with Not_found -> None) cands
               @ result in
  let sort_w (vars, cst, loc) =
    let vars = map_reduce ~cmp_k:cmp_v (+/) (!/0) vars in
    let vars =
      List.filter (fun (_,k) -> k <>/ !/0) vars in
    vars, cst, loc in
  let result = List.map sort_w result in
  (*[* Format.printf "NumS.disjelim: result=%a@\n%!"
    pr_ineqn result; *]*)
  let rec idemp eqn ineqn = function
    | e1::(e2::_ as tl) when (* nonq_cmp_w e1 e2 = 0 *)
        equal_w ~cmp_v e1 e2 -> idemp eqn ineqn tl
    | e::tl when List.exists (fun w -> zero_p (sum_w ~cmp_v e w)) tl ->
      (* Two inequalities forming an equation. *)
      idemp (e::eqn) ineqn
        (List.filter (fun w -> not (zero_p (sum_w ~cmp_v e w))) tl)
    | e::tl -> idemp eqn (e::ineqn) tl
    | [] -> eqn, ineqn in
  let eqn, ineqn =
    idemp [] [] (List.sort nonq_cmp_w result) in
  (*[* Format.printf "NumS.disjelim: solution@\neqn=%a@\nineqn=%a@\n%!"
    pr_eqn eqn pr_ineqn ineqn; *]*)
  let redundant_eqn =
    collect ~cmp_k:Num.compare_num
      (List.map (fun (vars,cst,lc) -> cst,(vars,lc)) eqn) in
  let redundant_eqn =
    Aux.concat_map
      (fun (_,ws) -> List.map
          (fun ((w1,lc1),(w2,lc2)) ->
             diff ~cmp_v (w1, !/0, lc1) (w2, !/0, lc2))
          (Aux.triangle ws))
      redundant_eqn in
  (*[* Format.printf "NumS.disjelim:@\neqn=%a@\nredundant=%a@\n%!"
    pr_eqn eqn pr_eqn redundant_eqn; *]*)
  let check_redund face ptope =
    let eqs, ineqs, _, _ =
      solve ~eqn ~ineqn:ptope ~cmp_v ~cmp_w q.uni_v in
    let ineqn = [mult !/(-1) face] in
    try ignore
          (solve ~strict:true ~eqs ~ineqs ~ineqn ~cmp_v ~cmp_w q.uni_v);
      false
    with Terms.Contradiction _ -> true in
  let rec nonredundant p1 = function
    | face::p2 ->
      if check_redund face (p1 @ p2) then nonredundant p1 p2
      else nonredundant (face::p1) p2
    | [] -> p1 in
  let ineqn = nonredundant [] ineqn in
  (* Generating opti atoms. *)
  let brs_eqs = List.map
      (fun (eqs, _) ->
         let eqn = eqn_of_eqs eqs in
         let eqn = eqn @ List.map (mult !/(-1)) eqn in
         let eqn = List.map
             (fun (_,_,lc as w) ->
                let lhs, rhs = expand_sides w in lhs, rhs, lc) eqn in
         Joint.transitive_cl eqn)
      polytopes in
  (*[* let pr_hasheqs ppf h =
    let eqs = Hashtbl.fold
        (fun (lhs,rhs) lc eqs -> Eq (lhs,rhs,lc)::eqs) h [] in
    pr_formula ppf eqs in
    Format.printf "NumS.disjelim: brs_eqs=@\n%a@\n%!"
    (pr_line_list "| " pr_hasheqs) brs_eqs; *]*)  
  (* Transitive closure of resulting equations and inequalities. *)
  let result = List.map
      (fun (_,_,lc as w) ->
         let (lhs, rhs as w_key) = expand_sides w in
         lhs, rhs, lc)
      result in
  let result = ineq_transitive_cl ~cmp_v result in
  let result = Hashtbl.fold
      (fun w_key loc cnj -> (w_key, loc)::cnj) result [] in
  let opt_cands = map_some
      (fun ((w_lhs, w_rhs as w_key), w_lc as w) ->
         let inds = mapi_some
             (fun i eqs ->
                if Hashtbl.mem eqs w_key then Some i else None)
             brs_eqs in
         if inds=[] then None
         else Some (w, ints_of_list inds))
      result in
  (*[* let pr_opt_cand ppf (((w_lhs, w_rhs), w_lc), inds) =
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
  (* TODO: redundant conversion, remove [unexpand_sides] and
     [expand_opti] and implement [is_directed]. *)
  let optis = List.map
      (fun (w1, w2) -> unexpand_sides ~cmp_v w1, unexpand_sides ~cmp_v w2)
      optis in
  let optis =
    List.map (fun (_,_,w1, w2) -> w1, w2)
      (map_some direct_opti optis) in
  (*[* Format.printf "NumS.disjelim: optis=@\n%a@\n%!"
    pr_optis optis; *]*)  
  (* Generating subopti atoms. *)
  let ptopes_ineqs = List.map
      (fun ptope ->
         let p_ineqs = List.map
             (fun (_,_,lc as w) ->
                let lhs, rhs = expand_sides w in
                lhs, rhs, lc) ptope in
         ineq_transitive_cl ~cmp_v p_ineqs)
      faces in
  let suboptis =
    Hashtbl.fold
      (fun (lhs, rhs as w_key) lc suboptis ->
         let w = NumDefs.diff lhs rhs in
         let vars, _ = NumDefs.flatten w in
         match vars with
         | [] -> suboptis
         | [_] when !no_subopti_of_cst || initstep -> suboptis
         | _ -> Left (w, w_key, lc) :: suboptis)
      (List.hd ptopes_ineqs) [] in
  let suboptis = List.fold_left
      (fun suboptis ptope ->
         (*[* let left, right = partition_choice suboptis in
           let left = List.map
             (fun (_, w, lc) -> unexpand_sides ~cmp_v (w, lc)) left in
           let right = List.map
             (fun (_, _, w1, w2, lc) ->
                unexpand_sides ~cmp_v (w1, lc),
                unexpand_sides ~cmp_v (w2, lc)) right in
           Format.printf "NumS.disjelim: subopti step@\nleft=%a;@ right=%a@\n%!"
           pr_ineqn left pr_suboptis right; *]*)
         (* TODO: allow weakening of candidate inequalities (by a constant) *)
         concat_map
           (function
             | Left (w, w_key, lc) as cand ->
               if Hashtbl.mem ptope w_key then [cand]
               else Hashtbl.fold
                   (fun (lhs, rhs as w_key2) lc2 more_subopt ->
                      let w2 = NumDefs.diff lhs rhs in
                      match NumDefs.direct_opti w w2 with
                      | Some (_,_,Add ([] | [Cst _]), _)
                        when !no_subopti_of_cst || initstep ->
                        more_subopt
                      | Some (_,_,_,Add ([] | [Cst _]))
                        when !no_subopti_of_cst || initstep ->
                        more_subopt
                      | Some _ when w_key < w_key2 ->
                        (*[* Format.printf
                                "subopti: w1=%a;@ w2=%a@\n%!"
                                pr_term w pr_term w2; *]*)
                        (* Aribtrary breaking of symmetry. *)
                        Right (w, w2, w_key, w_key2, loc_union lc lc2)
                        ::more_subopt
                      | _ -> more_subopt) ptope []
             | Right (w1, w2, w1_key, w2_key, lc) as cand ->
               if Hashtbl.mem ptope w1_key || Hashtbl.mem ptope w2_key
               then [cand] else [])
           suboptis)
      suboptis (List.tl ptopes_ineqs) in
  let suboptis = map_some
      (function
        | Left _ -> None
        | Right (w1_t, w2_t, w1_key, w2_key, lc) ->
          let w1 = unexpand_sides ~cmp_v (w1_key, lc) in
          let w2 = unexpand_sides ~cmp_v (w2_key, lc) in
          (*[* Format.printf
            "subopti-exp: w1_t=%a;@ w1=%a;@ w2_t=%a;@ w2=%a@\n%!"
            pr_term w1_t pr_w w1 pr_term w2_t pr_w w2; *]*)  
          Some (w1, w2))
      suboptis in
  (*[* Format.printf "NumS.disjelim: suboptis=@\n%a@\n%!"
    pr_suboptis suboptis; *]*)  
  [],
  List.map expand_opti optis @
    List.map expand_subopti suboptis @
    List.map (expand_atom true) (eqn @ redundant_eqn)
  @ List.map (expand_atom false) ineqn

let disjelim q ~preserve ~initstep brs =
  (*[* Format.printf "NumS.disjelim: preserve=%a #brs=%d@\ninit brs=@\n%a@\n%!"
    pr_vars preserve (List.length brs)
    (pr_line_list "| " pr_formula) brs; *]*)
  match brs with
  | [] -> assert false
  | [br] -> disjelim_aux q ~preserve ~initstep [br; br]
  | _ -> disjelim_aux q ~preserve ~initstep brs

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
let prune_single_redund ~cmp_v cnj =
  let rec aux pareto = function
    | [] -> pareto
    | a::cnj ->
      let cnj = List.filter (not % atomic_impl ~cmp_v a) cnj in
      if List.exists (fun b -> atomic_impl ~cmp_v b a) cnj
      then aux pareto cnj
      else aux (a::pareto) cnj in
  aux [] cnj

(* Dismisses contradictions. *)
let project ~cmp_v ~cmp_w ineqs ineqn =
  let rec proj ineqs ineqn =
    match ineqn with
    | [] -> ineqs
    | ([], cst, _)::ineqn (* when cst <=/ !/0 *) -> proj ineqs ineqn
    | ((v,k)::vars, cst, loc)::ineqn ->
      let (left, right), ineqs =
        try pop_assoc v ineqs
        with Not_found -> (WSet.empty, WSet.empty), ineqs in
      let ineq_l, ineq_r, more_ineqn = 
        let ohs = mult (!/(-1) // k) (vars, cst, loc) in
        if k >/ !/0
        then
          [], [ohs],
          wset_map_to_list (fun lhs -> diff ~cmp_v lhs ohs) left
        else
          [ohs], [],
          wset_map_to_list (fun rhs -> diff ~cmp_v ohs rhs) right in
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
        (v, (add_to_wset ineq_l left, add_to_wset ineq_r right))::ineqs in
      proj ineqs ineqn in
  proj ineqs ineqn

exception Not_satisfiable

let strict_sat ~cmp_v ~cmp_w ineqs ineqn =
  (*[* Format.printf
    "NumS.strict-sat: test ineqn=@ %a@\n%!" pr_ineqn ineqn; *]*)  
  let rec proj ineqs ineqn =
    match ineqn with
    | [] -> ()
    | ([], cst, _)::ineqn when cst </ !/0 -> proj ineqs ineqn
    | ([], cst, loc)::_ -> raise Not_satisfiable
    | ((v,k)::vars, cst, loc)::ineqn ->
      let (left, right), ineqs =
        try pop_assoc v ineqs
        with Not_found -> (WSet.empty, WSet.empty), ineqs in
      let ineq_l, ineq_r, more_ineqn = 
        let ohs = mult (!/(-1) // k) (vars, cst, loc) in
        if k >/ !/0
        then
          [], [ohs],
          wset_map_to_list (fun lhs -> diff ~cmp_v lhs ohs) left
        else
          [ohs], [],
          wset_map_to_list (fun rhs -> diff ~cmp_v ohs rhs) right in
      let more_ineqn = List.filter
        (function
        | [], cst, _ when cst </ !/0 -> false
        | [], cst, loc -> raise Not_satisfiable
        | _ -> true)
        more_ineqn in
      (*[* Format.printf
        "NumS.strict-sat: v=%s@\nmore_ineqn=@ %a@\n%!"
        (var_str v) pr_ineqn more_ineqn; *]*)  
      let ineqn =
        merge cmp_w (List.sort cmp_w more_ineqn) ineqn in
      let ineqs =
        (v, (add_to_wset ineq_l left, add_to_wset ineq_r right))::ineqs in
      proj ineqs ineqn in
  let res =
    try proj ineqs ineqn; true
    with Not_satisfiable -> false in
  (*[* Format.printf
    "NumS.strict-sat: result %b@\n%!" res; *]*)
  res

(* Checks redundancy with respect to all remaining inequalities. *)
let keep_nonredund ~cmp_v ~cmp_w ineqs l =
  let rec loop ineqs acc drop = function
    | [] -> ineqs, acc, drop
    | a::l ->
      if strict_sat ~cmp_v ~cmp_w ineqs [mult !/(-1) a]
      then loop (project ~cmp_v ~cmp_w ineqs [a]) (a::acc) drop l
      else loop ineqs acc (a::drop) l in
  loop ineqs [] [] l

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
  let cnj = prune_single_redund ~cmp_v (cnj_to_w_formula cnj) in
  let eqn, ineqn, optis, suboptis = split_formula cnj in
  let g_eqn, g_ineqn, g_optis, g_suboptis =
    split_flatten ~cmp_v guard_cnj in
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
  let init_ineqs = project ~cmp_v ~cmp_w []
      (List.sort cmp_w init_ineqn) in
  (*[* Format.printf "NumS.prune_redund:@\ninit_ineqs=@ %a@\n%!"
    pr_ineqs init_ineqs; *]*)
  let opti_subopti = choices
      (g_optis @ optis) (g_suboptis @ suboptis) in
  (* Keep the union of atoms kept for each disjunct *)
  let acc_ineqs, ineqn, _ = List.fold_left
      (fun (acc_ineqs, ineqn, cands) cho ->
         let o_ineqn = ineqn_of_eqineq_w cho in
         let acc_ineqs = project ~cmp_v ~cmp_w acc_ineqs o_ineqn in
         let acc_ineqs, more_ineqn, dropped =
           keep_nonredund ~cmp_v ~cmp_w acc_ineqs cands in
         acc_ineqs, more_ineqn @ ineqn, dropped)
      (init_ineqs, [], ineqn) opti_subopti in
  (* For now, optis and suboptis are filtered only in
     [prune_single_redund] at the beginning. *)
  (*[* Format.printf "NumS.prune_redund: result@\nineqn=@ %a@\n%!"
    pr_ineqn ineqn; *]*)
  cnj_to_num_formula (eqn, ineqn, optis, suboptis)

let prune_redundant q ?localvs ~initstep cnj =
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
  let guard, cnj =
    match localvs with
      | Some localvs when not initstep ->
        List.partition
          (fun c -> VarSet.is_empty (VarSet.inter localvs (fvs_atom c)))
          cnj
      | _ -> [], cnj in
  (*[* Format.printf
    "NumS.prune_redundant: guard=%a@ res=%a@\n%!"
    pr_formula guard pr_formula cnj; *]*)
  prune_redund ~cmp_v ~cmp_w guard cnj

let simplify q ?localvs elimvs cnj =
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
    List.filter (fun (v,_) -> not (VarSet.mem v elimvs)) eqs in
  (*let ineqs =
    List.filter (fun (v,_) -> not (VarSet.mem v elimvs)) ineqs in*)
  let ans = ans_to_num_formula (eqs, ineqs, optis, suboptis) in
  let ans =
    match localvs with
    | None -> prune_redund ~cmp_v ~cmp_w [] ans
    | Some localvs ->                   (* FIXME: when not initstep *)
      let guard, res = List.partition
          (fun c -> VarSet.is_empty (VarSet.inter localvs (fvs_atom c)))
          ans in
      prune_redund ~cmp_v ~cmp_w guard res in
  let vs = VarSet.inter elimvs (fvs_formula ans) in
  (*[* Format.printf "NumS.simplify:@\nres=%a@\n%!" pr_formula ans; *]*)
  VarSet.elements vs, ans

let converge q ?localvs ~initstep cnj1 cnj2 =
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
  let guard, res =
    match localvs with
      | Some localvs when not initstep ->
        List.partition
          (fun c -> VarSet.is_empty (VarSet.inter localvs (fvs_atom c)))
          res
      | _ -> [], res in
  (*[* Format.printf "NumS.converge:@\nans1=@ %a@\nans2=@ %a@\nres=@ %a%!"
    pr_formula ans1 pr_formula ans2 pr_formula res; *]*)
  prune_redund ~cmp_v ~cmp_w guard res


let initstep_heur q ~preserve cnj =
  (* Currently, only removes opti, resp. subopti (FIXME?)
     atoms k=min(a,b) | k=max(a,b), resp. min(a,b)<=k | k<=max(a,b) where
     a or b is a constant, assuming the atom is directed. *)
  List.filter
    (function
      | Eq _ | Leq _ -> true
      | Opti (Add ([Lin _; Cst _]), _, _)
      | Opti (_, Add ([Lin _; Cst _]), _) -> false
      | Opti (Add (_::_::_), Add (_::_::_), _) -> true
      | Opti _ -> false
      | Subopti (Add ([Lin _; Cst _]), _, _)
      | Subopti (_, Add ([Lin _; Cst _]), _) -> false
      | Subopti (Add (_::_::_), Add (_::_::_), _) -> true
      | Subopti _ -> false)
    cnj

type state = w_subst * ineqs * optis * suboptis
let empty_state = [], [], [], []

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

let holds q avs (eqs, ineqs, optis, suboptis : state) cnj : state =
  let cmp_v = make_cmp q in
  let cmp_w (vars1,_,_) (vars2,_,_) =
    match vars1, vars2 with
    | [], [] -> 0
    | _, [] -> -1
    | [], _ -> 1
    | (v1,_)::_, (v2,_)::_ -> cmp_v v1 v2 in
  let eqs, ineqs, optis, suboptis =
    solve ~use_quants:avs
      ~eqs ~ineqs ~optis ~suboptis ~cnj ~cmp_v ~cmp_w q.uni_v in
  eqs, ineqs, optis, suboptis

let negation_elim q ~verif_cns neg_cns =
  (*[* Format.printf "NumS.negation_elim:@\nneg_cns=@ %a@\n%!"
    (pr_line_list "| " pr_formula) (List.map fst neg_cns); *]*)
  (*[* Format.printf "verif_cns=@ %a@\n%!"
    (pr_line_list "| " pr_state) verif_cns; *]*)
  let validated_num d_n_cs =
    try
      List.iter
        (fun state -> ignore (satisfiable_exn ~state d_n_cs))
        verif_cns; true
    with Terms.Contradiction _ -> false in
  (* The formula will be conjoined to the branches. Note that the
          branch will be non-recursive.  *)
  let res = concat_map
      (fun (cnj, loc) ->
         let d_n_cs = find_map
             (fun (c, cs) ->
                match c with
                | Leq (lhs, rhs, lc) ->
                  let w = NumDefs.diff lhs rhs in
                  let k = denom w in
                  let lhs = NumDefs.scale_term ~-k 1 w in
                  let d_n_cs = Leq (lhs, Cst (-1, 1), loc)::cs in
                  if validated_num d_n_cs
                  then Some d_n_cs else None
                | Eq (lhs, rhs, lc) ->
                  let w = NumDefs.diff lhs rhs in
                  let k = denom w in
                  let lhs1 = NumDefs.scale_term ~-k 1 w in
                  let d1_n_cs = Leq (lhs1, Cst (-1, 1), loc)::cs in
                  if validated_num d1_n_cs then Some d1_n_cs
                  else
                    let lhs2 = NumDefs.scale_term k 1 w in
                    let d2_n_cs = Leq (lhs2, Cst (-1, 1), loc)::cs in
                    if validated_num d2_n_cs then Some d2_n_cs
                    else None
                | Opti _ -> None
                | Subopti (t1, t2, lc) ->
                  let k1 = denom t1 in
                  let lhs1 = NumDefs.scale_term ~-k1 1 t1 in
                  let k2 = denom t2 in
                  let lhs2 = NumDefs.scale_term ~-k2 1 t2 in
                  let d_n_cs =
                    Leq (lhs1, Cst (-1, 1), loc)::
                      Leq (lhs2, Cst (-1, 1), loc)::cs in
                  if validated_num d_n_cs then Some d_n_cs
                  else None)
             (one_out cnj) in
         (*[* Format.printf "NumS.negation_elim: selected d=@ %a@\n%!"
           (pr_some pr_formula) d_n_cs; *]*)
         list_some_list d_n_cs)
      neg_cns in
  (*[* Format.printf "NumS.negation_elim:@\nres=@ %a@\n%!"
    pr_formula res; *]*)
  res

type subst = (var_name * (term * loc)) list

let subst_num_formula sb phi =
  if sb=[] then phi
  else List.map (subst_atom (fun _ _ x->x) sb) phi

let subst_formula sb phi =
  if sb=[] then phi
  else List.map (subst_atom Terms.num_v_unbox sb) phi

(* match q.cmp_v v1 v2 with
  | Left_of -> 1
  | Right_of -> -1
  | Same_quant -> compare v2 v1
 *)
let separate_subst_aux q ~no_csts ~keep cnj =
  let cmp_v = make_cmp q in
  let cmp_v v1 v2 =
    let c1 = VarSet.mem v1 keep and c2 = VarSet.mem v2 keep in
    if c1 && c2 then cmp_v v1 v2
    else if c1 then -1
    else if c2 then 1
    else cmp_v v1 v2 in
  let cmp_w (vars1,_,_) (vars2,_,_) =
    match vars1, vars2 with
    | [], [] -> 0
    | _, [] -> -1
    | [], _ -> 1
    | (v1,_)::_, (v2,_)::_ -> cmp_v v1 v2 in
  let eqs, _, _, _ =
    solve ~cnj ~cmp_v ~cmp_w q.uni_v in
  let eqs, more_eqs = List.partition
      (fun (v,(vars,_,_)) ->
         not (no_csts && vars=[]) &&
         not (VarSet.mem v keep))
      eqs in
  (*[* Format.printf "NumS.separate_subst: eq-keys=%a@\n%!"
    pr_vars (vars_of_list (List.map fst eqs)); *]*)
  let _, ineqn, optis, suboptis = split_flatten ~cmp_v cnj in
  (* FIXME: drop [keep] variables before substituting *)
  let ineqn = List.map (subst_w ~cmp_v eqs) ineqn in
  let optis = List.map (subst_2w ~cmp_v eqs) optis in
  let suboptis = List.map (subst_2w ~cmp_v eqs) suboptis in
  let ineqn = List.filter
    (function [], cst, _ when cst <=/ !/0 -> false | _ -> true)
    ineqn in
  let sb = expand_subst eqs in
  let phi_num = cnj_to_num_formula ([], ineqn, optis, suboptis) in
  (*[* Format.printf "NumS.separate_subst:@ sb=%a@ phi=%a@\n%!"
    pr_num_subst sb pr_formula phi_num; *]*)
  let more = List.map
      (fun (v,(t,lc)) -> Eq (Lin (1,1,v), t, lc))
      (expand_subst more_eqs) in
  sb, more @ phi_num

(* Optimization. FIXME: check if worth it. *)
exception Not_substitution

(* FIXME: check if using [separate_subst_aux] instead can be fixed. *)
let separate_num_subst q ~no_csts ~keep cnj =
  try
    let sb, phi = partition_map
        (function
          | Eq (Lin _, Cst _, _) as a when no_csts -> Right a
          | Eq (Cst _, Lin _, _) as a when no_csts -> Right a
          | Eq (Lin (j,k,v1), (Lin (_,_,v2) as t), lc)
            when VarSet.mem v2 keep ->
            (* inverted coefficient *)
            Left (v1, (scale_term k j t, lc))
          | Eq (Lin (_,_,v1) as t, Lin (j,k,v2), lc)
            when VarSet.mem v1 keep ->
            Left (v2, (scale_term k j t, lc))
          | Eq (_, Lin (_,_,v), _) as a when VarSet.mem v keep ->
            Right a
          | Eq (Lin (_,_,v), _, _) as a when VarSet.mem v keep ->
            Right a
          | Eq (Lin (j,k,v1), t, lc)
            when VarSet.for_all
                (fun v2 -> q.cmp_v v1 v2 <> Left_of) (fvs_term t) ->
            Left (v1, (scale_term k j t, lc))
          | Eq (t, Lin (j,k,v1), lc)
            when VarSet.for_all
                (fun v2 -> q.cmp_v v1 v2 <> Left_of) (fvs_term t) ->
            Left (v1, (scale_term k j t, lc))
          | Eq _ -> raise Not_substitution
          | a -> Right a)
        cnj in
    (*[* Format.printf "NumS.separate_subst:@ pre-sb=%a@\n%!"
      pr_num_subst sb; *]*)
    let sb = List.map
        (function
          | _, [] -> assert false
          | v, [t, lc] -> v, (t, lc)
          | v, (sv :: _ as rhs) ->
            try v, List.find (fun (t,_) ->
                VarSet.exists (fun v->VarSet.mem v keep) (fvs_term t))
                rhs
            with Not_found -> v, sv)
        (collect sb) in
    (*[* Format.printf "NumS.separate_subst:@ post-sb=%a@\n%!"
      pr_num_subst sb; *]*)
    let keys = vars_of_list (List.map fst sb) in
    List.iter (fun (_,(t,_)) ->
        iter_term_vars (fun v->if VarSet.mem v keys
                         then raise Not_substitution) t)
      sb;
    sb, subst_num_formula sb phi
  with Not_substitution -> separate_subst_aux q ~no_csts ~keep cnj

let separate_subst q ?(no_csts=false) ?(keep=VarSet.empty) cnj =
  (*[* Format.printf "NumS.separate_subst: keep=%a@ cnj=%a@\n%!"
    pr_vars keep pr_formula cnj; *]*)
  let sb, phi = separate_num_subst q ~no_csts ~keep cnj in
  (*[* Format.printf "NumS.separate_subst: res phi=%a@\n%!"
    pr_formula phi; *]*)
  List.map (fun (v,(t,lc)) -> v, (Terms.num t, lc)) sb, phi

    
let transitive_cl cnj =
  let eqs = concat_map
    (function
      | Eq (t1, t2, loc) -> [t1, t2, loc; t2, t1, loc]
      | _ -> [])
    cnj in
  let ineqs = concat_map
    (function
      | Leq (t1, t2, loc) -> [t1, t2, loc]
      | _ -> [])
    cnj in
  let other = map_some
    (function Eq _ | Leq _ -> None | a -> Some a)
    cnj in
  let eqs = Joint.transitive_cl eqs in
  let cmp_v v1 v2 = Pervasives.compare v1 v2 in
  let ineqs = ineq_transitive_cl ~cmp_v ineqs in
  let cnj = Hashtbl.fold
      (fun (i,j) lc cnj -> if i<j then Eq (i, j, lc)::cnj else cnj)
      eqs [] in
  let cnj = Hashtbl.fold
      (fun (i,j) lc cnj -> Leq (i, j, lc)::cnj)
      ineqs cnj in
  other @ cnj
