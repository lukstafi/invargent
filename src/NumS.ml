(** Numeric sort operations for InvarGenT.

    Released under the GNU General Public Licence (version 2 or
    higher), NO WARRANTY of correctness etc. (C) Lukasz Stafiniak 2013
    @author Lukasz Stafiniak lukstafi (AT) gmail.com
    @since Mar 2013
*)

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

let early_num_abduction = ref false(* true *)
let abd_rotations = ref (* 2 *)3
let abd_prune_at = ref (* 4 *)6(* 10 *)
let abd_timeout_count = ref (* 500 *)1000(* 5000 *)(* 50000 *)
let abd_fail_timeout_count = ref 10
let disjelim_rotations = ref 3
let passing_ineq_trs = ref false

let abd_fail_flag = ref false
let abd_timeout_flag = ref false

let (!/) i = num_of_int i
type w = (var_name * num) list * num * loc
type w_subst = (var_name * w) list
type cw_subst = ((var_name, bool) choice * w) list
type ineqs = (var_name * (w list * w list)) list
type optis = (w * w) list

let mult c (vars, cst, loc) =
  List.map (fun (v,k) -> v, c */ k) vars, c */ cst, loc

let sum_w cmp (vars1, cst1, loc1) (vars2, cst2, loc2) =
  let loc = loc_union loc1 loc2 in
  let vars = map_reduce (+/) (!/0) (vars1 @ vars2) in
  let vars = List.sort cmp
    (List.filter (fun (_,k) -> k <>/ !/0) vars) in
  vars, cst1 +/ cst2, loc

let diff cmp w1 w2 = sum_w cmp w1 (mult !/(-1) w2)

let zero_p (vars, cst, _) = vars = [] && cst =/ !/0
let taut iseq (vars, cst, _) =
  vars = [] && ((iseq && cst =/ !/0) || (not iseq && cst <=/ !/0))

let equal_w cmp w1 w2 = zero_p (diff cmp w1 w2)

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
    (pr_sep_list ";" pr_w) wl (var_str v) (pr_sep_list ";" pr_w) wr

let pr_ineqs ppf (ineqs : ineqs) =
  pr_sep_list "," pr_ineq ppf ineqs

let pr_opti ppf (w1, w2) =
  Format.fprintf ppf "@[<2>opti(%a,@ %a)@]" pr_w w1 pr_w w2

let pr_optis ppf (optis : optis) =
  pr_sep_list "," pr_opti ppf optis

let pr_ans ppf (eqs, ineqs) =
  Format.fprintf ppf "%a@ ∧@ %a" pr_w_subst eqs pr_ineqs ineqs

let pr_eq ppf w = Format.fprintf ppf "%a@ = 0" pr_w w
let pr_ineq ppf w = Format.fprintf ppf "%a@ ≤ 0" pr_w w
let pr_eqn ppf eqn =
  pr_sep_list "," pr_eq ppf eqn
let pr_ineqn ppf ineqn =
  pr_sep_list "," pr_ineq ppf ineqn
let pr_eqnineqn ppf (eqn, ineqn) =
  Format.fprintf ppf "%a@ ∧@ %a" pr_eqn eqn pr_ineqn ineqn
let pr_eqineq_br ppf ((d_eqn, d_ineqn, _), (c_eqn, c_ineqn, _)) =
    Format.fprintf ppf "@[<2>%a,@ %a@ ⟹@ %a,@ %a@]"
    pr_eqn d_eqn pr_ineqn d_ineqn
    pr_eqn c_eqn pr_ineqn c_ineqn

let unsubst sb =
  List.map (fun (v, (vars, cst, loc)) -> (v, !/(-1))::vars, cst, loc) sb

let unsolve (ineqs : ineqs) : w list = concat_map
  (fun (v, (left, right)) ->
    List.map (fun (vars, cst, loc) -> (v, !/(-1))::vars, cst, loc)
      left @
      List.map (fun rhs ->
        let vars, cst, loc = mult !/(-1) rhs in
        (v, !/1)::vars, cst, loc)
      right)
  ineqs

let flatten cmp a : (w, w) choice option * (w*w) list =
  let rec flat ((vars, cst, loc), optis as acc) = function
    | Add sum ->
      List.fold_left flat acc sum
    | Cst (j,k) -> (vars, cst +/ (!/j // !/k), loc), optis
    | Lin (j,k,v) -> ((v, !/j // !/k)::vars, cst, loc), optis
    | Min (v,t1,t2) ->
      let zero = [], !/0, loc in
      let (vars1, cst1, lc1), optis = flat (zero, optis) t1 in
      let (vars2, cst2, lc2), optis = flat (zero, optis) t2 in
      ((v, !/1)::vars, cst, loc),
      (((v, !/1)::List.map (fun (v,k) -> v, !/(-1) */ k) vars1, cst1, lc1),
       ((v, !/1)::List.map (fun (v,k) -> v, !/(-1) */ k) vars2, cst2, lc2))
      ::optis
    | Max (v,t1,t2) -> 
      let zero = [], !/0, loc in
      let (vars1, cst1, lc1), optis = flat (zero, optis) t1 in
      let (vars2, cst2, lc2), optis = flat (zero, optis) t2 in
      ((v, !/1)::vars, cst, loc),
      (((v, !/(-1))::vars1, cst1, lc1),
       ((v, !/(-1))::vars2, cst2, lc2))
      ::optis in
  let collect t1 t2 loc =
    let zero = [], !/0, loc in
    let w1, optis = flat (zero, []) t1 in
    let w2, optis = flat (zero, optis) t2 in
    diff cmp w1 w2, optis in
  match a with
  | Eq (t1, t2, loc) ->
    let w, optis = collect t1 t2 loc in
    Some (Left w), optis
  | Leq (t1, t2, loc) ->
    let w, optis = collect t1 t2 loc in    
    Some (Right w), optis
  | Opti (t1, t2, loc) ->
    let zero = [], !/0, loc in
    let w1, optis = flat (zero, []) t1 in
    let w2, optis = flat (zero, optis) t2 in
    None, (w1, w2)::optis

let subst_w cmp (eqs : w_subst) (vars, cst, loc : w) : w =
  let sums = List.map
    (fun (v,k) ->
      try let vars, cst, _ = mult k (List.assoc v eqs) in vars, cst
      with Not_found -> [v,k], !/0)
    vars in
  let vars, csts = List.split sums in
  let vars = map_reduce (+/) (!/0) (List.concat vars) in
  let vars = List.sort cmp
    (List.filter (fun (_,k) -> k <>/ !/0) vars) in
  let cst = List.fold_left (+/) cst csts in
  vars, cst, loc

let subst_2w cmp (eqs : w_subst) (w1, w2) =
  subst_w cmp eqs w1, subst_w cmp eqs w2

let subst_ineqs cmp eqs ineqs = List.map
  (fun (v, (left, right)) ->
    v, (List.map (subst_w cmp eqs) left, List.map (subst_w cmp eqs) right))
  ineqs

let subst_one cmp (v, w) (vars, cst, loc as arg) =
  try
    let k, vars = pop_assoc v vars in
    let w_vs, w_cst, w_loc = mult k w in
    let vars = map_reduce (+/) (!/0) (w_vs @ vars) in
    let vars = List.sort cmp
      (List.filter (fun (_,k) -> k <>/ !/0) vars) in
    let cst = w_cst +/ cst in
    vars, cst, loc
  with Not_found -> arg

let subst_one_sb cmp w_sb sb =
  List.map (fun (v, w) -> v, subst_one cmp w_sb w) sb

let frac_of_num k =
  let k = ratio_of_num k in
  Big_int.int_of_big_int (Ratio.numerator_ratio k),
  Big_int.int_of_big_int (Ratio.denominator_ratio k)

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

let expand_sides (vars, cst, loc) =
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

let expand_atom equ (_,_,loc as w) =
  let left, right = expand_sides w in
  if equ then Eq (left, right, loc) else Leq (left, right, loc)

let expand_subst eqs =
  List.map (fun (v, (_,_,loc as w)) -> v, (expand_w w, loc)) eqs    

let expand_opti ((_,_,loc as w1), w2) =
  Opti (expand_w w1, expand_w w2, loc)

let ans_to_num_formula (eqs, ineqs, optis) =
  List.map (expand_atom true) (unsubst eqs)
  @ List.map (expand_atom false) (unsolve ineqs)
  @ List.map expand_opti optis

let eqineq_to_num_formula (eqn, ineqn) =
  List.map (expand_atom true) eqn
  @ List.map (expand_atom false) ineqn

let cnj_to_num_formula (eqn, ineqn, optis) =
  List.map (expand_atom true) eqn
  @ List.map (expand_atom false) ineqn
  @ List.map expand_opti optis

let num_to_formula phi = List.map (fun a -> Terms.A (Terms.Num_atom a)) phi

let eqineq_loc_union (eqn, ineqn) =
  List.fold_left loc_union dummy_loc
    (List.map (fun (_,_,lc) -> lc) (eqn @ ineqn))

let un_ans (eqs, ineqs) = unsubst eqs, unsolve ineqs

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

let split_flatten cmp cnj =
  let more_eqineqn, more_optis =
    List.split (List.map (flatten cmp) cnj) in
  let more_eqineqn = map_some (fun x->x) more_eqineqn in
  let more_optis = List.concat more_optis in
  let more_eqn, more_ineqn = partition_choice more_eqineqn in
  more_eqn, more_ineqn, more_optis

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
    ?(eqs=[]) ?(ineqs=[]) ?(eqs'=[])
    ?(optis=[]) ?(eqn=[]) ?(ineqn=[]) ?(cnj=[])
    cmp cmp_w uni_v =
  let use_quants, bvs = match use_quants with
    | None -> false, VarSet.empty
    | Some bvs -> true, bvs in
  let eqs = if eqs' = [] then eqs else List.map
      (fun (v,eq) -> v, subst_w cmp eqs' eq) eqs @ eqs' in
  let ineqs = if eqs' = [] then ineqs else List.map
      (fun (v,(wl,wr)) -> v,
        (List.map (subst_w cmp eqs') wl,
         List.map (subst_w cmp eqs') wr)) ineqs in
  let more_eqn, more_ineqn, more_optis = split_flatten cmp cnj in
  let eqn = eqn @ flat2 optis @ more_eqn in
  let ineqn = ineqn @ more_ineqn in
  assert (not strict || eqn = []);
  let eqn = if eqs=[] then eqn else List.map (subst_w cmp eqs) eqn in
  let ineqn = if eqs=[] then ineqn else List.map (subst_w cmp eqs) ineqn in
  let eqn = List.map
    (fun (vars, cst, loc) ->
      List.filter (fun (v,k)->k <>/ !/0) vars, cst, loc) eqn in
  let eqn = List.sort cmp_w eqn in
  (*[* Format.printf "NumS.solve:@ eqn=@ %a@ ineqn=@ %a@\n%!"
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
      let acc = subst_one_sb cmp w_sb acc in
      let eqn = List.map (subst_one cmp w_sb) eqn in
      elim (w_sb::acc) eqn
    | ([], cst, loc)::eqn when cst =/ !/0 -> elim acc eqn
    | ([], cst, loc)::eqn ->
      let msg =
        "Failed numeric equation ("^Num.string_of_num cst^"=0)" in
      raise (Terms.Contradiction (Num_sort, msg, None, loc)) in
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
    concat_map
      (fun (v, w) ->
        try
          let left, right = List.assoc v ineqs in
          List.map (fun lhs -> diff cmp lhs w) left @
            List.map (fun rhs -> diff cmp w rhs) right
        with Not_found -> [])
      eqn in
  let ineqn = List.sort cmp_w (more_ineqn @ ineqn) in
  (*[* Format.printf "NumS.solve:@\neqs=%a@\nsimplified ineqn=@ %a@\n%!"
    pr_w_subst (eqn @ eqs) pr_ineqn ineqn; *]*)
  let project v (vars, cst, loc as lhs) rhs =
    if equal_w cmp lhs rhs
    then
      let w = (v, !/(-1))::vars, cst, loc in
      if strict then
        let a = expand_atom false w in
        let t1, t2 = match a with
          | Leq (t1, t2, _) -> t1, t2 | _ -> assert false in
        raise (Terms.Contradiction
                 (Num_sort, "Failed numeric strict inequality",
                  Some (Terms.num t1, Terms.num t2), loc))
      else Right w
    else Left (diff cmp lhs rhs) in
  let rec proj ineqs implicits ineqn =
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
        try pop_assoc v ineqs with Not_found -> ([], []), ineqs in
      let ineq_l, ineq_r, (more_ineqn, more_implicits) = 
        let ohs = mult (!/(-1) // k) (vars, cst, loc) in
        if k >/ !/0
        then
          [], [ohs],
          partition_map (fun lhs -> project v lhs ohs) left
        else
          [ohs], [],
          partition_map (fun rhs -> project v ohs rhs) right in
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
      let ineqn =
        merge cmp_w (List.sort cmp_w more_ineqn) ineqn in
      let ineqs = (v, (ineq_l @ left, ineq_r @ right))::ineqs in
      proj ineqs (more_implicits @ implicits) ineqn in
  let propagate (m, n) =
    let (m_vars, m_cst, _ as m) = subst_w cmp eqn m
    and (n_vars, n_cst, _ as n) = subst_w cmp eqn n in
    if m_vars=[] && m_cst =/ !/0 || n_vars=[] && n_cst =/ !/0
    then None
    (* Possible contradiction will be recognized from the implicit
       equality on next iteration. *)
    else if m_vars=[] && m_cst <>/ !/0 then Some (Right n)
    else if n_vars=[] && n_cst <>/ !/0 then Some (Right m)
    else if equal_w cmp m n then Some (Right m)
    else Some (Left (m, n)) in
  let optis =
    if eqn = [] then optis, []
    else partition_choice (map_some propagate optis) in
  eqn @ eqs, proj ineqs [] ineqn, optis

let solve ?use_quants ?strict ?eqs ?ineqs ?eqs' ?optis ?eqn ?ineqn ?cnj
    cmp cmp_w uni_v =
  let rec loop (eqs,(ineqs,implicits1),(optis,implicits2)) =
    let implicits = implicits2 @ implicits1 in
    if implicits=[] then eqs, ineqs, optis
    else (
      (*[* Format.printf "solve: implicits=%a@\n%!"
        pr_eqn implicits; *]*)
      loop
        (solve_aux ?use_quants ?strict ~eqs ~ineqs ~optis ~eqn:implicits
           cmp cmp_w uni_v)) in
  loop (solve_aux ?use_quants ?strict ?eqs ?ineqs ?eqs' ?optis
          ?eqn ?ineqn ?cnj cmp cmp_w uni_v)

let fvs_w (vars, _, _) = vars_of_list (List.map fst vars)


exception Result of w_subst * ineqs * optis

let debug_dep = ref 0
let no_pass_msg = "Could not solve numeric SCA (algorithm step 5b)"

let implies cmp cmp_w uni_v eqs ineqs c_eqn c_ineqn =
  List.for_all
    (fun w ->
      match subst_w cmp eqs w with
      | [], cst, _ -> cst =/ !/0
      | w' ->
        (*[* Format.printf "implies: false eq w=%a@ w'=%a@\n%!"
          pr_w w pr_w w'; *]*)
        false)
    c_eqn
  && List.for_all
    (fun w ->
      let ineqn = [mult !/(-1) w] in
      try ignore
            (solve ~strict:true ~eqs ~ineqs ~ineqn cmp cmp_w uni_v);
        (*[* Format.printf "implies: false ineq w=%a@\n%!"
          pr_w w; *]*)        
        false
      with Terms.Contradiction _ -> true)
    c_ineqn

(* FIXME *)
let implies_ans cmp cmp_w uni_v (eqs, ineqs, optis) (c_eqn, c_ineqn, c_optis) =
  implies cmp cmp_w uni_v eqs ineqs c_eqn c_ineqn  

(* FIXME: should [bvs] variables be considered not universal? *)
let revert_cst_n_uni cmp cmp_v uni_v ~bvs eqs0 c_ineqn0 c_optis0 =
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
           uni_v v1 ||
           not (cmp_v v1 v2 = Left_of) in
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
         let leq (v1,_) (v2,_) = not (cmp_v v1 v2 = Left_of) in
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
  let c6eqs = c6eqs @ List.map (fun (v,w)->v, subst_w cmp u_sb w) eqs0 in
  (*[* Format.printf "revert:@ old_sb=%a@ c6eqs=%a@\neqs0=%a@\n%!"
    pr_w_subst old_sb pr_w_subst c6eqs pr_w_subst eqs0; *]*)
  let eqs0 = old_sb @ eqs0 in
  let c6_ineqn0 =
      List.map (subst_w cmp u_sb) c_ineqn0 in
  let c6_optis0 =
      List.map (subst_2w cmp u_sb) c_optis0 in
  c6eqs, eqs0, c6_ineqn0, c6_optis0

exception Timeout
type w_atom = Eq_w of w | Ineq_w of w | Opti_w of (w * w)

let rec taut = function
  | Eq_w (vars, cst, _) -> vars=[] && cst =/ !/0
  | Ineq_w (vars, cst, _) -> vars=[] && cst <=/ !/0
  | Opti_w (w1, w2) -> taut (Ineq_w w1) && taut (Ineq_w w2)

let pr_w_atom ppf = function
  | Eq_w w -> Format.fprintf ppf "%a=0" pr_w w
  | Ineq_w w -> Format.fprintf ppf "%a≤0" pr_w w
  | Opti_w (w1, w2) -> Format.fprintf ppf "opti(%a,%a)" pr_w w1 pr_w w2

(* Equality-like atoms cannot be weakened using transitivity with an
   inequality while remaining in the same class of atoms. *)
let iseq_w_atom = function
  | Eq_w _ -> true
  | Ineq_w _ -> false
  | Opti_w _ -> true

let split_w_atom = function
  | Eq_w w -> [w], [], []
  | Ineq_w w -> [], [w], []
  | Opti_w w12 -> [], [], [w12]

let trans_w_atom cmp tr = function
  | Eq_w w -> Eq_w (sum_w cmp tr w)
  | Ineq_w w -> Ineq_w (sum_w cmp tr w)
  | Opti_w (w1, w2) -> Opti_w (sum_w cmp tr w1, sum_w cmp tr w2)

(* FIXME: [d_optis] will be eliminated prior to entering here. *)
let abd_simple cmp cmp_w cmp_v uni_v ~bvs ~discard ~validate
    skip (eqs_i, ineqs_i, optis_i)
    ((d_eqn, d_ineqn, d_optis), (c_eqn, c_ineqn, c_optis)) =
  let skip = ref skip in
  let counter = ref 0 in
  try
    (* 1 *)
    let d_eqn' = List.map (subst_w cmp eqs_i) d_eqn
    and c_eqn' = List.map (subst_w cmp eqs_i) c_eqn in
    let d_ineqn' = List.map (subst_w cmp eqs_i) d_ineqn
    and d_optis' = List.map (subst_2w cmp eqs_i) d_optis
    and c_ineqn' = List.map (subst_w cmp eqs_i) c_ineqn
    and c_optis' = List.map (subst_2w cmp eqs_i) c_optis in
    (* Extract (almost) all equations implied by premise and conclusion. *)
    let eqs0, _, _ =
      solve ~ineqs:ineqs_i ~eqn:(d_eqn' @ c_eqn')
        ~ineqn:(flat2 c_optis' @ d_ineqn' @ c_ineqn') cmp cmp_w uni_v in
    (* [eqs0] does not contain [eqs_i]. *)
    let d_ineqn0 = List.map (subst_w cmp eqs0) d_ineqn' in
    let d_optis0 = List.map (subst_2w cmp eqs0) d_optis' in
    let c_ineqn0 = List.map (subst_w cmp eqs0) c_ineqn' in
    let c_optis0 = List.map (subst_2w cmp eqs0) c_optis' in
    (* 2 *)
    let zero = [], !/0, dummy_loc in
    let prune (vars, _, _ as w) =
      if List.length vars < !abd_prune_at then Some w else None in
    let add_tr ks_eq eq_trs a =
      (*[* Format.printf "add_eq/ineq_tr: a=%a@\n%!" pr_w a; *]*)
      let kas = lazmap (fun k -> mult k a) ks_eq in
      let add_kas tr =
        lazmap_some (fun ka -> prune (sum_w cmp ka tr)) kas in
      lazconcat_map add_kas eq_trs in
    let add_atom_tr ks_eq eq_trs = function
      | Eq_w a | Ineq_w a -> add_tr ks_eq eq_trs a
      | Opti_w (a1, a2) -> add_tr ks_eq (add_tr ks_eq eq_trs a1) a2 in
    (*[* Format.printf
      "NumS.abd_simple: 2.@\neqs_i=@ %a@\nineqs_i=@ %a@\nd_eqn=@ %a@ d_ineqn=@ %a@\nc_eqn=@ %a@\nc_ineqn=@ %a@\nd_ineqn0=@ %a@\nc_ineqn0=@ %a@\neqs0=@ %a@\n%!"
      pr_w_subst eqs_i pr_ineqs ineqs_i pr_eqn d_eqn pr_ineqn d_ineqn
      pr_eqn c_eqn pr_ineqn c_ineqn pr_ineqn d_ineqn0
      pr_ineqn c_ineqn0 pr_w_subst eqs0;
    *]*)
    (* 3 *)
    let eqs0, c6eqs, c6ineqn, c6optis =
      revert_cst_n_uni cmp cmp_v uni_v ~bvs eqs0 c_ineqn0 c_optis0 in
    (* 4 *)
    let rec loop add_eq_tr add_ineq_tr eq_trs ineq_trs
        eqs_acc ineqs_acc optis_acc
        c6eqs c0eqs c6ineqn c0ineqn c6optis c0optis =
      (*[* let ddepth = incr debug_dep; !debug_dep in *]*)
      incr counter; if !counter > !abd_timeout_count then raise Timeout;
      let a, c6a, c0eqs, c6eqs, c0ineqn, c6ineqn, c0optis, c6optis =
        match c0eqs, c6eqs, c0ineqn, c6ineqn, c0optis, c6optis with
        | (v,(vs,cst,lc))::c0eqs, (c6v,(c6vs,c6cst,c6lc))::c6eqs,
          c0ineqn, c6ineqn, c0optis, c6optis ->
          let a = (v,!/(-1))::vs,cst,lc
          and c6a = (c6v,!/(-1))::c6vs,c6cst,c6lc in
          Eq_w a, Eq_w c6a, c0eqs, c6eqs, c0ineqn, c6ineqn, c0optis, c6optis
        | [], [], a::c0ineqn, c6a::c6ineqn, c0optis, c6optis ->
          Ineq_w a, Ineq_w c6a, [], [], c0ineqn, c6ineqn, c0optis, c6optis
        | [], [], [], [], a::c0optis, c6a::c6optis ->
          Opti_w a, Opti_w c6a, [], [], [], [], c0optis, c6optis
        | [], [], [], [], [], [] ->
          if (!skip > 0 && (decr skip; true))
          || List.exists
               (implies_ans cmp cmp_w uni_v (eqs_acc, ineqs_acc, optis_acc))
               (discard : (w list * w list * optis) list)
          then
            (raise
               (Terms.Contradiction
                  (Num_sort,
                   "Numeric SCA: skipping", None, dummy_loc)))
          else raise (Result (eqs_acc, ineqs_acc, optis_acc))
        | _ -> assert false in
      (* 5 *)
      (* We get a substitution in [~eqs:(eqs_acc @ c0eqs)]
         because initial equations [c0eqs] are a solved form with
         [eqs_i], and all transformations are through equations
         absent from [eqs_acc]. *)
      let b_eqs, b_ineqs, b_optis =
        solve ~eqs:(eqs_acc @ c0eqs)
          ~ineqs:ineqs_acc ~eqn:d_eqn ~ineqn:(d_ineqn0 @ c0ineqn)
          ~optis:(optis_acc @ d_optis0 @ c0optis)
          cmp cmp_w uni_v in
      (*[* Format.printf
        "NumS.abd_simple: [%d] 5. a=@ %a@\nb_eqs=@ %a@\nb_ineqs=@ %a@\n%!"
        ddepth pr_w_atom a pr_w_subst b_eqs pr_ineqs b_ineqs;
      *]*)

      if taut a
      || implies cmp cmp_w uni_v b_eqs b_ineqs c_eqn c_ineqn
      then (
        (* 6 *)
        (* [ineq_trs] include [eq_trs]. *)
        (*[* Format.printf "NumS.abd_simple: [%d] STEP 6.@\nc6remain=%a@\n%!"
          ddepth pr_w_subst c6eqs;
        *]*)
        loop add_eq_tr add_ineq_tr eq_trs ineq_trs eqs_acc
          ineqs_acc optis_acc c6eqs c0eqs c6ineqn c0ineqn c6optis c0optis)
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
            let eqn, ineqn, optin = split_w_atom a' in
            let eqs_acc, ineqs_acc, optis_acc =
              solve ~use_quants:bvs
                ~eqs:eqs_acc ~ineqs:ineqs_acc ~optis:(optin @ optis_acc)
                ~eqn ~ineqn cmp cmp_w uni_v in
            ignore (validate (eqs_acc, ineqs_acc, optis_acc));
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
              eqs_acc ineqs_acc optis_acc
              c6eqs c0eqs c6ineqn c0ineqn c6optis c0optis
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
        laziter (fun tr -> try_trans (trans_w_atom cmp tr a)) trs;
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
        let add_Eq_tr = add_atom_tr ks_eq in
        let eq_trs = List.fold_left add_eq_tr eq_trs d_eqn' in
        let add_ineq_tr = add_tr ks_ineq in
        let add_Ineq_tr = add_atom_tr ks_ineq in
        let ineq_trs = List.fold_left add_ineq_tr eq_trs d_ineqn0 in
        loop add_Eq_tr add_Ineq_tr eq_trs ineq_trs
          eqs_i ineqs_i optis_i
          c6eqs eqs0 c6ineqn c_ineqn0 c6optis c_optis0
      done; None
    with Result (ans_eqs, ans_ineqs, ans_optis) ->
      Some (ans_eqs, ans_ineqs, ans_optis)
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
  type accu = w_subst * ineqs * optis
  type args = {
    cmp : (var_name * Num.num -> var_name * Num.num -> int);
    cmp_w : (w -> w -> int);
    cmp_v : (var_name -> var_name -> var_scope);
    uni_v : (var_name -> bool);
    bvs : VarSet.t}
  type answer = accu
  type discarded = w list * w list * optis
  type branch = (w list * w list * optis) * (w list * w list * optis)

  let abd_fail_timeout = !abd_fail_timeout_count
  let abd_fail_flag = abd_fail_flag

  let abd_simple {cmp; cmp_w; cmp_v; uni_v; bvs}
      ~discard ~validate acc br =
    abd_simple cmp cmp_w cmp_v uni_v ~bvs
      ~discard ~validate 0 acc br

  let extract_ans ans = ans

  (* FIXME *)
  let discard_ans (eqs, ineqs, optis) =
    unsubst eqs, unsolve ineqs, optis

  let concl_of_br ((_, concl) : branch) =
    num_to_formula (cnj_to_num_formula concl)

  let is_taut (eqs, ineqs, optis) = eqs=[] && ineqs=[] && optis=[]

  (* FIXME *)
  let pr_branch pp ((d_eqn, d_ineqn, d_optis), (c_eqn, c_ineqn, c_optis)) =
    Format.fprintf pp
      "@[<2>d_eqn=%a@\nd_ineqn=%a@\n⟹@\nc_eqn=%a@\nc_ineqn=%a@\n@]"
      pr_eqn d_eqn pr_ineqn d_ineqn pr_eqn c_eqn pr_ineqn c_ineqn

  (* FIXME *)
  let pr_ans pp (eqs, ineqs, optis) =
    Format.fprintf pp "eqs=%a@\nineqs=%a@\n%!"
      pr_w_subst eqs pr_ineqs ineqs
end

module JCA = Joint.JointAbduction (NumAbd)

(* FIXME: eliminate optis from premise, but first try simplifying
   them with both premise and conclusion of a branch. *)
let abd q ~bvs ~discard ?(iter_no=2) brs =
  abd_timeout_flag := false;
  let cmp_v = make_cmp q in
  let cmp (v1,_) (v2,_) = cmp_v v1 v2 in
  let cmp_w (vars1,cst1,_) (vars2,cst2,_) =
    match vars1, vars2 with
    | [], [] -> 0
    | _, [] -> -1
    | [], _ -> 1
    | (v1,_)::_, (v2,_)::_ -> cmp_v v1 v2 in
  (*[* Format.printf "NumS.abd: iter_no=%d@ bvs=%s@\n%!"
    iter_no
    (String.concat "," (List.map var_str (VarSet.elements bvs))); *]*)
  let brs = List.map
      (fun (nonrec, prem, concl) ->
         nonrec,
         split_flatten cmp prem,
         split_flatten cmp concl)
      brs in
  (* Raise [Contradiction] from [abd] when constraints are not
     satisfiable. *)
  (* FIXME: handle [optis] *)
  List.iter
    (fun (_, (d_eqn, d_ineqn, d_optis), (c_eqn, c_ineqn, c_optis)) ->
       ignore (solve
                 ~eqn:(d_eqn @ c_eqn) ~ineqn:(d_ineqn @ c_ineqn)
                 cmp cmp_w q.uni_v))
    brs;
  (* FIXME *)
  let validate (eqs, ineqs, optis) = List.iter
      (* FIXME: handle [optis] *)
      (fun (_, (d_eqn, d_ineqn, d_optis), (c_eqn, c_ineqn, c_optis)) ->
         (*[* Format.printf "validate:@\nd_eqn=%a@\nc_eqn=%a@\nd_ineqn=%a@\nc_ineqn=%a@\n%!"
           pr_eqn d_eqn pr_eqn c_eqn pr_ineqn d_ineqn pr_ineqn c_ineqn; *]*)
         let (*[* br_eqs,br_ineqs,br_optis *]*) _ =
           solve ~eqs ~ineqs
             ~eqn:(d_eqn @ c_eqn) ~ineqn:(d_ineqn @ c_ineqn)
             cmp cmp_w q.uni_v in
         (*[* Format.printf "br_eqs=%a@\nbr_ineqs=%a@\nbr_optis=%a@\n%!"
           pr_w_subst br_eqs pr_ineqs br_ineqs pr_optis br_optis; *]*)
         ())
      brs in
  let brs, unproc_brs =
    if iter_no > 1 || !early_num_abduction
    then brs, []
    else List.partition
        (fun (nonrec, prem, concl) -> nonrec) brs in
  let brs = List.map (fun (_, prem, concl) -> prem, concl) brs in
  let brs = List.stable_sort
      (fun ((pe1,pi1,po1),_) ((pe2,pi2,po2),_) ->
         (List.length pe1 + List.length pi1 + List.length po1) -
           (List.length pe2 + List.length pi2 + List.length po2))
      brs in
  (*[* Format.printf "NumS.abd: brs=@\n| %a@\n%!"
    (pr_line_list "| " pr_eqineq_br) brs;
  *]*)
    let discard =
      List.map (split_flatten cmp) discard in
    let elim_uni =
      (* FIXME: rethink *)
      concat_map
        (fun (_,_,(concl_eqs, _, _)) ->
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
        {cmp; cmp_w; NumAbd.cmp_v = q.cmp_v; uni_v = q.uni_v; bvs}
        ~discard ~validate ([], [], []) brs in
    [], elim_uni @ ans_to_num_formula ans


let i2f = float_of_int
let expand_eqineqs eqs ineqs =
  let ans = List.map (expand_atom true) (unsubst eqs) in
  ans @ List.map (expand_atom false) (unsolve ineqs)

let disjelim q ~preserve brs =
  (*[* Format.printf "NumS.disjelim: brs=@ %a@\n%!"
    (pr_line_list "| " pr_formula) brs; *]*)
  let vars = List.map fvs_formula brs in
  let common = List.fold_left VarSet.inter preserve vars in
  let cmp_v = make_cmp q in
  let cmp_v v1 v2 =
    let v1c = VarSet.mem v1 common and v2c = VarSet.mem v2 common in
    if v1c && not v2c then 1
    else if v2c && not v1c then -1
    else cmp_v v1 v2 in
  let cmp (v1,_) (v2,_) = cmp_v v1 v2 in
  let cmp_w (vars1,cst1,_) (vars2,cst2,_) =
    match vars1, vars2 with
    | [], [] -> 0
    | _, [] -> -1
    | [], _ -> 1
    | (v1,_)::_, (v2,_)::_ -> cmp_v v1 v2 in
  let polytopes, elim_eqs = List.split
      (List.map
         (fun cnj ->
            (*[* Format.printf
              "NumS.disjelim:@ solving cnj==%a@\n%!"
              pr_formula cnj; *]*)
            let eqs, ineqs, optis =
              solve ~cnj cmp cmp_w q.uni_v in
            let eqs, elim_eqs = List.partition
                (fun (v, _) -> VarSet.mem v common) eqs in
            (eqs, ineqs), elim_eqs)
         brs) in
  (*[* Format.printf
    "NumS.disjelim:@ preserve=%a@ common=%a@ elim_eqs=@\n%a@\n%!"
    pr_vars preserve pr_vars common
    (pr_line_list "| " pr_w_subst) elim_eqs; *]*)
  let polytopes = List.map2
      (fun (eqs, ineqs) esb ->
         List.map (fun (v,w) -> v, subst_w cmp esb w) eqs,
         subst_ineqs cmp esb ineqs)
      polytopes elim_eqs in
  (* FIXME *)
  let unpack_optis esb optis =
    concat_map (fun (w1,w2) ->
        [subst_w cmp esb w1; subst_w cmp esb w2]) optis in    
  let faces : w list list = List.map2
      (fun br esb -> concat_map
          (fun a -> match (flatten cmp a) with
             | Some (Right w), optis ->
               subst_w cmp esb w :: unpack_optis esb optis
             | Some (Left w), optis ->
               let w = subst_w cmp esb w in
               w :: mult !/(-1) w :: unpack_optis esb optis
             | None, _ -> []) br)
      brs elim_eqs in
  let check face =
    let ineqn = [mult !/(-1) face] in
    List.for_all
      (fun (eqs, ineqs) ->
         try ignore
               (solve ~strict:true ~eqs ~ineqs ~ineqn cmp cmp_w q.uni_v);
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
  let result = concat_map fst selected in
  let result = map_some
      (fun cands -> try Some (List.find check cands)
        with Not_found -> None) cands
               @ result in
  let sort_w (vars, cst, loc) =
    let vars = map_reduce (+/) (!/0) vars in
    let vars = List.sort cmp
        (List.filter (fun (_,k) -> k <>/ !/0) vars) in
    vars, cst, loc in
  let result = List.map sort_w result in
  let rec idemp eqn ineqn = function
    | e1::(e2::_ as tl) when nonq_cmp_w e1 e2 = 0 -> idemp eqn ineqn tl
    | e::tl when List.exists (fun w -> zero_p (sum_w cmp e w)) tl ->
      idemp (e::eqn) ineqn
        (List.filter (fun w -> not (zero_p (sum_w cmp e w))) tl)
    | e::tl -> idemp eqn (e::ineqn) tl
    | [] -> eqn, ineqn in
  let eqn, ineqn =
    idemp [] [] (List.sort nonq_cmp_w result) in
  let redundant_eqn =
    collect ~cmp_k:Num.compare_num
      (List.map (fun (vars,cst,lc) -> cst,(vars,lc)) eqn) in
  let redundant_eqn =
    Aux.concat_map
      (fun (_,ws) -> List.map
          (fun ((w1,lc1),(w2,lc2)) ->
             diff cmp (w1, !/0, lc1) (w2, !/0, lc2))
          (Aux.triangle ws))
      redundant_eqn in
  (*[* Format.printf "NumS.disjelim:@\neqn=%a@\nredundant=%a@\n%!"
    pr_eqn eqn pr_eqn redundant_eqn; *]*)
  let check face ptope =
    let eqs, ineqs, optis =
      solve ~eqn ~ineqn:ptope cmp cmp_w q.uni_v in
    let ineqn = [mult !/(-1) face] in
    try ignore (solve ~strict:true ~eqs ~ineqs ~ineqn cmp cmp_w q.uni_v);
      false
    with Terms.Contradiction _ -> true in
  let rec nonredundant p1 = function
    | face::p2 ->
      if check face (p1 @ p2) then nonredundant p1 p2
      else nonredundant (face::p1) p2
    | [] -> p1 in
  [],
  List.map (expand_atom true) (eqn @ redundant_eqn)
  @ List.map (expand_atom false) (nonredundant [] ineqn)

let simplify q elimvs cnj =
  (*[* Format.printf "NumS.simplify: elimvs=%s;@\ncnj=@ %a@\n%!"
    (String.concat "," (List.map var_str (VarSet.elements elimvs)))
    pr_formula cnj; *]*)
  (* FIXME: does [elimvs] give correct order of vars? Write test. *)
  let cmp_v = make_cmp q in
  let cmp (v1,_) (v2,_) = cmp_v v1 v2 in
  let cmp_w (vars1,_,_) (vars2,_,_) =
    match vars1, vars2 with
    | [], [] -> 0
    | _, [] -> -1
    | [], _ -> 1
    | (v1,_)::_, (v2,_)::_ -> cmp_v v1 v2 in
  let eqs, ineqs, optis =
    solve ~cnj cmp cmp_w q.uni_v in
  let eqs =
    List.filter (fun (v,_) -> not (VarSet.mem v elimvs)) eqs in
  (*let ineqs =
    List.filter (fun (v,_) -> not (VarSet.mem v elimvs)) ineqs in*)
  (* FIXME *)
  let optis = [] in
  let ans = ans_to_num_formula (eqs, ineqs, optis) in
  let vs = VarSet.inter elimvs (fvs_formula ans) in
  let cmp a1 a2 = compare
      (replace_loc_atom dummy_loc a1) (replace_loc_atom dummy_loc a2) in
  let res = unique_sorted ~cmp ans in
  (*[* Format.printf "NumS.simplify:@\nres=%a@\n%!" pr_formula res; *]*)
  VarSet.elements vs, res

(*
let rec cleanup_typ t =
  let rec flat (vars, cst as acc) = function
    | Nadd sum -> List.fold_left flat acc sum
    | NCst i -> vars, cst + i
    | (TVar _ | TCons (_, [])) as t -> t::vars, cst
    | TCons (n, ts) -> TCons (n, List.map cleanup_typ ts)::vars, cst
    | Fun (t1, t2) -> Fun (cleanup_typ t1, cleanup_typ t2)::vars, cst in
  match flat ([], 0) t with
  | [], i -> NCst i
  | [tv], 0 -> tv
  | tvs, i -> Nadd (NCst i::tvs)
   
let cleanup_formula = map_in_formula cleanup_typ
*)

(*
let equivalent q cnj1 cnj2 =
  (*[* Format.printf "NumS.equivalent:@ cnj1=@ %a@ cnj2=@ %a@\n%!"
    pr_formula cnj1 pr_formula cnj2; *]*)
  let cmp_v = make_cmp VarSet.empty cmp_v in
  let cmp (v1,_) (v2,_) = cmp_v v1 v2 in
  let cmp_w (vars1,_,_) (vars2,_,_) =
    match vars1, vars2 with
    | [], [] -> 0
    | _, [] -> -1
    | [], _ -> 1
    | (v1,_)::_, (v2,_)::_ -> cmp_v v1 v2 in
  let cmp_vw (v1, w1) (v2, w2) =
    let c = compare v1 v2 in
    if c=0 then cmp_w w1 w2 else c in
  let eqs1, (ineqs1, implicits1) =
    solve ~cnj:cnj1 cmp cmp_w uni_v in
  let eqs1, _ = solve ~eqs:eqs1 ~eqn:implicits1 cmp cmp_w uni_v in
  let eqs2, (ineqs2, implicits2) =
    solve ~cnj:cnj2 cmp cmp_w uni_v in
  let eqs2, _ = solve ~eqs:eqs2 ~eqn:implicits2 cmp cmp_w uni_v in
  let eqs1 = List.map (fun (v,w) -> v, unloc w) eqs1
  and eqs2 = List.map (fun (v,w) -> v, unloc w) eqs2 in
*) (* and now what... *)

let converge q cnj1 cnj2 =
  (*[* Format.printf "NumS.converge:@\ncnj1=@ %a@\ncnj2=@ %a@\n%!"
    pr_formula cnj1 pr_formula cnj2; *]*)
  let cmp_v = make_cmp q in
  let cmp (v1,_) (v2,_) = cmp_v v1 v2 in
  let cmp_w (vars1,_,_) (vars2,_,_) =
    match vars1, vars2 with
    | [], [] -> 0
    | _, [] -> -1
    | [], _ -> 1
    | (v1,_)::_, (v2,_)::_ -> cmp_v v1 v2 in
  (*let params = map_opt params
    (List.fold_left
    (fun acc (_,ps) -> VarSet.union acc ps) VarSet.empty) in*)
  let eqs1, ineqs1, optis1 =
    solve ~cnj:cnj1 cmp cmp_w q.uni_v in
  let eqs2, ineqs2, optis2 =
    solve ~cnj:cnj2 cmp cmp_w q.uni_v in
  (* FIXME *)
  let optis1 = [] and optis2 = [] in
  let ans1 = ans_to_num_formula (eqs1, ineqs1, optis1) in
  let ans2 = ans_to_num_formula (eqs2, ineqs2, optis2) in
  let eq2ineq = function
    | Eq (t1, t2, lc) -> [Leq (t1, t2, lc); Leq (t2, t1, lc)]
    | a -> [a] in
  let ans1 = concat_map eq2ineq ans1
  and ans2 = concat_map eq2ineq ans2 in
  (*[* Format.printf "NumS.converge:@\nans1=@ %a@\nans2=@ %a@\n%!"
    pr_formula ans1 pr_formula ans2; *]*)
  (* FIXME: Actually, include transitivity! *)
  formula_inter (cnj1 @ ans1) (cnj2 @ ans2)

type state = w_subst * ineqs
let empty_state = [], []

let formula_of_state (eqs, ineqs) = expand_eqineqs eqs ineqs

let satisfiable ?state cnj =
  let eqs, ineqs = match state with
    | None -> None, None
    | Some (eqs, ineqs) -> Some eqs, Some ineqs in
  let uni_v _ = false in
  let cmp_v v1 v2 = compare v1 v2 in
  let cmp (v1,_) (v2,_) = cmp_v v1 v2 in
  let cmp_w (vars1,_,_) (vars2,_,_) =
    match vars1, vars2 with
    | [], [] -> 0
    | _, [] -> -1
    | [], _ -> 1
    | (v1,_)::_, (v2,_)::_ -> cmp_v v1 v2 in
  try
    let eqs, ineqs, optis =
      solve ?eqs ?ineqs ~cnj cmp cmp_w uni_v in
    Right (eqs, ineqs)
  with Terms.Contradiction _ as e -> Left e

let satisfiable_exn ?state cnj =
  let eqs, ineqs = match state with
    | None -> None, None
    | Some (eqs, ineqs) -> Some eqs, Some ineqs in
  let uni_v _ = false in
  let cmp_v v1 v2 = compare v1 v2 in
  let cmp (v1,_) (v2,_) = cmp_v v1 v2 in
  let cmp_w (vars1,_,_) (vars2,_,_) =
    match vars1, vars2 with
    | [], [] -> 0
    | _, [] -> -1
    | [], _ -> 1
    | (v1,_)::_, (v2,_)::_ -> cmp_v v1 v2 in
  let eqs, ineqs, optis =
    solve ?eqs ?ineqs ~cnj cmp cmp_w uni_v in
  eqs, ineqs

let holds q avs (eqs, ineqs : state) cnj : state =
  let cmp_v = make_cmp q in
  let cmp (v1,_) (v2,_) = cmp_v v1 v2 in
  let cmp_w (vars1,_,_) (vars2,_,_) =
    match vars1, vars2 with
    | [], [] -> 0
    | _, [] -> -1
    | [], _ -> 1
    | (v1,_)::_, (v2,_)::_ -> cmp_v v1 v2 in
  let eqs, ineqs, optis =
    solve ~use_quants:avs
      ~eqs ~ineqs ~cnj cmp cmp_w q.uni_v in
  eqs, ineqs

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
let separate_subst_aux q ~keep cnj =
  let cmp_v v1 v2 =
    let c1 = VarSet.mem v1 keep and c2 = VarSet.mem v2 keep in
    if c1 && c2 then 0
    else if c1 then -1
    else if c2 then 1
    else make_cmp q v1 v2 in
  let cmp (v1,_) (v2,_) = cmp_v v1 v2 in
  let cmp_w (vars1,_,_) (vars2,_,_) =
    match vars1, vars2 with
    | [], [] -> 0
    | _, [] -> -1
    | [], _ -> 1
    | (v1,_)::_, (v2,_)::_ -> cmp_v v1 v2 in
  let eqs, _, _ =
    solve ~cnj cmp cmp_w q.uni_v in
  (*[* Format.printf "NumS.separate_subst: eq-keys=%a@\n%!"
    pr_vars (vars_of_list (List.map fst eqs)); *]*)
  (* FIXME *)
  let _, ineqn, optis = split_flatten cmp cnj in
  let ineqn = List.map (subst_w cmp eqs) ineqn in
  let optis = List.map (subst_2w cmp eqs) optis in
  let ineqn = List.filter
    (function [], cst, _ when cst <=/ !/0 -> false | _ -> true)
    ineqn in
  let sb = expand_subst eqs in
  (* FIXME *)
  let phi_num = cnj_to_num_formula ([], ineqn, optis) in
  (*[* Format.printf "NumS.separate_subst:@ sb=%a@ phi=%a@\n%!"
    pr_num_subst sb pr_formula phi_num; *]*)
  sb, phi_num

(* Optimization. TODO: check if worth it. *)
exception Not_substitution

let separate_num_subst q ~keep cnj =
  try
    let sb, phi = partition_map
        (function
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
  with Not_substitution -> separate_subst_aux q ~keep cnj

let separate_subst q ?(keep=VarSet.empty) cnj =
  (*[* Format.printf "NumS.separate_subst: keep=%a@ cnj=%a@\n%!"
    pr_vars keep pr_formula cnj; *]*)
  let sb, phi = separate_num_subst q ~keep cnj in
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
  let eqs = Joint.transitive_cl eqs in
  let ineqs = Joint.transitive_cl ineqs in
  let cnj = Hashtbl.fold
      (fun (i,j) lc cnj -> if i<j then Eq (i, j, lc)::cnj else cnj)
      eqs [] in
  let cnj = Hashtbl.fold
      (fun (i,j) lc cnj -> Leq (i, j, lc)::cnj)
      ineqs cnj in
  cnj
