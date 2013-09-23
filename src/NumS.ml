(** Numeric sort operations for InvarGenT.

    Released under the GNU General Public Licence (version 2 or
    higher), NO WARRANTY of correctness etc. (C) Lukasz Stafiniak 2013
    @author Lukasz Stafiniak lukstafi (AT) gmail.com
    @since Mar 2013
*)

open Terms
open Num
open Aux
let (!/) i = num_of_int i

type w = (var_name * num) list * num * loc
type w_subst = (var_name * w) list
type cw_subst = ((var_name, bool) choice * w) list
type ineqs = (var_name * (w list * w list)) list
  

let mult c (vars, cst, loc) =
  List.map (fun (v,k) -> v, c */ k) vars, c */ cst, loc

let sum_w cmp (vars1, cst1, loc1) (vars2, cst2, loc2) =
  let loc = loc_union loc1 loc2 in
  let vars = map_reduce (+/) (!/0) (vars1 @ vars2) in
  let vars = List.sort cmp
    (List.filter (fun (_,k) -> k <>/ !/0) vars) in
  vars, cst1 +/ cst2, loc

let diff cmp w1 w2 = sum_w cmp w1 (mult !/(-1) w2)

let zero_p (vars, cst, _) = vars = [] && cst = !/0

let equal_w cmp w1 w2 = zero_p (diff cmp w1 w2)


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

let pr_ans ppf (eqs, ineqs) =
  Format.fprintf ppf "%a@ ∧@ %a" pr_w_subst eqs pr_ineqs ineqs

let pr_eq ppf w = Format.fprintf ppf "%a@ = 0" pr_w w
let pr_ineq ppf w = Format.fprintf ppf "%a@ ≤ 0" pr_w w
let pr_eqn ppf eqn =
  pr_sep_list "," pr_eq ppf eqn
let pr_ineqn ppf ineqn =
  pr_sep_list "," pr_ineq ppf ineqn
let pr_eqineq_br ppf ((d_eqn, d_ineqn), (c_eqn, c_ineqn)) =
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
  

let flatten cmp a : (w, w) choice =
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
    Left (collect t1 t2 loc)
  | Leq (t1, t2, loc) ->
    Right (collect t1 t2 loc)
  | _ -> assert false

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

let expand_w (vars, cst, loc) =
  let vars = List.map (fun (v,k) -> v, ratio_of_num k) vars in
  let cst = ratio_of_num cst in
  let denoms =
    List.map (fun (_,k) -> Ratio.denominator_ratio k) vars in
  let denoms = Ratio.denominator_ratio cst :: denoms in
  let sc = List.fold_left
    Big_int.(fun a b -> div_big_int (mult_big_int a b) (gcd_big_int a b))
    (Big_int.big_int_of_int 1) denoms in
  let vars = List.map
    (fun (v,k) -> v, Ratio.int_of_ratio (Ratio.mult_big_int_ratio sc k))
    vars in
  let cst = Ratio.int_of_ratio (Ratio.mult_big_int_ratio sc cst) in
  let left, right = List.partition (fun (_,k) -> k > 0) vars in
  let right = List.map (fun (v,k) -> v, ~-k) right in
  let expand (v,k) = Array.to_list (Array.make k (TVar v)) in
  let left = (if cst > 0 then [NCst cst] else [])
    @ concat_map expand left in
  let right = (if cst < 0 then [NCst (~-cst)] else [])
    @ concat_map expand right in
  left, right

let expand_atom equ (_,_,loc as w) =
  let left, right = expand_w w in
  let left = match left with [t] -> t | _ -> Nadd left in
  let right = match right with [t] -> t | _ -> Nadd right in
  if equ then Eqty (left, right, loc) else Leq (left, right, loc)

let expand_subst eqs =
  let aux (v, (vars, cst, loc)) =
    let w = (v, !/(-1))::vars, cst, loc in
    match expand_w w with
    | [TVar v], rhs | rhs, [TVar v] -> Aux.Right (v, (Nadd rhs, loc))
    | _ -> Aux.Left w in
  Aux.partition_map aux eqs    
    

let ans_to_formula (eqs, ineqs) =
  List.map (expand_atom true) (unsubst eqs)
  @ List.map (expand_atom false) (unsolve ineqs)

let eqineq_to_formula (eqn, ineqn) =
  List.map (expand_atom true) eqn
  @ List.map (expand_atom false) ineqn

let eqineq_loc_union (eqn, ineqn) =
  List.fold_left loc_union dummy_loc
    (List.map (fun (_,_,lc) -> lc) (eqn @ ineqn))

let un_ans (eqs, ineqs) = unsubst eqs, unsolve ineqs

(* Assumption: [v] is downstream of all [vars] *)
let quant_viol uni_v paramvs bvs v vars =
  let res = uni_v v && not (VarSet.mem v bvs)
    && not (VarSet.mem v paramvs) in
  if res then
  Format.printf "NumS.quant_viol: v=%s; uni(v)=%b; bvs(v)=%b@\n%!"
    (var_str v) (uni_v v) (VarSet.mem v bvs);
  (* *)
  res

let solve ?use_quants ?(strict=false)
    ?(eqs=[]) ?(ineqs=[]) ?(eqs'=[])
    ?(eqn=[]) ?(ineqn=[]) ?(cnj=[])
    cmp cmp_w uni_v =
  let use_quants, paramvs, bvs = match use_quants with
    | None -> false, VarSet.empty, VarSet.empty
    | Some (paramvs, bvs) -> true, paramvs, bvs in
  let eqs = if eqs' = [] then eqs else List.map
      (fun (v,eq) -> v, subst_w cmp eqs' eq) eqs @ eqs' in
  let ineqs = if eqs' = [] then ineqs else List.map
      (fun (v,(wl,wr)) -> v,
        (List.map (subst_w cmp eqs') wl,
         List.map (subst_w cmp eqs') wr)) ineqs in
  let more_eqn, more_ineqn = partition_map (flatten cmp) cnj in
  let eqn = eqn @ more_eqn in
  let ineqn = ineqn @ more_ineqn in
  assert (not strict || eqn = []);
  let eqn = if eqs=[] then eqn else List.map (subst_w cmp eqs) eqn in
  let ineqn = if eqs=[] then ineqn else List.map (subst_w cmp eqs) ineqn in
  let eqn = List.map
    (fun (vars, cst, loc) ->
      List.filter (fun (v,k)->k <>/ !/0) vars, cst, loc) eqn in
  let eqn = List.sort cmp_w eqn in
  (* Format.printf "NumS.solve: eqn=@ %a@\n%!" pr_eqn eqn; * *)
  let rec elim acc = function
    | [] -> List.rev acc
    | ((v, k)::vars, cst, loc)::eqn
        when use_quants && quant_viol uni_v paramvs bvs v vars ->
      let t1, t2 =
        match expand_atom true ((v, k)::vars, cst, loc) with
        | Eqty (t1, t2, _) -> t1, t2
        | _ -> assert false in
      raise (Contradiction (Num_sort,
                            "Quantifier violation (numeric equation)",
                            Some (t1, t2), loc))
    | ((v, k)::vars, cst, loc)::eqn ->
      let w_sb = v, mult (!/(-1) // k) (vars, cst, loc) in
      let acc = subst_one_sb cmp w_sb acc in
      let eqn = List.map (subst_one cmp w_sb) eqn in
      elim (w_sb::acc) eqn
    | ([], cst, loc)::eqn when cst =/ !/0 -> elim acc eqn
    | ([], cst, loc)::eqn ->
      let msg =
        "Failed numeric equation ("^Num.string_of_num cst^"=0)" in
      raise (Contradiction (Num_sort, msg, None, loc)) in
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
  let project v (vars, cst, loc as lhs) rhs =
    if equal_w cmp lhs rhs
    then
      let w = (v, !/(-1))::vars, cst, loc in
      if strict then
        let a = expand_atom false w in
        let t1, t2 = match a with
          | Leq (t1, t2, _) -> t1, t2 | _ -> assert false in
        raise (Contradiction (Num_sort, "Failed numeric strict inequality",
                              Some (t1, t2), loc))
      else Right w
    else Left (diff cmp lhs rhs) in
  let rec proj ineqs implicits ineqn =
    match ineqn with
    | [] -> ineqs, implicits
    | ([], cst, _)::ineqn
        when (strict && cst </ !/0) || (not strict && cst <=/ !/0) ->
      proj ineqs implicits ineqn
    | ([], cst, loc)::_ ->
      raise (Contradiction (Num_sort, "Failed numeric inequality",
                            None, loc))
    | ((v, k)::vars, cst, loc)::ineqn
        when use_quants && quant_viol uni_v paramvs bvs v vars ->
      let t1, t2 =
        match expand_atom false ((v, k)::vars, cst, loc) with
        | Leq (t1, t2, _) -> t1, t2
        | _ -> assert false in
      raise (Contradiction (Num_sort,
                            "Quantifier violation (numeric inequality)",
                            Some (t1, t2), loc))
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
          raise (Contradiction (Num_sort, "Failed numeric inequality",
                                Some (t1, t2), loc))
        | _ -> true)
        more_ineqn in
      let ineqn =
        merge cmp_w (List.sort cmp_w more_ineqn) ineqn in
      let ineqs = (v, (ineq_l @ left, ineq_r @ right))::ineqs in
      proj ineqs (more_implicits @ implicits) ineqn in
  eqn @ eqs, proj ineqs [] ineqn

let fvs_w (vars, _, _) = vars_of_list (List.map fst vars)


let abd_rotations = ref (* 1 *)2

exception Result of w_subst * ineqs

let debug_dep = ref 0
let no_pass_msg = "Could not solve numeric SCA (algorithm step 5b)"

let implies cmp cmp_w uni_v eqs ineqs c_eqn c_ineqn =
  List.for_all
    (fun w ->
      match subst_w cmp eqs w with
      | [], cst, _ -> cst =/ !/0
      | _ -> false)
    c_eqn
  && List.for_all
    (fun w ->
      let ineqn = [mult !/(-1) w] in
      try ignore
            (solve ~strict:true ~eqs ~ineqs ~ineqn cmp cmp_w uni_v);
          false
      with Contradiction _ -> true)
    c_ineqn

let implies_ans cmp cmp_w uni_v (eqs, ineqs) (c_eqn, c_ineqn) =
  implies cmp cmp_w uni_v eqs ineqs c_eqn c_ineqn  

let abd_simple cmp cmp_w uni_v ~paramvs ~bvs ~validate
    skip (eqs_i, ineqs_i) ((d_eqn, d_ineqn), (c_eqn, c_ineqn)) =
  let skip = ref skip in
  (* 1 *)
  let big_k = Array.init (!abd_rotations - 1) (fun k -> !/(k+2)) in
  let big_k =
    Array.append big_k (Array.map (fun k-> !/1 // k) big_k) in
  let ks_eq = (* 1a1 *)
    Array.to_list
      (Array.append [|!/0; !/1; !/(-1)|]
         (Array.append big_k (Array.map (fun k -> !/(-1) */ k) big_k))) in
  let ks_ineq = (* 1b1 *)
    Array.to_list (Array.append [|!/0; !/1|] big_k) in
  let ks_eq = laz_of_list ks_eq
  and ks_ineq = laz_of_list ks_ineq in
  let zero = [], !/0, dummy_loc in
  let eq_trs = List.fold_left
    (fun eq_trs a ->
      let kas = lazmap (fun k -> mult k a) ks_eq in
      let add_kas tr = lazmap (fun ka -> sum_w cmp ka tr) kas in
      lazconcat_map add_kas eq_trs)
    (laz_single zero) d_eqn in
  let ineq_trs = List.fold_left
    (fun ineq_trs a ->
      let kas = lazmap (fun k -> mult k a) ks_ineq in
      let add_kas tr = lazmap (fun ka -> sum_w cmp ka tr) kas in
      lazconcat_map add_kas ineq_trs)
    eq_trs d_ineqn in
  try
    Format.printf
       "NumS.abd_simple: 1.@\neqs=@ %a@\nineqs=@ %a@\nd_eqn=@ %a@ d_ineqn=@ %a@\nc_eqn=@ %a@ c_ineqn=@ %a@\n%!"
      pr_w_subst eqs_i pr_ineqs ineqs_i pr_eqn d_eqn pr_ineqn d_ineqn
       pr_eqn c_eqn pr_ineqn c_ineqn;
       (* *)
    (* 2 *)
    let rec loop eqs_acc ineqs_acc eq_cands ineq_cands =
      let ddepth = incr debug_dep; !debug_dep in
      let a, iseq, eq_cands, ineq_cands =
        match eq_cands, ineq_cands with
        | a::eq_cands, ineq_cands ->
          a, true, eq_cands, ineq_cands
        | [], a::ineq_cands ->
          a, false, [], ineq_cands
        | [], [] ->
          if !skip > 0 then
            (decr skip; raise
              (Contradiction (Num_sort,
                              "Numeric SCA: skipping", None, dummy_loc)))
          else raise (Result (eqs_acc, ineqs_acc)) in
      (* 3 *)
      let eqn = eq_cands @ d_eqn in
      let ineqn = ineq_cands @ d_ineqn in
      let b_eqs, (b_ineqs, b_implicits) =
        solve ~eqs:eqs_acc ~ineqs:ineqs_acc ~eqn ~ineqn cmp cmp_w uni_v in
      let b_eqs, (b_ineqs, _) =
        solve ~eqs:b_eqs ~ineqs:b_ineqs ~eqn:b_implicits cmp cmp_w uni_v in
      Format.printf
         "NumS.abd_simple: [%d] 3. iseq=%b@ a=@ %a@\nb_eqs=@ %a@\nb_ineqs=@ %a@\n%!"
         ddepth iseq pr_w a pr_w_subst b_eqs pr_ineqs b_ineqs;
         (* *)
      
      if implies cmp cmp_w uni_v b_eqs b_ineqs c_eqn c_ineqn
      then
        loop eqs_acc ineqs_acc eq_cands ineq_cands
      else
        (* 5 *)
        (* [ineq_trs] include [eq_trs]! *)
        let trs = if iseq then eq_trs else ineq_trs in
        Format.printf
           "NumS.abd_simple: [%d] 5. a=@ %a@\n%!" ddepth pr_w a;
           (* *)
        let passes = ref false in
        laziter (fun tr ->
          try
            (* 5a *)
            let a' = sum_w cmp tr a in
            Format.printf
               "NumS.abd_simple: [%d] 5a. trying a'=@ %a@ ...@\n%!"
               ddepth pr_w a';
               (* *)
            let eqn, ineqn = if iseq then [a'], [] else [], [a'] in
            let eqs_acc, (ineqs_acc, acc_implicits) =
              solve ~use_quants:(paramvs,bvs)
                ~eqs:eqs_acc ~ineqs:ineqs_acc
                ~eqn ~ineqn cmp cmp_w uni_v in
            let eqs_acc, (ineqs_acc, _) =
              solve ~use_quants:(paramvs,bvs)
                ~eqs:eqs_acc ~ineqs:ineqs_acc
                ~eqn:acc_implicits cmp cmp_w uni_v in
            ignore (validate eqs_acc ineqs_acc);
            passes := true;
            Format.printf "NumS.abd_simple: [%d] 5a. validated@\n%!" ddepth;
             (* *)
            (* 5c TODO *)
            (*let ineq_trs =
              if !passing_ineq_trs then
              else ineq_trs in*)
            (* 5d *)
            (* (try                         *)
               loop eqs_acc ineqs_acc eq_cands ineq_cands
            (* with Contradiction _ -> ()) *)
          with Contradiction (_,msg,tys,_) when msg != no_pass_msg ->
            Format.printf
              "NumS.abd_simple: [%d] 4a. invalid (%s)@\n%!" ddepth msg;
            match tys with None -> ()
            | Some (t1, t2) ->
              Format.printf "types involved:@ t1=%a@ t2=%a@\n%!"
                (pr_ty false) t1 (pr_ty false) t2;
            (* *)
            ()
        ) trs;
        if not !passes then (
          (* 5b *)
          Format.printf
             "NumS.abd_simple: [%d] 4c. failed a=@ %a@ ...@\n%!"
             ddepth pr_w a;
             (* *)
          raise (Contradiction (Num_sort, no_pass_msg, None, dummy_loc))) in
    (* 2 *)
    try loop eqs_i ineqs_i c_eqn c_ineqn; None
    with Result (ans_eqs, ans_ineqs) -> Some (ans_eqs, ans_ineqs)
  with Contradiction _ -> None

let make_cmp paramvs cmp_v v1 v2 =
  (* Order: return positive if [v1] should be more to the right: more
  upstream, or if only [v2] is a parameter. *)
  let c1 = VarSet.mem v1 paramvs and c2 = VarSet.mem v2 paramvs in
  if c1 && c2 then compare v2 v1
  else if c1 then -1
  else if c2 then 1
  else match cmp_v v1 v2 with
  | Upstream -> 1
  | Downstream -> -1
  | _ -> compare v2 v1

let abd cmp_v uni_v ~paramvs ~bparams ~discard ?(iter_no=2) brs =
  let bvs = List.fold_left
    (fun acc (_,ps) -> VarSet.union acc ps) VarSet.empty bparams in
  let cmp_v = make_cmp paramvs cmp_v in
  let cmp (v1,_) (v2,_) = cmp_v v1 v2 in
  let cmp_w (vars1,cst1,_) (vars2,cst2,_) =
    match vars1, vars2 with
    | [], [] -> 0
    | _, [] -> -1
    | [], _ -> 1
    | (v1,_)::_, (v2,_)::_ -> cmp_v v1 v2 in
  Format.printf "NumS.abd: iter_no=%d@ bvs=%s@\n%!"
    iter_no
    (String.concat "," (List.map var_str (VarSet.elements bvs))); (* *)
  let brs = List.map
    (fun (nonrec, prem, concl) ->
      nonrec,
      partition_map (flatten cmp) prem,
      partition_map (flatten cmp) concl)
    brs in
  (* Raise [Contradiction] from [abd] when constraints are not
     satisfiable. *)
  List.iter
    (fun (_, (d_eqn, d_ineqn), (c_eqn, c_ineqn)) ->
      ignore (solve
                ~eqn:(d_eqn @ c_eqn) ~ineqn:(d_ineqn @ c_ineqn)
                cmp cmp_w uni_v))
    brs;
  let validate eqs ineqs = List.iter
    (fun (_, (d_eqn, d_ineqn), (c_eqn, c_ineqn)) ->
      ignore (solve ~eqs ~ineqs
                ~eqn:(d_eqn @ c_eqn) ~ineqn:(d_ineqn @ c_ineqn)
                cmp cmp_w uni_v))
    brs in
  let brs = map_some
    (fun (nonrec, prem, concl) ->
      if iter_no > 1 || nonrec then Some (prem, concl) else None) brs in
  Format.printf "NumS.abd: brs=@\n| %a@\n%!"
    (pr_line_list "| " pr_eqineq_br) brs;
  (* *)
  let br0 = 0, List.hd brs in
  let more_brs = List.map (fun br -> -1, br) (List.tl brs) in

  let time = ref (Sys.time ()) in
  let rec loop failed acc runouts = function
    | [] ->
      let _, (prem, concl) =
        Aux.maximum ~leq:(fun (i,_) (j,_) -> i<=j) runouts in
      raise (Suspect (ans_to_formula acc
                      @ eqineq_to_formula prem @ eqineq_to_formula concl,
                      eqineq_loc_union concl))
    | (skip, br as obr)::more_brs ->
      let ddepth = incr debug_dep; !debug_dep in
      Format.printf
        "NumS.abd-loop: [%d] skip=%d, #runouts=%d@\n%a@\n%!"
        ddepth skip (List.length runouts) pr_eqineq_br br; (* *)
      match abd_simple cmp cmp_w uni_v ~paramvs ~bvs
        ~validate skip acc br with
      | Some acc when List.exists (implies_ans cmp cmp_w uni_v acc) failed ->
        Format.printf "NumS.abd: reset matching failed [%d]@\n%!" ddepth; (* *)
        loop failed ([], []) runouts ((skip+1, br)::more_brs)
      | Some acc ->
        let ntime = Sys.time () in
          Format.printf "NumS.abd: loop ans: [%d] (%.2fs)@\neqs=%a@\nineqs=%a@\n%!" ddepth (ntime -. !time)
          pr_w_subst (fst acc) pr_ineqs (snd acc); time := ntime; (* *)
        check_runouts failed acc obr more_brs [] runouts
      | None ->
        if skip <= 0 && acc = ([],[])
        then (
          Format.printf
            "NumS.abd-loop: quit failed [%d] at skip=%d failed=%d@ ans=%a@\n%!" ddepth
          skip (List.length failed) pr_ans acc; (* *)
          ignore (loop failed acc (obr::runouts) []));
        let failed = if skip <= 0 then un_ans acc::failed else failed in
        Format.printf
          "NumS.abd: reset first [%d] at skip=%d failed=%d@ ans=%a@\n%!" ddepth
          skip (List.length failed) pr_ans acc; (* *)
        loop failed ([], []) ((0, br)::runouts) more_brs

  and check_runouts failed acc (dskip, dbr as done_br)
      more_brs done_runouts = function
    | [] -> check_brs failed acc (List.rev done_runouts) [done_br] more_brs
    | (confls, br as obr)::more_runouts ->
      let ddepth = incr debug_dep; !debug_dep in
      Format.printf
        "NumS.abd-check_runouts: [%d] confls=%d, #done=%d@\n%a@\n%!"
        ddepth confls (List.length done_runouts) pr_eqineq_br br; (* *)
      match abd_simple cmp cmp_w uni_v ~paramvs ~bvs
        ~validate 0 acc br with
      | Some acc when List.exists (implies_ans cmp cmp_w uni_v acc) failed ->
        Format.printf "NumS.abd: reset runouts matching failed [%d]@\n%!" ddepth; (* *)
        loop failed ([], [])
          ((confls+1, br)::List.rev_append done_runouts more_runouts)
          ((dskip+1, dbr)::more_brs)
      | Some acc ->
        let ntime = Sys.time () in
          Format.printf "NumS.abd: runouts ans: [%d] (%.2fs)@\neqs=%a@\nineqs=%a@\n%!" ddepth (ntime -. !time)
          pr_w_subst (fst acc) pr_ineqs (snd acc); time := ntime; (* *)
        check_runouts failed acc done_br more_brs (obr::done_runouts) more_runouts
      | None ->
        if acc = ([],[])
        then (
          Format.printf
            "NumS.abd-check_runouts: quit failed [%d] at failed=%d@ ans=%a@\n%!" ddepth
          (List.length failed) pr_ans acc; (* *)
          ignore (loop failed acc (obr::done_runouts@more_runouts) []));
        Format.printf
          "NumS.abd: reset runouts [%d] at confls=%d failed=%d@ ans=%a@\n%!" ddepth
          confls (List.length failed + 1) pr_ans acc; (* *)
        loop (un_ans acc::failed) ([], [])
          ((confls+1, br)::List.rev_append done_runouts more_runouts)
          ((dskip+1, dbr)::more_brs)
      
  and check_brs failed acc runouts done_brs = function
    | [] -> acc
    | (skip, br as obr)::more_brs ->
      let ddepth = incr debug_dep; !debug_dep in
      Format.printf
        "NumS.abd-check_brs: [%d] skip=%d, #done=%d@\n%a@\n%!"
        ddepth skip (List.length done_brs) pr_eqineq_br br; (* *)
      match abd_simple cmp cmp_w uni_v ~paramvs ~bvs
        ~validate 0 acc br with
      | Some acc when List.exists (implies_ans cmp cmp_w uni_v acc) failed ->
        Format.printf "NumS.abd: reset check matching failed [%d]@\n%!" ddepth; (* *)
        loop failed ([], [])
          runouts ((skip+1, br)::List.rev_append done_brs more_brs)
      | Some acc ->
        let ntime = Sys.time () in
          Format.printf "NumS.abd: check ans: [%d] (%.2fs)@\neqs=%a@\nineqs=%a@\n%!" ddepth (ntime -. !time)
          pr_w_subst (fst acc) pr_ineqs (snd acc); time := ntime; (* *)
        check_brs failed acc runouts (obr::done_brs) more_brs
      | None ->
        if acc = ([],[])
        then (
          Format.printf
            "NumS.abd-check_brs: quit failed [%d] at failed=%d@ ans=%a@\n%!" ddepth
          (List.length failed) pr_ans acc; (* *)
          ignore (loop failed acc (obr::runouts) []));
        Format.printf
          "NumS.abd: reset check [%d] at skip=%d failed=%d@ ans=%a@\n%!" ddepth
          skip (List.length failed + 1) pr_ans acc; (* *)
        loop (un_ans acc::failed) ([], [])
          runouts ((skip+1, br)::List.rev_append done_brs more_brs) in

  let failed =
    List.map (partition_map (flatten cmp)) discard in
  [], ans_to_formula (loop failed ([], []) [] (br0::more_brs))

let disjelim_rotations = ref 3

let i2f = float_of_int
let expand_eqineqs eqs ineqs =
  let ans = List.map (expand_atom true) (unsubst eqs) in
  ans @ List.map (expand_atom false) (unsolve ineqs)

let disjelim cmp_v uni_v brs =
  Format.printf "NumS.disjelim: brs=@ %a@\n%!"
    (pr_line_list "| " pr_formula) brs;
  let vars = List.map fvs_formula brs in
  let common =
    match vars with [] -> assert false
    | [vars] -> vars
    | hd::tl -> List.fold_left VarSet.inter hd tl in
  let cmp_v = make_cmp VarSet.empty cmp_v in
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
    (fun br esb -> concat_map
       (fun a -> match (flatten cmp a) with
       | Right w -> [subst_w cmp esb w]
       | Left w -> let w = subst_w cmp esb w in [w; mult !/(-1) w]) br)
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
    | e1::(e2::_ as tl) when compare_w e1 e2 = 0 -> idemp eqn ineqn tl
    | e::tl when List.exists (fun w -> zero_p (sum_w cmp e w)) tl ->
      idemp (e::eqn) ineqn
        (List.filter (fun w -> not (zero_p (sum_w cmp e w))) tl)
    | e::tl -> idemp eqn (e::ineqn) tl
    | [] -> eqn, ineqn in
  let eqn, ineqn =
    idemp [] [] (List.sort compare result) in
  let redundant_eqn =
    collect ~cmp:(fun (c1,_) (c2,_) -> Num.compare_num c1 c2)
      (List.map (fun (vars,cst,lc) -> cst,(vars,lc)) eqn) in
  let redundant_eqn =
    Aux.concat_map
      (fun (_,ws) -> List.map
          (fun ((w1,lc1),(w2,lc2)) ->
             diff cmp (w1, !/0, lc1) (w2, !/0, lc2))
          (Aux.triangle ws))
      redundant_eqn in
  Format.printf "NumS.disjelim:@\neqn=%a@\nredundant=%a@\n%!"
    pr_eqn eqn pr_eqn redundant_eqn; (* *)
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
  [], List.map (expand_atom true) (eqn @ redundant_eqn)
    @ List.map (expand_atom false) (redundant [] ineqn)

let simplify cmp_v uni_v elimvs cnj =
  Format.printf "NumS.simplify: elimvs=%s;@\ncnj=@ %a@\n%!"
    (String.concat "," (List.map var_str (VarSet.elements elimvs)))
    pr_formula cnj;
  (* FIXME: does [elimvs] give correct order of vars? Write test. *)
  let cmp_v = make_cmp elimvs cmp_v in
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
  let eqs, (ineqs, implicits) =
    solve ~cnj cmp cmp_w uni_v in
  let eqs, _ = solve ~eqs ~eqn:implicits cmp cmp_w uni_v in
  let eqs =
    List.filter (fun (v,_) -> not (VarSet.mem v elimvs)) eqs in
  let ineqs =
    List.filter (fun (v,_) -> not (VarSet.mem v elimvs)) ineqs in
  let ans = ans_to_formula (eqs, ineqs) in
  let cmp a1 a2 = compare
      (replace_loc_atom dummy_loc a1) (replace_loc_atom dummy_loc a2) in
  [], unique_sorted ~cmp ans

(*
let equivalent cmp_v uni_v cnj1 cnj2 =
  Format.printf "NumS.equivalent:@ cnj1=@ %a@ cnj2=@ %a@\n%!"
    pr_formula cnj1 pr_formula cnj2;
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

let converge cmp_v uni_v cnj1 cnj2 =
  Format.printf "NumS.converge:@\ncnj1=@ %a@\ncnj2=@ %a@\n%!"
    pr_formula cnj1 pr_formula cnj2;
  let cmp_v = make_cmp VarSet.empty cmp_v in
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
    let eqs1, (ineqs1, implicits1) =
      solve ~cnj:cnj1 cmp cmp_w uni_v in
    let eqs1, _ = solve ~eqs:eqs1 ~eqn:implicits1 cmp cmp_w uni_v in
    let eqs2, (ineqs2, implicits2) =
      solve ~cnj:cnj2 cmp cmp_w uni_v in
    let eqs2, _ = solve ~eqs:eqs2 ~eqn:implicits2 cmp cmp_w uni_v in
    let ans1 = ans_to_formula (eqs1, ineqs1) in
    let ans2 = ans_to_formula (eqs2, ineqs2) in
    let eq2ineq = function
      | Eqty (t1, t2, lc) -> [Leq (t1, t2, lc); Leq (t2, t1, lc)]
      | a -> [a] in
    let ans1 = concat_map eq2ineq ans1
    and ans2 = concat_map eq2ineq ans2 in
  Format.printf "NumS.converge:@\nans1=@ %a@\nans2=@ %a@\n%!"
    pr_formula ans1 pr_formula ans2;
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
    let eqs, (ineqs, implicits) =
      solve ?eqs ?ineqs ~cnj cmp cmp_w uni_v in
    let eqs, _ = solve ~eqs ~eqn:implicits cmp cmp_w uni_v in
    Right (eqs, ineqs)
  with Contradiction _ as e -> Left e

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
  let eqs, (ineqs, implicits) =
    solve ?eqs ?ineqs ~cnj cmp cmp_w uni_v in
  let eqs, _ = solve ~eqs ~eqn:implicits cmp cmp_w uni_v in
  eqs, ineqs

let holds cmp_v uni_v (eqs, ineqs : state) cnj : state =
  let cmp_v = make_cmp VarSet.empty cmp_v in
  let cmp (v1,_) (v2,_) = cmp_v v1 v2 in
  let cmp_w (vars1,_,_) (vars2,_,_) =
    match vars1, vars2 with
    | [], [] -> 0
    | _, [] -> -1
    | [], _ -> 1
    | (v1,_)::_, (v2,_)::_ -> cmp_v v1 v2 in
  let eqs, (ineqs, implicits) =
    solve ~use_quants:(VarSet.empty,VarSet.empty)
      ~eqs ~ineqs ~cnj cmp cmp_w uni_v in
  let eqs, _ = solve ~use_quants:(VarSet.empty,VarSet.empty)
    ~eqs ~eqn:implicits cmp cmp_w uni_v in
  eqs, ineqs


let separate_subst cmp_v uni_v cnj =
  let cmp_v = make_cmp VarSet.empty cmp_v in
  let cmp (v1,_) (v2,_) = cmp_v v1 v2 in
  let cmp_w (vars1,_,_) (vars2,_,_) =
    match vars1, vars2 with
    | [], [] -> 0
    | _, [] -> -1
    | [], _ -> 1
    | (v1,_)::_, (v2,_)::_ -> cmp_v v1 v2 in
  let eqs, (_, implicits) =
    solve ~cnj cmp cmp_w uni_v in
  let eqs, _ = solve
    ~eqs ~eqn:implicits cmp cmp_w uni_v in
  let _, ineqn = partition_map (flatten cmp) cnj in
  let ineqn = List.map (subst_w cmp eqs) ineqn in
  let ineqn = List.filter
    (function [], cst, _ when cst <=/ !/0 -> false | _ -> true)
    ineqn in
  let eqn, sb = expand_subst eqs in
  sb, eqineq_to_formula (eqn, ineqn)
    
