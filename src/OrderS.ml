(** Order sort operations for InvarGenT.

    Released under the GNU General Public Licence (version 2 or
    higher), NO WARRANTY of correctness etc. (C) Lukasz Stafiniak 2013
    @author Lukasz Stafiniak lukstafi (AT) gmail.com
    @since Mar 2013
*)

let early_ord_abduction = ref (* false *)true
let abd_prune_at = ref (* 4 *)6(* 10 *)
let abd_timeout_count = ref (* 500 *)1000(* 5000 *)(* 50000 *)
let abd_fail_timeout_count = ref 10
let int_pruning = ref true
let strong_int_pruning = ref false
let passing_ineq_trs = ref false
let no_subopti_of_cst = ref true

let abd_fail_flag = ref false
let abd_timeout_flag = ref false

open Defs
open OrderDefs
(* open Terms *)
open Aux

let order_of = function
  | Terms.Alien (Terms.Order_term t) -> t
  | Terms.TVar v when var_sort v = Num_sort -> OVar v
  | _ -> assert false

let sort_formula = List.map
    Terms.(function
        | Eqty (t1, t2, loc) ->
          Eq (order_of t1, order_of t2, loc)
        | A (Order_atom a) -> a
        | _ -> assert false)

let formula_of_sort = List.map Terms.(fun a -> A (Order_atom a))

let sort_of_subst = List.map
    (fun (v, (t, lc)) -> Eq (OVar v, order_of t, lc))

(* FIXME: or *)
    (*Terms.(function
        | Eq (t1, t2, loc) ->
          Eqty (Alien (Order_term t1), Alien (Order_term t2), loc)
        | a -> A (Order_atom a))*)

type w =
  | WCst of int
  | WVar of int * var_name
  | WTop

(* A structure for Fourier-Motzkin elimination of a system of
    inequalities, including those with minimums and
    maximums. Invariant: *)
type v_system = {
  lhs_cst : int * loc;                  (* always satisfied by zero *)
  lhs_vars : (int * loc) VarMap.t;
  lhs_minis : (int * var_name * int * var_name * loc) list;
  rhs_cst : (int * loc) option;
  rhs_vars : (int * loc) VarMap.t;
  rhs_maxis : (int * var_name * int * var_name * loc) list;
}
type system = {
  v_system : v_system VarMap.t;
  c_lhs_minis : (int * var_name * int * var_name * loc) list;
  c_rhs_maxis : (int * var_name * int * var_name * loc) list;
}  

let taut_w iseq w1 w2 =
  if w1 = w2 then true
  else match iseq, w1, w2 with
    | false, _, WTop | false, WCst 0, _ -> true
    | false, WCst i, WCst j -> i <= j
    | true, _, _ when w1 = w2 -> true
    | _ -> false

(* Is v1+i1 <= v2+i2? *)
let sys_leq i1 v1 i2 v2 system =
  try
    let v_sys = VarMap.find v1 system.v_system in
    let i4, _ = VarMap.find v2 v_sys.rhs_vars in
    i2 - i1 >= i4
  with Not_found -> false

(* Is v1+i1 <= 0? *)
let sys_leq_c i1 v1 system =
  try
    let v_sys = VarMap.find v1 system.v_system in
    match v_sys.rhs_cst with
    | Some (i4, _) -> ~-i1 >= i4
    | None -> false
  with Not_found -> false

(* Is 0 <= v2+i2? *)
let sys_c_leq i2 v2 system =
  try
    let v_sys = VarMap.find v2 system.v_system in
    let i4, _ = v_sys.lhs_cst in
    ~-i2 <= i4
  with Not_found -> false

type w_atom =
  | Falsehood of loc
  | Leq_w of w * w * loc
  | MinLeq_w of w * w * w * loc
  | LeqMax_w of w * w * w * loc

let rec succs i v =
  if i <= 0 then OVar v else Succ (succs (i-1) v)
let rec succs_nat i =
  if i <= 0 then Zero else Succ (succs_nat (i-1))

let unsolve (system : system) : formula =
  let c_minleqs, c_eqmins = partition_map
      (fun (i2, v2, i3, v3, lc) ->
         let i1 = if i2 < 0 || i3 < 0 then ~-(min i2 i3) else 0 in
         let i2' = i2 + i1 and i3' = i3 + i1 in
         if sys_leq_c i2 v2 system && sys_leq_c i3 v3 system
         then Right
             (EqMin (succs_nat i1, succs i2' v2, succs i3' v3, lc),
              [v2, i2; v3, i3])
         else Left                      (* FIXME: rethink *)
             (MinLeq (succs i2' v2, succs i3' v3, succs_nat i1, lc)))
      system.c_lhs_minis in
  let c_eqmins, implicit_leq_c = List.split c_eqmins in
  let implicit_leq_c = List.concat implicit_leq_c in
  let c_leqmaxs, c_eqmaxs = partition_map
      (fun (i2, v2, i3, v3, lc) ->
         let i1 = if i2 < 0 || i3 < 0 then ~-(min i2 i3) else 0 in
         let i2' = i2 + i1 and i3' = i3 + i1 in
         if sys_c_leq i2 v2 system && sys_c_leq i3 v3 system
         then Right
             (EqMax (succs_nat i1, succs i2' v2, succs i3' v3, lc),
              [v2, i2; v3, i3])
         else Left                      (* FIXME: rethink *)
             (LeqMax (succs_nat i1, succs i2' v2, succs i3' v3, lc)))
      system.c_rhs_maxis in
  let c_eqmaxs, implicit_geq_c = List.split c_eqmaxs in
  let implicit_geq_c = List.concat implicit_geq_c in
  c_minleqs @ c_eqmins @ c_leqmaxs @ c_eqmaxs @
    concat_varmap
      (fun v v_sys ->
         let lhs_c_i, lhs_c_lc = v_sys.lhs_cst
         and rhs_c_i, rhs_c_lc =
           match v_sys.rhs_cst with
           | Some (i, lc) -> Some i, Some lc
           | None -> None, None in
         let cst =
           if Some lhs_c_i > rhs_c_i then assert false
           else if Some lhs_c_i = rhs_c_i
           then [Eq (OVar v, succs_nat lhs_c_i, lhs_c_lc)]
           else
             let lhs_cst =
               if lhs_c_i <= 0 then []
               else if List.mem_assoc v implicit_geq_c &&
                       List.assoc v implicit_geq_c >= lhs_c_i
               then []
               else [Leq (succs_nat lhs_c_i, OVar v, lhs_c_lc)] in
             let rhs_cst =
               match rhs_c_i with
               | None -> []
               | Some rhs_c_i ->
                 if rhs_c_i < 0 then assert false
                 else if List.mem_assoc v implicit_leq_c &&
                         List.assoc v implicit_leq_c <= rhs_c_i
                 then []
                 else [Leq (OVar v, succs_nat rhs_c_i, unsome rhs_c_lc)] in
             lhs_cst @ rhs_cst in
         let minleqs, eqmins = partition_map
             (fun (i2, v2, i3, v3, lc) ->
                let i1 = if i2 < 0 || i3 < 0 then ~-(min i2 i3) else 0 in
                let i2 = i2 + i1 and i3 = i3 + i1 in
                if sys_leq i1 v i2 v2 system && sys_leq i1 v i3 v3 system
                then Right
                    (EqMin (succs i1 v, succs i2 v2, succs i3 v3, lc),
                     [i1, v, i2, v2; i1, v, i3, v3])
                else Left
                    (MinLeq (succs i2 v2, succs i3 v3, succs i1 v, lc)))
             v_sys.lhs_minis in
         let eqmins, implicit1 = List.split eqmins in
         let leqmaxs, eqmaxs = partition_map
             (fun (i2, v2, i3, v3, lc) ->
                let i1 = if i2 < 0 || i3 < 0 then ~-(min i2 i3) else 0 in
                let i2 = i2 + i1 and i3 = i3 + i1 in
                if sys_leq i2 v2 i1 v system && sys_leq i3 v3 i1 v system
                then Right
                    (EqMax (succs i1 v, succs i2 v2, succs i3 v3, lc),
                     [i2, v2, i1, v; i3, v3, i1, v])
                else Left
                    (LeqMax (succs i1 v, succs i2 v2, succs i3 v3, lc)))
             v_sys.rhs_maxis in
         let eqmaxs, implicit2 = List.split eqmaxs in
         let implicit_leqs = List.concat (implicit1 @ implicit2) in
         let implied (i3, v3, i4, v4) (i1, v1, i2, v2) =
           v1 = v3 && v2 = v4 && i2 - i1 <= i4 - i3 in
         let lhs_vs = concat_varmap
             (fun v2 (i2, lc) ->
                try
                  let i3, lc' = VarMap.find v2 v_sys.lhs_vars in
                  if i2 <> i3 then raise Not_found
                  else if v <= v2 then []  (* no redundancy *)
                  else if i2 < 0
                  then [Eq (succs (~-i2) v, OVar v2, loc_union lc lc')]
                  else [Eq (OVar v, succs i2 v2, loc_union lc lc')]
                with Not_found ->
                  if List.exists (implied (i2, v2, 0, v)) implicit_leqs
                  then []
                  else if i2 < 0
                  then [Leq (OVar v2, succs (~-i2) v, lc)]
                  else [Leq (succs i2 v2, OVar v, lc)])
             v_sys.lhs_vars in
         let rhs_vs = concat_varmap
             (fun v2 (i2, lc) ->
                try
                  let i3, lc' = VarMap.find v2 v_sys.lhs_vars in
                  if i2 <> i3 then raise Not_found
                  else if i2 < 0
                  then [Eq (succs (~-i2) v, OVar v2, loc_union lc lc')]
                  else [Eq (OVar v, succs i2 v2, loc_union lc lc')]
                with Not_found ->
                  if List.exists (implied (0, v, i2, v2)) implicit_leqs
                  then []
                  else if i2 < 0
                  then [Leq (succs (~-i2) v, OVar v2, lc)]
                  else [Leq (OVar v, succs i2 v2, lc)])
             v_sys.rhs_vars in
         cst @ eqmins @ eqmaxs @ minleqs @ leqmaxs @ lhs_vs @ rhs_vs)
      system.v_system

let flatten a : w_atom list =
  (* We no longer have min/max subterms *)
  let rec flat i = function
    | Zero -> WCst i
    | Top -> WTop
    | OVar v -> WVar (i, v)
    | Succ o -> flat (i+1) o in
  match a with
  | Eq (t1, t2, loc) ->
    let w1 = flat 0 t1 in
    let w2 = flat 0 t2 in
    [Leq_w (w1, w2, loc); Leq_w (w2, w1, loc)]
  | Leq (t1, t2, loc) ->
    let w1 = flat 0 t1 in
    let w2 = flat 0 t2 in
    [Leq_w (w1, w2, loc)]
  | EqMin (t1, t2, t3, loc) ->
    let w1 = flat 0 t1 in
    let w2 = flat 0 t2 in
    let w3 = flat 0 t3 in
    [Leq_w (w1, w2, loc); Leq_w (w1, w3, loc); MinLeq_w (w2, w3, w1, loc)]
  | MinLeq (t1, t2, t3, loc) ->
    let w1 = flat 0 t1 in
    let w2 = flat 0 t2 in
    let w3 = flat 0 t3 in
    [MinLeq_w (w1, w2, w3, loc)]
  | EqMax (t1, t2, t3, loc) ->
    let w1 = flat 0 t1 in
    let w2 = flat 0 t2 in
    let w3 = flat 0 t3 in
    [Leq_w (w2, w1, loc); Leq_w (w3, w1, loc); LeqMax_w (w1, w2, w3, loc)]
  | LeqMax (t1, t2, t3, loc) ->
    let w1 = flat 0 t1 in
    let w2 = flat 0 t2 in
    let w3 = flat 0 t3 in
    [LeqMax_w (w1, w2, w3, loc)]

let flatten_formula cnj = concat_map flatten cnj

(* Quantifier violation when the rightmost variable of an atom (here
   represented by a list of its terms) is universally quantified (not
   a [bvs] parameter). *)
let quant_viol cmp_v uni_v bvs ts =
  let vars = VarSet.elements (vars_of_map fvs_term ts) in
  let v = maximum ~leq:(fun v1 v2 -> cmp_v v1 v2 <> Right_of) vars in
  let res = uni_v v && not (VarSet.mem v bvs) in
  (*[* if res then
   Format.printf "OrderS.quant_viol: v=%s; uni(v)=%b; bvs(v)=%b@\n%!"
    (var_str v) (uni_v v) (VarSet.mem v bvs);
  *]*)
  res

(*
let solve_aux ?use_quants ?(strict=false)
    ~eqs ~ineqs ~eqs' ~optis ~suboptis ~eqn ~ineqn ~cnj
    ~cmp_v ~cmp_w uni_v = TODO

let solve_get_eqn ?use_quants ?strict
    ?(eqs=[]) ?(ineqs=[]) ?(eqs'=[])
    ?(optis=[]) ?(suboptis=[]) ?(eqn=[]) ?(ineqn=[]) ?(cnj=[])
    ~cmp_v ~cmp_w uni_v = (* TODO *)
  (*[* Format.printf
    "NumS.main-solve: start@\ninit_st=@ %a@\neqn=%a@\nineqn=%a@\ncnj=%a@\n%!"
    pr_state (eqs, ineqs, optis, suboptis) pr_eqn eqn pr_ineqn ineqn
    pr_formula cnj; *]*)
  let all_implicit = ref [] in
  let rec loop (eqs,ineqs,optis,suboptis,implicits) =
    if implicits=[] then eqs, ineqs, optis, suboptis
    else (
      (*[* Format.printf "solve: implicits=%a@\n%!"
        pr_eqn implicits; *]*)
      all_implicit := implicits @ !all_implicit;
      loop
        (solve_aux ?use_quants ?strict ~eqs ~ineqs ~optis ~suboptis
           ~eqn:implicits
           ~eqs':[] ~ineqn:[] ~cnj:[] ~cmp_v ~cmp_w uni_v)) in
  if eqn=[] && (eqs=[] || eqs'=[]) && ineqn=[] && optis=[] &&
     suboptis=[] && cnj=[]
  then (eqs @ eqs', ineqs, [], []), []
  else
    let res =
      loop (solve_aux ?use_quants ?strict ~eqs ~ineqs ~eqs' ~optis ~suboptis
              ~eqn ~ineqn ~cnj ~cmp_v ~cmp_w uni_v) in
    (*[* Format.printf "NumS.main-solve: done@\n%a@\n@\n%!"
      pr_state res; *]*)
    res, !all_implicit
*)

let solve ?use_quants ?strict
    ?eqs ?ineqs ?eqs' ?optis ?suboptis ?eqn ?ineqn ?cnj
    ~cmp_v ~cmp_w uni_v = failwith "TODO"
(*
  let res, implicits =
    solve_get_eqn ?use_quants ?strict
      ?eqs ?ineqs ?eqs' ?optis ?suboptis ?eqn ?ineqn ?cnj
      ~cmp_v ~cmp_w uni_v in
  (*[* if implicits <> []
  then Format.printf "NumS.main-solve: implicits=@ %a@\n%!"
      pr_ineqn implicits; *]*)
  res
*)

let separate_subst q cnj =
  if cnj = [] then [], [] else failwith "Order.separate_subst: TODO"

let disjelim q ~preserve ~initstep brs =
  [], []                                (* TODO *)

let initstep_heur q cnj =
  cnj                                   (* TODO *)

(* exception Result of TODO *)
