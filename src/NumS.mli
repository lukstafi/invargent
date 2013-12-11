(** Numeric sort operations for InvarGenT.

    Released under the GNU General Public Licence (version 2 or
    higher), NO WARRANTY of correctness etc. (C) Lukasz Stafiniak 2013
    @author Lukasz Stafiniak lukstafi (AT) gmail.com
    @since Mar 2013
*)

(** Try four times as many linear combinations (k,-k,1/k,-1/k). *)
val abd_rotations : int ref
(** Start abduction on all branches rather than only non-recursive. *)
val early_num_abduction : bool ref
(** Keep less than N elements in abduction sums (default <6). *)
val abd_prune_at : int ref
val abd_timeout_count : int ref
val abd_fail_timeout_count : int ref
val passing_ineq_trs : bool ref

val abd_fail_flag : bool ref
val abd_timeout_flag : bool ref
(** For uniformity, return an empty list as introduced
    variables. Raise [Contradiction] if constraints are contradictory
    and [Suspect] if no answer can be found. *)
val abd :
  Terms.quant_ops ->
  bvs:Terms.VarSet.t ->
  discard:Terms.formula list ->
  ?iter_no:int ->
  (bool * Terms.formula * Terms.formula) list ->
  Terms.var_name list * Terms.formula

(** Twice as many angles of rotation are tried out for *)
val disjelim_rotations : int ref
(** For uniformity, we return an empty list as introduced variables. *)
val disjelim :
  Terms.quant_ops -> preserve:Terms.VarSet.t ->
  Terms.formula list -> Terms.var_name list * Terms.formula

(** Eliminate provided variables from the substitution part of solved
    form and generally simplify the formula, but do not perform
    quantifier elimination -- preserve those variables that are not
    equal to something else. *)
val simplify :
  Terms.quant_ops ->
  Terms.VarSet.t -> Terms.formula -> 
  Terms.var_name list * Terms.formula

(** Flatten additions, collect constants *)
val cleanup_typ : Terms.typ -> Terms.typ
val cleanup_formula : Terms.formula -> Terms.formula
(*
val equivalent :
  Terms.cmp_v -> Terms.uni_v ->
  Terms.formula ->  Terms.formula -> 
  bool
*)
(** Intersect atoms of the formulas, but only after generating
    consequences via Fourier elimination and turning equations into
    pairs of inequalities. *)
val converge :
  Terms.quant_ops ->
  Terms.formula -> Terms.formula -> Terms.formula

type state
val empty_state : state
val formula_of_state : state -> Terms.formula
val satisfiable : ?state:state -> Terms.atom list -> (exn, state) Aux.choice
val satisfiable_exn : ?state:state -> Terms.atom list -> state
(** Incremental check whether |= Q.A. Raises [Contradiction]. *)
val holds :
  Terms.quant_ops -> Terms.VarSet.t ->
  state -> Terms.formula -> state

val separate_subst :
  Terms.quant_ops ->
  Terms.formula -> Terms.subst * Terms.formula
