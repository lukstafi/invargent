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
(** Treat the numerical domain as integers when computing negative
    constraints. Default [true]. *)
val abd_int_negation : bool ref
(** Treat the numerical domain as integers when pruning
    formulas. Default [true]. *)
val int_pruning : bool ref
(** When pruning, discard constraints that force a variable to a
    single value. Default [false]. *)
val strong_int_pruning : bool ref
val passing_ineq_trs : bool ref
(** Do not create subopti atoms of the form [k<=max(C,..)] etc. where
    [C] is a constant (default true). *)
val no_subopti_of_cst : bool ref

val num_of : Terms.typ -> NumDefs.term
val sort_formula : Terms.formula -> NumDefs.formula
val formula_of_sort : NumDefs.formula -> Terms.formula
val sort_of_subst : Terms.subst -> NumDefs.formula

type subst = (Defs.var_name * (NumDefs.term * Defs.loc)) list

val subst_num_formula : subst -> NumDefs.formula -> NumDefs.formula
val subst_formula : Terms.subst -> NumDefs.formula -> NumDefs.formula

val abd_fail_flag : bool ref
val abd_timeout_flag : bool ref
(** For uniformity, return an empty list as introduced
    variables. Raise [Contradiction] if constraints are contradictory
    and [Suspect] if no answer can be found. *)
val abd :
  Defs.quant_ops ->
  bvs:Defs.VarSet.t ->
  discard:NumDefs.formula list ->
  ?iter_no:int ->
  (bool * NumDefs.formula * NumDefs.formula) list ->
  Defs.var_name list * NumDefs.formula

(** Twice as many angles of rotation are tried out for *)
val disjelim_rotations : int ref
(** For uniformity, we return an empty list as introduced variables. *)
val disjelim :
  Defs.quant_ops -> preserve:Defs.VarSet.t -> initstep:bool ->
  NumDefs.formula list -> Defs.var_name list * NumDefs.formula

(** Eliminate provided variables from the substitution part of solved
    form and generally simplify the formula, but do not perform
    quantifier elimination -- preserve those variables that are not
    equal to something else. *)
val simplify :
  Defs.quant_ops ->
  ?localvs:Defs.VarSet.t -> ?guard:NumDefs.formula ->
  Defs.VarSet.t -> NumDefs.formula -> 
  Defs.var_name list * NumDefs.formula

(** Prune atoms implied by other atoms -- for efficiency, only single
    other atoms, i.e. "atom-on-atom", are considered. Prefer other
    atoms over opti atoms. *)
val prune_redundant :
  Defs.quant_ops -> ?localvs:Defs.VarSet.t ->
  ?guard:NumDefs.formula -> initstep:bool ->
  NumDefs.formula -> NumDefs.formula

(** Intersect atoms of the formulas, but only after generating
    consequences via Fourier elimination and turning equations into
    pairs of inequalities. *)
val converge :
  Defs.quant_ops -> ?localvs:Defs.VarSet.t -> ?guard:NumDefs.formula ->
  initstep:bool ->
  NumDefs.formula -> NumDefs.formula -> NumDefs.formula

type state
val empty_state : state
val formula_of_state : state -> NumDefs.formula
val pr_state : Format.formatter -> state -> unit
val satisfiable :
  ?state:state -> NumDefs.formula -> (exn, state) Aux.choice
val satisfiable_exn : ?state:state -> NumDefs.formula -> state
(** Incremental check whether |= Q.A. Raises [Contradiction]. *)
val holds :
  Defs.quant_ops -> Defs.VarSet.t ->
  state -> NumDefs.formula -> state
val negation_elim :
  Defs.quant_ops -> bvs:Defs.VarSet.t ->
  verif_cns:state list ->
  (NumDefs.formula * Defs.loc) list ->
  NumDefs.formula
val separate_subst :
  Defs.quant_ops -> ?no_csts:bool -> ?keep:Defs.VarSet.t -> NumDefs.formula ->
  Terms.subst * NumDefs.formula
val initstep_heur :
  Defs.quant_ops -> preserve:Defs.VarSet.t ->
  NumDefs.formula -> NumDefs.formula

val transitive_cl : NumDefs.formula -> NumDefs.formula
