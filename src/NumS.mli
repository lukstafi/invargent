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
(** Treat the numerical domain as integers when pruning
    formulas. Default [true]. *)
val int_pruning : bool ref
(** When pruning, discard constraints that force a variable to a
    single value. Default [false]. *)
val strong_int_pruning : bool ref
val passing_ineq_trs : bool ref
(** Do not create subopti atoms of the form [k<=max(C,..)] etc. where
    [C] is a constant (default true). *)
val subopti_of_cst : [`No_sides | `Left_side | `Both_sides] ref
(** Replace variable=constant equations by variable=variable equations
    in initial abduction candidates to promote generality of
    answers. Default [true]. *)
val revert_csts : bool ref
(** How much to penalize an abduction candidate inequality for
    belonging to some formula in the discard list. Default [2]. *)
val discard_penalty : int ref
(** How much to penalize an abduction candidate inequality for
    containing a constant term. Default [4]. *)
val affine_penalty : int ref
(** How much to reward introducing a constraint on so-far
    unconstrained varialbe (or penalize, if negative). Default [2]. *)
val reward_constrn : int ref
(** How much to penalize for complexity; the coefficient $a$ in the
    description of {!complexity_scale}. Default [2.5]. *)
val complexity_penalty : float ref
(** How much to penalize for variables that are not parameters but
    instead instances from use sites of existential types. Default [6]. *)
val nonparam_vars_penalty : int ref
(** Prefer bound coming from outer scope, to inequality between two
    local parameters. Default [false]. *)
val prefer_bound_to_local : bool ref
(** Prefer a bound coming from outer scope, to inequality between two
    outer scope parameters. Default [false]. *)
val prefer_bound_to_outer : bool ref
(** Limit the effect of [prefer_bound_to_local] and
    [prefer_bound_to_outer] to inequalities with a constant 1. This
    corresponds to an upper bound of zero-indexed array/matrix/etc. *)
val only_off_by_1 : bool ref
(** Penalize abductive guess when the supporting argument comes from
    the partial answer, instead of from the current premise. Default [4]. *)
val concl_abd_penalty : int ref
(** Filter out less general abduction candidate atoms (does not
    guarantee overall more general answers). Default [false]. *)
val more_general : bool ref
(** How to scale coefficients when computing complexity: either by
    raising to the given power i.e. [a*k^b], or by linear scaling with
    a jump at the given threshold with the given height
    i.e. $a*k + a*1_{b<=k}$. Default [`LinThres (2, 2.0)]. *)
val complexity_scale : [`LinThres of int * float | `Pow of float] ref
(** Twice as many angles of rotation are tried out for *)
val disjelim_rotations : int ref
(** How many opti atoms: [x = min(a, b)], [x = max(a, b)] in a
    postcondition. *)
val max_opti_postcond : int ref
(** How many subopti atoms: [min(a, b) <= x], [x <= max(a, b)] in a
    postcondition. *)
val max_subopti_postcond : int ref
(* TODO: export more knobs, i.e. global reference variables; also add their
   command-line interfaces in [InvarGenT.main]. *)

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
  xbvs:(int * Defs.VarSet.t) list ->
  ?orig_ren:(Defs.var_name, Defs.var_name) Hashtbl.t ->
  ?b_of_v:(Defs.var_name -> Defs.var_name) ->
  upward_of:(Defs.var_name -> Defs.var_name -> bool) ->
  nonparam_vars:Defs.VarSet.t ->
  discard:NumDefs.formula list ->
  ?iter_no:int ->
  (bool * (int * (Defs.var_name * Defs.var_name) list) list *
     NumDefs.formula * NumDefs.formula) list ->
  Defs.var_name list * NumDefs.formula

(** For uniformity, we return an empty list as introduced variables. *)
val disjelim :
  Defs.quant_ops -> target_vs:Defs.VarSet.t -> preserve:Defs.VarSet.t ->
  bvs:Defs.VarSet.t -> param_bvs:Defs.VarSet.t ->
  guess:bool -> initstep:bool ->
  (NumDefs.formula * NumDefs.formula) list ->
  Defs.var_name list * NumDefs.formula * NumDefs.formula *
    NumDefs.formula list

(** Eliminate provided variables from the substitution part of solved
    form and generally simplify the formula, but do not perform
    quantifier elimination -- preserve those variables that are not
    equal to something else. *)
val simplify :
  Defs.quant_ops ->
  ?keepvs:Defs.VarSet.t -> ?localvs:Defs.VarSet.t -> ?guard:NumDefs.formula ->
  Defs.VarSet.t -> NumDefs.formula -> 
  Defs.var_name list * NumDefs.formula

(** Prune atoms implied by other atoms -- for efficiency, only single
    other atoms, i.e. "atom-on-atom", are considered. Prefer other
    atoms over opti atoms. *)
val prune_redundant :
  Defs.quant_ops -> ?localvs:Defs.VarSet.t ->
  ?guard:NumDefs.formula ->
  initstep:bool ->
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
val num_to_formula : NumDefs.formula -> Terms.formula
val pr_state : Format.formatter -> state -> unit
val satisfiable :
  ?state:state -> NumDefs.formula -> (exn, state) Aux.choice
val satisfiable_exn : ?state:state -> NumDefs.formula -> state
(* States computed by [satisfiable] should be used, to match the variable
   ordering. *)
val implies_cnj : state -> NumDefs.formula -> bool
(** Incremental check whether |= Q.A. Raises [Contradiction]. *)
val holds :
  Defs.quant_ops -> Defs.VarSet.t ->
  state -> NumDefs.formula -> state
(** Incremental check whether |= Q.A. Collects implied formulas that
    would not hold if the given parameters were universally quantified.
    Raises [Contradiction]. *)
val abductive_holds :
  Defs.quant_ops -> bvs:Defs.VarSet.t ->
  state -> NumDefs.formula -> state * NumDefs.formula
val negation_elim :
  Defs.quant_ops -> bvs:Defs.VarSet.t ->
  verif_cns:state list ->
  (NumDefs.formula * Defs.loc) list ->
  NumDefs.formula
val separate_subst :
  Defs.quant_ops -> ?no_csts:bool -> ?keep:Defs.VarSet.t ->
  ?bvs:Defs.VarSet.t -> apply:bool -> NumDefs.formula ->
  Terms.subst * (Defs.var_name * NumDefs.term) list * NumDefs.formula

val transitive_cl : Defs.quant_ops -> NumDefs.formula -> NumDefs.formula
