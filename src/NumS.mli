(** Numeric sort operations for InvarGenT.

    Released under the GNU General Public Licence (version 2 or
    higher), NO WARRANTY of correctness etc. (C) Lukasz Stafiniak 2013
    @author Lukasz Stafiniak lukstafi (AT) gmail.com
    @since Mar 2013
*)

(** Retry a failed search with fitted scalar equations. *)
val with_affine_retry : (unit -> 'a) -> 'a
(** Retry a failed declaration with joint equation fits and projected numeric guards. *)
val with_joint_retry : (unit -> 'a) -> 'a
val observe_guard_choices : (unit -> 'a) -> 'a * bool
val with_combined_guards : (unit -> 'a) -> 'a

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
val complexity_scale : [`LinThres of float * float | `Pow of float] ref
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

(** Propose an integer-affine key at recursive uses of a translated scalar
    interval. The caller must check the proposal against the full program. *)
val fit_interval_call :
  index:Defs.var_name -> key:Defs.var_name -> samples:int list ->
  bands:(int * int) list ->
  package:(Defs.var_name * Defs.var_name * NumDefs.formula) ->
  NumDefs.formula -> Defs.loc -> NumDefs.atom option

(** If a single line fails, [piecewise] also tries minima and maxima of
    lines and piecewise integer interpolation. Extra variables in each
    candidate are local to one call. *)
val fit_interval_calls :
  ?piecewise:bool -> index:Defs.var_name -> key:Defs.var_name -> samples:int list ->
  bands:(int * int) list -> package:(Defs.var_name * Defs.var_name * NumDefs.formula) ->
  NumDefs.formula -> Defs.loc -> NumDefs.formula list

(** Symbolic extrema of admissible keys across any number of exposed input
    indices, for fixed forbidden bands and integer-affine key bounds. *)
val symbolic_interval_calls :
  inputs:Defs.VarSet.t -> key:Defs.var_name -> bands:(int * int) list ->
  package:(Defs.var_name * Defs.var_name * NumDefs.formula) ->
  NumDefs.formula -> Defs.loc -> NumDefs.formula list

(** Select the full guard check when a key occurs on only one side of a
    disjunction or opposing bounds include an exposed admission face. *)
val has_conditional_key_bound : keys:Defs.var_name list -> NumDefs.formula -> bool

(** Propose two extremal keys and the constraints defining their values. *)
val interval_endpoints : inputs:Defs.VarSet.t -> key:Defs.var_name ->
  NumDefs.formula -> Defs.loc -> (NumDefs.term * NumDefs.term * NumDefs.formula) option

(** Candidate keys at the strict boundaries of a disjunctive package
    inequality, using the observed payload and exposed input indices. *)
val refuting_keys : inputs:Defs.VarSet.t -> key:Defs.var_name -> result:Defs.var_name ->
  NumDefs.formula -> NumDefs.term list

type key_probe = { target_value : NumDefs.term; clip_lower : NumDefs.term; clip_upper : NumDefs.term }

(** Each proposal gives a target and the endpoints onto which to clip it.
    The accompanying formula defines fresh extrema from the input indices. *)
val component_keys : inputs:Defs.VarSet.t -> key:Defs.var_name -> result:Defs.var_name ->
  post:NumDefs.formula -> NumDefs.formula -> Defs.loc ->
  key_probe list * NumDefs.formula

(** Select a legal key by guarded affine cases, allowing the interval's
    lower and upper offsets to depend on observed integer arguments. The graph
    covers the original key domain even if avoidance is impossible. When
    [checks] is supplied, require every written opening to miss those bands
    before returning a proposal. *)
val guarded_interval_call :
  ?checks:(NumDefs.term * NumDefs.term) list ->
  inputs:Defs.VarSet.t -> key:Defs.var_name -> result:Defs.var_name ->
  bands:(NumDefs.term * NumDefs.term) list -> post:NumDefs.formula ->
  NumDefs.formula -> Defs.loc -> NumDefs.formula list

val num_of : Terms.typ -> NumDefs.term
val sort_formula : Terms.formula -> NumDefs.formula
val formula_of_sort : NumDefs.formula -> Terms.formula
val sort_of_assoc :
  (Defs.var_name * (Terms.typ * Defs.loc)) list -> NumDefs.formula
val sort_of_subst : Terms.subst -> NumDefs.formula

type subst = (NumDefs.term * Defs.loc) Defs.VarMap.t

val subst_num_formula : subst -> NumDefs.formula -> NumDefs.formula
val subst_formula : Terms.subst -> NumDefs.formula -> NumDefs.formula

val abd_fail_flag : bool ref
val abd_timeout_flag : bool ref
(** For uniformity, return an empty list as introduced
    variables. Raise [Contradiction] if constraints are contradictory
    and [Suspect] if no answer can be found. Optional [caller_checks] are the
    unsplit positive obligations used to validate a recovered input bound. *)
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
  ?caller_checks:(NumDefs.formula * NumDefs.formula) list ->
  (bool * (int * Terms.hvsubst) list *
     NumDefs.formula * NumDefs.formula) list ->
  Defs.var_name list * NumDefs.formula

(** For uniformity, we return an empty list as introduced variables. *)
val disjelim :
  Defs.quant_ops -> ?previous:NumDefs.formula -> target_vs:Defs.VarSet.t -> preserve:Defs.VarSet.t ->
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

(** Simplify the local constraints under their guard. In the initial
    supplier generalization, [allow_weakening] also admits consequences of
    the supplied formula. Extrema are checked before accepting a change. *)
val prune_redundant :
  Defs.quant_ops -> ?allow_weakening:bool -> ?localvs:Defs.VarSet.t ->
  ?guard:NumDefs.formula ->
  initstep:bool ->
  NumDefs.formula -> NumDefs.formula

(** Widen aligned postconditions by retaining old atoms implied by the
    new summary. Optional suppliers can also prove an atom over the shared
    interface when every projected branch entails it. An empty list
    disables this branch check. With [recover_caps], a new bound on that
    interface can tighten one arm of a retained bound by a constant. *)
val converge :
  Defs.quant_ops -> ?recover_caps:bool -> ?localvs:Defs.VarSet.t -> ?guard:NumDefs.formula ->
  ?suppliers:(Defs.VarSet.t * NumDefs.formula list) ->
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
(** Existential projection over rational indices. The result is a disjunction
    of conjunctions. Atoms independent of [vars] retain their original form. *)
val project_exists : vars:Defs.VarSet.t -> NumDefs.formula -> NumDefs.formula list
type cycle_domain = Outside_directions | Empty_cycle | Cycle_guard of NumDefs.formula

(** A recursive data value with affine field indices. Project a common
    inductive bound for each live guard direction when its pullbacks fit. *)
val affine_cycle_guard : params:Defs.var_name list -> guard:NumDefs.formula ->
  fields:NumDefs.term list list -> Defs.loc -> cycle_domain

(** Replay a direct constructor against the cells of a proposed recursive scheme. *)
val replay_cycle : params:Defs.var_name list -> guard:NumDefs.formula -> fields:NumDefs.term list list ->
  NumDefs.formula -> Defs.loc -> bool
(** Check a numeric value alias after identifying the requested public tuple. *)
val cycle_alias : premise:NumDefs.formula -> hidden:Defs.VarSet.t -> NumDefs.formula -> Defs.loc -> bool
(** Enlarge a certified cone by exact field preimages until it covers the caller domains. *)
val caller_cycle_guard : params:Defs.var_name list -> guard:NumDefs.formula -> fields:NumDefs.term list list ->
  demands:NumDefs.formula list -> Defs.loc -> NumDefs.formula option
(** Recognize a folded scheme that a plain alias can reuse verbatim. *)
val is_folded_domain : params:Defs.var_name list -> NumDefs.formula -> Defs.loc -> bool
(** Construct and check a private folded norm for planar fields with an expanding slack. *)
val folded_caller_guard : params:Defs.var_name list -> guard:NumDefs.formula -> fields:NumDefs.term list list ->
  demands:NumDefs.formula list -> Defs.loc -> NumDefs.formula option
(** Private component bounds and field obligations for a checked spectral scheme. *)
val spectral_cycle_guard : params:Defs.var_name list -> guard:NumDefs.formula ->
  fields:NumDefs.term list list -> Defs.loc -> (NumDefs.formula * NumDefs.formula) option
val join_cycle_guards : params:Defs.var_name list -> fields:NumDefs.term list list -> old:NumDefs.formula ->
  guard:NumDefs.formula -> bounds:NumDefs.formula -> future:NumDefs.formula ->
  Defs.loc -> NumDefs.formula option

(** Feasibility of a numeric premise and a finite conjunction of
    admission => postcondition clauses. Use fresh private witnesses for each
    distinct opening. Cells licensing the same opening may share its postcondition. *)
val conditional_satisfiable :
  NumDefs.formula -> (NumDefs.formula * NumDefs.formula) list -> bool
(** Feasibility of [pre] and [forall keys. admission => exists witnesses. post]
    over the rationals. An optional [integer_result] designates a term of the
    free observation whose value must be integral. With [integer_inputs] the
    checker also uses necessary joint integer constraints on the actual inputs
    and result. Admissions are a union of cells. The two sets of bound
    coordinates must be fresh for [pre] and disjoint from one another. *)
val common_result_possible :
  ?integer_result:NumDefs.term -> ?integer_inputs:NumDefs.term list ->
  keys:Defs.VarSet.t -> witnesses:Defs.VarSet.t ->
  admissions:NumDefs.formula list -> post:NumDefs.formula -> NumDefs.formula -> bool
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
  Terms.subst * NumDefs.term Defs.VarMap.t * NumDefs.formula

val transitive_cl : Defs.quant_ops -> NumDefs.formula -> NumDefs.formula
