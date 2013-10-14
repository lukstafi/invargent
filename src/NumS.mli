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
(** For uniformity, return an empty list as introduced
    variables. Raise [Contradiction] if constraints are contradictory
    and [Suspect] if no answer can be found. [paramvs] includes alien
    variables, *)
val abd :
  (Terms.var_name -> Terms.var_name -> Terms.var_scope) ->
  (Terms.var_name -> bool) ->
  paramvs:Terms.VarSet.t ->
  bparams:(Terms.var_name * Terms.VarSet.t) list ->
  discard:Terms.formula list ->
  ?iter_no:int ->
  (bool * Terms.formula * Terms.formula) list ->
  Terms.var_name list * Terms.formula

(** Twice as many angles of rotation are tried out for *)
val disjelim_rotations : int ref
(** For uniformity, we return an empty list as introduced variables. *)
val disjelim :
  (Terms.var_name -> Terms.var_name -> Terms.var_scope) ->
  (Terms.var_name -> bool) ->
  Terms.formula list -> Terms.var_name list * Terms.formula

(** Perform quantifier elimination on provided variables and generally
    simplify the formula. Since linear arithmetic has quantifier
    elimination, always returns empty variable list. *)
val simplify :
  (Terms.var_name -> Terms.var_name -> Terms.var_scope) ->
  (Terms.var_name -> bool) ->
  Terms.VarSet.t -> Terms.formula -> 
  Terms.var_name list * Terms.formula
(*
val equivalent :
  (Terms.var_name -> Terms.var_name -> Terms.var_scope) ->
  (Terms.var_name -> bool) -> Terms.formula ->  Terms.formula -> 
  bool
*)
(** Intersect atoms of the formulas, but only after generating
    consequences via Fourier elimination and turning equations into
    pairs of inequalities. *)
val converge :
  (Terms.var_name -> Terms.var_name -> Terms.var_scope) ->
  (Terms.var_name -> bool) ->
  Terms.formula -> Terms.formula -> Terms.formula

type state
val empty_state : state
val formula_of_state : state -> Terms.formula
val satisfiable : ?state:state -> Terms.atom list -> (exn, state) Aux.choice
val satisfiable_exn : ?state:state -> Terms.atom list -> state
(** Incremental check whether |= Q.A. Raises [Contradiction]. *)
val holds :
  (Terms.var_name -> Terms.var_name -> Terms.var_scope) ->
  (Terms.var_name -> bool) ->
  state -> Terms.formula -> state

val separate_subst :
  (Terms.var_name -> Terms.var_name -> Terms.var_scope) ->
  (Terms.var_name -> bool) ->
  Terms.formula -> Terms.subst * Terms.formula
