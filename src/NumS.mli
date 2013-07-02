(** Numeric sort operations for InvarGenT.

    Released under the GNU General Public Licence (version 2 or
    higher), NO WARRANTY of correctness etc. (C) Lukasz Stafiniak 2013
    @author Lukasz Stafiniak lukstafi (AT) gmail.com
    @since Mar 2013
*)

(** For uniformity, we return an empty list as introduced
    variables. Raise [Suspect] if no answer can be found. *)
val abd :
  (Terms.var_name -> Terms.var_name -> Terms.var_scope) ->
  (Terms.var_name -> bool) ->
  Terms.params ->  
  (Terms.formula * Terms.formula) list ->
  Terms.var_name list * Terms.formula
val abd_s :
  (Terms.var_name -> Terms.var_name -> Terms.var_scope) ->
  (Terms.var_name -> bool) ->
  Terms.params ->  
  Terms.formula -> Terms.formula ->
  (Terms.var_name list * Terms.formula) option

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
  Terms.var_name list -> Terms.formula -> 
  Terms.var_name list * Terms.formula

val satisfiable : Terms.atom list -> bool

type state
val empty_state : state
val formula_of_state : state -> Terms.formula
(** Incremental check whether |= Q.A. Raises [Contradiction]. *)
val holds :
  (Terms.var_name -> Terms.var_name -> Terms.var_scope) ->
  (Terms.var_name -> bool) ->
  state -> Terms.formula -> state
