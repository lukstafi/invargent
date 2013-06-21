(** Abduction for InvarGenT.

    Released under the GNU General Public Licence (version 2 or
    higher), NO WARRANTY of correctness etc. (C) Lukasz Stafiniak 2013
    @author Lukasz Stafiniak lukstafi (AT) gmail.com
    @since Mar 2013
*)

val abd_simple :
  (Terms.var_name -> Terms.var_name -> Terms.var_scope) ->
  (Terms.var_name -> bool) ->
  (Terms.VarSet.elt list -> Terms.subst -> unit) -> int ->
  Terms.var_name list * Terms.subst ->
  Terms.subst * Terms.subst ->
  (Terms.var_name list * Terms.subst)
  option
val abd_typ :
  (Terms.var_name -> Terms.var_name -> Terms.var_scope) ->
  (Terms.var_name -> bool) ->
  ?fincheck:(Terms.var_name list * Terms.subst -> bool) ->
  (Terms.subst * Terms.subst) list ->
  Terms.var_name list * Terms.subst * Terms.formula list
(* Raises [Suspect] if no answer can be found. *)
val abd :
  (Terms.var_name -> Terms.var_name -> Terms.var_scope) ->
  (Terms.var_name -> bool) ->
  ?fincheck:(Terms.var_name list * Terms.subst -> bool) ->
  (Terms.formula * Terms.formula) list ->
  Terms.var_name list * Terms.formula
val abd_mockup_num :
  (Terms.var_name -> Terms.var_name -> Terms.var_scope) ->
  (Terms.var_name -> bool) ->
  (Terms.formula * Terms.formula) list ->
  (Terms.formula * Terms.formula) list option
val abd_s :
  (Terms.var_name -> Terms.var_name -> Terms.var_scope) ->
  (Terms.var_name -> bool) ->
  Terms.formula -> Terms.formula ->
  (Terms.var_name list * Terms.formula) option
