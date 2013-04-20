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
  (Terms.subst * Terms.subst) list ->
  (Terms.var_name list * Terms.subst * Terms.atom list list) option
val abd :
  (Terms.var_name -> Terms.var_name -> Terms.var_scope) ->
  (Terms.var_name -> bool) ->
  (Terms.atom list * Terms.atom list) list ->
  (Terms.var_name list * Terms.atom list) option
val abd_mockup_num :
  (Terms.var_name -> Terms.var_name -> Terms.var_scope) ->
  (Terms.var_name -> bool) ->
  (Terms.atom list * Terms.atom list) list ->
  (Terms.atom list * Terms.atom list) list option
