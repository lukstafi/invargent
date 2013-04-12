(** Numeric sort operations for InvarGenT.

    Released under the GNU General Public Licence (version 2 or
    higher), NO WARRANTY of correctness etc. (C) Lukasz Stafiniak 2013
    @author Lukasz Stafiniak lukstafi (AT) gmail.com
    @since Mar 2013
*)

val satisfiable_num : Terms.atom list -> bool
val abd_num :
  (Terms.var_name -> Terms.var_name -> Terms.var_scope) ->
  (Terms.var_name -> bool) ->
  (Terms.formula * Terms.formula) list ->
  (Terms.VarSet.t * Terms.atom list) list
