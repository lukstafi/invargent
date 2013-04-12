(** Abduction for InvarGenT.

    Released under the GNU General Public Licence (version 2 or
    higher), NO WARRANTY of correctness etc. (C) Lukasz Stafiniak 2013
    @author Lukasz Stafiniak lukstafi (AT) gmail.com
    @since Mar 2013
*)
val abd_simple :
  (Terms.var_name -> Terms.var_name -> Terms.var_scope) ->
  (Terms.var_name -> bool) ->
  Terms.subst * Terms.subst ->
  (Terms.var_name list * (Terms.var_name * (Terms.typ * Terms.loc)) list *
   Terms.atom list)
  list
val abd_typ :
  (Terms.var_name -> Terms.var_name -> Terms.var_scope) ->
  (Terms.var_name -> bool) ->
  (Terms.subst * Terms.subst) list ->
  (Terms.VarSet.t * Terms.atom list * Terms.atom list list) list
(* val satisfiable_num : 'a -> bool *)
(* val abd_num : 'a -> 'b -> 'c -> ('d list * 'e list) list *)
val abd :
  (Terms.var_name -> Terms.var_name -> Terms.var_scope) ->
  (Terms.var_name -> bool) ->
  (Terms.atom list * Terms.atom list) list ->
  (Terms.VarSet.elt list * Terms.atom list) list
