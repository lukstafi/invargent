(** Disjunction elimination for InvarGenT.

    Released under the GNU General Public Licence (version 2 or
    higher), NO WARRANTY of correctness etc. (C) Lukasz Stafiniak 2013
    @author Lukasz Stafiniak lukstafi (AT) gmail.com
    @since Mar 2013
*)

val disjelim :
  Terms.quant_ops ->
  do_num:bool ->
  Terms.formula list ->
  Terms.var_name list * Terms.atom list
