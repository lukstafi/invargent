(** Disjunction elimination for InvarGenT.

    Released under the GNU General Public Licence (version 2 or
    higher), NO WARRANTY of correctness etc. (C) Lukasz Stafiniak 2013
    @author Lukasz Stafiniak lukstafi (AT) gmail.com
    @since Mar 2013
*)

val disjelim :
  Terms.quant_ops -> preserve:Terms.VarSet.t -> do_num:bool ->
  Terms.formula list ->
  Terms.var_name list * Terms.atom list

(** Filter the initial postcondition, found from non-recursive
    branches only, so that it does not constrain variables to
    constants if other constraints on the variables are available. *)
val initstep_heur :
  Terms.quant_ops -> preserve:Terms.VarSet.t -> Terms.formula -> Terms.formula
