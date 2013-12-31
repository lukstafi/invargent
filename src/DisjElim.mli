(** Disjunction elimination for InvarGenT.

    Released under the GNU General Public Licence (version 2 or
    higher), NO WARRANTY of correctness etc. (C) Lukasz Stafiniak 2013
    @author Lukasz Stafiniak lukstafi (AT) gmail.com
    @since Mar 2013
*)

val disjelim :
  Defs.quant_ops -> bvs:Defs.VarSet.t -> preserve:Defs.VarSet.t
  -> do_num:bool -> Terms.formula list ->
  Defs.var_name list * Terms.atom list

(** Filter the initial postcondition, found from non-recursive
    branches only, so that it does not constrain variables to
    constants if other constraints on the variables are available. *)
val initstep_heur :
  Defs.quant_ops -> preserve:Defs.VarSet.t -> Terms.formula -> Terms.formula
