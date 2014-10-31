(** Disjunction elimination for InvarGenT.

    Released under the GNU General Public Licence (version 2 or
    higher), NO WARRANTY of correctness etc. (C) Lukasz Stafiniak 2013
    @author Lukasz Stafiniak lukstafi (AT) gmail.com
    @since Mar 2013
*)

(** Allow more general argument types by inferring more existential
    result type. Default value [false]. *)
val more_existential : bool ref

val disjelim :
  Defs.quant_ops -> bvs:Defs.VarSet.t -> preserve:Defs.VarSet.t ->
  do_num:bool -> initstep:bool -> Terms.formula list ->
  Terms.subst * (Defs.var_name list * Terms.atom list)
