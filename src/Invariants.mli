(** Solving second-order i.e. formula variables for InvarGenT.

    Released under the GNU General Public Licence (version 2 or
    higher), NO WARRANTY of correctness etc. (C) Lukasz Stafiniak 2013
    @author Lukasz Stafiniak lukstafi (AT) gmail.com
    @since Mar 2013
*)
val early_postcond_abd : bool ref
type chi_subst = (int * (Terms.var_name list * Terms.formula)) list
val neg_constrns : bool ref
val solve :
  Terms.quant_ops -> (int * Terms.loc) list -> (int, int) Hashtbl.t ->
  (Terms.formula * Terms.formula) list ->
  Terms.quant_ops * Terms.formula * chi_subst
