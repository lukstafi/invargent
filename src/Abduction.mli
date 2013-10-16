(** Abduction for InvarGenT.

    Released under the GNU General Public Licence (version 2 or
    higher), NO WARRANTY of correctness etc. (C) Lukasz Stafiniak 2013
    @author Lukasz Stafiniak lukstafi (AT) gmail.com
    @since Mar 2013
*)
type skip_kind = Superset_old_mod | Equ_old_mod
val skip_kind : skip_kind ref

(** If [more_general=false] works usually faster, if it doesn't work
    try [more_general=true] (gives the same or better answers). *)
val more_general : bool ref


type vparams = (Terms.var_name * Terms.VarSet.t) list
val pr_vparams : Format.formatter -> vparams -> unit
val abd_simple :
  Terms.quant_ops ->
  ?without_quant:unit ->
  bvs:Terms.VarSet.t -> zvs:Terms.VarSet.t ->
  bparams:vparams -> zparams:vparams ->
  validate:(Terms.var_name list -> Terms.subst -> unit) ->
  discard:Terms.subst list ->
  int ->
  Terms.var_name list * Terms.subst ->
  Terms.subst * Terms.subst ->
  (Terms.var_name list * Terms.subst) option
val abd_typ :
  Terms.quant_ops ->
  bvs:Terms.VarSet.t -> zvs:Terms.VarSet.t ->
  bparams:vparams -> zparams:vparams ->
  ?dissociate:bool ->
  validate:(Terms.var_name list -> Terms.subst -> unit) ->
  discard:Terms.subst list ->
  (Terms.subst * Terms.subst) list ->
  Terms.subst *                         (* alien_eqs *)
  Terms.var_name list * Terms.subst * (Terms.formula * Terms.formula) list
(** Raises [Contradiction] if constraints are contradictory and
    [NoAnswer] when no answer can be found. *)
val abd :
  Terms.quant_ops ->
  bvs:Terms.VarSet.t -> zvs:Terms.VarSet.t ->
  bparams:vparams -> zparams:vparams ->
  ?iter_no:int ->
  discard:(Terms.sort * Terms.formula list) list ->
  (bool * Terms.formula * Terms.formula) list ->
  Terms.subst *                         (* alien_eqs *)
  (Terms.var_name list * Terms.formula)
val abd_mockup_num :
  Terms.quant_ops ->
  bvs:Terms.VarSet.t ->
  zvs:Terms.VarSet.t ->
  bparams:vparams ->
  zparams:vparams ->
  (Terms.formula * Terms.formula) list ->
  (Terms.formula * Terms.formula) list option
