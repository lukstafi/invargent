(** Abduction for InvarGenT.

    Released under the GNU General Public Licence (version 2 or
    higher), NO WARRANTY of correctness etc. (C) Lukasz Stafiniak 2013
    @author Lukasz Stafiniak lukstafi (AT) gmail.com
    @since Mar 2013
*)
type skip_kind = Superset_old_mod | Equ_old_mod
val skip_kind : skip_kind ref

(** [more_general=true] might produce a more general answer but is too
    costly; default [false]. *)
val more_general : bool ref
(** [richer_answers=true] produces answers in more cases because it tries
    answers with redundant atoms first, but can produce answers that
    are not most general. Default [false]. *)
val richer_answers : bool ref
val timeout_count : int ref
val fail_timeout_count : int ref
val no_alien_prem : bool ref

val abd_fail_flag : bool ref
val abd_timeout_flag : bool ref

val abd_simple :
  Terms.quant_ops ->
  ?without_quant:unit ->
  bvs:Terms.VarSet.t ->
  pms:Terms.VarSet.t -> dissociate:bool ->
  validate:((Terms.var_name list * Terms.subst) -> unit) ->
  discard:((Terms.var_name list * Terms.subst) list) ->
  int ->
  Terms.var_name list * Terms.subst ->
  Terms.subst * Terms.formula * Terms.subst ->
  (Terms.VarSet.t * (Terms.var_name list * Terms.subst)) option
val abd_typ :
  Terms.quant_ops ->
  bvs:Terms.VarSet.t ->
  ?dissociate:bool ->
  validate:((Terms.var_name list * Terms.subst) -> unit) ->
  discard:((Terms.var_name list * Terms.subst) list) ->
  (Terms.subst * Terms.formula * Terms.subst) list ->
  Terms.VarSet.t * Terms.subst *        (* alien_eqs *)
  Terms.var_name list * Terms.subst * (Terms.formula * Terms.formula) list
(** Raises [Contradiction] if constraints are contradictory and
    [NoAnswer] when no answer can be found. Returns candidate
    parameters [cand_bvs], alien subterm substitution [alien_eqs] and
    the answer. *)
val abd :
  Terms.quant_ops ->
  bvs:Terms.VarSet.t ->
  ?iter_no:int ->
  discard:(Terms.sort * Terms.formula list) list ->
  (bool * Terms.formula * Terms.formula) list ->
  Terms.VarSet.t * Terms.subst *
  (Terms.var_name list * Terms.formula)
val abd_mockup_num :
  Terms.quant_ops ->
  bvs:Terms.VarSet.t ->
  (Terms.formula * Terms.formula) list ->
  (Terms.formula * Terms.formula) list option
