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
  Defs.quant_ops ->
  ?without_quant:unit ->
  bvs:Defs.VarSet.t ->
  pms:Defs.VarSet.t -> dissociate:bool ->
  validate:((Defs.var_name list * Terms.subst) -> unit) ->
  discard:((Defs.var_name list * Terms.subst) list) ->
  int ->
  Defs.var_name list * Terms.subst ->
  Terms.sep_formula * Terms.subst ->
  (Defs.VarSet.t * (Defs.var_name list * Terms.subst)) option
val abd_typ :
  Defs.quant_ops ->
  bvs:Defs.VarSet.t ->
  ?dissociate:bool ->
  validate:((Defs.var_name list * Terms.subst) -> unit) ->
  discard:((Defs.var_name list * Terms.subst) list) ->
  (Terms.sep_formula * Terms.subst) list ->
  Defs.VarSet.t * Terms.subst *        (* alien_eqs *)
  Defs.var_name list * Terms.subst *
    (Terms.sep_formula * Terms.sep_formula) list

type discarded =
  ((Defs.var_name list * Terms.subst) list,
   NumDefs.formula list, unit) Terms.sep_sorts
(** Raises [Contradiction] if constraints are contradictory and
    [NoAnswer] when no answer can be found. Returns candidate
    parameters [cand_bvs], alien subterm substitution [alien_eqs] and
    the answer. *)
val abd :
  Defs.quant_ops ->
  bvs:Defs.VarSet.t ->
  ?iter_no:int ->
  discard:discarded ->
  (bool * Terms.formula * Terms.formula) list ->
  Defs.VarSet.t * Terms.subst *
  (Defs.var_name list * Terms.formula)
val abd_mockup_num :
  Defs.quant_ops ->
  bvs:Defs.VarSet.t ->
  (Terms.formula * Terms.formula) list ->
  (NumDefs.formula * NumDefs.formula) list option
