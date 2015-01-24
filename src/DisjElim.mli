(** Disjunction elimination for InvarGenT.

    Released under the GNU General Public Licence (version 2 or
    higher), NO WARRANTY of correctness etc. (C) Lukasz Stafiniak 2013
    @author Lukasz Stafiniak lukstafi (AT) gmail.com
    @since Mar 2013
*)

(** Allow more general argument types by inferring more existential
    result type. Default value [false]. *)
val more_existential : bool ref
(** If [drop_csts=true], drop assignments of existential variables to
    constants during initial steps of main algorithm, as long as the
    variables are constrained in other atoms of the answer. Default
    [true]. *)
val drop_csts : bool ref

val disjelim :
  Defs.quant_ops -> ?target:Defs.var_name ->
  bvs:Defs.VarSet.t -> param_bvs:Defs.VarSet.t ->
  (* preserve:Defs.VarSet.t -> *) up_of_anchor:(Defs.var_name -> bool) ->
  do_num:bool -> guess:bool -> initstep:bool -> residuum:Terms.formula ->
  (Terms.formula * Terms.formula) list ->
  Terms.formula * (Defs.var_name list * Terms.formula)
