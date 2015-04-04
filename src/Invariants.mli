(** Solving second-order i.e. formula variables for InvarGenT.

    Released under the GNU General Public Licence (version 2 or
    higher), NO WARRANTY of correctness etc. (C) Lukasz Stafiniak 2013
    @author Lukasz Stafiniak lukstafi (AT) gmail.com
    @since Mar 2013
*)
val early_postcond_abd : bool ref
val timeout_count : int ref
val timeout_flag : bool ref
val unfinished_postcond_flag : bool ref
val use_prior_discards : bool ref
(** If [true], do not use specific heuristic settings for definitions
    with assertions. Currently, when [false], {!NumS.reward_constrn}
    is set to [-1] for definitions with assertions. *)
val same_with_assertions : bool ref
(** Breakdown of steps through the main iteration to achieve
    convergence, counting from 0. The iteration:

    * [disj_step.(0)] is when inferring any postconditions starts,
    * [disj_step.(1)] is when inferring numerical postconditions starts,
    * [disj_step.(2)] is when using only non-rec branches ends,
    * [disj_step.(3)] is when second-phase abduction starts,
    * [disj_step.(4)] is when guessing in constraint generation ends,
    * [disj_step.(5)] is when convergence of postconditions is enforced.
 *)
val disj_step : int array

type chi_subst = (int * (Defs.var_name list * Terms.formula)) list
val neg_constrns : bool ref
val solve :
  uses_pos_assertions:bool ->
  Defs.quant_ops -> (int * Defs.loc) list -> (int, int) Hashtbl.t ->
  (Terms.formula * Terms.formula) list ->
  Defs.quant_ops * Terms.formula * chi_subst
