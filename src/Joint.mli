(** Algorithms shared across sorts for InvarGenT.

    Released under the GNU General Public Licence (version 2 or
    higher), NO WARRANTY of correctness etc. (C) Lukasz Stafiniak 2013
    @author Lukasz Stafiniak lukstafi (AT) gmail.com
    @since Mar 2013
*)

open Defs
open Terms
open Aux

module type ABD_PARAMS = sig
  type accu
  type args
  type answer
  type discarded
  type branch
  type br_state
  type validation = (VarSet.t * br_state) list
  val abd_fail_timeout : int ref
  val abd_fail_flag : bool ref
  (** The variables passed to [validate] should be the variables of
      the atom whose addition to the partial answer is being
      validated. Usually only one of [validation], [validate] is used. *)
  val abd_simple :
    args -> discard:discarded list ->
    validation:validation ->
    validate:(VarSet.t -> answer -> unit) ->    
    neg_validate:(answer -> int) ->
    accu -> branch -> (accu * validation) option
  val extract_ans : accu -> answer
  val discard_ans : accu -> discarded
  val concl_of_br : branch -> formula
  val is_taut : answer -> bool
  val pr_branch : Format.formatter -> branch -> unit
  val pr_ans : Format.formatter -> answer -> unit
end

val debug_dep : int ref

module JointAbduction (P : ABD_PARAMS) : sig
  val abd :
    P.args -> discard:P.discarded list ->
    P.validation ->
    validate:(VarSet.t -> P.answer -> unit) ->
    neg_validate:(P.answer -> int) ->
    P.accu -> P.branch list -> P.accu
end

val transitive_cl : ('a * 'a * loc) list -> ('a * 'a, loc) Hashtbl.t
