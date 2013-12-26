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
  val abd_fail_timeout : int
  val abd_fail_flag : bool ref
  val abd_simple :
    args -> discard:discarded list -> validate:(answer -> unit) ->
    accu -> branch -> accu option
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
    P.args -> discard:P.discarded list -> validate:(P.answer -> unit) ->
    P.accu -> P.branch list -> P.accu
end

val transitive_cl : ('a * 'a * loc) list -> ('a * 'a, loc) Hashtbl.t
