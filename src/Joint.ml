(** Algorithms shared across sorts for InvarGenT.

    Released under the GNU General Public Licence (version 2 or
    higher), NO WARRANTY of correctness etc. (C) Lukasz Stafiniak 2013
    @author Lukasz Stafiniak lukstafi (AT) gmail.com
    @since Mar 2013
*)

open Terms
open Aux

module type ABD_PARAMS = sig
  type accu
  type args
  type answer
  type discarded
  type branch
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

let debug_dep = ref 0

module JointAbduction (P : ABD_PARAMS) = struct

  let abd args ~discard ~validate init_acc brs =
    let culprit = ref None
    and best_done = ref (-1) in
    let rec loop discard acc done_brs aside_brs = function
      | [] ->
        let best =
          List.length done_brs > !best_done &&
          (best_done := List.length done_brs; true) in
        check_aside best discard acc done_brs aside_brs
      | br::more_brs ->
        let ddepth = incr debug_dep; !debug_dep in
        Format.printf
          "abd-loop: [%d] #discard=%d, #done_brs=%d, #aside_brs=%d, #more_brs=%d@\n%a@\n%!"
          ddepth (List.length discard) (List.length done_brs)
          (List.length aside_brs)
          (List.length more_brs) P.pr_branch br; (* *)
        match P.abd_simple args ~discard ~validate acc br with
        | Some acc ->
          loop discard acc (br::done_brs) aside_brs more_brs
        | None ->
          loop discard acc done_brs (br::aside_brs) more_brs

    and check_aside best discard acc done_brs = function
      | [] -> acc
      | br::aside_brs as all_aside ->
        let ddepth = incr debug_dep; !debug_dep in
        Format.printf
          "abd-aside: [%d] #discard=%d, #done_brs=%d, #aside_brs=%d@\n%a@\n%!"
          ddepth (List.length discard) (List.length done_brs)
          (List.length aside_brs) P.pr_branch br; (* *)
        match P.abd_simple args ~discard ~validate acc br with
        | Some acc ->
          check_aside best discard acc (br::done_brs) aside_brs
        | None ->
          if best then culprit := Some br;
          if P.is_taut (P.extract_ans acc)
          then (
            Format.printf
              "abd-check_aside: quit failed [%d] at@ ans=%a@\n%!" ddepth
              P.pr_ans (P.extract_ans acc); (* *)
            let concl = P.concl_of_br (unsome !culprit) in
            let lc = List.fold_left loc_union dummy_loc
                (List.map atom_loc concl) in
            raise (Suspect (concl, lc)))
          else
            loop (P.discard_ans acc::discard) init_acc [] []
              (all_aside @ List.rev done_brs) in

    if brs = [] then init_acc
    else loop discard init_acc [] [] brs    

end
