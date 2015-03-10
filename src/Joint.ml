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
  val abd_simple :
    args -> discard:discarded list ->
    validation:validation ->
    neg_validate:(answer -> int) ->
    accu -> branch -> (accu * validation) option
  val extract_ans : accu -> answer
  val discard_ans : accu -> discarded
  val concl_of_br : branch -> formula
  val is_taut : answer -> bool
  val pr_branch : Format.formatter -> branch -> unit
  val pr_ans : Format.formatter -> answer -> unit
end

let debug_dep = ref 0

module JointAbduction (P : ABD_PARAMS) = struct

  let abd args ~discard (init_validation : P.validation) ~neg_validate
      init_acc brs =
    P.abd_fail_flag := false;
    let culprit = ref None
    and best_done = ref (-1) in
    let rec loop fails discard acc (validation : P.validation)
        done_brs aside_brs = function
      | [] ->
        let best =
          List.length done_brs > !best_done &&
          (best_done := List.length done_brs; true) in
        check_aside fails best discard acc validation done_brs aside_brs
      | br::more_brs ->
        (*[* let ddepth = incr debug_dep; !debug_dep in *]*)
        (*[* Format.printf
          "abd-loop: [%d] #discard=%d, #done_brs=%d, #aside_brs=%d, \
          #more_brs=%d@\n%a@\n%!"
          ddepth (List.length discard) (List.length done_brs)
          (List.length aside_brs)
          (List.length more_brs) P.pr_branch br; *]*)
        match P.abd_simple args ~discard ~validation
                ~neg_validate acc br with
        | Some (acc, validation) ->
          loop fails discard acc validation (br::done_brs)
            aside_brs more_brs
        | None ->
          if fails > !P.abd_fail_timeout
          then (
            (*[* Format.printf
              "Joint.abd-loop: TIMEOUT %d failed [%d] at@ ans=%a@\n%!"
              fails ddepth
              P.pr_ans (P.extract_ans acc); *]*)
            let concl =
              match !culprit with
              | None -> []
              | Some br -> P.concl_of_br br in
            let lc = List.fold_left loc_union dummy_loc
                (List.map atom_loc concl) in
            P.abd_fail_flag := true;
            raise (Suspect (concl, lc)));
          loop (fails+1) discard acc validation done_brs
            (br::aside_brs) more_brs

    and check_aside fails best discard acc (validation : P.validation)
        done_brs = function
      | [] -> acc
      | br::aside_brs as all_aside ->
        (*[* let ddepth = incr debug_dep; !debug_dep in *]*)
        (*[* Format.printf
          "abd-aside: [%d] #discard=%d, #done_brs=%d, #aside_brs=%d@\n%a@\n%!"
          ddepth (List.length discard) (List.length done_brs)
          (List.length aside_brs) P.pr_branch br; *]*)
        match P.abd_simple args ~discard ~validation
                ~neg_validate acc br with
        | Some (acc, validation) ->
          check_aside fails best discard acc validation (br::done_brs)
            aside_brs
        | None ->
          if best then culprit := Some br;
          if P.is_taut (P.extract_ans acc) || fails > !P.abd_fail_timeout
          then (
            (*[* Format.printf
              "abd-check_aside: quit failed [%d] at fails=%d@ \
               fail_timeout=%d@ ans=%a@\n%!" ddepth fails !P.abd_fail_timeout
              P.pr_ans (P.extract_ans acc); *]*)
            let concl =
              match !culprit with
              | None -> []
              | Some br -> P.concl_of_br br in
            let lc = List.fold_left loc_union dummy_loc
                (List.map atom_loc concl) in
            if fails > !P.abd_fail_timeout then P.abd_fail_flag := true;
            raise (Suspect (concl, lc)))
          else
            loop (fails+1) (P.discard_ans acc::discard)
              init_acc init_validation [] []
              (all_aside @ List.rev done_brs) in

    if brs = [] then init_acc
    else loop 0 discard init_acc init_validation [] [] brs    

end


let transitive_cl edge_l =
  let edges = Hashtbl.create 8 in
  let nodes = Hashtbl.create 8 in
  List.iter
    (fun (t1, t2, loc) ->
        Hashtbl.replace nodes t1 (); Hashtbl.replace nodes t2 ();
        Hashtbl.replace edges (t1, t2) loc)
    edge_l;
  (* Floyd-Warshall algo *)
  let add i j k =
    if not (Hashtbl.mem edges (i, j)) then
      let lc1 = Hashtbl.find edges (i, k)
      and lc2 = Hashtbl.find edges (k, j) in
      let lc = loc_union lc1 lc2 in
      Hashtbl.add edges (i, j) lc in
  Hashtbl.iter
    (fun k _ ->
    Hashtbl.iter
      (fun i _ ->
      Hashtbl.iter
        (fun j _ -> try add i j k with Not_found -> ())
        nodes) nodes) nodes;
  edges
