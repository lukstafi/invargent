(** Order sort operations tests for InvarGenT.

    Released under the GNU General Public Licence (version 2 or
    higher), NO WARRANTY of correctness etc. (C) Lukasz Stafiniak 2013
    @author Lukasz Stafiniak lukstafi (AT) gmail.com
    @since Mar 2013
*)
open OUnit

let debug = ref true(* false *)

open Aux
open Defs
open OrderDefs
(* open Terms *)
open OrderS

let cmp_v v1 v2 = Same_quant
let uni_v v = v=VNam (Order_sort, "tx")
              || v=VNam (Order_sort, "ty")
let q = {cmp_v; uni_v; same_as = fun _ _ -> ()}

let tests = "OrderS" >::: [ ]
