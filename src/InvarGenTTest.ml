(** Main executable tests for InvarGenT.

    Released under the GNU General Public Licence (version 2 or
    higher), NO WARRANTY of correctness etc. (C) Lukasz Stafiniak 2013
    @author Lukasz Stafiniak lukstafi (AT) gmail.com
    @since Mar 2013
*)
open OUnit

let input_file file =
  let f = open_in file in
  let buf = Buffer.create 256 in
  (try
     while true do Buffer.add_channel buf f 1 done
   with End_of_file -> ());
  Buffer.contents buf

let test_case file () =
  let ntime = Sys.time () in
  Terms.reset_state ();
  Infer.reset_state ();
  let file = "./examples/"^file^".gadt" in
  (try
     InvarGenT.process_file file;
     assert_equal ~printer:(fun x->x)
       (input_file (file^"i.target"))
       (input_file (file^"i"))
   with (Terms.Report_toplevel _ | Terms.Contradiction _) as exn ->
     ignore (Format.flush_str_formatter ());
     Terms.pr_exception Format.str_formatter exn;
     assert_failure (Format.flush_str_formatter ()));
  Format.printf " t=%.3fs " (Sys.time () -. ntime)

let tests = "InvarGenT" >::: [
      "simple eval" >:: test_case "simple_eval";
      "eval" >:: test_case "eval";
      "equal1_wrong" >:: test_case "equal1_wrong";
      "equal_test" >:: test_case "equal_test";
      "equal_assert" >:: test_case "equal_assert";
      "binary_plus" >:: test_case "binary_plus";
      "flatten_pairs" >:: test_case "flatten_pairs";
      "equational_reas" >:: test_case "equational_reas";
      "filter" >:: test_case "filter";
      "filter_map" >:: test_case "filter_map";
      "binary_upper_bound" >:: test_case "binary_upper_bound";
      "mutual_recursion_eval" >:: test_case "mutual_recursion_eval";
      "binomial_heap_nonrec" >:: test_case "binomial_heap_nonrec";
      "binomial_heap" >::
        (fun () -> todo "requires `min` and `max`";
          test_case "binomial_heap" ())
    ]
