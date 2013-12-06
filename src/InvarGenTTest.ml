(** Main executable tests for InvarGenT.

    Released under the GNU General Public Licence (version 2 or
    higher), NO WARRANTY of correctness etc. (C) Lukasz Stafiniak 2013
    @author Lukasz Stafiniak lukstafi (AT) gmail.com
    @since Mar 2013
*)
open OUnit

let debug = ref (* true *)false

let input_file file =
  let f = open_in file in
  let buf = Buffer.create 256 in
  (try
     while true do Buffer.add_channel buf f 1 done
   with End_of_file -> ());
  Buffer.contents buf

let test_case file () =
  if !debug then Printexc.record_backtrace true;
  let ntime = Sys.time () in
  Terms.reset_state ();
  Infer.reset_state ();
  let file =
    let f = "./examples/"^file^".gadt" in
    if Sys.file_exists f then f
    else 
      let f = "../examples/"^file^".gadt" in
      if Sys.file_exists f then f
      else assert false in
  (try
     InvarGenT.process_file ~do_sig:true file;
     assert_equal ~printer:(fun x->x)
       (input_file (file^"i.target"))
       (input_file (file^"i"))
   with (Terms.Report_toplevel _ | Terms.Contradiction _) as exn ->
     ignore (Format.flush_str_formatter ());
     Terms.pr_exception Format.str_formatter exn;
     let msg = Format.flush_str_formatter () in
     Format.printf "@\n%s@\n%!"  msg;
     Printexc.print_backtrace stdout;
     assert_failure msg);
  Format.printf " t=%.3fs " (Sys.time () -. ntime)

let tests = "InvarGenT" >::: [
      "simple eval" >::
        (fun () ->
           skip_if !debug "debug";
           test_case "simple_eval" ());
      "eval" >::
        (fun () ->
           skip_if !debug "debug";
           test_case "eval" ());
      "equal1_wrong" >::
        (fun () ->
           skip_if !debug "debug";
           test_case "equal1_wrong" ());
      "equal_test" >::
        (fun () ->
           skip_if !debug "debug";
           test_case "equal_test" ());
      "equal_assert" >::
        (fun () ->
           skip_if !debug "debug";
           test_case "equal_assert" ());
      "binary_plus" >::
        (fun () ->
           skip_if !debug "debug";
           test_case "binary_plus" ());
      "flatten_pairs" >::
        (fun () ->
           skip_if !debug "debug";
           test_case "flatten_pairs" ());
      "equational_reas" >::
        (fun () ->
           skip_if !debug "debug";
           test_case "equational_reas" ());
      "filter" >::
        (fun () ->
           skip_if !debug "debug";
           test_case "filter" ());
      "filter_map" >::
        (fun () ->
           skip_if !debug "debug";
           test_case "filter_map" ());
      "binary_upper_bound" >::
        (fun () ->
           skip_if !debug "debug";
           test_case "binary_upper_bound" ());
      "mutual_simple_recursion_eval" >::
        (fun () ->
           skip_if !debug "debug";
           test_case "mutual_simple_recursion_eval" ());
      "binomial_heap_nonrec" >::
        (fun () ->
           skip_if !debug "debug";
           test_case "binomial_heap_nonrec" ());
      "mutual_recursion_eval" >::
        (fun () ->
           skip_if !debug "debug";
           test_case "mutual_recursion_eval" ());
      "binomial_heap" >::
        (fun () ->
           todo "requires `min` and `max`";
           test_case "binomial_heap" ())
    ]


let () =
  let executable = Filename.basename Sys.executable_name in
  let chop f =
    try Filename.chop_extension f with Invalid_argument _ -> f in
  let executable = chop (chop executable) in
  if executable = "InvarGenTTest"
  then ignore (OUnit.run_test_tt ~verbose:true tests)
