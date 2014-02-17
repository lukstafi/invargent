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

let test_case ?(test_annot=false) ?(richer_answers=false) file () =
  if !debug then Printexc.record_backtrace true;
  let ntime = Sys.time () in
  Terms.reset_state ();
  Infer.reset_state ();
  let file =
    let f = "./examples/"^file in
    if Sys.file_exists (f^".gadt") then f
    else 
      let f = "../examples/"^file in
      if Sys.file_exists (f^".gadt") then f
      else (
        (*[* Format.printf "not found f=%s@\n%!" (f^".gadt"); *]*)
        assert false) in
  let old_richer_answers = !Abduction.richer_answers in
  Abduction.richer_answers := richer_answers;
  (try
     let verif_res =
       InvarGenT.process_file ~do_sig:true ~do_ml:true
         ~full_annot:test_annot (file^".gadt") in
     assert_equal ~printer:(fun x->x)
       (input_file (file^".gadti.target"))
       (input_file (file^".gadti"));
     assert_bool "Failed verification of .ml/.mli code"
       (verif_res = None || verif_res = Some 0);
     if test_annot
     then assert_equal ~printer:(fun x->x)
         (input_file (file^".ml.target"))
         (input_file (file^".ml"))
   with (Defs.Report_toplevel _ | Terms.Contradiction _
        | Terms.NoAnswer _) as exn ->
     ignore (Format.flush_str_formatter ());
     Terms.pr_exception Format.str_formatter exn;
     let msg = Format.flush_str_formatter () in
     Format.printf "@\n%s@\n%!"  msg;
     Printexc.print_backtrace stdout;
     assert_failure msg);
  Abduction.richer_answers := old_richer_answers;
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
      "simple when" >::
        (fun () ->
           skip_if !debug "debug";
           test_case "simple_when" ());
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
      "simple eval-annot" >::
        (fun () ->
           skip_if !debug "debug";
           test_case ~test_annot:true "simple_eval" ());
      "eval-annot" >::
        (fun () ->
           skip_if !debug "debug";
           test_case ~test_annot:true "eval" ());
      "equational_reas-annot" >::
        (fun () ->
           skip_if !debug "debug";
           test_case ~test_annot:true "equational_reas" ());
      "mutual_recursion_eval-annot" >::
        (fun () ->
           skip_if !debug "debug";
           test_case ~test_annot:true "mutual_recursion_eval_docs" ());
      "concat_strings-export" >::
        (fun () ->
           skip_if !debug "debug";
           test_case ~test_annot:true "concat_strings" ());
      "non_pointwise_split" >::
        (fun () ->
           skip_if !debug "debug";
           test_case ~richer_answers:true "non_pointwise_split" ());
      "non_pointwise_avl_small_rec" >::
        (fun () ->
           skip_if !debug "debug";
           test_case "non_pointwise_avl_small_rec" ());
      "non_pointwise_avl_small" >::
        (fun () ->
           skip_if !debug "debug";
           test_case "non_pointwise_avl_small" ());
      "non_pointwise_avl" >::
        (fun () ->
           skip_if !debug "debug";
           test_case "non_pointwise_avl" ());
      "non_pointwise_vary" >::
        (fun () ->
           todo "should not pass, turn into a test for error reporting";
           test_case "non_pointwise_vary" ());
      "avl_tree" >::
        (fun () ->
           (* skip_if !debug "debug"; *)
           test_case "avl_tree" ());
    ]

let () =
  let executable = Filename.basename Sys.executable_name in
  let chop f =
    try Filename.chop_extension f with Invalid_argument _ -> f in
  let executable = chop (chop executable) in
  if executable = "InvarGenTTest"
  then ignore (OUnit.run_test_tt ~verbose:true tests)
