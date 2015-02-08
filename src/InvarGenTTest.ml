(** Main executable tests for InvarGenT.

    Released under the GNU General Public Licence (version 2 or
    higher), NO WARRANTY of correctness etc. (C) Lukasz Stafiniak 2013
    @author Lukasz Stafiniak lukstafi (AT) gmail.com
    @since Mar 2013
*)
open OUnit

let debug = ref (*[* true *]*)false

let input_file file =
  let f = open_in file in
  let buf = Buffer.create 256 in
  (try
     while true do Buffer.add_channel buf f 1 done
   with End_of_file -> ());
  Buffer.contents buf

let test_case ?(test_annot=false) ?richer_answers ?more_general_num
    ?prefer_guess ?abd_rotations ?num_abd_timeout
    ?num_abd_fail_timeout ?nodeadcode file () =
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
  (match richer_answers with
   | None -> ()
   | Some richer_answers -> Abduction.richer_answers := richer_answers);
  let old_more_general_num = !NumS.more_general in
  (match more_general_num with
   | None -> ()
   | Some more_general_num -> NumS.more_general := more_general_num);
  let old_prefer_guess = !Abduction.prefer_guess in
  (match prefer_guess with
   | None -> ()
   | Some prefer_guess -> Abduction.prefer_guess := prefer_guess);
  let old_abd_rotations = !NumS.abd_rotations in
  (match abd_rotations with
   | None -> ()
   | Some abd_rotations -> NumS.abd_rotations := abd_rotations);  
  let old_num_abd_timeout = !NumS.abd_timeout_count in
  (match num_abd_timeout with
   | None -> ()
   | Some num_abd_timeout -> NumS.abd_timeout_count := num_abd_timeout);  
  let old_num_abd_fail_timeout = !NumS.abd_fail_timeout_count in
  (match num_abd_fail_timeout with
   | None -> ()
   | Some num_abd_fail_timeout ->
     NumS.abd_fail_timeout_count := num_abd_fail_timeout);
  let old_nodeadcode = !Defs.nodeadcode in
  (match nodeadcode with
   | None -> ()
   | Some nodeadcode -> Defs.nodeadcode := nodeadcode);
  (try
     let verif_res =
       (*[* Format.printf "test_case: file=%s@\n%!" file; *]*)
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
   with
   | (Defs.Report_toplevel _ | Terms.Contradiction _
     | Terms.NoAnswer _) as exn ->
     ignore (Format.flush_str_formatter ());
     Terms.pr_exception Format.str_formatter exn;
     let msg = Format.flush_str_formatter () in
     Format.printf "@\n%s@\n%!"  msg;
     Printexc.print_backtrace stdout;
     Abduction.richer_answers := old_richer_answers;
     NumS.more_general := old_more_general_num;
     Abduction.prefer_guess := old_prefer_guess;
     NumS.abd_rotations := old_abd_rotations;
     NumS.abd_timeout_count := old_num_abd_timeout;
     NumS.abd_fail_timeout_count := old_num_abd_fail_timeout;
     Defs.nodeadcode := old_nodeadcode;
     assert_failure msg
   | exn ->
     Abduction.richer_answers := old_richer_answers;
     NumS.more_general := old_more_general_num;
     Abduction.prefer_guess := old_prefer_guess;
     NumS.abd_rotations := old_abd_rotations;
     NumS.abd_timeout_count := old_num_abd_timeout;
     NumS.abd_fail_timeout_count := old_num_abd_fail_timeout;
     Defs.nodeadcode := old_nodeadcode;
     raise exn);
  Abduction.richer_answers := old_richer_answers;
  NumS.more_general := old_more_general_num;
  Abduction.prefer_guess := old_prefer_guess;
  NumS.abd_rotations := old_abd_rotations;
  NumS.abd_timeout_count := old_num_abd_timeout;
  NumS.abd_fail_timeout_count := old_num_abd_fail_timeout;
  Defs.nodeadcode := old_nodeadcode;
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
      "binary_plus-harder" >::
        (fun () ->
           todo "currently requiring expanded arguments";
           skip_if !debug "debug";
           test_case "binary_plus-harder" ());
      "flatten_pairs" >::
        (fun () ->
           skip_if !debug "debug";
           test_case "flatten_pairs" ());
      "flatten_quadrs" >::
        (fun () ->
           skip_if !debug "debug";
           test_case ~abd_rotations:4 "flatten_quadrs" ());
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
      "ex_config_pc" >::
        (fun () ->
           skip_if !debug "debug";
           test_case "ex_config_pc" ());
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
      "list-head" >::
        (fun () ->
           skip_if !debug "debug";
           test_case "list_head" ());
      "pointwise-head" >::
        (fun () ->
           todo "beyond current negation handling for term constraints";
           skip_if !debug "debug";
           test_case "pointwise_head" ());
      "pointwise-refine" >::
        (fun () ->
           skip_if !debug "debug";
           test_case "pointwise_refine" ());
      "pointwise-rbtree_rotate" >::
        (fun () ->
           skip_if !debug "debug";
           test_case "pointwise_rbtree_rotate" ());
      "pointwise-zip2-simpler1" >::
        (fun () ->
           skip_if !debug "debug";
           test_case "pointwise_zip2-simpler1" ());
      "pointwise-zip2-simpler2" >::
        (fun () ->
           skip_if !debug "debug";
           test_case "pointwise_zip2-simpler2" ());
      "pointwise-zip2-simpler3" >::
        (fun () ->
           skip_if !debug "debug";
           test_case "pointwise_zip2-simpler3" ());
      "pointwise-zip2-simpler4" >::
        (fun () ->
           skip_if !debug "debug";
           test_case "pointwise_zip2-simpler4" ());
      "pointwise-zip2" >::
        (fun () ->
           (* This test is close enough. *)
           skip_if !debug "debug";
           test_case "pointwise_zip2" ());
      "pointwise-zip2-harder" >::
        (fun () ->
           todo "too hard but not call-by-value";
           skip_if !debug "debug";
           test_case "pointwise_zip2-harder" ());
      "pointwise-avl_rotl" >::
        (fun () ->
           skip_if !debug "debug";
           test_case "pointwise_avl_rotl" ());
      "pointwise-avl_ins" >::
        (fun () ->
           skip_if !debug "debug";
           test_case "pointwise_avl_ins" ());
      "pointwise-extract0" >::
        (fun () ->
           skip_if !debug "debug";
           test_case "pointwise_extract0" ());
      "pointwise-extract1" >::
        (fun () ->
           skip_if !debug "debug";
           test_case "pointwise_extract1" ());
      "pointwise-extract2" >::
        (fun () ->
           skip_if !debug "debug";
           test_case "pointwise_extract2" ());
      "pointwise-extract" >::
        (fun () ->
           skip_if !debug "debug";
           test_case "pointwise_extract" ());
      "pointwise-run_state" >::
        (fun () ->
           skip_if !debug "debug";
           test_case "pointwise_run_state" ());
      "non_outsidein-rx" >::
        (fun () ->
           skip_if !debug "debug";
           test_case "non_outsidein-rx" ());
      "non_pointwise-split" >::
        (fun () ->
           skip_if !debug "debug";
           test_case "non_pointwise_split" ());
      "non_pointwise-avl_small_rec" >::
        (fun () ->
           skip_if !debug "debug";
           test_case "non_pointwise_avl_small_rec" ());
      "non_pointwise-avl_small" >::
        (fun () ->
           skip_if !debug "debug";
           test_case "non_pointwise_avl_small" ());
      (* "non_pointwise-vary" >::
        (fun () ->
           (* TODO: should not pass unless in a non-default setting *)
           test_case_fail "non_pointwise_vary" ()); *)
      "non_pointwise-avl_rotr" >::
        (fun () ->
           skip_if !debug "debug";
           test_case "non_pointwise_avl" ());
      "avl_delmin-simpler" >::
        (fun () ->
           skip_if !debug "debug";
           test_case "avl_delmin-simpler" ());
      "non_pointwise-avl_delmin-modified" >::
        (fun () ->
           skip_if !debug "debug";
           test_case "non_pointwise_avl_delmin-modified" ());
      "non_pointwise-avl_delmin" >::
        (fun () ->
           skip_if !debug "debug";
           test_case "non_pointwise_avl_delmin" ());
      "non_pointwise-avl_delmin2" >::
        (fun () ->
           skip_if !debug "debug";
           test_case "non_pointwise_avl_delmin2" ());
      "non_pointwise-fd_comp" >::
        (fun () ->
           skip_if !debug "debug";
           test_case "non_pointwise_fd_comp" ());
      "non_pointwise-fd_comp2" >::
        (fun () ->
           skip_if !debug "debug";
           test_case "non_pointwise_fd_comp2" ());
      "non_pointwise-fd_comp-harder" >::
        (fun () ->
           todo "currently requiring expanded arguments";
           skip_if !debug "debug";
           test_case "non_pointwise_fd_comp-harder" ());
      "non_pointwise-zip1-simpler" >::
        (fun () ->
           skip_if !debug "debug";
           test_case ~prefer_guess:true "non_pointwise_zip1-simpler" ());
      "non_pointwise-zip1-simpler2" >::
        (fun () ->
           skip_if !debug "debug";
           test_case ~prefer_guess:true "non_pointwise_zip1-simpler2" ());
      "non_pointwise-zip1-modified" >::
        (fun () ->
           skip_if !debug "debug";
           test_case ~prefer_guess:true "non_pointwise_zip1-modified" ());
      "non_pointwise-zip1" >::
        (fun () ->
           skip_if !debug "debug";
           test_case "non_pointwise_zip1" ());
      "non_pointwise-leq" >::
        (fun () ->
           skip_if !debug "debug";
           test_case ~prefer_guess:true "non_pointwise_leq" ());
      "non_pointwise-run_state" >::
        (fun () ->
           skip_if !debug "debug";
           test_case "non_pointwise_run_state" ());
      "non_pointwise-run_state2" >::
        (fun () ->
           skip_if !debug "debug";
           test_case "non_pointwise_run_state2" ());
      "avl_tree" >::
        (fun () ->
           skip_if !debug "debug";
           test_case "avl_tree" ());
      "binomial_heap-ins_tree" >::
        (fun () ->
           todo "TODO";
           skip_if !debug "debug";
           test_case "binomial_heap-ins_tree" ());
      "binomial_heap-merge" >::
        (fun () ->
           todo "TODO";
           skip_if !debug "debug";
           test_case "binomial_heap-merge" ());
      "binomial_heap" >::
        (fun () ->
           todo "TODO";
           skip_if !debug "debug";
           test_case "binomial_heap" ());
      "liquid_dotprod-simpler" >::
        (fun () ->
           skip_if !debug "debug";
           test_case "liquid_dotprod_simpler" ());
      "liquid_dotprod" >::
        (fun () ->
           skip_if !debug "debug";
           test_case "liquid_dotprod" ());
      "liquid_bcopy-simpler" >::
        (fun () ->
           skip_if !debug "debug";
           test_case "liquid_bcopy_simpler" ());
      "liquid_bcopy" >::
        (fun () ->
           skip_if !debug "debug";
           test_case "liquid_bcopy" ());
      "liquid_bsearch-simpler" >::
        (fun () ->
           skip_if !debug "debug";
           test_case "liquid_bsearch_simpler" ());
      "liquid_bsearch" >::
        (fun () ->
           skip_if !debug "debug";
           test_case "liquid_bsearch" ());
      "liquid_bsearch-harder" >::
        (fun () ->
           skip_if !debug "debug";
           test_case "liquid_bsearch_harder" ());
      "liquid_bsearch2-simpler" >::
        (fun () ->
           skip_if !debug "debug";
           test_case "liquid_bsearch2_simpler" ());
      "liquid_bsearch2-simpler2" >::
        (fun () ->
           skip_if !debug "debug";
           test_case "liquid_bsearch2_simpler2" ());
      "liquid_bsearch2" >::
        (fun () ->
           skip_if !debug "debug";
           test_case "liquid_bsearch2" ());
      "liquid_bsearch2-harder1" >::
        (fun () ->
           skip_if !debug "debug";
           test_case "liquid_bsearch2_harder1" ());
      "liquid_bsearch2-harder2" >::
        (fun () ->
           skip_if !debug "debug";
           test_case "liquid_bsearch2_harder2" ());
      "liquid_bsearch2-harder3" >::
        (fun () ->
           skip_if !debug "debug";
           test_case ~test_annot:true "liquid_bsearch2_harder3" ());
      "liquid_bsearch2-harder4" >::
        (fun () ->
           todo "too hard to guess the existential type";
           skip_if !debug "debug";
           test_case "liquid_bsearch2_harder4" ());
      "liquid_queen-simpler" >::
        (fun () ->
           skip_if !debug "debug";
           test_case "liquid_queen_simpler" ());
      "liquid_queen" >::
        (fun () ->
           skip_if !debug "debug";
           test_case "liquid_queen" ());
      "liquid_isort-simpler1" >::
        (fun () ->
           skip_if !debug "debug";
           test_case "liquid_isort_simpler1" ());
      "liquid_isort-simpler2" >::
        (fun () ->
           skip_if !debug "debug";
           test_case "liquid_isort_simpler2" ());
      "liquid_isort-simpler3" >::
        (fun () ->
           skip_if !debug "debug";
           test_case ~more_general_num:true "liquid_isort_simpler3" ());
      "liquid_isort-simpler" >::
        (fun () ->
           skip_if !debug "debug";
           test_case "liquid_isort_simpler" ());
      "liquid_isort" >::
        (fun () ->
           skip_if !debug "debug";
           test_case "liquid_isort" ());
      "liquid_isort-harder" >::
        (fun () ->
           skip_if !debug "debug";
           test_case "liquid_isort_harder" ());
      "liquid_vecswap_simpler" >::
        (fun () ->
           skip_if !debug "debug";
           test_case "liquid_vecswap_simpler" ());
      "liquid_vecswap" >::
        (fun () ->
           skip_if !debug "debug";
           test_case "liquid_vecswap" ());
      "liquid_isort-full" >::
        (fun () ->
           skip_if !debug "debug";
           test_case "liquid_isort_full" ());
      "liquid_tower_showposts" >::
        (fun () ->
           skip_if !debug "debug";
           test_case "liquid_tower_showposts" ());
      "liquid_tower_simpler" >::
        (fun () ->
           skip_if !debug "debug";
           test_case "liquid_tower_simpler" ());
      "liquid_tower" >::
        (fun () ->
           skip_if !debug "debug";
           test_case "liquid_tower" ());
      "liquid_tower_harder" >::
        (fun () ->
           todo "too hard for current numerical abduction";
           skip_if !debug "debug";
           test_case "liquid_tower_harder" ());
      "liquid_matmult" >::
        (fun () ->
           skip_if !debug "debug";
           test_case "liquid_matmult" ());
      "liquid_heapsort-heapify-simpler" >::
        (fun () ->
           skip_if !debug "debug";
           test_case "liquid_heapsort_heapify_simpler" ());
      "liquid_heapsort-heapify-simpler2" >::
        (fun () ->
           (* TODO: improve time *)
           skip_if !debug "debug";
           test_case "liquid_heapsort_heapify_simpler2" ());
      "liquid_heapsort-heapify-simpler3" >::
        (fun () ->
           skip_if !debug "debug";
           test_case "liquid_heapsort_heapify_simpler3" ());
      "liquid_heapsort-heapify" >::
        (fun () ->
           skip_if !debug "debug";
           test_case "liquid_heapsort_heapify" ());
      "liquid_heapsort-heapsort-simpler" >::
        (fun () ->
           skip_if !debug "debug";
           test_case "liquid_heapsort_heapsort_simpler" ());
      "liquid_heapsort-heapsort" >::
        (fun () ->
           skip_if !debug "debug";
           test_case "liquid_heapsort_heapsort" ());
      "liquid_heapsort" >::
        (fun () ->
           skip_if !debug "debug";
           test_case "liquid_heapsort" ());
      "liquid_fft_simpler" >::
        (fun () ->
           todo "FIXME";
           skip_if !debug "debug";
           test_case "liquid_fft_simpler" ());
      "liquid_fft" >::
        (fun () ->
           todo "FIXME";
           skip_if !debug "debug";
           test_case "liquid_fft" ());
      "liquid_simplex_step_2" >::
        (fun () ->
           (* TODO: add invariant cleanup for top-level pattern-match let *)
           skip_if !debug "debug";
           test_case "liquid_simplex_step_2" ());
      "liquid_simplex_step_3" >::
        (fun () ->
           (* Ideally, we would like to introduce a precondition that
              j <= j' + 1, but InvarGenT only guesses required invariants. *)
           todo "too hard for InvarGenT 2.0";
           skip_if !debug "debug";
           test_case "liquid_simplex_step_3" ());
      "liquid_simplex_step_3a" >::
        (fun () ->
           skip_if !debug "debug";
           test_case "liquid_simplex_step_3a" ());
      "liquid_simplex" >::
        (fun () ->
           todo "FIXME";
           skip_if !debug "debug";
           test_case "liquid_simplex" ());
      "liquid_simplex-harder" >::
        (fun () ->
           todo "too hard for InvarGenT 2.0";
           skip_if !debug "debug";
           test_case "liquid_simplex_harder" ());
      "liquid_gauss" >::
        (fun () ->
           todo "TODO";
           skip_if !debug "debug";
           test_case "liquid_gauss" ());
      "liquid_qsort" >::
        (fun () ->
           todo "TODO";
           skip_if !debug "debug";
           test_case "liquid_qsort" ());
    ]

let () =
  let executable = Filename.basename Sys.executable_name in
  let chop f =
    try Filename.chop_extension f with Invalid_argument _ -> f in
  let executable = chop (chop executable) in
  if executable = "InvarGenTTest"
  then ignore (OUnit.run_test_tt ~verbose:true tests)
