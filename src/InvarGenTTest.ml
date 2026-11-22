(** Main executable tests for InvarGenT.

    Released under the GNU General Public Licence (version 2 or
    higher), NO WARRANTY of correctness etc. (C) Lukasz Stafiniak 2013
    @author Lukasz Stafiniak lukstafi (AT) gmail.com
    @since Mar 2013
*)
open OUnit

let debug = ref (*[* true *]*)false
let short_tests_only = ref false

let input_file file =
  let f = open_in file in
  let buf = Buffer.create 256 in
  (try
     while true do Buffer.add_channel buf f 1 done
   with End_of_file -> ());
  Buffer.contents buf

let signature_tokens text =
  let buf = Lexing.from_string text in
  let rec read acc = match Lexer.token buf with
    | Parser.EOF -> List.rev acc
    | token -> read (token :: acc) in
  read []

let example_path name =
  let path = "./examples/" ^ name in
  if Sys.file_exists (path ^ ".gadt") then path else "../examples/" ^ name

let test_case ?(test_annot=false) ?(do_ml=true) ?(cmp_sig=(=))
    ?drop_assert_false
    ?richer_answers ?more_general_num
    ?prefer_guess ?ty_abd_timeout
    ?prefer_bound_to_local ?prefer_bound_to_outer
    ?only_off_by_1 ?same_with_assertions ?reward_constrn
    ?abd_rotations ?num_abd_timeout
    ?num_abd_fail_timeout ?nodeadcode file () =
  if !debug then Printexc.record_backtrace true;
  let ntime = Sys.time () in
  Terms.reset_state ();
  Infer.reset_state ();
  let file = example_path file in
  let old_drop_assert_false = !OCaml.drop_assert_false in
  (match drop_assert_false with
   | None -> ()
   | Some drop_assert_false -> OCaml.drop_assert_false := drop_assert_false);
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
  let old_timeout_count = !Abduction.timeout_count in
  (match ty_abd_timeout with
   | None -> ()
   | Some timeout_count -> Abduction.timeout_count := timeout_count);
  let old_prefer_bound_to_local = !NumS.prefer_bound_to_local in
  (match prefer_bound_to_local with
   | None -> ()
   | Some prefer_bound_to_local ->
     NumS.prefer_bound_to_local := prefer_bound_to_local);
  let old_prefer_bound_to_outer = !NumS.prefer_bound_to_outer in
  (match prefer_bound_to_outer with
   | None -> ()
   | Some prefer_bound_to_outer ->
     NumS.prefer_bound_to_outer := prefer_bound_to_outer);
  let old_only_off_by_1 = !NumS.only_off_by_1 in
  (match only_off_by_1 with
   | None -> ()
   | Some only_off_by_1 ->
     NumS.only_off_by_1 := only_off_by_1);
  let old_same_with_assertions = !Invariants.same_with_assertions in
  (match same_with_assertions with
   | None -> ()
   | Some same_with_assertions ->
     Invariants.same_with_assertions := same_with_assertions);
  let old_reward_constrn = !NumS.reward_constrn in
  (match reward_constrn with
   | None -> ()
   | Some reward_constrn ->
     NumS.reward_constrn := reward_constrn);
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
       InvarGenT.process_file ~do_sig:true ~do_ml
         ~full_annot:test_annot (file^".gadt") in
     assert_equal ~cmp:cmp_sig ~printer:(fun x->x)
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
     OCaml.drop_assert_false := old_drop_assert_false;
     Abduction.richer_answers := old_richer_answers;
     NumS.more_general := old_more_general_num;
     Abduction.prefer_guess := old_prefer_guess;
     Abduction.timeout_count := old_timeout_count;
     NumS.prefer_bound_to_local := old_prefer_bound_to_local;
     NumS.prefer_bound_to_outer := old_prefer_bound_to_outer;
     NumS.only_off_by_1 := old_only_off_by_1;
     Invariants.same_with_assertions := old_same_with_assertions;
     NumS.reward_constrn := old_reward_constrn;
     NumS.abd_rotations := old_abd_rotations;
     NumS.abd_timeout_count := old_num_abd_timeout;
     NumS.abd_fail_timeout_count := old_num_abd_fail_timeout;
     Defs.nodeadcode := old_nodeadcode;
     assert_failure msg
   | exn ->
     OCaml.drop_assert_false := old_drop_assert_false;
     Abduction.richer_answers := old_richer_answers;
     NumS.more_general := old_more_general_num;
     Abduction.prefer_guess := old_prefer_guess;
     Abduction.timeout_count := old_timeout_count;
     NumS.prefer_bound_to_local := old_prefer_bound_to_local;
     NumS.prefer_bound_to_outer := old_prefer_bound_to_outer;
     NumS.only_off_by_1 := old_only_off_by_1;
     Invariants.same_with_assertions := old_same_with_assertions;
     NumS.reward_constrn := old_reward_constrn;
     NumS.abd_rotations := old_abd_rotations;
     NumS.abd_timeout_count := old_num_abd_timeout;
     NumS.abd_fail_timeout_count := old_num_abd_fail_timeout;
     Defs.nodeadcode := old_nodeadcode;
     raise exn);
  OCaml.drop_assert_false := old_drop_assert_false;
  Abduction.richer_answers := old_richer_answers;
  NumS.more_general := old_more_general_num;
  Abduction.prefer_guess := old_prefer_guess;
  Abduction.timeout_count := old_timeout_count;
  NumS.prefer_bound_to_local := old_prefer_bound_to_local;
  NumS.prefer_bound_to_outer := old_prefer_bound_to_outer;
  NumS.only_off_by_1 := old_only_off_by_1;
  Invariants.same_with_assertions := old_same_with_assertions;
  NumS.reward_constrn := old_reward_constrn;
  NumS.abd_rotations := old_abd_rotations;
  NumS.abd_timeout_count := old_num_abd_timeout;
  NumS.abd_fail_timeout_count := old_num_abd_fail_timeout;
  Defs.nodeadcode := old_nodeadcode;
  Format.printf " t=%.3fs " (Sys.time () -. ntime)

let run_example ?cmp_sig name () =
  test_case ?cmp_sig name ();
  let file = example_path name ^ ".ml" in
  assert_equal ~printer:string_of_int 0 (Sys.command ("ocaml -noinit " ^ Filename.quote file))

let infer_source ?(integer_target=false) source =
  Terms.reset_state ();
  Infer.reset_state ();
  let program = Parser.program Lexer.token (Lexing.from_string source) in
  Infer.infer_prog ~integer_target ~check_excluded:InvarGenT.solve_checked
    InvarGenT.solver (Infer.normalize_program program)

let rejects_source ?integer_target source =
  try ignore (infer_source ?integer_target source); false
  with Defs.Report_toplevel _ | Terms.Contradiction _ | Terms.NoAnswer _ -> true

let tests = "InvarGenT" >::: [
      "repeating a supplier preserves the other upper bound" >::
        test_case "choice_arms"
          ~cmp_sig:(fun a b -> signature_tokens a = signature_tokens b);
      "one witness for three equal result indices" >:: test_case "equal_triple";
      "separate existential indices after the first unequal pair" >::
        test_case "separating_pair"
          ~cmp_sig:(fun a b -> signature_tokens a = signature_tokens b);
      "an equality client needs a shared result index" >:: (fun () ->
        let program step =
          "datatype Nat\ndatacons Z : Nat\ndatacons S : Nat ⟶ Nat\n" ^
          "external let equal : ∀i. (Num i, Num i) → Bool = \"fun (x,y) -> x=y\"\n" ^
          "let rec pair = efunction Z -> (0,0) | S t -> let (x,y) = pair t in " ^ step ^
          "\nlet seen = let xy = pair (S (S Z)) in equal xy" in
        ignore (infer_source (program "(y+1,x+1)"));
        assert_bool "the second successor returns (1,2)"
          (rejects_source (program "(1,x+1)")));
      "a scaled index can become an independent witness" >:: (fun () ->
        let code = "datatype Nat\ndatacons Z : Nat\ndatacons S : Nat ⟶ Nat\n" ^
          "datatype Seed\ndatacons V : ∀i. Num i ⟶ Seed\n" ^
          "external let seed : Seed = \"V 1\"\n" ^
          "external let band : ∀i,j[2 i≤j]. (Num i, Num j) → Bool = \"fun _ -> true\"\n" ^
          "let rec pair = efunction Z -> let V z = seed in (z,2*z) " ^
          "| S t -> let (x,y) = pair t in (x,y+1)\n" in
        ignore (infer_source (code ^ "let seen = let xy = pair (S Z) in band xy")));
      "partial annotations can infer stronger guards" >:: (fun () ->
        let code = "external let positive : ∀i[1≤i]. Num i → Num i = \"fun x -> x\"\n" ^
          "let f : ∀i. Num i → Num i = fun x -> positive x\n" in
        ignore (infer_source (code ^ "let ok = f 1"));
        assert_bool "the inferred guard must reach the caller"
          (rejects_source (code ^ "let bad = f 0")));
      "recursive uses satisfy the written guard" >:: (fun () ->
        let code = "let rec f : ∀i[1≤i]. Num i → Num 0 = fun x -> " in
        ignore (infer_source (code ^ "f (x+1)"));
        assert_bool "decrement eventually leaves the declared domain"
          (rejects_source (code ^ "f (x+ -1)")));
      "written existential checks each returning branch" >:: (fun () ->
        let code = "datatype Nat\ndatacons Z : Nat\ndatacons S : Nat ⟶ Nat\n" ^
          "let f : Nat → ∃n[1≤n]. Num n = efunction Z -> 1 | S _ -> " in
        ignore (infer_source (code ^ "2"));
        assert_bool "zero does not inhabit the annotated package"
          (rejects_source (code ^ "0")));
      "partial annotation for both symbolic floor shifts" >::
        test_case "symbolic_floor_hint"
          ~cmp_sig:(fun a b -> signature_tokens a = signature_tokens b);
      "the final answer independently rules out assert false" >:: (fun () ->
        let old_check = !Invariants.neg_constrns
        and old_since = !Abduction.num_neg_since in
        let restore () = Invariants.neg_constrns := old_check;
          Abduction.num_neg_since := old_since in
        Invariants.neg_constrns := false;
        Abduction.num_neg_since := max_int / 2;
        (try
           ignore (infer_source "let f = if 1 <= 0 then assert false else 1");
           assert_bool "the final guard admits zero"
             (rejects_source "let f = if 0 <= 0 then assert false else 1")
         with e -> restore (); raise e);
        restore ());
      "the restarted pair inference gets a fresh widening window" >:: (fun () ->
        let old = !Invariants.timeout_count in
        Invariants.timeout_count := 24;
        (try test_case "capped_pair"
             ~cmp_sig:(fun a b -> signature_tokens a = signature_tokens b) ()
         with e -> Invariants.timeout_count := old; raise e);
        Invariants.timeout_count := old);
      "a guarded assertion constrains the matched argument" >:: (fun () ->
        let guard = "let rec f = function x when x <= 0 -> assert false | x -> x\n" in
        ignore (infer_source (guard ^ "let safe = f 1"));
        assert_bool "reachable assertion at zero"
          (rejects_source (guard ^ "let unsafe = f 0")));
      "signed arguments and arithmetic grouping in exported OCaml" >:: (fun () ->
        Terms.reset_state (); Infer.reset_state ();
        let source = "let rec scale x = -2 * (x + -1)\nlet result = scale (-3)" in
        let program = Parser.program Lexer.token (Lexing.from_string source) in
        let _, annot = Infer.infer_prog InvarGenT.solver (Infer.normalize_program program) in
        let old_type = !OCaml.num_is and old_module = !OCaml.num_is_mod in
        let export (ty, as_module, preamble, expected) =
          OCaml.num_is := ty; OCaml.num_is_mod := as_module;
          Format.asprintf "module Test_%s = struct@\n%s@\n%a@\nlet () = assert (result = %s)@\nend@\n"
            ty preamble (OCaml.pr_ml ~funtys:false ~lettys:false) annot expected in
        let cases =
          ["int", false, "", "8"; "float", false, "", "8.";
           "int64", false, "let int64_of_int = Int64.of_int\nlet add_int64 = Int64.add\nlet mult_int64 = Int64.mul", "8L";
           "counter", true, "type counter = int64\nmodule Counter = struct let of_int = Int64.of_int let (+) = Int64.add let ( * ) = Int64.mul end", "8L"] in
        let restore () = OCaml.num_is := old_type; OCaml.num_is_mod := old_module in
        let scripts = try List.map export cases with exn -> restore (); raise exn in
        restore ();
        let file, output = Filename.open_temp_file "invargent_arithmetic" ".ml" in
        List.iter (output_string output) scripts;
        close_out output;
        let status = Sys.command ("ocaml -noinit " ^ Filename.quote file) in
        Sys.remove file;
        assert_equal ~printer:string_of_int 0 status);
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
      "capped climb" >:: test_case "capped_climb";
      "two admissible cap increments at the floor boundary" >::
        test_case "moving_cap_interval"
          ~cmp_sig:(fun a b -> signature_tokens a = signature_tokens b);
      "moving floor with an inferred cap increment" >:: test_case "unit_floor_shift"
        ~cmp_sig:(fun a b -> signature_tokens a = signature_tokens b);
      "two recursive calls require a nonconvex floor guard" >::
        test_case "moving_floor_calls"
          ~cmp_sig:(fun a b -> signature_tokens a = signature_tokens b);
      "reversing the sign of the floor increment" >::
        test_case "reflected_floor"
          ~cmp_sig:(fun a b -> signature_tokens a = signature_tokens b);
      "shared floor indices survive endpoint projection" >::
        test_case "skew_floor"
          ~cmp_sig:(fun a b -> signature_tokens a = signature_tokens b);
      "recover a recursive payload from its affine tag" >:: test_case "tagged_floor"
        ~cmp_sig:(fun a b -> signature_tokens a = signature_tokens b);
      "keep the payload index across signed tag updates" >:: test_case "signed_tag"
        ~cmp_sig:(fun a b -> signature_tokens a = signature_tokens b);
      "a redundant constructor arm preserves recursive inference" >::
        test_case "redundant_supplier"
          ~cmp_sig:(fun a b -> signature_tokens a = signature_tokens b);
      "a supplier cap lowers with the rising floor" >::
        test_case "tighter_supplier"
          ~cmp_sig:(fun a b -> signature_tokens a = signature_tokens b);
      "recursive callers can use either supplier cap" >::
        test_case "crossing_caps"
          ~cmp_sig:(fun a b -> signature_tokens a = signature_tokens b);
      "restore caller checks after inferring a recursive package" >:: (fun () ->
        let body =
          "datatype Marker\ndatacons Mark : Marker\ndatatype Cargo\ndatacons Box : Cargo\n" ^
          "datatype Tag : type * type\ndatacons Left : ∀a. a ⟶ Tag (Marker,a)\n" ^
          "datacons Right : ∀a. a ⟶ Tag (a,Marker)\n" ^
          "datatype Nat\ndatacons Z : Nat\ndatacons S : Nat ⟶ Nat\n" ^
          "external let same : ∀a. a → a → Bool = \"fun x y -> x = y\"\n" ^
          "let rec f t = efunction Z -> let z = (match t with Left x -> x | Right x -> x) in (z,z) " ^
          "| S n -> f t n\ntest (" in
        let client tag use = body ^ "let (x,y) = f (" ^ tag ^ " Box) (S Z) in " ^ use ^ ")" in
        List.iter (fun tag -> ignore (infer_source (client tag "same x Box"))) ["Left"; "Right"];
        assert_bool "the omitted check needs Cargo = Marker"
          (rejects_source (client "Left" "same y Mark"));
        assert_bool "one conjunctive scheme cannot serve both marked calls"
          (rejects_source (client "Left" "let (a,b) = f (Right Box) Z in let ok = same a Box in same x Box")));
      "an impossible maximum excludes a failing branch" >:: test_case "impossible_maximum";
      "preserve guard evaluation and erase impossible payload clients" >::
        run_example "unreachable_payload";
      "an opaque guard admits a type valid on either outcome" >:: run_example "opaque_guard";
      "a guard inside an opened package excludes both marked calls" >:: run_example "guard_contract";
      "arithmetic can wrap before a constructor match" >:: run_example "guard_overflow";
      "a local guard helper can keep its inferred index" >:: run_example "local_guard_helper";
      "a local recursive definition supplies a necessary guard contract" >:: run_example "local_guard_pair";
      "one package relation excludes two arms and preserves the live arm" >::
        run_example "local_packed_guards";
      "an existential can hide a closure with a free argument type" >::
        test_case ~test_annot:true "packed_closure";
      "incompatible type demands reopen a provisional package" >:: run_example "observed_tag";
      "a failed abduction can fit a scalar index from two branches" >:: run_example "scaled_coordinate";
      "a scalar package keeps the common affine equation after an offset" >:: run_example "translated_coordinate";
      "two excluded guards need the same interior package parameter" >::
        run_example ~cmp_sig:(fun a b -> signature_tokens a = signature_tokens b) "interior_interval";
      "two interior forbidden bands constrain one recursive call" >::
        run_example ~cmp_sig:(fun a b -> signature_tokens a = signature_tokens b) "guarded_interval_bands";
      "a recursive package chooses its key from the input state" >::
        run_example ~cmp_sig:(fun a b -> signature_tokens a = signature_tokens b) "state_dependent_interval";
      "private witnesses preserve the public interval bound" >::
        run_example ~cmp_sig:(fun a b -> signature_tokens a = signature_tokens b) "public_interval_bound";
      "a public package cannot promise a negative result at state zero" >:: (fun () ->
        let source = input_file (example_path "public_interval_bound" ^ ".gadt") in
        let client = "\nexternal let negative : ∀i[i≤0]. Num i → Bool = \"fun n -> assert (n <= 0); true\"\n" ^
          "let broken = let p = run A (-3) Z in negative p" in
        assert_bool "the base result is one" (rejects_source ~integer_target:true (source ^ client)));
      "four states choose a recursive interval across two forbidden bands" >::
        run_example ~cmp_sig:(fun a b -> signature_tokens a = signature_tokens b) "four_state_interval";
      "both endpoints miss a reachable assertion in the interior" >:: (fun () ->
        let source = "external let sample : Num 0 → ∃j[0≤j ∧ j≤6]. Num j = \"fun _ -> 3\"\n" ^
          "let bad = let r = sample 0 in match r with v when 2 <= v && v <= 4 -> assert false | _ -> True" in
        assert_bool "three reaches the guard" (rejects_source ~integer_target:true source));
      "a local match contract carries the observed index into the package" >::
        run_example "observed_coordinate";
      "the state index reaches the package through a tail match" >:: run_example "state_coordinate";
      "a reachable package result must pass the final exclusion check" >:: (fun () ->
        let source = "datatype Nat\ndatacons Z : Nat\ndatacons S : Nat ⟶ Nat\n" ^
          "external let expects_nat : Nat → Bool = \"fun _ -> true\"\n" ^
          "let bad = let rec relay n = efunction Z -> n | S d -> relay n d in " ^
          "let r = relay 1 (S Z) in (match r with k when 1 <= k -> expects_nat k | _ -> True)" in
        assert_bool "the guarded value is a number" (rejects_source ~integer_target:true source));
      "a constructor index witnesses a guarded call" >:: test_case "guarded_payload";
      "a call reached after opening an earlier return" >:: test_case "ordered_calls";
      "a partial application through two local aliases" >:: test_case "function_alias";
      "recover the marked input through a callback" >:: test_case "callback_input";
      "a callback can receive a function with a written existential return" >::
        test_case "written_callback";
      "instantiate each required call separately" >:: test_case "marked_calls";
      "empty existential binders and OCaml type names" >:: test_case "packed_payload";
      "an affine tag survives a reflected recursive input" >:: test_case "affine_tag"
          ~cmp_sig:(fun a b -> signature_tokens a = signature_tokens b);
      "written caller cap at crossing rates" >::
        test_case "crossing_caps_annotated"
          ~cmp_sig:(fun a b -> signature_tokens a = signature_tokens b);
      "a supplier cap depending on twice the rate" >::
        test_case "double_rate_supplier"
          ~cmp_sig:(fun a b -> signature_tokens a = signature_tokens b);
      "moving floor and cap" >:: test_case "moving_floor"
        ~cmp_sig:(fun a b -> signature_tokens a = signature_tokens b);
      "cap across two result constructors" >:: test_case "split_shifted_climb"
        ~cmp_sig:(fun a b -> signature_tokens a = signature_tokens b);
      "shifted cap with a symbolic argument" >:: test_case "shifted_capped_climb"
        ~cmp_sig:(fun a b -> signature_tokens a = signature_tokens b);
      "max-capped climb" >:: test_case "max_capped_climb"
        ~cmp_sig:(fun a b -> signature_tokens a = signature_tokens b);
      "binary_plus" >::
        (fun () ->
           skip_if !debug "debug";
           test_case "binary_plus" ());
      "binary_plus-harder" >::
        (fun () ->
           todo "currently requiring expanded arguments";
           skip_if !debug "debug";
           test_case "binary_plus_harder" ());
      "flatten_pairs" >::
        (fun () ->
           skip_if !debug "debug";
           test_case "flatten_pairs" ());
      "flatten_quadrs" >::
        (fun () ->
           skip_if !debug "debug";
           test_case "flatten_quadrs" ());
      "flatten_septs" >::
        (fun () ->
           skip_if !debug "debug";
           test_case ~ty_abd_timeout:3000
             ~abd_rotations:4 "flatten_septs" ());
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
           test_case "pointwise_zip2_simpler1" ());
      "pointwise-zip2-simpler2" >::
        (fun () ->
           skip_if !debug "debug";
           test_case "pointwise_zip2_simpler2" ());
      "pointwise-zip2-simpler3" >::
        (fun () ->
           skip_if !debug "debug";
           test_case "pointwise_zip2_simpler3" ());
      "pointwise-zip2-simpler4" >::
        (fun () ->
           skip_if !debug "debug";
           test_case "pointwise_zip2_simpler4" ());
      "pointwise-zip2" >::
        (fun () ->
           skip_if !debug "debug";
           test_case "pointwise_zip2" ());
      "pointwise-zip2-harder" >::
        (fun () ->
           skip_if !debug "debug";
           test_case ~do_ml:false "pointwise_zip2_harder" ());
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
           test_case "non_outsidein_rx" ());
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
           test_case "avl_delmin_simpler" ());
      "non_pointwise-avl_delmin-modified" >::
        (fun () ->
           skip_if !debug "debug";
           test_case "non_pointwise_avl_delmin_modified" ());
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
           test_case "non_pointwise_fd_comp_harder" ());
      "non_pointwise-zip1-simpler" >::
        (fun () ->
           skip_if !debug "debug";
           test_case ~prefer_guess:true "non_pointwise_zip1_simpler" ());
      "non_pointwise-zip1-simpler2" >::
        (fun () ->
           skip_if !debug "debug";
           test_case ~prefer_guess:true "non_pointwise_zip1_simpler2" ());
      "non_pointwise-zip1-modified" >::
        (fun () ->
           skip_if !debug "debug";
           test_case ~prefer_guess:true "non_pointwise_zip1_modified" ());
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
           test_case "liquid_isort_simpler3" ());
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
      "liquid_tower_asserted" >::
        (fun () ->
           skip_if !debug "debug";
           test_case "liquid_tower_asserted" ());
      "liquid_tower" >::
        (fun () ->
           skip_if !debug "debug";
           test_case "liquid_tower" ());
      "liquid_tower_harder" >::
        (fun () ->
           skip_if !debug "debug";
           test_case ~prefer_bound_to_local:true "liquid_tower_harder" ());
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
      "liquid_simplex_step_2" >::
        (fun () ->
           skip_if !debug "debug";
           test_case "liquid_simplex_step_2" ());
      "liquid_simplex_step_2a" >::
        (fun () ->
           skip_if !debug "debug";
           test_case "liquid_simplex_step_2a" ());
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
           (* Type in target is slightly less general than most general type:
              ∀k, n[1 ≤ n ∧ 3 ≤ k]. Matrix (n, k) → Float *)
           test_case ~prefer_bound_to_local:true
             ~only_off_by_1:true "liquid_simplex_step_3a" ());
      "liquid_simplex_step_4" >::
        (fun () ->
           todo "too hard for current InvarGenT";
           skip_if !debug "debug";
           test_case "liquid_simplex_step_4" ());
      "liquid_simplex_step_4a" >::
        (fun () ->
           skip_if !debug "debug";
           test_case "liquid_simplex_step_4a" ());
      "liquid_simplex_step_5a" >::
        (fun () ->
           skip_if !debug "debug";
           test_case "liquid_simplex_step_5a" ());
      "liquid_simplex_step_6a_1" >::
        (fun () ->
           skip_if !debug "debug";
           test_case "liquid_simplex_step_6a_1" ());
      "liquid_simplex_step_6_2" >::
        (fun () ->
           skip_if !debug "debug";
           test_case "liquid_simplex_step_6_2" ());
      "liquid_simplex_step_6a_2" >::
        (fun () ->
           skip_if !debug "debug";
           test_case ~prefer_bound_to_local:true
             "liquid_simplex_step_6a_2" ());
      "liquid_simplex_step_6_3" >::
        (fun () ->
           skip_if !debug "debug";
           test_case "liquid_simplex_step_6_3" ());
      "liquid_simplex_step_6a_3" >::
        (fun () ->
           skip_if !debug "debug";
           test_case "liquid_simplex_step_6a_3" ());
      "liquid_simplex_step_6a" >::
        (fun () ->
           skip_if !debug "debug";
           test_case "liquid_simplex_step_6a" ());
      "liquid_simplex_step_7a" >::
        (fun () ->
           skip_if !debug "debug";
           test_case "liquid_simplex_step_7a" ());
      "liquid_simplex" >::
        (fun () ->
           skip_if !debug "debug";
           test_case ~test_annot:true "liquid_simplex" ());
      "liquid_simplex-harder" >::
        (fun () ->
           skip_if !debug "debug";
           skip_if !short_tests_only "long test: 53s";
           test_case "liquid_simplex_harder" ());
      "liquid_gauss_rowSwap" >::
        (fun () ->
           skip_if !debug "debug";
           test_case "liquid_gauss_rowSwap" ());
      "liquid_gauss_rowElim" >::
        (fun () ->
           skip_if !debug "debug";
           test_case "liquid_gauss_rowElim" ());
      "liquid_gauss_rowMax" >::
        (fun () ->
           (* The unuseful type inferred is correct, but we want better. *)
           todo "Beyond the scope of InvarGenT 2.0";
           skip_if !debug "debug";
           test_case "liquid_gauss_rowMax" ());
      "liquid_gauss_rowMax_2" >::
        (fun () ->
           skip_if !debug "debug";
           test_case "liquid_gauss_rowMax_2" ());
      "liquid_gauss_simpler" >::
        (fun () ->
           skip_if !debug "debug";
           test_case "liquid_gauss_simpler" ());
      "liquid_gauss_simpler_asserted" >::
        (fun () ->
           skip_if !debug "debug";
           test_case "liquid_gauss_simpler_asserted" ());
      "liquid_gauss" >::
        (fun () ->
           skip_if !debug "debug";
           test_case "liquid_gauss" ());
      "liquid_gauss2" >::
        (fun () ->
           skip_if !debug "debug";
           test_case ~prefer_bound_to_local:true "liquid_gauss2" ());
      "liquid_gauss_asserted" >::
        (fun () ->
           skip_if !debug "debug";
           test_case "liquid_gauss_asserted" ());
      "liquid_gauss_harder_asserted" >::
        (fun () ->
           skip_if !debug "debug";
           test_case "liquid_gauss_harder_asserted" ());
      "liquid_gauss_harder" >::
        (fun () ->
           todo "Too hard for current InvarGenT";
           skip_if !debug "debug";
           test_case "liquid_gauss_harder" ());
      "liquid_fft_ffor" >::
        (fun () ->
           skip_if !debug "debug";
           test_case "liquid_fft_ffor" ());
      "liquid_fft_simpler" >::
        (fun () ->
           skip_if !debug "debug";
           skip_if !short_tests_only "long test: 62s";
           test_case ~same_with_assertions:true
             "liquid_fft_simpler" ());
      "liquid_fft" >::
        (fun () ->
           skip_if !debug "debug";
           skip_if !short_tests_only "long test: 57s";
           test_case "liquid_fft" ());
      "liquid_fft_tests" >::
        (fun () ->
           skip_if !debug "debug";
           test_case "liquid_fft_tests" ());
      "liquid_fft_full" >::
        (fun () ->
           skip_if !debug "debug";
           skip_if !short_tests_only "long test: 66s";
           test_case "liquid_fft_full" ());
      "liquid_fft_full_asserted" >::
        (fun () ->
           skip_if !debug "debug";
           skip_if !short_tests_only "long test: 69s";
           test_case ~same_with_assertions:true
             "liquid_fft_full_asserted" ());
      "issue2" >::
        (fun () ->
           skip_if !debug "debug";
           test_case ~test_annot:true ~drop_assert_false:false
             "issue2" ());
      "compact_array" >::
        (fun () ->
           skip_if !debug "debug";
           test_case ~test_annot:true
             "compact_array" ());
      "eval_alt_syntax" >::
        (fun () ->
           skip_if !debug "debug";
           test_case "eval_alt_syntax" ());
    ]

let () =
  let executable = Filename.basename Sys.executable_name in
  let chop f =
    try Filename.chop_extension f with Invalid_argument _ -> f in
  let executable = chop (chop executable) in
  if executable = "InvarGenTTest"
  then ignore (OUnit.run_test_tt ~verbose:true tests)
