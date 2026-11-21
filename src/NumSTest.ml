(** Numeric sort operations tests for InvarGenT.

    Released under the GNU General Public Licence (version 2 or
    higher), NO WARRANTY of correctness etc. (C) Lukasz Stafiniak 2013
    @author Lukasz Stafiniak lukstafi (AT) gmail.com
    @since Mar 2013
*)
open OUnit

let debug = ref (* true *)false

open Aux
open Defs
open NumDefs
(* open Terms *)
open NumS

let cmp_v v1 v2 = Same_quant
let uni_v v = v=VNam (Type_sort, "tx")
              || v=VNam (Type_sort, "ty")
let q = {cmp_v; uni_v; same_as = (fun _ _ -> ());
         upward_of = (fun _ _ -> false)}

let numeric_formula s =
  sort_formula (Parser.formula Lexer.token (Lexing.from_string s))

let tests = "NumS" >::: [
  "extremum at a universal result index" >:: (fun () ->
    let q = {q with uni_v = (fun _ -> true)} in
    let goal = numeric_formula "n2<=max(n1+20,0)" in
    let vars = NumDefs.fvs_formula goal in
    let rejected =
      try ignore (holds q VarSet.empty empty_state goal); false
      with Terms.Contradiction _ -> true in
    assert_bool "the caller bound restricts an arbitrary result" rejected;
    let _, demand = abductive_holds q ~bvs:vars empty_state goal in
    assert_bool "Split receives the caller bound"
      (implies_cnj (satisfiable_exn demand) goal);
    ignore (holds q VarSet.empty empty_state
              (numeric_formula "n1<=max(2 n1,0)")));

  "widen against every supplier on the public interface" >:: (fun () ->
    let old = numeric_formula "n1<=n2 ∧ n2<=max(n1+20,0)" in
    let summary = numeric_formula "n1<=n2" in
    let public = NumDefs.fvs_formula old in
    let check interface branches expected =
      let result = converge q ~initstep:false
          ~suppliers:(interface, List.map numeric_formula branches) old summary in
      assert_equal ~printer:string_of_bool expected
        (implies_cnj (satisfiable_exn result) old) in
    let base = "n2=n1" and left = "n2<=n1+19" and right = "n2<=0" in
    check public [base; left; right] true;
    check public [base; left; "n2<=n1+21"] false;
    check public [base; "0<=n1"] false;
    check public [] false;
    check VarSet.empty [base; left; right] false);

  "keep a supplier extremum only when every branch proves it" >:: (fun () ->
    let cap = numeric_formula "n1<=max(n2+19,0)" in
    let preserve = fvs_formula cap in
    let target_vs = fvs_formula (numeric_formula "n1=0")
    and param_bvs = fvs_formula (numeric_formula "n2=0") in
    let check extra expected =
      let branches = ["n1=0"; "0<=n1 ∧ n1<=max(n2+19,0)"] @ extra in
      let _, _, result, _ = disjelim q ~target_vs ~preserve ~param_bvs
          ~bvs:VarSet.empty ~guess:false ~initstep:false
          (List.map (fun s -> [], numeric_formula s) branches) in
      assert_equal ~printer:string_of_bool expected
        (implies_cnj (satisfiable_exn result) cap) in
    check [] true;
    check ["n1=1"] false);

  "instantiate caller thresholds on the supplier result" >:: (fun () ->
    let cap = numeric_formula "n1<=max(n2+19,0)" in
    let target_vs = fvs_formula (numeric_formula "n1=0")
    and param_bvs = fvs_formula (numeric_formula "n2=0") in
    let check extra expected =
      let branches = ["n1=0"; "0<=n1 ∧ n1<=n2+19"] @ extra in
      let _, _, result, _ = disjelim q ~target_vs ~preserve:(fvs_formula cap)
          ~previous:(numeric_formula "n8<=max(n9+20,0)") ~param_bvs
          ~bvs:VarSet.empty ~guess:false ~initstep:false
          (List.map (fun s -> [], numeric_formula s) branches) in
      assert_bool "no caller-local variable escapes"
        (VarSet.subset (fvs_formula result) (fvs_formula cap));
      assert_equal ~printer:string_of_bool expected
        (implies_cnj (satisfiable_exn result) cap) in
    check [] true;
    check ["n1=1"] false);

  "extrema on ground inputs" >:: (fun () ->
    let goals = List.map (fun (text, holds) -> text, numeric_formula text, holds)
        ["n1 = max(n2,n3)", (fun x y z -> x = max y z);
         "n1 = min(n2,n3)", (fun x y z -> x = min y z);
         "n1 <= max(n2,n3)", (fun x y z -> x <= max y z);
         "min(n2,n3) <= n1", (fun x y z -> min y z <= x)] in
    for x = -2 to 2 do
      for y = -2 to 2 do
        for z = -2 to 2 do
          let given = Printf.sprintf "n1=%d ∧ n2=%d ∧ n3=%d" x y z in
          let st = satisfiable_exn (numeric_formula given) in
          List.iter (fun (text, goal, holds) ->
            assert_equal ~msg:(given ^ " implies " ^ text) ~printer:string_of_bool
              (holds x y z) (implies_cnj st goal)) goals
        done
      done
    done);

  "extrema under substitutions" >:: (fun () ->
    let feasible batches =
      try
        ignore (List.fold_left (fun state batch ->
          satisfiable_exn ~state (numeric_formula batch)) empty_state batches);
        true
      with Terms.Contradiction _ -> false in
    let values = "n1=0 ∧ n2=2 ∧ n3=1" in
    List.iter (fun (atom, expected) ->
      List.iter (fun batches ->
        assert_equal ~msg:(String.concat " then " batches) ~printer:string_of_bool
          expected (feasible batches))
        [[values ^ " ∧ " ^ atom]; [values;atom]; [atom;values]])
      ["min(n1,n2)<=n3", true; "n3<=max(n1,n2)", true;
       "n1+1<=max(n1,n1)", false; "min(n2,n3)<=n1", false;
       "n1=min(n1,n2)", true; "n1=max(n1,n2)", false]);

  "an early counterexample among many extrema" >:: (fun () ->
    let rec constraints n acc =
      if n = 0 then acc else
        let atom = Printf.sprintf "min(n%d,n%d)<=n%d" (3*n) (3*n+1) (3*n+2) in
        constraints (n-1) (atom :: acc) in
    let st = satisfiable_exn (numeric_formula (String.concat " ∧ " (constraints 30 []))) in
    assert_bool "the independent n1 is unrestricted"
      (not (implies_cnj st (numeric_formula "n1<=0"))));

  "extrema across alternatives" >:: (fun () ->
    List.iter (fun (given, goal, expected) ->
      let st = satisfiable_exn (numeric_formula given) in
      assert_equal ~msg:(given ^ " implies " ^ goal) ~printer:string_of_bool
        expected (implies_cnj st (numeric_formula goal)))
      ["min(n1,n2) <= n3 ∧ n3+1 <= n2", "n1 <= n3", true;
       "min(n1,n2) <= n3", "n1 <= n3", false;
       "n1+n2=0 ∧ n3=0", "min(n1,n2) <= n3", true;
       "n1+n2=0 ∧ n3=0", "n3 <= max(n1,n2)", true;
       "n1+n2=0 ∧ n3= -1", "min(n1,n2) <= n3", false;
       "n1<=n3 ∧ n2<=n3", "n3=max(n1,n2)", false;
       "n1=0 ∧ n1+n2<=2 n3 ∧ n2=max(n3,n1)", "n2=n1+n3", true;
       "n1<=n2 ∧ n2<=n3 ∧ n3<=n1 ∧ n4<=n1 ∧ n2<=n4", "n4=n3", true;
       "n1<=n2 ∧ n2<=n3 ∧ n1<=n3", "n1=n3", false]);

  "convex hull: basic cst" >::
    (fun () ->
      skip_if !debug "debug";
      Terms.reset_state ();
      Infer.reset_state ();
      (* try *)
      try
        Printexc.record_backtrace true;
        let brs = Parser.cn_branches Lexer.token
	  (Lexing.from_string " ⟹ n1 = n2 ∧ n3 <= n2 + 2
|  ⟹ n1 = n2 ∧ n3 <= n2
|  ⟹ n1 = n2 ∧ n3 <= n2 + 1") in
        let brs = List.map (fun (_, c) -> [], sort_formula c) brs in
        let preserve = List.fold_left
            (fun vs (_, br) -> VarSet.union vs (fvs_formula br))
            VarSet.empty brs in
        let bvs = VarSet.empty in
        let param_bvs = VarSet.empty in
        let vs, _, ans, _ = disjelim q ~target_vs:preserve
            ~guess:false ~initstep:false ~preserve ~param_bvs ~bvs brs in
        let ans = prune_redundant q ~initstep:true ans in
        ignore (Format.flush_str_formatter ());
        Format.fprintf Format.str_formatter "@[<2>∃%a.@ %a@]"
          (pr_sep_list "," pr_tyvar) vs pr_formula ans;
        assert_equal ~printer:(fun x -> x)
          "∃. n2 = n1 ∧ n3 ≤ n1 + 2"
          (Format.flush_str_formatter ())
      with (Report_toplevel _ | Terms.Contradiction _) as exn ->
        ignore (Format.flush_str_formatter ());
        Terms.pr_exception Format.str_formatter exn;
        assert_failure (Format.flush_str_formatter ())
      (* with exn ->
        Printexc.print_backtrace stdout;
        assert_failure (Printexc.to_string exn) *)
    );

  "convex hull: basic equations 1" >::
    (fun () ->
      skip_if !debug "debug";
      Terms.reset_state ();
      Infer.reset_state ();
      let old_max_subopti_postcond = !max_subopti_postcond in
      (* try *)
      try
        Printexc.record_backtrace true;
        let brs = Parser.cn_branches Lexer.token
	  (Lexing.from_string " ⟹ n1 = n3 ∧ n2 = n3
|  ⟹ n1 = n4 ∧ n2 = n4") in
        let brs = List.map (fun (_, c) -> [], sort_formula c) brs in
        let preserve = List.fold_left
            (fun vs (_, br) -> VarSet.union vs (fvs_formula br))
            VarSet.empty brs in
        let bvs = VarSet.empty in
        let param_bvs = VarSet.empty in
        max_subopti_postcond := 10;
        let vs, _, ans, _ = disjelim q ~target_vs:preserve
            ~guess:false ~initstep:false ~preserve ~bvs ~param_bvs brs in
        let ans = prune_redundant q ~initstep:false ans in
        max_subopti_postcond := old_max_subopti_postcond;
        ignore (Format.flush_str_formatter ());
        Format.fprintf Format.str_formatter "@[<2>∃%a.@ %a@]"
          (pr_sep_list "," pr_tyvar) vs pr_formula ans;
        assert_equal ~printer:(fun x -> x)
          "∃. n2 = n1 ∧ min (n3, n4)≤n2 ∧ n2≤max (n3, n4)"
          (Format.flush_str_formatter ())
      with (Report_toplevel _ | Terms.Contradiction _) as exn ->
        max_subopti_postcond := old_max_subopti_postcond;
        ignore (Format.flush_str_formatter ());
        Terms.pr_exception Format.str_formatter exn;
        assert_failure (Format.flush_str_formatter ())
      (* with exn ->
        Printexc.print_backtrace stdout;
        assert_failure (Printexc.to_string exn) *)
    );

  "convex hull: basic equations 2" >::
    (fun () ->
      skip_if !debug "debug";
      Terms.reset_state ();
      Infer.reset_state ();
      let old_max_subopti_postcond = !max_subopti_postcond in
      try
        Printexc.record_backtrace true;
        let brs = Parser.cn_branches Lexer.token
	  (Lexing.from_string " ⟹ n3 = n1 ∧ n4 = n1
|  ⟹ n3 = n2 ∧ n4 = n2") in
        let brs = List.map (fun (_, c) -> [], sort_formula c) brs in
        let preserve = List.fold_left
            (fun vs (_, br) -> VarSet.union vs (fvs_formula br))
            VarSet.empty brs in
        let bvs = VarSet.empty in
        let param_bvs = VarSet.empty in
        max_subopti_postcond := 10;
        let vs, _, ans, _ = disjelim q ~target_vs:preserve
            ~guess:false ~initstep:false ~preserve ~bvs ~param_bvs brs in
        let ans = prune_redundant q ~initstep:false ans in
        max_subopti_postcond := old_max_subopti_postcond;
        ignore (Format.flush_str_formatter ());
        Format.fprintf Format.str_formatter "@[<2>∃%a.@ %a@]"
          (pr_sep_list "," pr_tyvar) vs pr_formula ans;
        assert_equal ~printer:(fun x -> x)
          "∃. n4 = n3 ∧ n3≤max (n1, n2) ∧ min (n1, n2)≤n3"
          (Format.flush_str_formatter ())
      with (Report_toplevel _ | Terms.Contradiction _) as exn ->
        max_subopti_postcond := old_max_subopti_postcond;
        ignore (Format.flush_str_formatter ());
        Terms.pr_exception Format.str_formatter exn;
        assert_failure (Format.flush_str_formatter ())
      (* with exn ->
        Printexc.print_backtrace stdout;
        assert_failure (Printexc.to_string exn) *)
    );

  "convex hull: basic sides" >::
    (fun () ->
      skip_if !debug "debug";
      Terms.reset_state ();
      Infer.reset_state ();
      (* try *)
      try
        Printexc.record_backtrace true;
        let brs = Parser.cn_branches Lexer.token
	  (Lexing.from_string " ⟹ n1 <= n2 ∧ 0 <= n1 ∧ n2 <= 1
|  ⟹ n2 <= n1 + 2 ∧ 2 <= n2 ∧ n1 <= 1") in
        let brs = List.map (fun (_, c) -> [], sort_formula c) brs in
        let preserve = List.fold_left
            (fun vs (_, br) -> VarSet.union vs (fvs_formula br))
            VarSet.empty brs in
        let bvs = VarSet.empty in
        let param_bvs = VarSet.empty in
        let vs, _, ans, _ = disjelim q ~target_vs:preserve
            ~guess:false ~initstep:false ~preserve ~bvs ~param_bvs brs in
        ignore (Format.flush_str_formatter ());
        Format.fprintf Format.str_formatter "@[<2>∃%a.@ %a@]"
          (pr_sep_list "," pr_tyvar) vs pr_formula ans;
        assert_equal ~printer:(fun x -> x)
          "∃. 0 ≤ n1 ∧ n1 ≤ 1 ∧ n1 ≤ n2 ∧ n2 ≤ n1 + 2"
          (Format.flush_str_formatter ())
      with (Report_toplevel _ | Terms.Contradiction _) as exn ->
        ignore (Format.flush_str_formatter ());
        Terms.pr_exception Format.str_formatter exn;
        assert_failure (Format.flush_str_formatter ())
      (* with exn ->
        Printexc.print_backtrace stdout;
        assert_failure (Printexc.to_string exn) *)
    );

  "convex hull: basic angle" >::
    (fun () ->
      skip_if !debug "debug";
      Terms.reset_state ();
      Infer.reset_state ();
      let old_disjelim_rotations = !disjelim_rotations in
      (* try *)
      try
        Printexc.record_backtrace true;
        disjelim_rotations := 3;
        let brs = Parser.cn_branches Lexer.token
	  (Lexing.from_string " ⟹ n1 <= n2 ∧ 0 <= n1 ∧ n2 <= 1
|  ⟹ n2 <= n1 ∧ 2 <= n2 ∧ n1 <= 3") in
        let brs = List.map (fun (_, c) -> [], sort_formula c) brs in
        let preserve = List.fold_left
            (fun vs (_, br) -> VarSet.union vs (fvs_formula br))
            VarSet.empty brs in
        let bvs = VarSet.empty in
        let param_bvs = VarSet.empty in
        let vs, _, ans, _ = disjelim q ~target_vs:preserve
            ~guess:false ~initstep:false ~preserve ~bvs ~param_bvs brs in
        disjelim_rotations := old_disjelim_rotations;
        ignore (Format.flush_str_formatter ());
        Format.fprintf Format.str_formatter "@[<2>∃%a.@ %a@]"
          (pr_sep_list "," pr_tyvar) vs pr_formula ans;
        assert_equal ~printer:(fun x -> x)
          "∃. 0 ≤ n1 ∧ n1 ≤ 3 ∧ 2 n1 ≤ 3 n2 ∧ 3 n2 ≤ 2 n1 + 3"
          (Format.flush_str_formatter ())
      with (Report_toplevel _ | Terms.Contradiction _) as exn ->
        disjelim_rotations := old_disjelim_rotations;
        ignore (Format.flush_str_formatter ());
        Terms.pr_exception Format.str_formatter exn;
        assert_failure (Format.flush_str_formatter ())
      (* with exn ->
        Printexc.print_backtrace stdout;
        assert_failure (Printexc.to_string exn) *)
    );

]


let () =
  let executable = Filename.basename Sys.executable_name in
  let chop f =
    try Filename.chop_extension f with Invalid_argument _ -> f in
  let executable = chop (chop executable) in
  if executable = "NumSTest"
  then ignore (OUnit.run_test_tt ~verbose:true tests)
