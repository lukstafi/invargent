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

let tests = "NumS" >::: [

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
        let brs = List.map (sort_formula % snd) brs in
        let preserve = List.fold_left
            (fun vs br -> VarSet.union vs (fvs_formula br))
            VarSet.empty brs in
        let bvs = VarSet.empty in
        let param_bvs = VarSet.empty in
        let vs, ans = disjelim q ~target_vs:preserve
            ~initstep:false ~preserve ~param_bvs ~bvs brs in
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
        let brs = List.map (sort_formula % snd) brs in
        let preserve = List.fold_left
            (fun vs br -> VarSet.union vs (fvs_formula br))
            VarSet.empty brs in
        let bvs = VarSet.empty in
        let param_bvs = VarSet.empty in
        max_subopti_postcond := 10;
        let vs, ans = disjelim q ~target_vs:preserve
            ~initstep:false ~preserve ~bvs ~param_bvs brs in
        max_subopti_postcond := old_max_subopti_postcond;
        ignore (Format.flush_str_formatter ());
        Format.fprintf Format.str_formatter "@[<2>∃%a.@ %a@]"
          (pr_sep_list "," pr_tyvar) vs pr_formula ans;
        assert_equal ~printer:(fun x -> x)
          "∃. min (n4, n3)≤n2 ∧ n1≤max (n4, n3) ∧ n2≤max (n4, n1) ∧
  n2≤max (n4, n3) ∧ min (n4, n3)≤n1 ∧ min (n4, n2)≤n1 ∧ n2 = n1"
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
        let brs = List.map (sort_formula % snd) brs in
        let preserve = List.fold_left
            (fun vs br -> VarSet.union vs (fvs_formula br))
            VarSet.empty brs in
        let bvs = VarSet.empty in
        let param_bvs = VarSet.empty in
        max_subopti_postcond := 10;
        let vs, ans = disjelim q ~target_vs:preserve
            ~initstep:false ~preserve ~bvs ~param_bvs brs in
        max_subopti_postcond := old_max_subopti_postcond;
        ignore (Format.flush_str_formatter ());
        Format.fprintf Format.str_formatter "@[<2>∃%a.@ %a@]"
          (pr_sep_list "," pr_tyvar) vs pr_formula ans;
        assert_equal ~printer:(fun x -> x)
          "∃. min (n2, n1)≤n3 ∧ n3≤max (n2, n1) ∧ n4≤max (n2, n1) ∧
  n4≤max (n2, n3) ∧ min (n2, n1)≤n4 ∧ n4 = n3"
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
        let brs = List.map (sort_formula % snd) brs in
        let preserve = List.fold_left
            (fun vs br -> VarSet.union vs (fvs_formula br))
            VarSet.empty brs in
        let bvs = VarSet.empty in
        let param_bvs = VarSet.empty in
        let vs, ans = disjelim q ~target_vs:preserve
            ~initstep:false ~preserve ~bvs ~param_bvs brs in
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
        let brs = List.map (sort_formula % snd) brs in
        let preserve = List.fold_left
            (fun vs br -> VarSet.union vs (fvs_formula br))
            VarSet.empty brs in
        let bvs = VarSet.empty in
        let param_bvs = VarSet.empty in
        let vs, ans = disjelim q ~target_vs:preserve
            ~initstep:false ~preserve ~bvs ~param_bvs brs in
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
