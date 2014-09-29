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
let q = {cmp_v; uni_v; same_as = fun _ _ -> ()}

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
        let vs, ans = disjelim q ~initstep:false ~preserve brs in
        ignore (Format.flush_str_formatter ());
        Format.fprintf Format.str_formatter "@[<2>∃%a.@ %a@]"
          (pr_sep_list "," pr_tyvar) vs pr_formula ans;
        assert_equal ~printer:(fun x -> x)
          "∃. n1 = n2 ∧ n3 ≤ n1 + 2"
          (Format.flush_str_formatter ())
      with (Report_toplevel _ | Terms.Contradiction _) as exn ->
        ignore (Format.flush_str_formatter ());
        Terms.pr_exception Format.str_formatter exn;
        assert_failure (Format.flush_str_formatter ())
      (* with exn ->
        Printexc.print_backtrace stdout;
        assert_failure (Printexc.to_string exn) *)
    );

  "convex hull: basic equations" >::
    (fun () ->
      skip_if !debug "debug";
      Terms.reset_state ();
      Infer.reset_state ();
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
        let vs, ans = disjelim q ~initstep:false ~preserve brs in
        ignore (Format.flush_str_formatter ());
        Format.fprintf Format.str_formatter "@[<2>∃%a.@ %a@]"
          (pr_sep_list "," pr_tyvar) vs pr_formula ans;
        assert_equal ~printer:(fun x -> x)
          "∃. n2≤max (n3, n4) ∧ min (n3, n4)≤n2 ∧ n1≤max (n3, n4) ∧
  min (n3, n4)≤n1 ∧ min (n3, n2)≤n1 ∧ n1 = n2"
          (Format.flush_str_formatter ())
      with (Report_toplevel _ | Terms.Contradiction _) as exn ->
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
        let vs, ans = disjelim q ~initstep:false ~preserve brs in
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
      (* try *)
      try
        Printexc.record_backtrace true;
        let brs = Parser.cn_branches Lexer.token
	  (Lexing.from_string " ⟹ n1 <= n2 ∧ 0 <= n1 ∧ n2 <= 1
|  ⟹ n2 <= n1 ∧ 2 <= n2 ∧ n1 <= 3") in
        let brs = List.map (sort_formula % snd) brs in
        let preserve = List.fold_left
            (fun vs br -> VarSet.union vs (fvs_formula br))
            VarSet.empty brs in
        let vs, ans = disjelim q ~initstep:false ~preserve brs in
        ignore (Format.flush_str_formatter ());
        Format.fprintf Format.str_formatter "@[<2>∃%a.@ %a@]"
          (pr_sep_list "," pr_tyvar) vs pr_formula ans;
        assert_equal ~printer:(fun x -> x)
          "∃. 0 ≤ n1 ∧ n1 ≤ 3 ∧ 2 n1 ≤ 3 n2 ∧ 3 n2 ≤ 2 n1 + 3"
          (Format.flush_str_formatter ())
      with (Report_toplevel _ | Terms.Contradiction _) as exn ->
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
