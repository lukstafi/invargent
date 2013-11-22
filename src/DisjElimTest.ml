(** Disjunction elimination tests for InvarGenT.

    Released under the GNU General Public Licence (version 2 or
    higher), NO WARRANTY of correctness etc. (C) Lukasz Stafiniak 2013
    @author Lukasz Stafiniak lukstafi (AT) gmail.com
    @since Mar 2013
*)
open OUnit
open Terms
open Aux

let cmp_v v1 v2 = Same_quant
let uni_v v = v=VNam (Type_sort, "tx")
              || v=VNam (Type_sort, "ty")
let q = {cmp_v; uni_v; same_as = fun _ _ -> ()}

let test_case msg test result =
  Terms.reset_state ();
  Infer.reset_state ();
  (* try *)
  try
    Printexc.record_backtrace true;
    let brs = Parser.cn_branches Lexer.token
      (Lexing.from_string test) in
    let vs, ans = DisjElim.disjelim q
        ~preserve:VarSet.empty ~do_num:true
        (List.map (uncurry (@)) brs) in
    ignore (Format.flush_str_formatter ());
    Format.fprintf Format.str_formatter "@[<2>∃%a.@ %a@]"
      (pr_sep_list "," pr_tyvar) vs pr_formula ans;
    assert_equal ~msg ~printer:(fun x -> x)
      result
      (Format.flush_str_formatter ());
  with (Terms.Report_toplevel _ | Terms.Contradiction _) as exn ->
    ignore (Format.flush_str_formatter ());
    Terms.pr_exception Format.str_formatter exn;
    assert_failure (Format.flush_str_formatter ())
(* with exn -> *)
(*   Printexc.print_backtrace stdout; *)
(*   assert_failure (Printexc.to_string exn) *)


let tests = "DisjElim" >::: [

  "basic" >::
    (fun () ->
      test_case "abstract arg" " ⟹ ta = F A
| ⟹ ta = F B" "∃t1. ta = (F t1)";
      test_case "infer eq" " ⟹ ta = A ∧ tb = A
| ⟹ ta = B ∧ tb = B" "∃. tb = ta ∧ ta = tb";
      test_case "abstract bigger" " ⟹ ta = G (A, C)
| ⟹ ta = G (B, C)" "∃t1. ta = (G (t1, C))";
      test_case "abstract & infer" " ⟹ ta = G (A, C) ∧ C = tb
| ⟹ ta = G (B, D) ∧ D = tb" "∃t1. ta = (G (t1, tb))";

    );

  "simplified eval" >::
    (fun () ->
      test_case "eval" " (Term tf) = tc ∧ Int = tf ⟹ td = Int ∧ ta = (Term te → td) ∧ tc = (Term te)
| (Term tg) = tc ∧ Bool = tg ⟹ td = Bool ∧
    ta1 = (Term Int → Int) ∧ ta = (Term te → td) ∧ tc = (Term te)
| (Term ta3) = tc ∧ Int = ta3 ⟹ td = Int ∧
    ta9 = (Term Int → Int) ∧ ta6 = (Term Int → Int) ∧ ta = (Term te → td) ∧ tc = (Term te)
| (Term tc5) = tc ∧ (tc6, tc7) = tc5 ⟹ td = (tc8, tc9) ∧ td1 = td3 ∧
    td1 = (Term tc6 → tc8) ∧ td3 = (Term tc7 → tc9) ∧ ta = (Term te →
    td) ∧ tc = (Term te)"
        "∃. ta = (Term te → td) ∧ tc = (Term te)"
    );

]
