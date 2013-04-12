(** Abduction tests for InvarGenT.

    Released under the GNU General Public Licence (version 2 or
    higher), NO WARRANTY of correctness etc. (C) Lukasz Stafiniak 2013
    @author Lukasz Stafiniak lukstafi (AT) gmail.com
    @since Mar 2013
*)
open OUnit
open Terms

let tests = "Abduction" >::: [

  "simple abduction: eval" >::
    (fun () ->
      Terms.reset_counters ();
      Infer.reset_counters ();
      try
        let lhs1 = "(Term t6) = t3 ∧ Int = t6" in
        let rhs1 = "t7 = Int" in
        let lhs2 = "(Term t9) = t3 ∧ Bool = t9" in
        let rhs2 = "t10 = Bool ∧ t13 = (Term Int → Int)" in
        let lhs3 = "(Term t15) = t3 ∧ Int = t15" in
        let rhs3 =
          "t16 = Int ∧ t22 = (Term Int → Int) ∧ t19 = (Term Int → Int)" in
        let lhs4 = "(Term t24) = t3" in
        let rhs4 = "t34 = (Term Bool → Bool) ∧
    t31 = (Term t24 → t25) ∧ t28 = (Term t24 → t25)" in
        let lhs5 = "(Term t39) = t3 ∧ (t40, t41) = t39" in
        let rhs5 =
        "t42 = (t43, t44) ∧ t46 = (Term t40 → t43) ∧ t48 = (Term t41 → t44)" in
        let lhs6 = "(Term t51) = t3" in
        let rhs6 = "t57 = (t59, t60) ∧ t58 = t53 ∧
    t56 = (Term (t51, t52) → t59, t60)" in
        let lhs7 = "(t61, t62) = t57 ∧ (Term t51) = t3" in
        let rhs7 = "t61 = t58" in
        let lhs8 = "(Term t66) = t3" in
        let rhs8 = "t71 = (t73, t74) ∧ t72 = t67 ∧
    t70 = (Term (t65, t66) → t73, t74)" in
        let lhs9 = "(t75, t76) = t71 ∧ (Term t66) = t3" in
        let rhs9 = "t76 = t72" in
        ()
      with (Terms.Report_toplevel _ | Terms.Contradiction _) as exn ->
        ignore (Format.flush_str_formatter ());
        Terms.pr_exception Format.str_formatter exn;
        assert_failure (Format.flush_str_formatter ())
    );

]
