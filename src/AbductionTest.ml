(** Abduction tests for InvarGenT.

    Released under the GNU General Public Licence (version 2 or
    higher), NO WARRANTY of correctness etc. (C) Lukasz Stafiniak 2013
    @author Lukasz Stafiniak lukstafi (AT) gmail.com
    @since Mar 2013
*)
open OUnit
open Terms
open Abduction

let cmp_v v1 v2 = Same_quant
let uni_v v = false

let test_simple lhs_m rhs_m res =
  let lhs = Parser.formula Lexer.token (Lexing.from_string lhs_m) in
  let rhs = Parser.formula Lexer.token (Lexing.from_string rhs_m) in
  let lhs, _, _ = unify ~use_quants:false cmp_v uni_v lhs in
  let rhs, _, _ = unify ~use_quants:false cmp_v uni_v rhs in
  let anss = abd_simple cmp_v uni_v (lhs, rhs) in
  let anss =
    List.map
      (fun (vs, ans_typ, ans_num) ->
        to_formula ans_typ @ ans_num) anss in
  let str f = pr_to_str pr_formula f in
  assert_equal ~printer:(fun x -> x)
    ~msg:(lhs_m^" ⟹ "^rhs_m) res
    (String.concat ";\n" (List.map str anss))

let tests = "Abduction" >::: [

  "simple abduction: eval" >::
    (fun () ->
      Terms.reset_counters ();
      Infer.reset_counters ();
      try
        let lhs1 = "(Term tb) = ta ∧ Int = tb" in
        let rhs1 = "tc = Int" in
        test_simple lhs1 rhs1 "tc = tb;
ta = (Term tc);
tc = Int";
        let lhs2 = "(Term td) = ta ∧ Bool = td" in
        let rhs2 = "tf = Bool ∧ te = (Term Int → Int)" in
        test_simple lhs2 rhs2 "te = (Term Int → Int) ∧
tf = td;
ta = (Term tf) ∧
te = (Term Int → Int);
te = (Term Int → Int) ∧
tf = Bool";
        let lhs3 = "(Term tg) = ta ∧ Int = tg" in
        let rhs3 =
          "th = Int ∧ tj = (Term Int → Int)" in
        test_simple lhs3 rhs3 "";
        let lhs4 = "(Term tg) = ta ∧ Int = tg" in
        let rhs4 =
          "th = Int ∧ tj = (Term Int → Int) ∧ ti = (Term Int → Int)" in
        test_simple lhs4 rhs4 "";
        let lhs5 = "(Term tk) = ta" in
        let rhs5 = "tn = (Term Bool → Bool) ∧
    to = (Term tk → tl) ∧ tm = (Term tk → tl)" in
        test_simple lhs5 rhs5 "";
      with (Terms.Report_toplevel _ | Terms.Contradiction _) as exn ->
        ignore (Format.flush_str_formatter ());
        Terms.pr_exception Format.str_formatter exn;
        assert_failure (Format.flush_str_formatter ())
    );

]
