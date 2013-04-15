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

let p_formula s = Parser.formula Lexer.token (Lexing.from_string s)
let br_simple lhs rhs =
  let lhs, _, _ = unify ~use_quants:false cmp_v uni_v lhs in
  let rhs, _, _ = unify ~use_quants:false cmp_v uni_v rhs in
  lhs, rhs

let test_simple lhs_m rhs_m skip res =
  let lhs = p_formula lhs_m and rhs = p_formula rhs_m in
  let lhs, rhs = br_simple lhs rhs in
  let ans =
    match abd_simple cmp_v uni_v skip ([],[]) (lhs, rhs) with
    | None -> "none"
    | Some (vs, ans_typ) ->
      pr_to_str pr_formula
        (to_formula ans_typ) in
  assert_equal ~printer:(fun x -> x)
    ~msg:(lhs_m^" ⟹ "^rhs_m) res ans

(* tb-t6; ta-t3; tc-t7; td-t9; tf-t10; te-t13; tg-t15; th-t16;
   tj-t22; ti-t19; tk-t24; tn-t34; to-t31; tl-t25; tm-t28 *)
let lhs1 = "(Term tb) = ta ∧ Int = tb"
let rhs1 = "tc = Int"
let lhs2 = "(Term td) = ta ∧ Bool = td"
let rhs2 = "tf = Bool ∧ te = (Term Int → Int)"
let lhs3 = "(Term tg) = ta ∧ Int = tg"
let rhs3 = "th = Int ∧ tj = (Term Int → Int)"
let lhs4 = "(Term tg) = ta ∧ Int = tg"
let rhs4 =
  "th = Int ∧ tj = (Term Int → Int) ∧ ti = (Term Int → Int)"
let lhs5 = "(Term tk) = ta"
let rhs5 = "tn = (Term Bool → Bool) ∧
    to = (Term tk → tl) ∧ tm = (Term tk → tl)"



let tests = "Abduction" >::: [

  "simple abduction: eval" >::
    (fun () ->
      Terms.reset_counters ();
      Infer.reset_counters ();
      try
        test_simple lhs1 rhs1 0 "tb = tc";
        test_simple lhs1 rhs1 1 "ta = (Term tc)";
        test_simple lhs1 rhs1 2 "tc = Int";
        test_simple lhs2 rhs2 0 "td = tf ∧
te = (Term Int → Int)";
        test_simple lhs2 rhs2 1 "ta = (Term tf) ∧
te = (Term Int → Int)";
test_simple lhs2 rhs2 2 "te = (Term Int → Int) ∧
tf = Bool";
        test_simple lhs3 rhs3 0 "tg = th ∧
tj = (ta → th)";
        test_simple lhs3 rhs3 2 "tg = th ∧
tj = (Term th → th)";
        test_simple lhs4 rhs4 0 "tg = th ∧ ti = (ta → th) ∧
tj = (ta → th)";
        test_simple lhs5 rhs5 0 "tm = (ta → tl) ∧ tn = (Term Bool → Bool) ∧
to = (ta → tl)";
      with (Terms.Report_toplevel _ | Terms.Contradiction _) as exn ->
        ignore (Format.flush_str_formatter ());
        Terms.pr_exception Format.str_formatter exn;
        assert_failure (Format.flush_str_formatter ())
    );

  "joint term abduction: eval" >::
    (fun () ->
      Terms.reset_counters ();
      Infer.reset_counters ();
      try
        let lhs1 = p_formula lhs1 and rhs1 = p_formula rhs1 in
        let lhs2 = p_formula lhs2 and rhs2 = p_formula rhs2 in
        let lhs4 = p_formula lhs4 and rhs4 = p_formula rhs4 in
        let lhs5 = p_formula lhs5 and rhs5 = p_formula rhs5 in
        let lhs1, rhs1 = br_simple lhs1 rhs1 in
        let lhs2, rhs2 = br_simple lhs2 rhs2 in
        let lhs4, rhs4 = br_simple lhs4 rhs4 in
        let lhs5, rhs5 = br_simple lhs5 rhs5 in
        let ans =
          match abd_typ cmp_v uni_v
            [lhs1, rhs1; lhs2, rhs2; lhs4, rhs4; lhs5, rhs5] with
            | None -> "none"
            | Some (vs, ans_typ, _) ->
              pr_to_str pr_formula (to_formula ans_typ) in
        assert_equal ~printer:(fun x -> x)
          "" ans
      with (Terms.Report_toplevel _ | Terms.Contradiction _) as exn ->
        ignore (Format.flush_str_formatter ());
        Terms.pr_exception Format.str_formatter exn;
        assert_failure (Format.flush_str_formatter ())
    );

]
