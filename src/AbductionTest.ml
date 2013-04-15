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
    ~msg:(string_of_int skip^":"^lhs_m^" ⟹ "^rhs_m) res ans

(*  *)
let rhs0 = "tres = (Term tc → tb) ∧ ta = (Term tc)"
let lhs1 = "(Term td) = ta ∧ Int = td" and rhs1 = "tb = Int"
let lhs2 = "(Term te) = ta ∧ Bool = te" and rhs2 = "tb = Bool ∧
    tf = (Term Int → Int)"
let lhs3 = "(Term tg) = ta ∧ Int = tg" and rhs3 = "tb = Int ∧
    ti = (Term Int → Int) ∧ th = (Term Int → Int)"
let lhs4 = "(Term tj) = ta" and rhs4 = "tm = (Term Bool → Bool) ∧
    tl = (Term tj → tb) ∧ tk = (Term tj → tb)"
let lhs5 = "(Term tn) = ta ∧ (to, tp) = tn" and rhs5 = "tb = (tq, tr) ∧
    ts = (Term to → tq) ∧ tt = (Term tp → tr)"
let lhs6 = "(Term tu) = ta" and rhs6 = "tx = (ty, tz) ∧ tx = tb ∧
    tw = (Term (tu, tv) → ty, tz)"
let lhs7 = "(tA, tB) = tx ∧ (Term tu) = ta" and rhs7 = "tA = tx"
let lhs8 = "(Term tD) = ta" and rhs8 = "tF = (tH, tI) ∧ tG = tb ∧
    tE = (Term (tC, tD) → tH, tI)"
let lhs9 = "(tJ, tK) = tF ∧ (Term tD) = ta" and rhs9 = "tK = tG"


let tests = "Abduction" >::: [

  "simple abduction: eval" >::
    (fun () ->
      Terms.reset_counters ();
      Infer.reset_counters ();
      try
        test_simple lhs1 rhs1 0 "td = tb";
        test_simple lhs1 rhs1 1 "ta = (Term tb)";
        test_simple lhs1 rhs1 2 "tb = Int";
        test_simple lhs2 rhs2 0 "te = tb ∧
tf = (Term Int → Int)";
        test_simple lhs2 rhs2 1 "ta = (Term tb) ∧
tf = (Term Int → Int)";
test_simple lhs2 rhs2 2 "tb = Bool ∧
tf = (Term Int → Int)";
        test_simple lhs3 rhs3 0 "tg = tb ∧ th = (ta → tb) ∧
ti = (ta → tb)";
        test_simple lhs3 rhs3 2 "tg = tb ∧ th = (Term tb → tb) ∧
ti = (ta → tb)";
        test_simple lhs4 rhs4 0 "tk = (ta → tb) ∧ tl = (ta → tb) ∧
tm = (Term Bool → Bool)";
        (* takes almost 5 seconds!
        test_simple lhs5 rhs5 0 "tb = (tq, tr) ∧ tn = (t14261, t14784) ∧ ts = (Term t14261 → tq) ∧
tt = (Term t14784 → tr)"; *)
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
        let lhs0, rhs0 = [], p_formula rhs0 in
        let lhs1 = p_formula lhs1 and rhs1 = p_formula rhs1 in
        let lhs2 = p_formula lhs2 and rhs2 = p_formula rhs2 in
        let lhs4 = p_formula lhs4 and rhs4 = p_formula rhs4 in
        let lhs5 = p_formula lhs5 and rhs5 = p_formula rhs5 in
        let lhs0, rhs0 = br_simple lhs0 rhs0 in
        let lhs1, rhs1 = br_simple lhs1 rhs1 in
        let lhs2, rhs2 = br_simple lhs2 rhs2 in
        let lhs4, rhs4 = br_simple lhs4 rhs4 in
        let lhs5, rhs5 = br_simple lhs5 rhs5 in
        let ans =
          match abd_typ cmp_v uni_v
            [lhs0, rhs0; lhs1, rhs1;
             lhs2, rhs2; lhs4, rhs4; (* FIXME:
             lhs5, rhs5*)] with
            | None -> "none"
            | Some (vs, ans_typ, _) ->
              pr_to_str pr_formula (to_formula ans_typ) in
        assert_equal ~printer:(fun x -> x)
          "ta = (Term tc) ∧ td = tb ∧ te = tb ∧ tf = (Term Int → Int) ∧
tk = (Term tc → tb) ∧ tl = (Term tc → tb) ∧
tm = (Term Bool → Bool) ∧
tres = (Term tc → tb)" (* ... *) ans
      with (Terms.Report_toplevel _ | Terms.Contradiction _) as exn ->
        ignore (Format.flush_str_formatter ());
        Terms.pr_exception Format.str_formatter exn;
        assert_failure (Format.flush_str_formatter ())
    );

]
