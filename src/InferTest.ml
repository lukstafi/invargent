(** Inferring and normalizing formulas tests for InvarGenT.

    Released under the GNU General Public Licence (version 2 or
    higher), NO WARRANTY of correctness etc. (C) Lukasz Stafiniak 2013
    @author Lukasz Stafiniak lukstafi (AT) gmail.com
    @since Mar 2013
*)
open OUnit
open Infer

let tests = "Infer" >::: [
  "generating constraints" >::
    (fun () ->
      Terms.extype_id := 0;
      let prog = Parser.program Lexer.token
	(Lexing.from_string
"newtype Term : type
newtype Int
newtype Bool

external plus : Int → Int → Int
external is_zero : Int → Bool
external if : ∀a. Bool → a → a → a

newcons Lit : Int ⟶ Term Int
newcons Plus : Term Int * Term Int ⟶ Term Int
newcons IsZero : Term Int ⟶ Term Bool
newcons If : ∀a. Term Bool * Term a * Term a ⟶ Term a
newcons Pair : ∀a, b. Term a * Term b ⟶ Term (a, b)
newcons Fst : ∀a, b. Term (a, b) ⟶ Term a
newcons Snd : ∀a, b. Term (a, b) ⟶ Term b

let rec eval = function
  | Lit i -> i
  | IsZero x -> is_zero (eval x)
  | Plus (x, y) -> plus (eval x) (eval y)
  | If (b, t, e) -> if (eval b) (eval t) (eval e)
  | Pair (x, y) -> eval x, eval y
  | Fst p -> (match eval p with x, y -> x)
  | Snd p -> (match eval p with x, y -> y)") in
      try
        let cn = infer_prog_mockup prog in
        let cmp_v, uni_v, brs = normalize cn in
        ignore (Format.flush_str_formatter ());
        pr_brs Format.str_formatter brs;
        assert_equal ~printer:(fun x -> x)
" ⟹ 𝛘1(t2)
| 𝛘1(t1) ⟹ t1 = (t3 → Ex1 t4) ∧ t3 = (Term Int) ∧
    t3 = (Term Bool) ∧ t3 = (Term Int) ∧ t3 = (Term u17) ∧
    t3 = (Term (u30, u31)) ∧ t3 = (Term u41) ∧ t3 = (Term u56)
| (Term Int) = t3 ∧ 𝛘1(t1) ⟹ t5 = Int ∧ 𝛘2(t4, t5)
| (Term Bool) = t3 ∧ 𝛘1(t1) ⟹ t7 = Int ∧ t6 = Bool ∧
    t9 = (t8 → t7) ∧ t8 = (Term Int) ∧ 𝛘2(t4, t6) ∧ 𝛘1(t9)
| (Term Int) = t3 ∧ 𝛘1(t1) ⟹ t14 = Int ∧ t11 = Int ∧ t10 = Int ∧
    t16 = (t15 → t14) ∧ t15 = (Term Int) ∧ t13 = (t12 → t11) ∧
    t12 = (Term Int) ∧ 𝛘2(t4, t10) ∧ 𝛘1(t16) ∧ 𝛘1(t13)
| (Term u18) = t3 ∧ 𝛘1(t1) ⟹ t26 = Bool ∧ u29 = t23 ∧
    u29 = t20 ∧ u29 = t19 ∧ t28 = (t27 → t26) ∧ t27 = (Term Bool) ∧
    t25 = (t24 → t23) ∧ t24 = (Term u18) ∧ t22 = (t21 → t20) ∧
    t21 = (Term u18) ∧ 𝛘2(t4, t19) ∧ 𝛘1(t28) ∧ 𝛘1(t25) ∧
    𝛘1(t22)
| (Term (u32, u33)) = t3 ∧ 𝛘1(t1) ⟹ t34 = (t35, t36) ∧
    t38 = (t37 → t35) ∧ t37 = (Term u32) ∧ t40 = (t39 → t36) ∧
    t39 = (Term u33) ∧ 𝛘2(t4, t34) ∧ 𝛘1(t38) ∧ 𝛘1(t40)
| (Term u43) = t3 ∧ 𝛘1(t1) ⟹ t49 = t46 ∧ t50 = t45 ∧
    t49 = (t51, t52) ∧ t48 = (t47 → t46) ∧ t47 = (Term (u43, u44)) ∧
    𝛘2(t4, t45) ∧ 𝛘1(t48)
| (t53, t54) = t49 ∧ (Term u43) = t3 ∧ 𝛘1(t1) ⟹ t53 = t50
| (Term u58) = t3 ∧ 𝛘1(t1) ⟹ t63 = t60 ∧ t64 = t59 ∧
    t63 = (t65, t66) ∧ t62 = (t61 → t60) ∧ t61 = (Term (u57, u58)) ∧
    𝛘2(t4, t59) ∧ 𝛘1(t62)
| (t67, t68) = t63 ∧ (Term u58) = t3 ∧ 𝛘1(t1) ⟹ t68 = t64"
          (Format.flush_str_formatter ());
      with (Terms.Report_toplevel _ | Terms.Contradiction _) as exn ->
        ignore (Format.flush_str_formatter ());
        Terms.pr_exception Format.str_formatter exn;
        assert_failure (Format.flush_str_formatter ())
    );
]
