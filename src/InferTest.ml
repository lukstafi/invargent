(** Inferring and normalizing formulas tests for InvarGenT.

    Released under the GNU General Public Licence (version 2 or
    higher), NO WARRANTY of correctness etc. (C) Lukasz Stafiniak 2013
    @author Lukasz Stafiniak lukstafi (AT) gmail.com
    @since Mar 2013
*)
open OUnit
open Infer
open Aux

let tests = "Infer" >::: [

  "constraints: eval" >::
    (fun () ->
      Terms.reset_state ();
      Infer.reset_state ();
      let prog = (normalize_program % Parser.program Lexer.token)
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
        let preserve, cn = infer_prog_mockup prog in
        (* Format.printf "cn:@\n%a@\n" pr_cnstrnt cn; *)
        let cmp_v, uni_v, brs = normalize cn in
        let uni_v v =
          try Hashtbl.find uni_v v with Not_found -> false in
        let sbrs = simplify preserve cmp_v uni_v brs in
        ignore (Format.flush_str_formatter ());
        pr_brs Format.str_formatter sbrs;
        assert_equal ~printer:(fun x -> x)
" ⟹ 𝛘1(t2)
| 𝛘1(t1) ⟹ t1 = (Term t5 → t4) ∧ t3 = (Term t5)
| (Term t6) = t3 ∧ Int = t6 ∧ 𝛘1(t1) ⟹ t4 = Int
| (Term t8) = t3 ∧ Bool = t8 ∧ 𝛘1(t1) ⟹ t4 = Bool ∧
    t11 = (Term Int → Int) ∧ 𝛘1(t11)
| (Term t13) = t3 ∧ Int = t13 ∧ 𝛘1(t1) ⟹ t4 = Int ∧
    t19 = (Term Int → Int) ∧ t16 = (Term Int → Int) ∧ 𝛘1(t19) ∧
    𝛘1(t16)
| (Term t21) = t3 ∧ 𝛘1(t1) ⟹ t30 = (Term Bool → Bool) ∧
    t27 = (Term t21 → t4) ∧ t24 = (Term t21 → t4) ∧ 𝛘1(t30) ∧
    𝛘1(t27) ∧ 𝛘1(t24)
| (Term t37) = t3 ∧ (t35, t36) = t37 ∧ 𝛘1(t1) ⟹ t4 = (t38, t39) ∧
    t41 = (Term t35 → t38) ∧ t43 = (Term t36 → t39) ∧ 𝛘1(t41) ∧
    𝛘1(t43)
| (Term t46) = t3 ∧ 𝛘1(t1) ⟹ t51 = (t53, t54) ∧ t52 = t4 ∧
    t50 = (Term (t46, t47) → t53, t54) ∧ 𝛘1(t50)
| (t55, t56) = t51 ∧ (Term t46) = t3 ∧ 𝛘1(t1) ⟹ t55 = t52
| (Term t60) = t3 ∧ 𝛘1(t1) ⟹ t64 = (t66, t67) ∧ t65 = t4 ∧
    t63 = (Term (t59, t60) → t66, t67) ∧ 𝛘1(t63)
| (t68, t69) = t64 ∧ (Term t60) = t3 ∧ 𝛘1(t1) ⟹ t69 = t65"
          (Format.flush_str_formatter ());
      with (Terms.Report_toplevel _ | Terms.Contradiction _) as exn ->
        ignore (Format.flush_str_formatter ());
        Terms.pr_exception Format.str_formatter exn;
        assert_failure (Format.flush_str_formatter ())
    );

  "constraints: filter" >::
    (fun () ->
      todo "numeric";
      Terms.reset_state ();
      Infer.reset_state ();
      let prog = (normalize_program % Parser.program Lexer.token)
	(Lexing.from_string
"newtype Bool
newtype List : type * num
newcons True : Bool
newcons False : Bool
newcons LNil : ∀a. List(a, 0)
newcons LCons : ∀n, a. a * List(a, n) ⟶ List(a, n+1)

newtype Bar
external f : Bar → Bool

let rec filter =
  efunction LNil -> LNil
    | LCons (x, l) -> match f x with
          True -> LCons (x, filter l)
	| False -> filter l") in
      try
        let preserve, cn = infer_prog_mockup prog in
        let cmp_v, uni_v, brs = normalize cn in
        let uni_v v =
          try Hashtbl.find uni_v v with Not_found -> false in
        let brs = simplify preserve cmp_v uni_v brs in
        (* Format.printf "cn:@\n%a@\n" pr_cnstrnt cn; *)
        ignore (Format.flush_str_formatter ());
        pr_brs Format.str_formatter brs;
        assert_equal ~printer:(fun x -> x)
" ⟹ 𝛘1(t2)
| 𝛘1(t1) ⟹ t1 = (List (t6, n5) → Ex1 t4) ∧ t3 = (List (t6, n5))
| (List (t8, n7)) = t3 ∧ 0 = n7 ∧ 𝛘1(t1) ⟹
    t9 = (List (t11, n10)) ∧ 0 = n10 ∧ 𝛘2(t4, t9)
| (List (t16, n15)) = t3 ∧ (n17 + 1) = n15 ∧ 𝛘1(t1) ⟹ t21 = Bool ∧
    t22 = t18 ∧ t16 = Bar ∧ 𝛘2(t4, t18)
| Bool = t21 ∧ (List (t16, n15)) = t3 ∧ (n17 + 1) = n15 ∧ 𝛘1(t1) ⟹
    t22 = (List (t16, n23)) ∧
    t27 = (List (t16, n17) → List (t16, n25)) ∧ (n25 + 1) = n23 ∧
    𝛘1(t27)
| Bool = t21 ∧ (List (t16, n15)) = t3 ∧ (n17 + 1) = n15 ∧ 𝛘1(t1) ⟹
    t29 = (List (t16, n17) → t22) ∧ 𝛘1(t29)"
          (Format.flush_str_formatter ());
      with (Terms.Report_toplevel _ | Terms.Contradiction _) as exn ->
        ignore (Format.flush_str_formatter ());
        Terms.pr_exception Format.str_formatter exn;
        assert_failure (Format.flush_str_formatter ())
    );

]
