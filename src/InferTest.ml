(** Inferring and normalizing formulas tests for InvarGenT.

    Released under the GNU General Public Licence (version 2 or
    higher), NO WARRANTY of correctness etc. (C) Lukasz Stafiniak 2013
    @author Lukasz Stafiniak lukstafi (AT) gmail.com
    @since Mar 2013
*)
open OUnit
open Infer

let tests = "Infer" >::: [

  "constraints: eval" >::
    (fun () ->
      Terms.reset_counters ();
      Infer.reset_counters ();
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
        let prog = Terms.infer_sorts prog in
        let cn = infer_prog_mockup prog in
        let cmp_v, uni_v, brs = normalize cn in
        ignore (Format.flush_str_formatter ());
        pr_brs Format.str_formatter brs;
        assert_equal ~printer:(fun x -> x)
" ⟹ 𝛘1(t2)
| 𝛘1(t1) ⟹ t1 = (Term t5 → Ex1 t4) ∧ t3 = (Term t5) ∧ t8 = t5 ∧
    t14 = t5 ∧ t23 = t5 ∧ t36 = t5 ∧ t49 = t5 ∧ t64 = t5
| (Term t6) = t3 ∧ Int = t6 ∧ 𝛘1(t1) ⟹ t7 = Int ∧ 𝛘2(t4, t7)
| (Term t9) = t3 ∧ Bool = t9 ∧ 𝛘1(t1) ⟹ t11 = Int ∧ t10 = Bool ∧
    t13 = (Term Int → Int) ∧ t12 = (Term Int) ∧ 𝛘2(t4, t10) ∧
    𝛘1(t13)
| (Term t15) = t3 ∧ Int = t15 ∧ 𝛘1(t1) ⟹ t20 = Int ∧ t17 = Int ∧
    t16 = Int ∧ t22 = (Term Int → Int) ∧ t21 = (Term Int) ∧
    t19 = (Term Int → Int) ∧ t18 = (Term Int) ∧ 𝛘2(t4, t16) ∧
    𝛘1(t22) ∧ 𝛘1(t19)
| (Term t24) = t3 ∧ 𝛘1(t1) ⟹ t32 = Bool ∧ t35 = t25 ∧
    t29 = t25 ∧ t26 = t25 ∧ t34 = (Term Bool → Bool) ∧
    t33 = (Term Bool) ∧ t31 = (Term t24 → t25) ∧ t30 = (Term t24) ∧
    t28 = (Term t24 → t25) ∧ t27 = (Term t24) ∧ 𝛘2(t4, t25) ∧
    𝛘1(t34) ∧ 𝛘1(t31) ∧ 𝛘1(t28)
| (Term t39) = t3 ∧ (t40, t41) = t39 ∧ 𝛘1(t1) ⟹ t42 = (t43, t44) ∧
    t46 = (Term t40 → t43) ∧ t45 = (Term t40) ∧
    t48 = (Term t41 → t44) ∧ t47 = (Term t41) ∧ 𝛘2(t4, t42) ∧
    𝛘1(t46) ∧ 𝛘1(t48)
| (Term t51) = t3 ∧ 𝛘1(t1) ⟹ t57 = (t59, t60) ∧ t58 = t53 ∧
    t54 = (t59, t60) ∧ t56 = (Term (t51, t52) → t59, t60) ∧
    t55 = (Term (t51, t52)) ∧ 𝛘2(t4, t53) ∧ 𝛘1(t56)
| (t61, t62) = t57 ∧ (Term t51) = t3 ∧ 𝛘1(t1) ⟹ t61 = t58
| (Term t66) = t3 ∧ 𝛘1(t1) ⟹ t71 = (t73, t74) ∧ t72 = t67 ∧
    t68 = (t73, t74) ∧ t70 = (Term (t65, t66) → t73, t74) ∧
    t69 = (Term (t65, t66)) ∧ 𝛘2(t4, t67) ∧ 𝛘1(t70)
| (t75, t76) = t71 ∧ (Term t66) = t3 ∧ 𝛘1(t1) ⟹ t76 = t72"
          (Format.flush_str_formatter ());
      with (Terms.Report_toplevel _ | Terms.Contradiction _) as exn ->
        ignore (Format.flush_str_formatter ());
        Terms.pr_exception Format.str_formatter exn;
        assert_failure (Format.flush_str_formatter ())
    );

  "constraints: filter" >::
    (fun () ->
      Terms.reset_counters ();
      Infer.reset_counters ();
      let prog = Parser.program Lexer.token
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
  function LNil -> LNil
    | LCons (x, l) -> match f x with
          True -> LCons (x, filter l)
	| False -> filter l") in
      try
        let prog = Terms.infer_sorts prog in
        let cn = infer_prog_mockup prog in
        (* Format.printf "cn:@\n%a@\n" pr_cnstrnt cn; *)
        let cmp_v, uni_v, brs = normalize cn in
        ignore (Format.flush_str_formatter ());
        pr_brs Format.str_formatter brs;
        assert_equal ~printer:(fun x -> x)
" ⟹ 𝛘1(t2)
| 𝛘1(t1) ⟹ t1 = (List (t6, n5) → Ex1 t4) ∧ t3 = (List (t6, n5)) ∧
    t13 = t6 ∧ n12 = n5
| (List (t8, n7)) = t3 ∧ 0 = n7 ∧ 𝛘1(t1) ⟹
    t9 = (List (t11, n10)) ∧ 0 = n10 ∧ 𝛘2(t4, t9)
| (List (t16, n15)) = t3 ∧ (n17 + 1) = n15 ∧ 𝛘1(t1) ⟹ t21 = Bool ∧
    t22 = t18 ∧ t19 = Bool ∧ t20 = Bar ∧ t16 = Bar ∧ 𝛘2(t4, t18)
| Bool = t21 ∧ (List (t16, n15)) = t3 ∧ (n17 + 1) = n15 ∧ 𝛘1(t1) ⟹
    t22 = (List (t16, n23)) ∧ t24 = t16 ∧
    t27 = (List (t16, n17) → List (t16, n25)) ∧
    t26 = (List (t16, n17)) ∧ (n25 + 1) = n23 ∧ 𝛘1(t27)
| Bool = t21 ∧ (List (t16, n15)) = t3 ∧ (n17 + 1) = n15 ∧ 𝛘1(t1) ⟹
    t29 = (List (t16, n17) → t22) ∧ t28 = (List (t16, n17)) ∧
    𝛘1(t29)"
          (Format.flush_str_formatter ());
      with (Terms.Report_toplevel _ | Terms.Contradiction _) as exn ->
        ignore (Format.flush_str_formatter ());
        Terms.pr_exception Format.str_formatter exn;
        assert_failure (Format.flush_str_formatter ())
    );

  "constraints: equal with assert and test" >::
    (fun () ->
      Terms.reset_counters ();
      Infer.reset_counters ();
      let prog = Parser.program Lexer.token
	(Lexing.from_string
"newtype Ty : type
newtype Int
newtype List : type
newcons Zero : Int
newcons Nil : ∀a. List a
newcons TInt : Ty Int
newcons TPair : ∀a, b. Ty a * Ty b ⟶ Ty (a, b)
newcons TList : ∀a. Ty a ⟶ Ty (List a)
newtype Bool
newcons True : Bool
newcons False : Bool
external eq_int : Int → Int → Bool
external b_and : Bool → Bool → Bool
external b_not : Bool → Bool
external forall2 : ∀a, b. (a → b → Bool) → List a → List b → Bool

let rec equal = function
  | TInt, TInt -> fun x y -> eq_int x y
  | TPair (t1, t2), TPair (u1, u2) ->  
    (fun (x1, x2) (y1, y2) ->
        b_and (equal (t1, u1) x1 y1)
              (equal (t2, u2) x2 y2))
  | TList t, TList u -> forall2 (equal (t, u))
  | TInt, TList l ->
    (function Nil -> assert false
    | _ -> fun _ -> False)
  | _ -> False
test b_not (equal (TInt, TList TInt) Zero Nil)") in
      try
        let prog = Terms.infer_sorts prog in
        let cn = infer_prog_mockup prog in
        let cmp_v, uni_v, brs = normalize cn in
        ignore (Format.flush_str_formatter ());
        pr_brs Format.str_formatter brs;
        assert_equal ~printer:(fun x -> x)
" ⟹ t103 = Bool ∧
  t114 = (Ty Int, Ty (List Int) → Int → List t105 → Bool) ∧
  t107 = (Ty Int, Ty (List Int)) ∧ t108 = (Ty Int) ∧ t110 = Int ∧
  t109 = (Ty (List Int)) ∧ t111 = (List Int) ∧ t113 = Int ∧
  t112 = Int ∧ t106 = Int ∧ t104 = (List t105) ∧ 𝛘1(t2) ∧
  𝛘1(t114)
| 𝛘1(t1) ⟹ t1 = (Ty t7, Ty t8 → Ex2 t4) ∧ t3 = (Ty t7, Ty t8) ∧
    t5 = (Ty t7) ∧ t6 = (Ty t8) ∧ t20 = (Ty t7) ∧ t21 = (Ty t8) ∧
    t22 = t7 ∧ t25 = t8 ∧ t63 = (Ty t7) ∧ t64 = (Ty t8) ∧
    t65 = t7 ∧ t67 = t8 ∧ t83 = (Ty t7) ∧ t84 = (Ty t8) ∧
    t85 = t7 ∧ t86 = t8 ∧ t102 = Bool ∧ 𝛘2(t4, t102)
| (t9, t10) = t3 ∧ (Ty t11) = t9 ∧ Int = t11 ∧ (Ty t12) = t10 ∧
    Int = t12 ∧ 𝛘1(t1) ⟹ t13 = (Int → Int → Bool) ∧
    t15 = (Int → Bool) ∧ t19 = Int ∧ t18 = Int ∧ t17 = Bool ∧
    t14 = Int ∧ t16 = Int ∧ 𝛘2(t4, t13)
| (t28, t29) = t3 ∧ (Ty t30) = t28 ∧ (t31, t32) = t30 ∧
    (Ty t33) = t29 ∧ (t34, t35) = t33 ∧ 𝛘1(t1) ⟹
    t36 = (t39, t40 → t38) ∧ t37 = (t39, t40) ∧ 𝛘2(t4, t36)
| (t41, t42) = t37 ∧ (t28, t29) = t3 ∧ (Ty t30) = t28 ∧
    (t31, t32) = t30 ∧ (Ty t33) = t29 ∧ (t34, t35) = t33 ∧ 𝛘1(t1)
    ⟹ t38 = (t45, t46 → t44) ∧ t43 = (t45, t46)
| (t47, t48) = t43 ∧ (t41, t42) = t37 ∧ (t28, t29) = t3 ∧
    (Ty t30) = t28 ∧ (t31, t32) = t30 ∧ (Ty t33) = t29 ∧
    (t34, t35) = t33 ∧ 𝛘1(t1) ⟹ t56 = Bool ∧ t49 = Bool ∧
    t44 = Bool ∧ t62 = (Ty t31, Ty t34 → t41 → t47 → Bool) ∧
    t59 = (Ty t31, Ty t34) ∧ t60 = (Ty t31) ∧ t61 = (Ty t34) ∧
    t58 = t41 ∧ t57 = t47 ∧
    t55 = (Ty t32, Ty t35 → t42 → t48 → Bool) ∧
    t52 = (Ty t32, Ty t35) ∧ t53 = (Ty t32) ∧ t54 = (Ty t35) ∧
    t51 = t42 ∧ t50 = t48 ∧ 𝛘1(t62) ∧ 𝛘1(t55)
| (t69, t70) = t3 ∧ (Ty t71) = t69 ∧ (List t72) = t71 ∧
    (Ty t73) = t70 ∧ (List t74) = t73 ∧ 𝛘1(t1) ⟹
    t76 = (t81 → t82 → Bool) ∧
    t75 = (List t81 → List t82 → Bool) ∧
    t80 = (Ty t72, Ty t74 → t81 → t82 → Bool) ∧
    t77 = (Ty t72, Ty t74) ∧ t78 = (Ty t72) ∧ t79 = (Ty t74) ∧
    𝛘2(t4, t75) ∧ 𝛘1(t80)
| (t88, t89) = t3 ∧ (Ty t90) = t88 ∧ Int = t90 ∧ (Ty t91) = t89 ∧
    (List t92) = t91 ∧ 𝛘1(t1) ⟹ t93 = (List t96 → Ex1 t95) ∧
    t94 = (List t96) ∧ t99 = (t100 → Bool) ∧ t101 = Bool ∧
    𝛘2(t4, t93) ∧ 𝛘3(t95, t99)
| (List t97) = t94 ∧ (t88, t89) = t3 ∧ (Ty t90) = t88 ∧ Int = t90 ∧
    (Ty t91) = t89 ∧ (List t92) = t91 ∧ 𝛘1(t1) ⟹ 𝛘3(t95, t98) ∧
    FALSE"
          (Format.flush_str_formatter ());
      with (Terms.Report_toplevel _ | Terms.Contradiction _) as exn ->
        ignore (Format.flush_str_formatter ());
        Terms.pr_exception Format.str_formatter exn;
        assert_failure (Format.flush_str_formatter ())
    );
]
