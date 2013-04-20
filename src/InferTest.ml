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
      Terms.reset_state ();
      Infer.reset_state ();
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
        let preserve, cn = infer_prog_mockup prog in
        (* Format.printf "cn:@\n%a@\n" pr_cnstrnt cn; *)
        let cmp_v, uni_v, brs = normalize cn in
        let uni_v v =
          try Hashtbl.find uni_v v with Not_found -> false in
        let brs = simplify preserve cmp_v uni_v brs in
        ignore (Format.flush_str_formatter ());
        pr_brs Format.str_formatter brs;
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
| (Term t35) = t3 ∧ (t36, t37) = t35 ∧ 𝛘1(t1) ⟹ t4 = (t38, t39) ∧
    t41 = (Term t36 → t38) ∧ t43 = (Term t37 → t39) ∧ 𝛘1(t41) ∧
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
      Terms.reset_state ();
      Infer.reset_state ();
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
  efunction LNil -> LNil
    | LCons (x, l) -> match f x with
          True -> LCons (x, filter l)
	| False -> filter l") in
      try
        let prog = Terms.infer_sorts prog in
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

  "constraints: equal with assert and test" >::
    (fun () ->
      Terms.reset_state ();
      Infer.reset_state ();
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
        let preserve, cn = infer_prog_mockup prog in
        let cmp_v, uni_v, brs = normalize cn in
        let uni_v v =
          try Hashtbl.find uni_v v with Not_found -> false in
        let brs = simplify preserve cmp_v uni_v brs in
        ignore (Format.flush_str_formatter ());
        pr_brs Format.str_formatter brs;
        assert_equal ~printer:(fun x -> x)
" ⟹ t107 = (Ty Int, Ty (List Int) → Int → List t98 → Bool) ∧
  𝛘1(t2) ∧ 𝛘1(t107)
| 𝛘1(t1) ⟹ t1 = (Ty t7, Ty t8 → Bool) ∧ t3 = (Ty t7, Ty t8) ∧
    t4 = Bool
| (t9, t10) = t3 ∧ (Ty t11) = t9 ∧ Int = t11 ∧ (Ty t12) = t10 ∧
    Int = t12 ∧ 𝛘1(t1) ⟹ t4 = (Int → Int → Bool)
| (t27, t28) = t3 ∧ (Ty t29) = t27 ∧ (t30, t31) = t29 ∧
    (Ty t32) = t28 ∧ (t33, t34) = t32 ∧ 𝛘1(t1) ⟹
    t4 = (t37, t38 → t36) ∧ t35 = (t37, t38)
| (t39, t40) = t35 ∧ (t27, t28) = t3 ∧ (Ty t29) = t27 ∧
    (t30, t31) = t29 ∧ (Ty t32) = t28 ∧ (t33, t34) = t32 ∧ 𝛘1(t1)
    ⟹ t36 = (t43, t44 → t42) ∧ t41 = (t43, t44)
| (t45, t46) = t41 ∧ (t39, t40) = t35 ∧ (t27, t28) = t3 ∧
    (Ty t29) = t27 ∧ (t30, t31) = t29 ∧ (Ty t32) = t28 ∧
    (t33, t34) = t32 ∧ 𝛘1(t1) ⟹ t42 = Bool ∧
    t60 = (Ty t30, Ty t33 → t39 → t45 → Bool) ∧
    t53 = (Ty t31, Ty t34 → t40 → t46 → Bool) ∧ 𝛘1(t60) ∧
    𝛘1(t53)
| (t67, t68) = t3 ∧ (Ty t69) = t67 ∧ (List t70) = t69 ∧
    (Ty t71) = t68 ∧ (List t72) = t71 ∧ 𝛘1(t1) ⟹
    t4 = (List t78 → List t79 → Bool) ∧
    t77 = (Ty t70, Ty t72 → t78 → t79 → Bool) ∧ 𝛘1(t77)
| (t85, t86) = t3 ∧ (Ty t87) = t85 ∧ Int = t87 ∧ (Ty t88) = t86 ∧
    (List t89) = t88 ∧ 𝛘1(t1) ⟹ t4 = (List t92 → t94 → Bool) ∧
    t90 = (List t92)
| (List t93) = t90 ∧ (t85, t86) = t3 ∧ (Ty t87) = t85 ∧ Int = t87 ∧
    (Ty t88) = t86 ∧ (List t89) = t88 ∧ 𝛘1(t1) ⟹ FALSE"
          (Format.flush_str_formatter ());
      with (Terms.Report_toplevel _ | Terms.Contradiction _) as exn ->
        ignore (Format.flush_str_formatter ());
        Terms.pr_exception Format.str_formatter exn;
        assert_failure (Format.flush_str_formatter ())
    );
]
