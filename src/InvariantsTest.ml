(** Solving second-order i.e. formula variables tests for InvarGenT.

    Released under the GNU General Public Licence (version 2 or
    higher), NO WARRANTY of correctness etc. (C) Lukasz Stafiniak 2013
    @author Lukasz Stafiniak lukstafi (AT) gmail.com
    @since Mar 2013
*)
open OUnit
open Terms
open Aux

let test_case msg test result chi residuum =
      Terms.reset_state ();
      Infer.reset_state ();
      let prog = Parser.program Lexer.token
	(Lexing.from_string test) in
      try
        let prog = Terms.infer_sorts prog in
        let preserve, cn = Infer.infer_prog_mockup prog in
        Format.printf "cn: %s@\n%a@\n%!" msg Infer.pr_cnstrnt cn; (* *)
        let cmp_v, uni_v, brs = Infer.normalize cn in
        Format.printf "brs: %s@\n%a@\n%!" msg Infer.pr_brs brs; (* *)
        let uni_v v =
          try Hashtbl.find uni_v v with Not_found -> false in
        let brs = Infer.simplify preserve cmp_v uni_v brs in
        Format.printf "simpl-brs: %s@\n%a@\n%!" msg Infer.pr_brs brs;
        (* *)
        let brs = List.map Infer.br_to_formulas brs in
        let _, _, (sol_res, sol_chi) =
          Invariants.solve cmp_v uni_v brs in
        let vs, ans = List.assoc chi sol_chi in
        ignore (Format.flush_str_formatter ());
        Format.fprintf Format.str_formatter "@[<2>∃%a.@ %a@]"
          (pr_sep_list "," pr_tyvar) vs pr_formula ans;
        assert_equal ~printer:(fun x -> x)
          result
          (Format.flush_str_formatter ());
        ignore (Format.flush_str_formatter ());
        Format.fprintf Format.str_formatter "@[<2>%a@]"
          pr_formula sol_res;
        assert_equal ~printer:(fun x -> x)
          residuum
          (Format.flush_str_formatter ());
      with (Terms.Report_toplevel _ | Terms.Contradiction _) as exn ->
        ignore (Format.flush_str_formatter ());
        Terms.pr_exception Format.str_formatter exn;
        assert_failure (Format.flush_str_formatter ())

let tests = "Invariants" >::: [

  "eval" >::
    (fun () ->
      todo "debug";
      test_case "eval term"
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
  | Snd p -> (match eval p with x, y -> y)"

        "∃t78. δ = (Term t78 → t78)" 1
        "t3 = (Term t78) ∧ t2 = (Term t79 → t79) ∧ t4 = t78 ∧ t5 = t78 ∧
  t11 = (Term Int → Int) ∧ t16 = (Term Int → Int) ∧
  t19 = (Term Int → Int) ∧ t24 = (Term t21 → t21) ∧
  t27 = (Term t21 → t21) ∧ t30 = (Term Bool → Bool) ∧ t38 = t36 ∧
  t39 = t37 ∧ t41 = (Term t36 → t36) ∧ t43 = (Term t37 → t37) ∧
  t50 = (Term (t46, t47) → t46, t47) ∧ t51 = (t46, t47) ∧ t52 = t46 ∧
  t53 = t46 ∧ t54 = t47 ∧ t63 = (Term (t59, t60) → t59, t60) ∧
  t64 = (t59, t60) ∧ t65 = t60 ∧ t66 = t59 ∧ t67 = t60 ∧
  t80 = Int ∧ t81 = Int ∧ t82 = Int ∧ t83 = Bool ∧ t84 = t21 ∧
  t85 = t21 ∧ t86 = t36 ∧ t87 = t37 ∧ t88 = (t46, t47) ∧
  t89 = (t59, t60)"
(*
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
*)
    );

  "filter" >::
    (fun () ->
      todo "existential";
      test_case "list filter"
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
	| False -> filter l"
        "" 1
        ""
(*
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
*)
    );

  "equal with test" >::
    (fun () ->
      todo "debug";
      test_case "equal terms"
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
  | _ -> fun _ _ -> False
test b_not (equal (TInt, TList TInt) Zero Nil)"
        "∃t140, t141. δ = (Ty t140, Ty t141 → t140 → t141 → Bool)" 1
        "t4 = (t140 → t141 → Bool) ∧ t3 = (Ty t140, Ty t141) ∧
  t2 = (Ty t104, Ty t105 → t104 → t105 → Bool) ∧ t7 = t140 ∧
  t8 = t141 ∧ t35 = (t30, t31) ∧ t36 = (t33, t34 → Bool) ∧
  t37 = t30 ∧ t38 = t31 ∧ t41 = (t33, t34) ∧ t42 = Bool ∧
  t43 = t33 ∧ t44 = t34 ∧
  t53 = (Ty t31, Ty t34 → t31 → t34 → Bool) ∧
  t60 = (Ty t30, Ty t33 → t30 → t33 → Bool) ∧
  t77 = (Ty t70, Ty t72 → t70 → t72 → Bool) ∧ t78 = t70 ∧
  t79 = t72 ∧ t80 = t140 ∧ t82 = t141 ∧ t86 = Int ∧
  t95 = (Ty Int, Ty (List Int) → Int → List Int → Bool) ∧
  t106 = Int ∧ t107 = (List Int) ∧ t108 = t30 ∧ t109 = t33 ∧
  t110 = t31 ∧ t111 = t34 ∧ t112 = t70 ∧ t113 = t72";
    );

  "equal with assert" >::
    (fun () ->
      todo "debug";
      test_case "equal terms"
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
  | _ -> fun _ _ -> False
  | TInt, TList l -> (function Nil -> assert false)
  | TList l, TInt -> (fun _ -> function Nil -> assert false)"
        "∃t156, t157. δ = (Ty t156, Ty t157 → t156 → t157 → Bool)" 1
        "t4 = (t156 → t157 → Bool) ∧ t3 = (Ty t156, Ty t157) ∧
  t2 = (Ty t122, Ty t123 → t122 → t123 → Bool) ∧ t7 = t156 ∧
  t8 = t157 ∧ t35 = (t30, t31) ∧ t36 = (t33, t34 → Bool) ∧
  t37 = t30 ∧ t38 = t31 ∧ t41 = (t33, t34) ∧ t42 = Bool ∧
  t43 = t33 ∧ t44 = t34 ∧
  t53 = (Ty t31, Ty t34 → t31 → t34 → Bool) ∧
  t60 = (Ty t30, Ty t33 → t30 → t33 → Bool) ∧
  t77 = (Ty t70, Ty t72 → t70 → t72 → Bool) ∧ t78 = t70 ∧
  t79 = t72 ∧ t80 = t156 ∧ t82 = t157 ∧ t124 = t30 ∧ t125 = t33 ∧
  t126 = t31 ∧ t127 = t34 ∧ t128 = t70 ∧ t129 = t72";
    );

  "equal with assert and test" >::
    (fun () ->
      todo "debug";
      test_case "equal terms"
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
  | _ -> fun _ _ -> False
  | TInt, TList l -> (function Nil -> assert false)
  | TList l, TInt -> (fun _ -> function Nil -> assert false)
test b_not (equal (TInt, TList TInt) Zero Nil)"
        "∃t170, t171. δ = (Ty t170, Ty t171 → t170 → t171 → Bool)" 1
        "t4 = (t170 → t171 → Bool) ∧ t3 = (Ty t170, Ty t171) ∧
  t2 = (Ty t134, Ty t135 → t134 → t135 → Bool) ∧ t7 = t170 ∧
  t8 = t171 ∧ t35 = (t30, t31) ∧ t36 = (t33, t34 → Bool) ∧
  t37 = t30 ∧ t38 = t31 ∧ t41 = (t33, t34) ∧ t42 = Bool ∧
  t43 = t33 ∧ t44 = t34 ∧
  t53 = (Ty t31, Ty t34 → t31 → t34 → Bool) ∧
  t60 = (Ty t30, Ty t33 → t30 → t33 → Bool) ∧
  t77 = (Ty t70, Ty t72 → t70 → t72 → Bool) ∧ t78 = t70 ∧
  t79 = t72 ∧ t80 = t170 ∧ t82 = t171 ∧ t116 = Int ∧
  t125 = (Ty Int, Ty (List Int) → Int → List Int → Bool) ∧
  t136 = Int ∧ t137 = (List Int) ∧ t138 = t30 ∧ t139 = t33 ∧
  t140 = t31 ∧ t141 = t34 ∧ t142 = t70 ∧ t143 = t72";
    );

  "binary plus" >::
    (fun () ->
      todo "numeric";
      test_case "binary plus"
"newtype Binary : num
newtype Carry : num

newcons Zero : Binary 0
newcons PZero : ∀n. Binary(n) ⟶ Binary(n+n)
newcons POne : ∀n. Binary(n) ⟶ Binary(n+n+1)

newcons CZero : Carry 0
newcons COne : Carry 1

let rec plus =
  function CZero ->
    (function Zero -> (fun b -> b)
      | PZero a1 as a ->
        (function Zero -> a
	  | PZero b1 -> PZero (plus CZero a1 b1)
	  | POne b1 -> POne (plus CZero a1 b1))
      | POne a1 as a ->
        (function Zero -> a
	  | PZero b1 -> POne (plus CZero a1 b1)
	  | POne b1 -> PZero (plus COne a1 b1)))
    | COne ->
    (function Zero ->
        (function Zero -> POne(Zero)
	  | PZero b1 -> POne b1
	  | POne b1 -> PZero (plus COne Zero b1))
      | PZero a1 as a ->
        (function Zero -> POne a1
	  | PZero b1 -> POne (plus CZero a1 b1)
	  | POne b1 -> PZero (plus COne a1 b1))
      | POne a1 as a ->
        (function Zero -> PZero (plus COne a1 Zero)
	  | PZero b1 -> PZero (plus COne a1 b1)
	  | POne b1 -> POne (plus COne a1 b1)))"
        "" 1
        ""
(*
" ⟹ 𝛘1(t2)
| 𝛘1(t1) ⟹ t1 = (Carry n5 → t4) ∧ t3 = (Carry n5)
| (Carry n6) = t3 ∧ 0 = n6 ∧ 𝛘1(t1) ⟹ t4 = (Binary n9 → t8) ∧
    t7 = (Binary n9)
| (Binary n10) = t7 ∧ 0 = n10 ∧ (Carry n6) = t3 ∧ 0 = n6 ∧ 𝛘1(t1)
    ⟹ t8 = (t12 → t12)
| (Binary n15) = t7 ∧ (n16 + n16) = n15 ∧ (Carry n6) = t3 ∧ 0 = n6 ∧
    𝛘1(t1) ⟹ t8 = (Binary n19 → t18) ∧ t17 = (Binary n19)
| (Binary n20) = t17 ∧ 0 = n20 ∧ (Binary n15) = t7 ∧
    (n16 + n16) = n15 ∧ (Carry n6) = t3 ∧ 0 = n6 ∧ 𝛘1(t1) ⟹
    t18 = t7
| (Binary n23) = t17 ∧ (n24 + n24) = n23 ∧ (Binary n15) = t7 ∧
    (n16 + n16) = n15 ∧ (Carry n6) = t3 ∧ 0 = n6 ∧ 𝛘1(t1) ⟹
    t18 = (Binary n25) ∧
    t31 = (Carry n30 → Binary n16 → Binary n24 → Binary n26) ∧
    (n26 + n26) = n25 ∧ 0 = n30 ∧ 𝛘1(t31)
| (Binary n34) = t17 ∧ (1 + n35 + n35) = n34 ∧ (Binary n15) = t7 ∧
    (n16 + n16) = n15 ∧ (Carry n6) = t3 ∧ 0 = n6 ∧ 𝛘1(t1) ⟹
    t18 = (Binary n36) ∧
    t42 = (Carry n41 → Binary n16 → Binary n35 → Binary n37) ∧
    (1 + n37 + n37) = n36 ∧ 0 = n41 ∧ 𝛘1(t42)
| (Binary n45) = t7 ∧ (1 + n46 + n46) = n45 ∧ (Carry n6) = t3 ∧
    0 = n6 ∧ 𝛘1(t1) ⟹ t8 = (Binary n49 → t48) ∧ t47 = (Binary n49)
| (Binary n50) = t47 ∧ 0 = n50 ∧ (Binary n45) = t7 ∧
    (1 + n46 + n46) = n45 ∧ (Carry n6) = t3 ∧ 0 = n6 ∧ 𝛘1(t1) ⟹
    t48 = t7
| (Binary n53) = t47 ∧ (n54 + n54) = n53 ∧ (Binary n45) = t7 ∧
    (1 + n46 + n46) = n45 ∧ (Carry n6) = t3 ∧ 0 = n6 ∧ 𝛘1(t1) ⟹
    t48 = (Binary n55) ∧
    t61 = (Carry n60 → Binary n46 → Binary n54 → Binary n56) ∧
    (1 + n56 + n56) = n55 ∧ 0 = n60 ∧ 𝛘1(t61)
| (Binary n64) = t47 ∧ (1 + n65 + n65) = n64 ∧ (Binary n45) = t7 ∧
    (1 + n46 + n46) = n45 ∧ (Carry n6) = t3 ∧ 0 = n6 ∧ 𝛘1(t1) ⟹
    t48 = (Binary n66) ∧
    t72 = (Carry n71 → Binary n46 → Binary n65 → Binary n67) ∧
    (n67 + n67) = n66 ∧ 1 = n71 ∧ 𝛘1(t72)
| (Carry n74) = t3 ∧ 1 = n74 ∧ 𝛘1(t1) ⟹
    t4 = (Binary n77 → t76) ∧ t75 = (Binary n77)
| (Binary n78) = t75 ∧ 0 = n78 ∧ (Carry n74) = t3 ∧ 1 = n74 ∧
    𝛘1(t1) ⟹ t76 = (Binary n81 → t80) ∧ t79 = (Binary n81)
| (Binary n82) = t79 ∧ 0 = n82 ∧ (Binary n78) = t75 ∧ 0 = n78 ∧
    (Carry n74) = t3 ∧ 1 = n74 ∧ 𝛘1(t1) ⟹ t80 = (Binary n83) ∧
    n85 = n84 ∧ (1 + n84 + n84) = n83 ∧ 0 = n85
| (Binary n88) = t79 ∧ (n89 + n89) = n88 ∧ (Binary n78) = t75 ∧
    0 = n78 ∧ (Carry n74) = t3 ∧ 1 = n74 ∧ 𝛘1(t1) ⟹
    t80 = (Binary n90) ∧ n89 = n91 ∧ (1 + n91 + n91) = n90
| (Binary n94) = t79 ∧ (1 + n95 + n95) = n94 ∧ (Binary n78) = t75 ∧
    0 = n78 ∧ (Carry n74) = t3 ∧ 1 = n74 ∧ 𝛘1(t1) ⟹
    t80 = (Binary n96) ∧
    t103 = (Carry n102 → Binary n100 → Binary n95 → Binary n97) ∧
    (n97 + n97) = n96 ∧ 1 = n102 ∧ 0 = n100 ∧ 𝛘1(t103)
| (Binary n106) = t75 ∧ (n107 + n107) = n106 ∧ (Carry n74) = t3 ∧
    1 = n74 ∧ 𝛘1(t1) ⟹ t76 = (Binary n110 → t109) ∧
    t108 = (Binary n110)
| (Binary n111) = t108 ∧ 0 = n111 ∧ (Binary n106) = t75 ∧
    (n107 + n107) = n106 ∧ (Carry n74) = t3 ∧ 1 = n74 ∧ 𝛘1(t1) ⟹
    t109 = (Binary n112) ∧ n107 = n113 ∧ (1 + n113 + n113) = n112
| (Binary n116) = t108 ∧ (n117 + n117) = n116 ∧ (Binary n106) = t75 ∧
    (n107 + n107) = n106 ∧ (Carry n74) = t3 ∧ 1 = n74 ∧ 𝛘1(t1) ⟹
    t109 = (Binary n118) ∧
    t124 = (Carry n123 → Binary n107 → Binary n117 → Binary n119) ∧
    (1 + n119 + n119) = n118 ∧ 0 = n123 ∧ 𝛘1(t124)
| (Binary n127) = t108 ∧ (1 + n128 + n128) = n127 ∧
    (Binary n106) = t75 ∧ (n107 + n107) = n106 ∧ (Carry n74) = t3 ∧
    1 = n74 ∧ 𝛘1(t1) ⟹ t109 = (Binary n129) ∧
    t135 = (Carry n134 → Binary n107 → Binary n128 → Binary n130) ∧
    (n130 + n130) = n129 ∧ 1 = n134 ∧ 𝛘1(t135)
| (Binary n138) = t75 ∧ (1 + n139 + n139) = n138 ∧ (Carry n74) = t3 ∧
    1 = n74 ∧ 𝛘1(t1) ⟹ t76 = (Binary n142 → t141) ∧
    t140 = (Binary n142)
| (Binary n143) = t140 ∧ 0 = n143 ∧ (Binary n138) = t75 ∧
    (1 + n139 + n139) = n138 ∧ (Carry n74) = t3 ∧ 1 = n74 ∧ 𝛘1(t1)
    ⟹ t141 = (Binary n144) ∧
    t151 = (Carry n150 → Binary n139 → Binary n147 → Binary n145) ∧
    (n145 + n145) = n144 ∧ 1 = n150 ∧ 0 = n147 ∧ 𝛘1(t151)
| (Binary n154) = t140 ∧ (n155 + n155) = n154 ∧ (Binary n138) = t75 ∧
    (1 + n139 + n139) = n138 ∧ (Carry n74) = t3 ∧ 1 = n74 ∧ 𝛘1(t1)
    ⟹ t141 = (Binary n156) ∧
    t162 = (Carry n161 → Binary n139 → Binary n155 → Binary n157) ∧
    (n157 + n157) = n156 ∧ 1 = n161 ∧ 𝛘1(t162)
| (Binary n165) = t140 ∧ (1 + n166 + n166) = n165 ∧
    (Binary n138) = t75 ∧ (1 + n139 + n139) = n138 ∧ (Carry n74) = t3 ∧
    1 = n74 ∧ 𝛘1(t1) ⟹ t141 = (Binary n167) ∧
    t173 = (Carry n172 → Binary n139 → Binary n166 → Binary n168) ∧
    (1 + n168 + n168) = n167 ∧ 1 = n172 ∧ 𝛘1(t173)"
*)
    );

  "binary plus with test" >::
    (fun () ->
      (* todo "numeric"; *)
      test_case "binary plus test"
"newtype Binary : num
newtype Carry : num
newtype Bool

newcons Zero : Binary 0
newcons PZero : ∀n. Binary(n) ⟶ Binary(n+n)
newcons POne : ∀n. Binary(n) ⟶ Binary(n+n+1)
newcons CZero : Carry 0
newcons COne : Carry 1

external eq_Binary :  ∀n. Binary(n) → Binary(n) → Bool

let rec plus =
  function CZero ->
    (function Zero -> (fun b -> b)
      | PZero a1 as a ->
        (function Zero -> a
	  | PZero b1 -> PZero (plus CZero a1 b1)
	  | POne b1 -> POne (plus CZero a1 b1))
      | POne a1 as a ->
        (function Zero -> a
	  | PZero b1 -> POne (plus CZero a1 b1)
	  | POne b1 -> PZero (plus COne a1 b1)))
    | COne ->
    (function Zero ->
        (function Zero -> POne(Zero)
	  | PZero b1 -> POne b1
	  | POne b1 -> PZero (plus COne Zero b1))
      | PZero a1 as a ->
        (function Zero -> POne a1
	  | PZero b1 -> POne (plus CZero a1 b1)
	  | POne b1 -> PZero (plus COne a1 b1))
      | POne a1 as a ->
        (function Zero -> PZero (plus COne a1 Zero)
	  | PZero b1 -> PZero (plus COne a1 b1)
	  | POne b1 -> POne (plus COne a1 b1)))
test (eq_Binary (plus (POne Zero) (PZero (POne Zero))) (POne (POne Zero)))"
        "" 1
        ""
    );

]
