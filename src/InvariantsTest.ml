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

        "∃t98. δ = (Term t98 → t98)" 1
        "t65 = t60 ∧ t52 = t46 ∧ t43 = (Term t37 → t37) ∧
  t41 = (Term t36 → t36) ∧ t39 = t37 ∧ t38 = t36 ∧
  t27 = (Term t21 → t21) ∧ t24 = (Term t21 → t21) ∧
  t3 = (Term t98) ∧ t2 = (Term t99 → t99) ∧ t4 = t98 ∧ t5 = t98 ∧
  t11 = (Term Int → Int) ∧ t16 = (Term Int → Int) ∧
  t19 = (Term Int → Int) ∧ t30 = (Term Bool → Bool) ∧
  t50 = (Term (t46, t47) → t46, t47) ∧ t51 = (t46, t47) ∧ t53 = t46 ∧
  t54 = t47 ∧ t63 = (Term (t59, t60) → t59, t60) ∧ t64 = (t59, t60) ∧
  t66 = t59 ∧ t67 = t60 ∧ t100 = Int ∧ t101 = Int ∧ t102 = Int ∧
  t103 = Bool ∧ t104 = t21 ∧ t105 = t21 ∧ t106 = t36 ∧ t107 = t37 ∧
  t108 = (t46, t47) ∧ t109 = (t59, t60)"
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
        "∃t191, t192. δ = (Ty t191, Ty t192 → t191 → t192 → Bool)" 1
        "t79 = t72 ∧ t78 = t70 ∧
  t77 = (Ty t70, Ty t72 → t70 → t72 → Bool) ∧ t44 = t34 ∧
  t43 = t33 ∧ t42 = Bool ∧ t41 = (t33, t34) ∧ t38 = t31 ∧
  t37 = t30 ∧ t36 = (t33, t34 → Bool) ∧ t35 = (t30, t31) ∧
  t4 = (t191 → t192 → Bool) ∧ t3 = (Ty t191, Ty t192) ∧
  t2 = (Ty t121, Ty t122 → t121 → t122 → Bool) ∧ t7 = t191 ∧
  t8 = t192 ∧ t53 = (Ty t31, Ty t34 → t31 → t34 → Bool) ∧
  t60 = (Ty t30, Ty t33 → t30 → t33 → Bool) ∧ t80 = t191 ∧
  t82 = t192 ∧ t86 = Int ∧
  t95 = (Ty Int, Ty (List Int) → Int → List Int → Bool) ∧
  t123 = Int ∧ t124 = (List Int) ∧ t125 = t30 ∧ t126 = t33 ∧
  t127 = t31 ∧ t128 = t34 ∧ t129 = t70 ∧ t130 = t72";
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
        "∃t204, t205. δ = (Ty t204, Ty t205 → t204 → t205 → Bool)" 1
        "t79 = t72 ∧ t78 = t70 ∧
  t77 = (Ty t70, Ty t72 → t70 → t72 → Bool) ∧ t44 = t34 ∧
  t43 = t33 ∧ t42 = Bool ∧ t41 = (t33, t34) ∧ t38 = t31 ∧
  t37 = t30 ∧ t36 = (t33, t34 → Bool) ∧ t35 = (t30, t31) ∧
  t4 = (t204 → t205 → Bool) ∧ t3 = (Ty t204, Ty t205) ∧
  t2 = (Ty t138, Ty t139 → t138 → t139 → Bool) ∧ t7 = t204 ∧
  t8 = t205 ∧ t53 = (Ty t31, Ty t34 → t31 → t34 → Bool) ∧
  t60 = (Ty t30, Ty t33 → t30 → t33 → Bool) ∧ t80 = t204 ∧
  t82 = t205 ∧ t140 = t30 ∧ t141 = t33 ∧ t142 = t31 ∧ t143 = t34 ∧
  t144 = t70 ∧ t145 = t72";
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
        "∃t221, t222. δ = (Ty t221, Ty t222 → t221 → t222 → Bool)" 1
        "t79 = t72 ∧ t78 = t70 ∧
  t77 = (Ty t70, Ty t72 → t70 → t72 → Bool) ∧ t44 = t34 ∧
  t43 = t33 ∧ t42 = Bool ∧ t41 = (t33, t34) ∧ t38 = t31 ∧
  t37 = t30 ∧ t36 = (t33, t34 → Bool) ∧ t35 = (t30, t31) ∧
  t4 = (t221 → t222 → Bool) ∧ t3 = (Ty t221, Ty t222) ∧
  t2 = (Ty t151, Ty t152 → t151 → t152 → Bool) ∧ t7 = t221 ∧
  t8 = t222 ∧ t53 = (Ty t31, Ty t34 → t31 → t34 → Bool) ∧
  t60 = (Ty t30, Ty t33 → t30 → t33 → Bool) ∧ t80 = t221 ∧
  t82 = t222 ∧ t116 = Int ∧
  t125 = (Ty Int, Ty (List Int) → Int → List Int → Bool) ∧
  t153 = Int ∧ t154 = (List Int) ∧ t155 = t30 ∧ t156 = t33 ∧
  t157 = t31 ∧ t158 = t34 ∧ t159 = t70 ∧ t160 = t72";
    );

  "binary plus" >::
    (fun () ->
      (* todo "numeric"; *)
      test_case "binary plus"
"newtype Binary : num
newtype Carry : num

newcons Zero : Binary 0
newcons PZero : ∀n [0≤n]. Binary(n) ⟶ Binary(n+n)
newcons POne : ∀n [0≤n]. Binary(n) ⟶ Binary(n+n+1)

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
   Binary addition legend:
   - t1: result
   - t3, n5: the carry bit and its value
   - n6: case when carry is 0
   - t7, n9, n13: the first number (A)
   - n10=0, t11, t12: case when A is 0
   - n15=2*n16: case when A ends with 0
   - t17, n19, n21: the second number (B)
   - t18, n25: the result (C)
   - n20=0: case when B is 0
   - n23=2*n24: case when B ends with 0
   - n25=2*n26: C ends with 0, recursive call A=n16, B=n24, C=n26
   - n30=0: recursive carry in above call
   - n32: B
   - n34=2*n35+1: case B ends with 1
   - n36=2*n37+1: C
   - recursive call carry=n41=0, A=n16, B=n35, C=n37
   - n43, n45=2*n46+1: case when A ends with 1
   - t47, n49, n51, n62: B
   - t48: C
   - n50=0: B is 0
   - n53=2*n54: B ends with 0
   - n55=2*n56: C ends with 0
   - recursive call carry=n60=0, A=n46, B=n54, C=n56
   - n64=2*n65+1: case B ends with 1
   - n66=2*n67: C ends with 0
   - recursive call carry=n71=1, A=n46, B=n65, C=n67
   - n73, n74=1: case carry is 1
   - t75, n77, n104, n136: A
   - n78=0: case A is 0
   - t79, n81, n92, n110, n114, n125, n142, n152, n163: B
   - n82=0: case B is 0
   - t80, n83=2*n84+1, n84=n85=0: C
   - n86=n88=2*n89: B ends with 0
   - n90=2*n91+1, n91=n89: C = B+1
   - n94=2*n95+1: B ends with 1
   - n96=2*n97: C ends with 0
   - recursive call carry=n102=1, A=n100=0, B=n95
   - n106=2*n107: case A ends with 0
   - n111=0: case B is 0
   - n112=2*n113+1, n113=n107: C ends with 1
   - n116=2*n117: case B ends with 0
   - n118=2*n119+1: C ends with 1
   - recursive call carry=n123=0, A=n107, B=n117, C=n119
   - n127=2*n128+1: case B ends with 1
   - n129=2*n130: C ends with 0
   - recursive call carry=n134=1, A=n107, B=n128, C=n130
   - n138=2*n139+1: case A ends with 1
   - n143=0: case B is 0
   - n144=2*n145: case C ends with 0
   - recursive call carry=n150=1, A=n139, B=n147=0, C=n145
   - n154=2*n155: case B ends with 0
   - n156=2*n157: C ends with 0
   - recursive call carry=n161=1, A=n139, B=n155, C=n157
   - n165=2*n166+1: case B ends with 1
   - n167=2*n168+1: C ends with 1
   - recursive call carry=n172=1, A=n139, B=n166, C=n168
   - alien subterm variables:
n266:=n172; n265:=n139; n264:=n166; n263:=n168; n262:=n161;
n261:=n139; n260:=n155; n259:=n157; n258:=n150; n257:=n139; n256:=n147;
n255:=n145; n254:=n19; n253:=n142; n252:=n134; n251:=n107; n250:=n128;
n249:=n130; n248:=n123; n247:=n107; n246:=n117; n245:=n119; n244:=n19;
n243:=n110; n242:=n102; n241:=n100; n240:=n95; n239:=n97; n238:=n19;
n237:=n81; n236:=n19; n235:=n19; n234:=n77; n233:=n71; n232:=n46; n231:=n65;
n230:=n67; n229:=n60; n228:=n46; n227:=n54; n226:=n56; n225:=n19; n224:=n49;
n223:=n41; n222:=n16; n221:=n35; n220:=n37; n219:=n30; n218:=n16; n217:=n24;
n216:=n26; n215:=n19; n214:=n19; n213:=n19; n212:=n19; n211:=n19; n210:=n9;
n209:=n9; n208:=n19; n207:=n19; n206:=n5; n205:=n5; n204:=n9; n203:=n19;
n202:=n19
 *)
    );

  "binary plus with test" >::
    (fun () ->
      todo "numeric";
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
