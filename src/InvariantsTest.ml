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
      (* todo "debug"; *)
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
      todo "debug";
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
        "∃n202, n203, n204, n205.
  δ = (Carry n205 → Binary n204 → Binary n203 → Binary n202) ∧
  n202 = (n205 + n204 + n203)" 1
        "n202 = (n5 + n204 + n203) ∧ n204 = (n9 + n205) ∧
  (n16 + n16 + n203) = (n19 + n204) ∧
  (n24 + n24 + n24 + n24 + n24 + n24 + n24 + n16) =
    (n271 + n203 + n203 + n203) ∧
  (n24 + n24 + n24) = (n272 + n203) ∧ (n24 + n24 + n16) = (n273 + n203) ∧
  (n24 + n24 + n24 + n24) = (n274 + n203 + n203) ∧
  (n24 + n24 + n24 + n24 + n24 + n16) = (n26 + n203 + n203) ∧
  (n24 + n24) = (n30 + n203) ∧
  (n24 + n24 + n24 + n24 + n24 + n24 + n24 + n24 + n24 + n24 + n24 + n24 +
     n16 + n16)
    = (n25 + n203 + n203 + n203 + n203 + n203) ∧
  (3 + n35 + n35 + n35 + n35 + n35 + n35 + n35 + n16) =
    (n275 + n203 + n203 + n203) ∧
  (1 + n35 + n35 + n35) = (n276 + n203) ∧
  (1 + n35 + n35 + n16) = (n277 + n203) ∧
  (2 + n35 + n35 + n35 + n35) = (n278 + n203 + n203) ∧
  (2 + n35 + n35 + n35 + n35 + n35 + n16) = (n37 + n203 + n203) ∧
  (1 + n35 + n35) = (n41 + n203) ∧
  (6 + n35 + n35 + n35 + n35 + n35 + n35 + n35 + n35 + n35 + n35 + n35 +
     n35 + n16 + n16)
    = (n36 + n203 + n203 + n203 + n203 + n203) ∧
  (1 + n46 + n46 + n203) = (n49 + n204) ∧
  (n54 + n54 + n54 + n54 + n54 + n54 + n54 + n46) =
    (n279 + n203 + n203 + n203) ∧
  (n54 + n54 + n54) = (n280 + n203) ∧ (n54 + n54 + n46) = (n281 + n203) ∧
  (n54 + n54 + n54 + n54) = (n282 + n203 + n203) ∧
  (n54 + n54 + n54 + n54 + n54 + n46) = (n56 + n203 + n203) ∧
  (n54 + n54) = (n60 + n203) ∧
  (1 + n54 + n54 + n54 + n54 + n54 + n54 + n54 + n54 + n54 + n54 + n54 +
     n54 + n46 + n46)
    = (n55 + n203 + n203 + n203 + n203 + n203) ∧
  (4 + n65 + n65 + n65 + n65 + n65 + n65 + n65 + n46) =
    (n283 + n203 + n203 + n203) ∧
  (1 + n65 + n65 + n65) = (n284 + n203) ∧
  (1 + n65 + n65 + n46) = (n285 + n203) ∧
  (3 + n65 + n65 + n65 + n65) = (n286 + n203 + n203) ∧
  (3 + n65 + n65 + n65 + n65 + n65 + n46) = (n67 + n203 + n203) ∧
  (2 + n65 + n65) = (n71 + n203) ∧
  (7 + n65 + n65 + n65 + n65 + n65 + n65 + n65 + n65 + n65 + n65 + n65 +
     n65 + n46 + n46)
    = (n66 + n203 + n203 + n203 + n203 + n203) ∧
  (1 + n204) = (n77 + n205) ∧ n203 = (n81 + n204) ∧ 0 = (n85 + n203) ∧
  0 = (n84 + n203 + n203) ∧
  1 = (n83 + n203 + n203 + n203 + n203 + n203) ∧
  (n89 + n89 + n89) = (n91 + n203) ∧
  (1 + n89 + n89 + n89 + n89 + n89 + n89 + n89 + n89) =
    (n90 + n203 + n203 + n203) ∧
  (5 + n95 + n95 + n95 + n95 + n95 + n95 + n95 + n95 + n95) =
    (n287 + n203 + n203 + n203 + n203) ∧
  (1 + n95 + n95 + n95) = (n288 + n203) ∧
  (2 + n95 + n95 + n95 + n95) = (n289 + n203 + n203) ∧
  (3 + n95 + n95 + n95 + n95) = (n290 + n203 + n203) ∧
  (4 + n95 + n95 + n95 + n95 + n95 + n95 + n95) = (n97 + n203 + n203 + n203) ∧
  (2 + n95 + n95) = (n102 + n203) ∧ (1 + n95 + n95) = (n100 + n203) ∧
  (9 + n95 + n95 + n95 + n95 + n95 + n95 + n95 + n95 + n95 + n95 + n95 +
     n95 + n95 + n95 + n95 + n95)
    = (n96 + n203 + n203 + n203 + n203 + n203 + n203 + n203) ∧
  (n107 + n107 + n203) = (n110 + n204) ∧ n107 = (n113 + n203) ∧
  (1 + n107 + n107) = (n112 + n203 + n203 + n203) ∧
  (n117 + n117 + n117 + n117 + n117 + n117 + n117 + n107) =
    (n291 + n203 + n203 + n203) ∧
  (n117 + n117 + n117) = (n292 + n203) ∧
  (n117 + n117 + n107) = (n293 + n203) ∧
  (n117 + n117 + n117 + n117) = (n294 + n203 + n203) ∧
  (n117 + n117 + n117 + n117 + n117 + n107) = (n119 + n203 + n203) ∧
  (n117 + n117) = (n123 + n203) ∧
  (1 + n117 + n117 + n117 + n117 + n117 + n117 + n117 + n117 + n117 + n117 +
     n117 + n117 + n107 + n107)
    = (n118 + n203 + n203 + n203 + n203 + n203) ∧
  (4 + n128 + n128 + n128 + n128 + n128 + n128 + n128 + n107) =
    (n295 + n203 + n203 + n203) ∧
  (1 + n128 + n128 + n128) = (n296 + n203) ∧
  (1 + n128 + n128 + n107) = (n297 + n203) ∧
  (3 + n128 + n128 + n128 + n128) = (n298 + n203 + n203) ∧
  (3 + n128 + n128 + n128 + n128 + n128 + n107) = (n130 + n203 + n203) ∧
  (2 + n128 + n128) = (n134 + n203) ∧
  (7 + n128 + n128 + n128 + n128 + n128 + n128 + n128 + n128 + n128 + n128 +
     n128 + n128 + n107 + n107)
    = (n129 + n203 + n203 + n203 + n203 + n203) ∧
  (1 + n139 + n139 + n203) = (n142 + n204) ∧
  (1 + n139) = (n299 + n203 + n203 + n203 + n203) ∧
  0 = (n300 + n203 + n203) ∧ n139 = (n301 + n203) ∧
  1 = (n302 + n203 + n203) ∧ (1 + n139) = (n145 + n203 + n203 + n203) ∧
  1 = (n150 + n203) ∧ 0 = (n147 + n203) ∧
  (2 + n139 + n139) = (n144 + n203 + n203 + n203 + n203 + n203 + n203 + n203) ∧
  (1 + n155 + n155 + n155 + n155 + n155 + n155 + n155 + n139) =
    (n303 + n203 + n203 + n203) ∧
  (n155 + n155 + n155) = (n304 + n203) ∧
  (n155 + n155 + n139) = (n305 + n203) ∧
  (1 + n155 + n155 + n155 + n155) = (n306 + n203 + n203) ∧
  (1 + n155 + n155 + n155 + n155 + n155 + n139) = (n157 + n203 + n203) ∧
  (1 + n155 + n155) = (n161 + n203) ∧
  (2 + n155 + n155 + n155 + n155 + n155 + n155 + n155 + n155 + n155 + n155 +
     n155 + n155 + n139 + n139)
    = (n156 + n203 + n203 + n203 + n203 + n203) ∧
  (4 + n166 + n166 + n166 + n166 + n166 + n166 + n166 + n139) =
    (n307 + n203 + n203 + n203) ∧
  (1 + n166 + n166 + n166) = (n308 + n203) ∧
  (1 + n166 + n166 + n139) = (n309 + n203) ∧
  (3 + n166 + n166 + n166 + n166) = (n310 + n203 + n203) ∧
  (3 + n166 + n166 + n166 + n166 + n166 + n139) = (n168 + n203 + n203) ∧
  (2 + n166 + n166) = (n172 + n203) ∧
  (8 + n166 + n166 + n166 + n166 + n166 + n166 + n166 + n166 + n166 + n166 +
     n166 + n166 + n139 + n139)
    = (n167 + n203 + n203 + n203 + n203 + n203) ∧
  t173 = (Carry n172 → Binary n139 → Binary n166 → Binary n168) ∧
  t162 = (Carry n161 → Binary n139 → Binary n155 → Binary n157) ∧
  t151 = (Carry n150 → Binary n139 → Binary n147 → Binary n145) ∧
  t141 = (Binary n202) ∧ t140 = (Binary n142) ∧
  t135 = (Carry n134 → Binary n107 → Binary n128 → Binary n130) ∧
  t124 = (Carry n123 → Binary n107 → Binary n117 → Binary n119) ∧
  t109 = (Binary n202) ∧ t108 = (Binary n110) ∧
  t103 = (Carry n102 → Binary n100 → Binary n95 → Binary n97) ∧
  t80 = (Binary n202) ∧ t79 = (Binary n81) ∧
  t76 = (Binary n203 → Binary n202) ∧ t75 = (Binary n77) ∧
  t72 = (Carry n71 → Binary n46 → Binary n65 → Binary n67) ∧
  t61 = (Carry n60 → Binary n46 → Binary n54 → Binary n56) ∧
  t48 = (Binary n202) ∧ t47 = (Binary n49) ∧
  t42 = (Carry n41 → Binary n16 → Binary n35 → Binary n37) ∧
  t31 = (Carry n30 → Binary n16 → Binary n24 → Binary n26) ∧
  t18 = (Binary n202) ∧ t17 = (Binary n19) ∧ t12 = (Binary n203) ∧
  t8 = (Binary n203 → Binary n202) ∧ t7 = (Binary n9) ∧
  t4 = (Binary n204 → Binary n203 → Binary n202) ∧ t3 = (Carry n5) ∧
  t2 = (Carry n270 → Binary n269 → Binary n268 → Binary n267) ∧
  n267 = (n270 + n269 + n268)"
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
      todo "debug";
      test_case "binary plus test"
"newtype Binary : num
newtype Carry : num
newtype Bool

newcons Zero : Binary 0
newcons PZero : ∀n [0≤n]. Binary(n) ⟶ Binary(n+n)
newcons POne : ∀n [0≤n]. Binary(n) ⟶ Binary(n+n+1)
newcons CZero : Carry 0
newcons COne : Carry 1

external eq_Binary :  ∀n [0≤n]. Binary(n) → Binary(n) → Bool

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
test (eq_Binary (plus CZero (POne Zero) (PZero (POne Zero)))
                   (POne (POne Zero)))"
        "∃n224, n225, n226, n227.
  δ = (Carry n227 → Binary n226 → Binary n225 → Binary n224) ∧
  n224 = (n227 + n226 + n225)" 1
        "(n24 + n16) = n26 ∧ 0 = n30 ∧ (n24 + n24 + n16 + n16) = n25 ∧
  (n35 + n16) = n37 ∧ 0 = n41 ∧ (1 + n35 + n35 + n16 + n16) = n36 ∧
  (n54 + n46) = n56 ∧ 0 = n60 ∧ (1 + n54 + n54 + n46 + n46) = n55 ∧
  (1 + n65 + n46) = n67 ∧ 1 = n71 ∧ (2 + n65 + n65 + n46 + n46) = n66 ∧
  0 = n85 ∧ 0 = n84 ∧ 1 = n83 ∧ n89 = n91 ∧ (1 + n89 + n89) = n90 ∧
  (1 + n95) = n97 ∧ 1 = n102 ∧ 0 = n100 ∧ (2 + n95 + n95) = n96 ∧
  n107 = n113 ∧ (1 + n107 + n107) = n112 ∧ (n117 + n107) = n119 ∧
  0 = n123 ∧ (1 + n117 + n117 + n107 + n107) = n118 ∧
  (1 + n128 + n107) = n130 ∧ 1 = n134 ∧
  (2 + n128 + n128 + n107 + n107) = n129 ∧ (1 + n139) = n145 ∧
  1 = n150 ∧ 0 = n147 ∧ (2 + n139 + n139) = n144 ∧
  (1 + n155 + n139) = n157 ∧ 1 = n161 ∧
  (2 + n155 + n155 + n139 + n139) = n156 ∧ (1 + n166 + n139) = n168 ∧
  1 = n172 ∧ (3 + n166 + n166 + n139 + n139) = n167 ∧
  t173 = (Carry n172 → Binary n139 → Binary n166 → Binary n168) ∧
  t162 = (Carry n161 → Binary n139 → Binary n155 → Binary n157) ∧
  t151 = (Carry n150 → Binary n139 → Binary n147 → Binary n145) ∧
  t141 = (Binary n224) ∧ t140 = (Binary n142) ∧
  t135 = (Carry n134 → Binary n107 → Binary n128 → Binary n130) ∧
  t124 = (Carry n123 → Binary n107 → Binary n117 → Binary n119) ∧
  t109 = (Binary n224) ∧ t108 = (Binary n110) ∧
  t103 = (Carry n102 → Binary n100 → Binary n95 → Binary n97) ∧
  t80 = (Binary n224) ∧ t79 = (Binary n81) ∧
  t76 = (Binary n225 → Binary n224) ∧ t75 = (Binary n77) ∧
  t72 = (Carry n71 → Binary n46 → Binary n65 → Binary n67) ∧
  t61 = (Carry n60 → Binary n46 → Binary n54 → Binary n56) ∧
  t48 = (Binary n224) ∧ t47 = (Binary n49) ∧
  t42 = (Carry n41 → Binary n16 → Binary n35 → Binary n37) ∧
  t31 = (Carry n30 → Binary n16 → Binary n24 → Binary n26) ∧
  t18 = (Binary n224) ∧ t17 = (Binary n19) ∧ t12 = (Binary n225) ∧
  t8 = (Binary n225 → Binary n224) ∧ t7 = (Binary n9) ∧
  t4 = (Binary n226 → Binary n225 → Binary n224) ∧ t3 = (Carry n5) ∧
  t2 = (Carry n296 → Binary n295 → Binary n294 → Binary n293) ∧
  t193 = (Carry n192 → Binary n188 → Binary n182 → Binary n194) ∧
  1 = n340 ∧ n139 = n339 ∧ n166 = n338 ∧ (1 + n166 + n139) = n337 ∧
  1 = n336 ∧ n139 = n335 ∧ n155 = n334 ∧ (1 + n155 + n139) = n333 ∧
  1 = n332 ∧ n139 = n331 ∧ 0 = n330 ∧ (1 + n139) = n329 ∧
  n225 = n142 ∧ 1 = n328 ∧ n107 = n327 ∧ n128 = n326 ∧
  (1 + n128 + n107) = n325 ∧ 0 = n324 ∧ n107 = n323 ∧ n117 = n322 ∧
  (n117 + n107) = n321 ∧ n225 = n110 ∧ 1 = n320 ∧ 0 = n319 ∧
  n95 = n318 ∧ (1 + n95) = n317 ∧ n225 = n81 ∧ n226 = n77 ∧
  1 = n316 ∧ n46 = n315 ∧ n65 = n314 ∧ (1 + n65 + n46) = n313 ∧
  0 = n312 ∧ n46 = n311 ∧ n54 = n310 ∧ (n54 + n46) = n309 ∧
  n225 = n49 ∧ 0 = n308 ∧ n16 = n307 ∧ n35 = n306 ∧
  (n35 + n16) = n305 ∧ 0 = n304 ∧ n16 = n303 ∧ n24 = n302 ∧
  (n24 + n16) = n301 ∧ n225 = n19 ∧ n226 = n9 ∧ n227 = n5 ∧
  3 = n297 ∧ n293 = (n296 + n295 + n294) ∧ 3 = n175 ∧ 0 = n178 ∧
  1 = n176 ∧ 2 = n182 ∧ 0 = n185 ∧ 1 = n183 ∧ 1 = n188 ∧
  0 = n189 ∧ 0 = n192 ∧ 0 = n190 ∧ 1 = n184 ∧ 0 = n186 ∧
  3 = n194 ∧ 1 = n177 ∧ 0 = n179 ∧ 0 = n300 ∧ 1 = n299 ∧ 2 = n298"
    );

  "escape castle" >::
    (fun () ->
      todo "universal";
      test_case "escape castle"
"newtype Room
newtype Yard
newtype Outside

newtype Placement : type
newcons Room : Room ⟶ Placement Room
newcons Yard : Yard ⟶ Placement Yard
newcons Outside : Outside ⟶ Placement Outside

external leave : Room → ∃a. Placement a
external enter : Yard → Room

let rec escape = function Outside x -> x
  | Room x ->
    let y = leave x in
    escape y
  | Yard x ->
    let y = leave (enter x) in
    escape y"
        "∃t5. δ = Placement t5 → Outside" 1
        ""

    );

  "find castle" >::
    (fun () ->
      todo "existential";
      test_case "find castle small"
"newtype Room
newtype Yard
newtype Village

newtype Castle : type
newtype Placement : type
newcons Room : Room ⟶ Castle Room
newcons Yard : Yard ⟶ Castle Yard
newcons CastleRoom : Room ⟶ Placement Room
newcons CastleYard : Yard ⟶ Placement Yard
newcons Village : Village ⟶ Placement Village

external wander : ∀a. Placement a → ∃b. Placement b

let rec find = efunction
  | CastleRoom x -> Room x
  | CastleYard x -> Yard x
  | Village x ->
    let y = wander x in
    find y"
        "" 1
        "";

      test_case "find castle big"
"newtype Room
newtype Yard
newtype Garden
newtype Village

newtype Castle : type
newtype Placement : type
newcons Room : Room ⟶ Castle Room
newcons Yard : Yard ⟶ Castle Yard
newcons CastleRoom : Room ⟶ Placement Room
newcons CastleYard : Yard ⟶ Placement Yard
newcons Garden : Garden ⟶ Placement Garden
newcons Village : Village ⟶ Placement Village

external wander : ∀a. Placement a → ∃b. Placement b

let rec find = efunction
  | CastleRoom x -> Room x
  | CastleYard x -> Yard x
  | Garden x ->
    let y = wander x in
    find y
  | Village x ->
    let y = wander x in
    find y"
        "" 1
        ""

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
newcons LCons : ∀n, a [0≤n]. a * List(a, n) ⟶ List(a, n+1)

newtype Bar
external f : Bar → Bool

let rec filter =
  efunction LNil -> LNil
    | LCons (x, l) -> match f x with
          True -> LCons (x, filter l)
	| False -> filter l"
        "" 1
        ""

    );


]
