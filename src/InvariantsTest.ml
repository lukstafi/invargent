(** Solving second-order i.e. formula variables tests for InvarGenT.

    Released under the GNU General Public Licence (version 2 or
    higher), NO WARRANTY of correctness etc. (C) Lukasz Stafiniak 2013
    @author Lukasz Stafiniak lukstafi (AT) gmail.com
    @since Mar 2013
*)
open OUnit
open Terms
open Aux

let test_case msg test answers =
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
        let test_sol (chi, result) =
          let vs, ans = List.assoc chi sol_chi in
          ignore (Format.flush_str_formatter ());
          Format.fprintf Format.str_formatter "@[<2>∃%a.@ %a@]"
            (pr_sep_list "," pr_tyvar) vs pr_formula ans;
          assert_equal ~printer:(fun x -> x)
            result
            (Format.flush_str_formatter ()) in
        List.iter test_sol answers
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

        [1, "∃t93. δ = (Term t93 → t93)"]
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
        [1, "∃t191, t192. δ = (Ty t191, Ty t192 → t191 → t192 → Bool)"]
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
        [1, "∃t204, t205. δ = (Ty t204, Ty t205 → t204 → t205 → Bool)"]
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
        [1, "∃t221, t222. δ = (Ty t221, Ty t222 → t221 → t222 → Bool)"]
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
        [1,"∃n263, n264, n265, n266.
  δ = (Carry n266 → Binary n265 → Binary n264 → Binary n263) ∧
  n263 = (n266 + n265 + n264)"]
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
n266:=n5; n265:=n9; n264:=n19; n263:=n19; n262:=n5; n261:=n9;
n260:=n19; n259:=n19; n258:=n9; n257:=n19; n256:=n19; n255:=n19; n254:=n19;
n253:=n19; n252:=n30; n251:=n16; n250:=n24; n249:=n26; n248:=n41; n247:=n16;
n246:=n35; n245:=n37; n244:=n49; n243:=n19; n242:=n60; n241:=n46; n240:=n54;
n239:=n56; n238:=n71; n237:=n46; n236:=n65; n235:=n67; n234:=n19; n233:=n19;
n232:=n77; n231:=n81; n230:=n19; n229:=n102; n228:=n100; n227:=n95;
n226:=n97; n225:=n110; n224:=n19; n223:=n123; n222:=n107; n221:=n117;
n220:=n119; n219:=n134; n218:=n107; n217:=n128; n216:=n130; n215:=n142;
n214:=n19; n213:=n150; n212:=n139; n211:=n147; n210:=n145; n209:=n161;
n208:=n139; n207:=n155; n206:=n157; n205:=n172; n204:=n139; n203:=n166;
n202:=n168
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
        [1,"∃n285, n286, n287, n288.
  δ = (Carry n288 → Binary n287 → Binary n286 → Binary n285) ∧
  n285 = (n288 + n287 + n286)"]
    );

  "flatten_pairs" >::
    (fun () ->
      (* todo "debug"; *)
      test_case "list flatten_pairs"
"newtype Bool
newtype List : type * num
newcons True : Bool
newcons False : Bool
newcons LNil : ∀a. List(a, 0)
newcons LCons : ∀n, a [0≤n]. a * List(a, n) ⟶ List(a, n+1)

let rec flatten_pairs =
  function LNil -> LNil
    | LCons ((x, y), l) ->
      LCons (x, LCons (y, flatten_pairs l))"
        [1,""];

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
        [1,"∃t5. δ = Placement t5 → Outside"]

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
        [1,"";
         2,""];

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
        [1,"";
         2,""];

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
        [1,"";
         2,""];

    );


]
