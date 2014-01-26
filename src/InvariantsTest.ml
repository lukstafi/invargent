(** Solving second-order i.e. formula variables tests for InvarGenT.

    Released under the GNU General Public Licence (version 2 or
    higher), NO WARRANTY of correctness etc. (C) Lukasz Stafiniak 2013
    @author Lukasz Stafiniak lukstafi (AT) gmail.com
    @since Mar 2013
*)
open OUnit
open Defs
open Terms
open Aux

let debug = ref false(* true *)

let test_common more_general more_existential msg test =
  let ntime = Sys.time () in
  Terms.reset_state ();
  Infer.reset_state ();
  let prog = (Infer.normalize_program % Parser.program Lexer.token)
      (Lexing.from_string test) in
  let new_ex_types, preserve, orig_cn = Infer.infer_prog_mockup prog in
  (*[* Format.printf "orig_cn: %s@\n%a@\n%!" msg
    Infer.pr_cnstrnt orig_cn; *]*)
  let q_ops, cn = Infer.prenexize orig_cn in
  let exty_res_of_chi, brs = Infer.normalize q_ops cn in
  (*[* Format.printf "brs: %s@\n%a@\n%!" msg Infer.pr_brs brs; *]*)
  let brs = Infer.simplify preserve q_ops brs in
  (*[* Format.printf "simpl-brs: %s@\n%a@\nex_types:@\n%!"
    msg Infer.pr_brs brs;
  List.iter
    (fun (i,loc) ->
       let (allvs, phi, ty, n, pvs) =
         Hashtbl.find sigma (Extype i) in
       let ty = match ty with [ty] -> ty | _ -> assert false in
       Format.printf "∃%d: pvs=%a@ allvs=%a@ t=%a@ phi=%a@\n%!"
         i pr_vars (vars_of_list pvs) pr_vars (vars_of_list allvs)
         pr_ty ty pr_formula phi)
    !all_ex_types;
  *]*)
  Abduction.more_general := more_general;
  DisjElim.more_existential := more_existential;
  let _, res, sol =
    Invariants.solve q_ops new_ex_types exty_res_of_chi brs in
  Abduction.more_general := false;
  DisjElim.more_existential := false;
  (*[* Format.printf
    "Test: res=@\n%a@\n%!" pr_formula res;
  List.iter
    (fun (i,loc) ->
       let (allvs, phi, ty, n, pvs) =
         Hashtbl.find sigma (Extype i) in
       let ty = match ty with [ty] -> ty | _ -> assert false in
       Format.printf "so∃%d: pvs=%a@ allvs=%a@ t=%a@ phi=%a@\n%!"
         i pr_vars (vars_of_list pvs) pr_vars (vars_of_list allvs)
         pr_ty ty pr_formula phi)
    !all_ex_types;
  *]*)
  Format.printf " t=%.3fs " (Sys.time () -. ntime);
  q_ops, res, sol

let test_case ?(more_general=false) ?(more_existential=false)
    msg test answers =
  if !debug then Printexc.record_backtrace true;
  try
    let q, res, sol =
      test_common more_general more_existential msg test in
    let test_sol (chi, result) =
      let _, (vs, ans) = nice_ans (List.assoc chi sol) in
      ignore (Format.flush_str_formatter ());
      Format.fprintf Format.str_formatter "@[<2>∃%a.@ %a@]"
        (pr_sep_list "," pr_tyvar) vs pr_formula ans;
      assert_equal ~printer:(fun x -> x)
        result
        (Format.flush_str_formatter ()) in
    List.iter test_sol answers
  with (Defs.Report_toplevel _ | Terms.Contradiction _) as exn ->
    ignore (Format.flush_str_formatter ());
    Terms.pr_exception Format.str_formatter exn;
    Abduction.more_general := false;
    DisjElim.more_existential := false;
    assert_failure (Format.flush_str_formatter ())

let test_nonrec_case ?(more_general=false) ?(more_existential=false)
    msg test answers =
  if !debug then Printexc.record_backtrace true;
  try
    let q, res, sol = test_common more_general more_existential msg test in
    let test_sol (v, result) =
      let res_sb, _ = Infer.separate_subst q res in
      let ty = fst (List.assoc (VId (Type_sort, v)) res_sb) in
      ignore (Format.flush_str_formatter ());
      Format.fprintf Format.str_formatter "%a" pr_ty ty;
      assert_equal ~printer:(fun x -> x)
        result
        (Format.flush_str_formatter ()) in
    List.iter test_sol answers
  with (Report_toplevel _ | Contradiction _) as exn ->
    ignore (Format.flush_str_formatter ());
    Terms.pr_exception Format.str_formatter exn;
    Abduction.more_general := false;
    DisjElim.more_existential := false;
    assert_failure (Format.flush_str_formatter ())

let tests = "Invariants" >::: [

  "simple eval" >::
    (fun () ->
      skip_if !debug "debug";
      test_case "eval term"
"newtype Term : type
external let plus : Int → Int → Int = \"(+)\"
external let is_zero : Int → Bool = \"(=) 0\"
newcons Lit : Int ⟶ Term Int
newcons Plus : Term Int * Term Int ⟶ Term Int
newcons IsZero : Term Int ⟶ Term Bool
newcons If : ∀a. Term Bool * Term a * Term a ⟶ Term a

let rec eval = function
  | Lit i -> i
  | IsZero x -> is_zero (eval x)
  | Plus (x, y) -> plus (eval x) (eval y)
  | If (b, t, e) -> match eval b with True -> eval t | False -> eval e"

        [1, "∃a. δ = (Term a → a)"]
    );

  "simple assert false" >::
    (fun () ->
      skip_if !debug "debug";
      test_case "eval term"
"newtype Term : type
newcons Lit : Int ⟶ Term Int
newcons IsZero : Term Int ⟶ Term Bool
external let is_zero : Int → Bool = \"(=) 0\"

let rec eval = function
  | Lit i -> i
  | True -> assert false
  | IsZero x -> is_zero (eval x)"

        [1, "∃a. δ = (Term a → a)"]
    );


  "foo without when 1" >::
    (fun () ->
      skip_if !debug "debug";
      test_case "foo without when, positive"
"newtype Positive : num
newcons Pos : ∀n [0 ≤ n]. Num n ⟶ Positive n

let rec foo = function i -> Pos (i + -7)"

        [1, "∃n. δ = (Num (n + 7) → Positive n) ∧ 0 ≤ n"]
    );

  "foo without when 2" >::
    (fun () ->
      skip_if !debug "debug";
      test_case "foo without when, non-negative and non-positive"
"newtype Signed : num
newcons Pos : ∀n [0 ≤ n]. Num n ⟶ Signed n
newcons Neg : ∀n [n ≤ 0]. Num n ⟶ Signed n

let rec foo = function
  | i -> Pos (i + -7)
  | i -> Neg (i + -7)"

        [1, "∃. δ = (Num 7 → Signed 0)"]
    );

  "foo with when 1" >::
    (fun () ->
      skip_if !debug "debug";
      test_case "foo with when"
"newtype Signed : num
newcons Pos : ∀n [0 ≤ n]. Num n ⟶ Signed n
newcons Neg : ∀n [n ≤ 0]. Num n ⟶ Signed n

let rec foo = function
  | i when 7 <= i -> Pos (i + -7)
  | i when i <= 7 -> Neg (i + -7)"

        [1, "∃n. δ = (Num (n + 7) → Signed n)"]
    );

  "foo with when 2" >::
    (fun () ->
      skip_if !debug "debug";
      test_case "foo with when, unsafe positive"
"newtype Positive : num
newcons Pos : ∀n [0 ≤ n]. Num n ⟶ Positive n

let rec foo = function
  | i when 7 <= i -> Pos (i + -7)"

        [1, "∃n. δ = (Num (n + 7) → Positive n)"]
    );

  "eval" >::
    (fun () ->
       skip_if !debug "debug";
       test_case "eval term"
"newtype Term : type

external let plus : Int → Int → Int = \"(+)\"
external let is_zero : Int → Bool = \"(=) 0\"

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
  | If (b, t, e) -> (match eval b with True -> eval t | False -> eval e)
  | Pair (x, y) -> eval x, eval y
  | Fst p -> (match eval p with x, y -> x)
  | Snd p -> (match eval p with x, y -> y)"

        [1, "∃a. δ = (Term a → a)"]
    );

  "equal1 wrong type" >::
    (fun () ->
       skip_if !debug "debug";
       test_case "equal1 wrong type"
"newtype Ty : type
newtype List : type
newcons Zero : Int
newcons Nil : ∀a. List a
newcons TInt : Ty Int
newcons TPair : ∀a, b. Ty a * Ty b ⟶ Ty (a, b)
newcons TList : ∀a. Ty a ⟶ Ty (List a)
external let eq_int : Int → Int → Bool = \"(=)\"
external let b_and : Bool → Bool → Bool = \"(&&)\"
external let b_not : Bool → Bool = \"not\"
external forall2 : ∀a, b. (a → b → Bool) → List a → List b → Bool = \"forall2\"

let rec equal1 = function
  | TInt, TInt -> fun x y -> eq_int x y
  | TPair (t1, t2), TPair (u1, u2) ->  
    (fun (x1, x2) (y1, y2) ->
        b_and (equal1 (t1, u1) x1 y1)
              (equal1 (t2, u2) x2 y2))
  | TList t, TList u -> forall2 (equal1 (t, u))
  | _ -> fun _ _ -> False"
        [1, "∃a, b. δ = ((Ty a, Ty b) → a → a → Bool)"]
    );

  "equal with test" >::
    (fun () ->
       skip_if !debug "debug";
       test_case "equal terms"
"newtype Ty : type
newtype List : type
newcons Zero : Int
newcons Nil : ∀a. List a
newcons TInt : Ty Int
newcons TPair : ∀a, b. Ty a * Ty b ⟶ Ty (a, b)
newcons TList : ∀a. Ty a ⟶ Ty (List a)
external let eq_int : Int → Int → Bool = \"(=)\"
external let b_and : Bool → Bool → Bool = \"(&&)\"
external let b_not : Bool → Bool = \"not\"
external forall2 : ∀a, b. (a → b → Bool) → List a → List b → Bool = \"forall2\"

let rec equal = function
  | TInt, TInt -> fun x y -> eq_int x y
  | TPair (t1, t2), TPair (u1, u2) ->  
    (fun (x1, x2) (y1, y2) ->
        b_and (equal (t1, u1) x1 y1)
              (equal (t2, u2) x2 y2))
  | TList t, TList u -> forall2 (equal (t, u))
  | _ -> fun _ _ -> False
test b_not (equal (TInt, TList TInt) Zero Nil)"
        [1, "∃a, b. δ = ((Ty a, Ty b) → a → b → Bool)"]
    );

  "equal with assert" >::
    (fun () ->
       skip_if !debug "debug";
       test_case "equal terms"
"newtype Ty : type
newtype List : type
newcons Zero : Int
newcons Nil : ∀a. List a
newcons TInt : Ty Int
newcons TPair : ∀a, b. Ty a * Ty b ⟶ Ty (a, b)
newcons TList : ∀a. Ty a ⟶ Ty (List a)
external let eq_int : Int → Int → Bool = \"(=)\"
external let b_and : Bool → Bool → Bool = \"(&&)\"
external let b_not : Bool → Bool = \"not\"
external forall2 : ∀a, b. (a → b → Bool) → List a → List b → Bool = \"forall2\"

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
        [1, "∃a, b. δ = ((Ty a, Ty b) → a → b → Bool)"]
    );

  "equal with assert and test" >::
    (fun () ->
       skip_if !debug "debug";
       test_case "equal terms"
"newtype Ty : type
newtype List : type
newcons Zero : Int
newcons Nil : ∀a. List a
newcons TInt : Ty Int
newcons TPair : ∀a, b. Ty a * Ty b ⟶ Ty (a, b)
newcons TList : ∀a. Ty a ⟶ Ty (List a)
external let eq_int : Int → Int → Bool = \"(=)\"
external let b_and : Bool → Bool → Bool = \"(=)\"
external let b_not : Bool → Bool = \"not\"
external forall2 : ∀a, b. (a → b → Bool) → List a → List b → Bool = \"forall2\"

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
        [1, "∃a, b. δ = ((Ty a, Ty b) → a → b → Bool)"]
    );

  "map mono" >::
    (fun () ->
       skip_if !debug "debug";
       test_case "list map simplest numeric"
"newtype Elem
newtype List : num
newcons LNil : List 0
newcons LCons : ∀n [0≤n]. Elem * List n ⟶ List (n+1)

let rec map = fun f ->
  function LNil -> LNil
    | LCons (x, xs) ->
      let ys = map f xs in
      LCons (f x, ys)"
        [1,"∃n. δ = ((Elem → Elem) → List n → List n)"];
    );

  "append expanded" >::
    (fun () ->
       skip_if !debug "debug";
       test_case "list append simple numeric"
"newtype Elem
newtype List : num
newcons LNil : List 0
newcons LCons : ∀n [0≤n]. Elem * List n ⟶ List (n+1)

let rec append =
  function LNil -> (function LNil -> LNil | LCons (_,_) as l -> l)
    | LCons (x, xs) ->
      (function LNil -> LCons (x, append xs LNil)
        | LCons (_,_) as l -> LCons (x, append xs l))"
        [1,"∃n, k. δ = (List k → List n → List (n + k))"];
    );

  "interleave" >::
    (fun () ->
       skip_if !debug "debug";
       test_case "list interleave simple numeric"
"newtype Elem
newtype List : num
newcons LNil : List 0
newcons LCons : ∀n [0≤n]. Elem * List n ⟶ List (n+1)

let rec interleave =
  function LNil -> (function LNil -> LNil | LCons (_,_) as l -> l)
    | LCons (x, xs) as l1 ->
      function LNil -> l1
        | LCons (y,ys) -> LCons (x, LCons (y, interleave xs ys))"
        [1,"∃n, k. δ = (List k → List n → List (n + k))"];
    );

  "interleave 3" >::
    (fun () ->
       skip_if !debug "debug";
       test_case "list interleave 3 args simple numeric"
"newtype Elem
newtype List : num
newcons LNil : List 0
newcons LCons : ∀n [0≤n]. Elem * List n ⟶ List (n+1)

let rec interleave3 =
  function LNil -> 
    (function LNil -> (function LNil -> LNil | LCons (_,_) as l -> l)
      | LCons (x,xs) as l2 ->
        (function LNil -> l2
          | LCons (y,ys) -> LCons (x, LCons (y, interleave3 LNil xs ys))))
  | LCons (x, xs) as l1 ->
    (function
      | LNil ->
        (function LNil -> l1
        | LCons (z,zs) -> LCons (x, LCons (z, interleave3 xs LNil zs)))
      | LCons (y,ys) as l2 ->
        (function LNil -> LCons (x, LCons (y, interleave3 xs ys LNil))
          | LCons (z,zs) ->
            LCons (x, LCons (y, LCons (z, interleave3 xs ys zs)))))"
        [1,"∃n, k, i. δ = (List i → List k → List n → List (n + k + i))"];
    );

  "append" >::
    (fun () ->
       todo "disjunctive patterns";
       skip_if !debug "debug";
       test_case "list append numeric"
"newtype Elem
newtype List : num
newcons LNil : List 0
newcons LCons : ∀n [0≤n]. Elem * List n ⟶ List (n+1)

let rec append =
  function LNil -> (function (LNil | LCons (_,_)) as l -> l)
    | LCons (x, xs) -> (fun l -> LCons (x, append xs l))"
        [1,"∃n, k. δ = (List n → List k → List (n + k))"];
    );

  "binary increment" >::
    (fun () ->
       skip_if !debug "debug";
       test_case "binary increment"
"newtype Binary : num

newcons Zero : Binary 0
newcons PZero : ∀n [0≤n]. Binary n ⟶ Binary(2 n)
newcons POne : ∀n [0≤n]. Binary n ⟶ Binary(2 n + 1)

let rec increment =
  function Zero -> POne Zero
    | PZero a1 -> POne a1
    | POne a1 -> PZero (increment a1)"
        [1,"∃n. δ = (Binary n → Binary (n + 1))"]
    );

  "binary plus expanded" >::
    (fun () ->
       skip_if !debug "debug";
       test_case "binary plus"
"newtype Binary : num
newtype Carry : num

newcons Zero : Binary 0
newcons PZero : ∀n [0≤n]. Binary n ⟶ Binary(2 n)
newcons POne : ∀n [0≤n]. Binary n ⟶ Binary(2 n + 1)

newcons CZero : Carry 0
newcons COne : Carry 1

let rec plus =
  function CZero ->
    (function Zero ->
        (function Zero -> Zero
          | PZero _ as b -> b
          | POne _ as b -> b)
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
        [1,"∃n, k, i. δ = (Carry i → Binary k → Binary n → Binary (n + k + i))"]
    );

  "binary plus" >::
    (fun () ->
       todo "disjunctive patterns";
       skip_if !debug "debug";
       test_case "binary plus"
"newtype Binary : num
newtype Carry : num

newcons Zero : Binary 0
newcons PZero : ∀n [0≤n]. Binary n ⟶ Binary(2 n)
newcons POne : ∀n [0≤n]. Binary n ⟶ Binary(2 n + 1)

newcons CZero : Carry 0
newcons COne : Carry 1

let rec plus =
  function CZero ->
    (function Zero -> (function (Zero | PZero _ | POne _) as b -> b)
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
        [1,"∃n, k, i. δ = (Carry i → Binary k → Binary n → Binary (n + k + i))"]
    );

  "binary plus with test" >::
    (fun () ->
       skip_if !debug "debug";
       test_case "binary plus test"
"newtype Binary : num
newtype Carry : num

newcons Zero : Binary 0
newcons PZero : ∀n [0≤n]. Binary n ⟶ Binary(2 n)
newcons POne : ∀n [0≤n]. Binary n ⟶ Binary(2 n + 1)
newcons CZero : Carry 0
newcons COne : Carry 1

external let eq_Binary :  ∀n [0≤n]. Binary n → Binary n → Bool = \"(=)\"

let rec plus =
  function CZero ->
    (function
      | Zero ->
        (function Zero -> Zero
          | PZero _ as b -> b
          | POne _ as b -> b)
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
        [1,"∃n, k, i. δ = (Carry i → Binary k → Binary n → Binary (n + k + i))"]
    );

  "flatten_pairs" >::
    (fun () ->
       skip_if !debug "debug";
       test_case "list flatten_pairs"
"newtype List : type * num
newcons LNil : ∀a. List(a, 0)
newcons LCons : ∀n, a [0≤n]. a * List(a, n) ⟶ List(a, n+1)

let rec flatten_pairs =
  function LNil -> LNil
    | LCons ((x, y), l) ->
      LCons (x, LCons (y, flatten_pairs l))"
        [1,"∃n, a. δ = (List ((a, a), n) → List (a, 2 n))"];
    );

  "escape castle" >::
    (fun () ->
       skip_if !debug "debug";
       test_case "escape castle"
"newtype Room
newtype Yard
newtype Outside

newtype Placement : type
newcons Room : Room ⟶ Placement Room
newcons Yard : Yard ⟶ Placement Yard
newcons Outside : Outside ⟶ Placement Outside

external leave : Room → ∃t. Placement t = \"leave\"
external enter : Yard → Room = \"enter\"

let rec escape = function Outside x -> x
  | Room x ->
    let y = leave x in
    escape y
  | Yard x ->
    let y = leave (enter x) in
    escape y"
        [1,"∃a. δ = (Placement a → Outside)"]

    );

  "easy nested universal" >::
    (fun () ->
       skip_if !debug "debug";
       test_case "less nested universal"
"newtype Place : type
newtype Nearby : type * type
newcons Transitive : ∀a,b,c. Nearby (a, b) * Nearby (b, c) ⟶ Nearby (a, c)
external wander : ∀a. Place a → ∃b. (Place b, Nearby (a, b)) = \"wander\"
newtype Meet : type * type
newcons Close : ∀a,b. Nearby (a, b) ⟶ Meet (a, b)
newcons NotClose : ∀a, b. Meet (a, b)
external compare : ∀a,b. Place a → Place b → Meet (a, b) = \"compare\"
let rec walk = fun x goal ->
  match compare x goal with
  | Close g -> g
  | NotClose ->
    let y, to_y = wander x in
    Transitive (to_y, walk y goal)"
        [1,"∃a, b. δ = (Place a → Place b → Nearby (a, b))"];
    );

  "equational nested universal" >::
    (fun () ->
       skip_if !debug "debug";
       test_case "equational nested universal"
"newtype Place : type
newtype Nearby : type * type
newtype A
newtype B
newcons LocA : Place A
newcons LocB : Place B
external is_nearby : ∀a,b. Nearby (a, b) → Bool = \"is_nearby\"
newcons Here : ∀a. Place a * Place a ⟶ Nearby (a, a)
newcons Transitive : ∀a,b,c. Nearby (a, b) * Nearby (b, c) ⟶ Nearby (a, c)
external wander : ∀a. Place a → ∃b. (Place b, Nearby (a, b)) = \"wander\"
newtype Meet : type * type
newcons Same : ∀a,b [a=b]. Meet (a, b)
newcons NotSame : ∀a, b. Meet (a, b)
external compare : ∀a,b. Place a → Place b → Meet (a, b) = \"compare\"
let rec walk = fun x goal ->
  match compare x goal with
  | Same -> Here (x, goal)
  | NotSame ->
    let y, to_y = wander x in
    Transitive (to_y, walk y goal)
test (is_nearby (walk LocA LocB))"
        [1,"∃a, b. δ = (Place a → Place b → Nearby (a, b))"];
    );


  "double nested universal" >::
    (fun () ->
       skip_if !debug "debug";
       test_case "double nested universal"
"newtype Place : type
newtype Nearby : type * type
newtype A
newtype B
newcons LocA : Place A
newcons LocB : Place B
external is_nearby : ∀a,b. Nearby (a, b) → Bool = \"is_nearby\"
newcons Transitive : ∀a,b,c. Nearby (a, b) * Nearby (b, c) ⟶ Nearby (a, c)
external wander : ∀a. Place a → ∃b. (Place b, Nearby (a, b)) = \"wander\"
newtype Meet : type * type
newcons Close : ∀a,b. Nearby (a, b) ⟶ Meet (a, b)
newcons NotClose : ∀a, b. Meet (a, b)
external compare : ∀a,b. Place a → Place b → Meet (a, b) = \"compare\"
let rec walk = fun x goal ->
  match compare x goal with
  | Close g -> g
  | NotClose ->
    let y, to_y = wander x in
    let to_z = walk y goal in
    Transitive (to_y, to_z)
test (is_nearby (walk LocA LocB))"
        [1,"∃a, b. δ = (Place a → Place b → Nearby (a, b))"];
    );

  "find castle" >::
    (fun () ->
       skip_if !debug "debug";
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

external wander : ∀a. Placement a → ∃b. Placement b = \"wander\"

let rec find_castle = efunction
  | CastleRoom x -> Room x
  | CastleYard x -> Yard x
  | Village _ as x ->
    let y = wander x in
    find_castle y"
        [2,"∃a. δ = (Placement a → ∃2:a.Castle a)"];
    );

  "find castle big" >::
    (fun () ->
       skip_if !debug "debug";
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

external wander : ∀a. Placement a → ∃b. Placement b = \"wander\"

let rec find = efunction
  | CastleRoom x -> Room x
  | CastleYard x -> Yard x
  | Garden _ as x ->
    let y = wander x in
    find y
  | Village _ as x ->
    let y = wander x in
    find y"
        [2,"∃a. δ = (Placement a → ∃2:a.Castle a)"];
    );

  "search castle shortcut" >::
    (fun () ->
       skip_if !debug "debug";
       test_case "search castle shortcut"
"newtype Room
newtype Yard
newtype Village

newtype Castle : type
newtype Placement : type
newcons Room : Room ⟶ Castle Room
newcons Yard : Yard ⟶ Castle Yard
newcons CastleRoom : Room ⟶ Placement Room
newcons Village : Village ⟶ Placement Village

newtype Explore
newcons Ordinary : Explore
newcons Shortcut : Yard ⟶ Explore

external wander : ∀a. Placement a → ∃b. Placement b = \"wander\"
external check : ∀a. Placement a → Explore = \"check\"

let rec search = efunction
  | CastleRoom x -> Room x
  | Village _ as x ->
    let y = wander x in
    ematch check y with
    | Ordinary -> search y
    | Shortcut z -> Yard z"
        [2,"∃a. δ = (Placement a → ∃3:a.Castle a)"];
    );

  "search castle distance" >::
    (fun () ->
       skip_if !debug "debug";
       test_case "find castle distance"
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

external wander : ∀a. Placement a → ∃b. Placement b = \"wander\"
external closer : ∀a. Placement a → Bool = \"closer\"

let rec search = efunction
  | CastleRoom x -> Room x
  | CastleYard x -> Yard x
  | Village _ as x ->
    let y = wander x in
    ematch closer y with
    | True -> search y
    | False -> search x"
        [2,"∃a. δ = (Placement a → ∃3:a.Castle a)"];
    );

  "search castle distance A/B" >::
    (fun () ->
       skip_if !debug "debug";
       test_case "find castle distance A/B"
"newtype Boolean : type
newtype A
newtype B
newcons True : Boolean A
newcons False : Boolean B
newtype Room
newtype Yard
newtype Village

newtype Castle : type
newtype Placement : type
newcons Room : Room ⟶ Castle Room
newcons Yard : Yard ⟶ Castle Yard
newcons CastleRoom : Room ⟶ Placement Room
newcons CastleYard : Yard ⟶ Placement Yard
newcons Village : Village ⟶ Placement Village

external wander : ∀a. Placement a → ∃b. Placement b = \"wander\"
external closer : ∀a. Placement a → ∃b. Boolean b = \"closer\"

let rec search = efunction
  | CastleRoom x -> Room x
  | CastleYard x -> Yard x
  | Village _ as x ->
    let y = wander x in
    let b = closer y in
    ematch b with
    | True -> search y
    | False -> search x"
        [2,"∃a. δ = (Placement a → ∃4:a.Castle a)"];
    );

  "castle not existential" >::
    (fun () ->
       skip_if !debug "debug";
       test_case "castle not existential"
"newtype Yard
newtype Village

newtype Castle : type
newtype Placement : type
newcons Yard : Yard ⟶ Castle Yard
newcons CastleYard : Yard ⟶ Placement Yard
newcons Village : Village ⟶ Placement Village

external wander : Village → ∃b. Placement b = \"wander\"

let rec search = efunction
  | CastleYard x -> Yard x
  | Village x ->
    let y = wander x in
    search y"
        [2,"∃a. δ = (Placement a → ∃2:.Castle Yard)"];
    );

  "castle nested not existential" >::
    (fun () ->
       skip_if !debug "debug";
       test_case "castle nested not existential"
"newtype Answer
newcons No : Answer
newcons Nearby : Answer
newtype Yard
newtype Village

newtype Castle : type
newtype Placement : type
newcons Closeby : Castle Yard
newcons Yard : Yard ⟶ Castle Yard
newcons CastleYard : Yard ⟶ Placement Yard
newcons Village : Village ⟶ Placement Village

external wander : Village → ∃b. Placement b = \"wander\"
external entrance : Village → Answer = \"entrance\"

let rec search = efunction
  | CastleYard x -> Yard x
  | Village x ->
    ematch entrance x with
    | Nearby -> Closeby
    | No ->
      let y = wander x in
      search y"
        [2,"∃a. δ = (Placement a → ∃3:.Castle Yard)"];
    );

  "castle nested existential factored" >::
    (fun () ->
       skip_if !debug "debug";
       test_case "castle nested existential factored"
"newtype Answer
newcons Yes : Answer
newcons No : Answer
newtype Room
newtype Yard
newtype Village

newtype Castle : type
newtype Placement : type
newcons Yard : Yard ⟶ Castle Yard
newcons CastleYard : Yard ⟶ Placement Yard
newcons Village : Village ⟶ Placement Village

external wander : Village → ∃b. Placement b = \"wander\"
external entrance : Village → Answer = \"entrance\"
external enter : ∀a. Placement a → Castle a = \"enter\"

let rec search = efunction
  | CastleYard x -> Yard x
  | Village x ->
    let y = wander x in
    ematch entrance x with
    | Yes ->
      enter y
    | No ->
      search y"
        [2,"∃a. δ = (Placement a → ∃3:a.Castle a)"];
    );

  "castle nested existential" >::
    (fun () ->
       skip_if !debug "debug";
       test_case "castle nested existential"
"newtype Answer
newcons Yes : Answer
newcons No : Answer
newtype Yard
newtype Village
newtype Room
newtype Castle : type
newtype Placement : type
newcons Yard : Yard ⟶ Castle Yard
newcons CastleYard : Yard ⟶ Placement Yard
newcons Village : Village ⟶ Placement Village

external wander : Village → ∃b. Placement b = \"wander\"
external entrance : Village → Answer = \"entrance\"
external enter : ∀a. Placement a → Castle Room = \"enter\"

let rec search = efunction
  | CastleYard x -> Yard x
  | Village x ->
    ematch entrance x with
    | Yes ->
      let y = wander x in
      enter y
    | No ->
      let y = wander x in
      search y"
        [2,"∃a. δ = (Placement a → ∃3:a.Castle a)"];
    );

  "existential by hand" >::
    (fun () ->
       skip_if !debug "debug";
       test_case "existential by hand"
"newtype Place : type
newtype Nearby : type * type
newtype Near : type
newcons Here : ∀a. Place a ⟶ Nearby (a, a)
newcons Near : ∀a,b. Nearby (a, b) ⟶ Near a
newcons Transitive : ∀a,b,c. Nearby (a, b) * Nearby (b, c) ⟶ Nearby (a, c)
external wander : ∀a. Place a → ∃b. (Place b, Nearby (a, b)) = \"wander\"
external finish : ∀a. Place a → Bool = \"finish\"
let rec walk = fun x ->
  match finish x with
  | True -> Near (Here x)
  | False ->
    let y, to_y = wander x in
    match walk y with
    | Near to_z ->
      Near (Transitive (to_y, to_z))"
        [1,"∃a. δ = (Place a → Near a)"];
    );

  "existential with param" >::
    (fun () ->
       skip_if !debug "debug";
       test_case ~more_existential:true "existential with param"
"newtype Place : type
newtype Nearby : type * type
newcons Here : ∀a. Place a ⟶ Nearby (a, a)
newcons Transitive : ∀a,b,c. Nearby (a, b) * Nearby (b, c) ⟶ Nearby (a, c)
external wander : ∀a. Place a → ∃b. (Place b, Nearby (a, b)) = \"wander\"
external finish : ∀a. Place a → Bool = \"finish\"
let rec walk = fun x ->
  ematch finish x with
  | True -> Here x
  | False ->
    let y, to_y = wander x in
    let to_z = walk y in
    Transitive (to_y, to_z)"
        [2,"∃a. δ = (Place a → ∃2:b.Nearby (a, b))"];
    );

  "universal option" >::
    (fun () ->
       skip_if !debug "debug";
       test_case "universal option"
"newtype Option : type
newcons None : ∀a. Option a
newcons Some : ∀a. a ⟶ Option a

let rec one_of =
  function (Some _ as a) -> (function _ -> a)
  | None -> (function None -> None | (Some _ as b) -> b)"
        [1,"∃a. δ = (Option a → Option a → Option a)"];
    );

  "existential option" >::
    (fun () ->
       skip_if !debug "debug";
       test_case ~more_existential:true "existential option"
"newtype Option : type
newcons None : ∀a. Option a
newcons Some : ∀a. a ⟶ Option a

let rec one_of =
  efunction (Some _ as a) -> (efunction _ -> a)
  | None -> (efunction None -> None | (Some _ as b) -> b)"
        [2,"∃a, b. δ = (Option a → Option b → ∃3:a.Option a)"];
    );

  "not existential option" >::
    (fun () ->
       skip_if !debug "debug";
       test_case "not existential option"
"newtype Option : type
newcons None : ∀a. Option a
newcons Some : ∀a. a ⟶ Option a
external f : ∀a. a → a → a = \"f\"

let rec one_of =
  efunction (Some a) -> (efunction None -> a | (Some b) -> f a b)
  | None -> (efunction (Some b) -> b)"
        [2,"∃a. δ = (Option a → Option a → ∃3:.a)"];
    );

  "non-num map not existential poly" >::
    (fun () ->
       skip_if !debug "debug";
       test_case "list without length map not existential poly"
"newtype List : type
newcons LNil : ∀a. List a
newcons LCons : ∀a. a * List a ⟶ List a

let rec map = fun f ->
  efunction LNil -> LNil
    | LCons (x, xs) ->
      let ys = map f xs in
      LCons (f x, ys)"
        [2,"∃a, b. δ = ((a → b) → List a → ∃1:.List b)"];
    );

  "non-num map not existential mono" >::
    (fun () ->
       skip_if !debug "debug";
       test_case "list without length map not existential mono"
"newtype List : type
newcons LNil : ∀a. List a
newcons LCons : ∀a. a * List a ⟶ List a
newtype Foo
newtype Bar

external f : Foo → Bar = \"f\"

let rec map =
  efunction LNil -> LNil
    | LCons (x, xs) ->
      let ys = map xs in
      LCons (f x, ys)"
        [2,"∃. δ = (List Foo → ∃1:.List Bar)"];
    );

  "map not existential mono" >::
    (fun () ->
       skip_if !debug "debug";
       test_case "list map not existential mono"
"newtype Elem
newtype List : num
newcons LNil : List 0
newcons LCons : ∀n [0≤n]. Elem * List n ⟶ List(n+1)

external f : Elem → Elem = \"f\"

let rec map =
  efunction LNil -> LNil
    | LCons (x, xs) ->
      let ys = map xs in
      LCons (f x, ys)"
        [2,"∃n. δ = (List n → ∃1:[0 ≤ n].List n)"];
    );

  "map not existential poly" >::
    (fun () ->
       skip_if !debug "debug";
       test_case "list map not existential poly"
"newtype List : type * num
newcons LNil : ∀a. List(a, 0)
newcons LCons : ∀n, a [0≤n]. a * List(a, n) ⟶ List(a, n+1)

let rec map = fun f ->
  efunction LNil -> LNil
    | LCons (x, xs) ->
      let ys = map f xs in
      LCons (f x, ys)"
        [2,"∃n, a, b. δ = ((a → b) → List (a, n) → ∃1:[0 ≤ n].List (b, n))"];
    );

  "map not existential instance" >::
    (fun () ->
       skip_if !debug "debug";
       test_case "list map not existential mono"
"newtype List : type * num
newcons LNil : ∀a. List(a, 0)
newcons LCons : ∀n, a [0≤n]. a * List(a, n) ⟶ List(a, n+1)
newtype Foo
newtype Bar

external f : Foo → Bar = \"f\"

let rec map =
  efunction LNil -> LNil
    | LCons (x, xs) ->
      let ys = map xs in
      LCons (f x, ys)"
        [2,"∃n. δ = (List (Foo, n) → ∃1:[0 ≤ n].List (Bar, n))"];
    );

  "filter mono" >::
    (fun () ->
       skip_if !debug "debug";
       test_case "monomorphic list filter"
"newtype Bar
newtype List : num
newcons LNil : List 0
newcons LCons : ∀n [0≤n]. Bar * List n ⟶ List(n+1)
external f : Bar → Bool = \"f\"

let rec filter =
  efunction LNil -> LNil
    | LCons (x, xs) ->
      ematch f x with
        | True ->
          let ys = filter xs in
          LCons (x, ys)
	| False ->
          filter xs"
        [2,"∃n. δ = (List n → ∃2:k[k ≤ n ∧ 0 ≤ k ∧ 0 ≤ n].List k)"];

    );

  "filter Bar" >::
    (fun () ->
       skip_if !debug "debug";
       test_case "list filter: Bar"
"newtype List : type * num
newcons LNil : ∀a. List(a, 0)
newcons LCons : ∀n, a [0≤n]. a * List(a, n) ⟶ List(a, n+1)

newtype Bar
external f : Bar → Bool = \"f\"

let rec filter =
  efunction LNil -> LNil
    | LCons (x, xs) ->
      ematch f x with
        | True ->
          let ys = filter xs in
          LCons (x, ys)
	| False ->
          filter xs"
        [2,"∃n.
  δ =
    (List (Bar, n) → ∃2:k[k ≤ n ∧ 0 ≤ k ∧ 0 ≤ n].List (Bar, k))"];

    );

  "filter poly" >::
    (fun () ->
       skip_if !debug "debug";
       test_case "polymorphic list filter"
"newtype List : type * num
newcons LNil : ∀a. List(a, 0)
newcons LCons : ∀n, a [0≤n]. a * List(a, n) ⟶ List(a, n+1)

let rec filter = fun f ->
  efunction LNil -> LNil
    | LCons (x, xs) ->
      ematch f x with
        | True ->
          let ys = filter f xs in
          LCons (x, ys)
	| False ->
          filter f xs"
        [2,"∃n, a.
  δ =
    ((a → Bool) → List (a, n) → ∃2:k[k ≤ n ∧ 0 ≤ k ∧
       0 ≤ n].List (a, k))"];

    );

  "poly filter map" >::
    (fun () ->
       skip_if !debug "debug";
       test_case "list filter map"
"newtype List : type * num
newcons LNil : ∀a. List(a, 0)
newcons LCons : ∀n, a [0≤n]. a * List(a, n) ⟶ List(a, n+1)

let rec filter = fun f g ->
  efunction LNil -> LNil
    | LCons (x, xs) ->
      ematch f x with
        | True ->
          let ys = filter f g xs in
          LCons (g x, ys)
	| False ->
          filter f g xs"
        [2,"∃n, a, b.
  δ =
    ((a → Bool) → (a → b) → List (a, n) → ∃2:k[k ≤ n ∧
       0 ≤ k ∧ 0 ≤ n].List (b, k))"];

    );

  "binary upper bound-wrong" >::
    (fun () ->
       skip_if !debug "debug";
       (* We need to expand the branch when the first argument is
          [Zero] from [efunction b -> b] to the cases as below, to
          convey the fact that the numerical parameter is non-negative. *)
       test_case "binary upper bound -- bitwise or"
"newtype Binary : num
newcons Zero : Binary 0
newcons PZero : ∀n [0≤n]. Binary n ⟶ Binary(2 n)
newcons POne : ∀n [0≤n]. Binary n ⟶ Binary(2 n + 1)

let rec ub = efunction
  | Zero -> (efunction b -> b)
  | PZero a1 as a ->
      (efunction Zero -> a
        | PZero b1 ->
          let r = ub a1 b1 in
          PZero r
        | POne b1 ->
          let r = ub a1 b1 in
          POne r)
  | POne a1 as a ->
      (efunction Zero -> a
        | PZero b1 ->
          let r = ub a1 b1 in
          POne r
        | POne b1 ->
          let r = ub a1 b1 in
          POne r)"
        [2,"∃n, k.
  δ =
    (Binary k → Binary n → ∃4:i[i ≤ n + k ∧ n ≤ i ∧
       0 ≤ k].Binary i)"]
    );

  "binary upper bound expanded" >::
    (fun () ->
       skip_if !debug "debug";
       (* We need to expand the branch when the first argument is
          [Zero] from [efunction b -> b] to the cases as below, to
          convey the fact that the numerical parameter is non-negative. *)
       test_case "binary upper bound -- bitwise or"
"newtype Binary : num
newcons Zero : Binary 0
newcons PZero : ∀n [0≤n]. Binary(n) ⟶ Binary(n+n)
newcons POne : ∀n [0≤n]. Binary(n) ⟶ Binary(n+n+1)

let rec ub = efunction
  | Zero ->
      (efunction Zero -> Zero
        | PZero b1 as b -> b
        | POne b1 as b -> b)
  | PZero a1 as a ->
      (efunction Zero -> a
        | PZero b1 ->
          let r = ub a1 b1 in
          PZero r
        | POne b1 ->
          let r = ub a1 b1 in
          POne r)
  | POne a1 as a ->
      (efunction Zero -> a
        | PZero b1 ->
          let r = ub a1 b1 in
          POne r
        | POne b1 ->
          let r = ub a1 b1 in
          POne r)"
        [2,"∃n, k.
  δ =
    (Binary k → Binary n → ∃4:i[i ≤ n + k ∧ n ≤ i ∧ k ≤ i ∧
       0 ≤ k ∧ 0 ≤ n].Binary i)"]
    );

  "binary upper bound" >::
    (fun () ->
       todo "disjunctive patterns";
       skip_if !debug "debug";
       (* We need to expand the branch when the first argument is
          [Zero] from [efunction b -> b] to the cases as below, to
          convey the fact that the numerical parameter is non-negative. *)
       test_case "binary upper bound -- bitwise or"
"newtype Binary : num
newcons Zero : Binary 0
newcons PZero : ∀n [0≤n]. Binary n ⟶ Binary(2 n)
newcons POne : ∀n [0≤n]. Binary n ⟶ Binary(2 n + 1)

let rec ub = efunction
  | Zero -> (efunction (Zero | PZero _ | POne _) as b -> b)
  | PZero a1 as a ->
      (efunction Zero -> a
        | PZero b1 ->
          let r = ub a1 b1 in
          PZero r
        | POne b1 ->
          let r = ub a1 b1 in
          POne r)
  | POne a1 as a ->
      (efunction Zero -> a
        | PZero b1 ->
          let r = ub a1 b1 in
          POne r
        | POne b1 ->
          let r = ub a1 b1 in
          POne r)"
        [2,"∃n, k.
  δ =
    (Binary k → Binary n → ∃4:i[0 ≤ k ∧ n ≤ i ∧
       i ≤ n + k].Binary i)"]
    );

  "nested recursion simple eval" >::
    (fun () ->
       skip_if !debug "debug";
       test_case "nested recursion eval with literal numbers only"
"newtype Term : type
newtype Num : num
newtype Calc : num

external let is_zero : ∀i. Num i → Bool = \"(=) 0\"

newcons Lit : ∀k. Num k ⟶ Calc k

newcons IsZero : ∀k. Calc k ⟶ Term Bool
newcons If : ∀a. Term Bool * Term a * Term a ⟶ Term a

let rec eval =
  let rec calc =
    function
    | Lit i -> i in
  function
  | IsZero x -> is_zero (calc x)
  | If (b, t, e) -> match eval b with True -> eval t | False -> eval e"

        [1, "∃a. δ = (Term a → a)";
        2, "∃n. δ = (Calc n → Num n)"]
    );

  "nested recursion eval" >::
    (fun () ->
       skip_if !debug "debug";
       test_case "nested recursion eval with plus only"
"newtype Term : type
newtype Num : num
newtype Calc : num

external let is_zero : ∀i. Num i → Bool = \"(=) 0\"

newcons Lit : ∀k. Num k ⟶ Calc k
newcons Plus : ∀i,j. Calc i * Calc j ⟶ Calc (i+j)

newcons IsZero : ∀k. Calc k ⟶ Term Bool
newcons If : ∀a. Term Bool * Term a * Term a ⟶ Term a
newcons Pair : ∀a, b. Term a * Term b ⟶ Term (a, b)
newcons Fst : ∀a, b. Term (a, b) ⟶ Term a
newcons Snd : ∀a, b. Term (a, b) ⟶ Term b

let rec eval =
  let rec calc =
    function
    | Lit i -> i
    | Plus (i, j) -> calc i + calc j in
  function
  | IsZero x -> is_zero (calc x)
  | If (b, t, e) -> (match eval b with True -> eval t | False -> eval e)
  | Pair (x, y) -> eval x, eval y
  | Fst p -> (match eval p with x, y -> x)
  | Snd p -> (match eval p with x, y -> y)"

        [1, "∃a. δ = (Term a → a)";
        2, "∃n. δ = (Calc n → Num n)"]
    );

  "mutual recursion simple calc" >::
    (fun () ->
       skip_if !debug "debug";
       test_case "mutual recursion simple universal eval and existential calc"
"newtype Term : type
newtype Num : num
newtype Calc

external let is_zero : ∀i. Num i → Bool = \"(=) 0\"
external cond : ∀i,j. Bool → Num i → Num j → ∃k. Num k = \"fun c a b -> if c then a else b\"

newcons Lit : ∀k. Num k ⟶ Calc
newcons Cond : Term Bool * Calc * Calc ⟶ Calc

newcons IsZero : Calc ⟶ Term Bool
newcons If : ∀a. Term Bool * Term a * Term a ⟶ Term a

let rec eval =
  let rec calc =
    efunction
    | Lit i -> i
    | Cond (b, t, e) ->
      let rt = calc t in
      let re = calc e in
      cond (eval b) rt re in
  function
  | IsZero x -> let r = calc x in is_zero r
  | If (b, t, e) -> match eval b with True -> eval t | False -> eval e"

        [2, "∃a. δ = (Term a → a)";
        3, "∃. δ = (Calc → ∃2:n.Num n)"]
    );

  "mutual recursion medium calc" >::
    (fun () ->
       skip_if !debug "debug";
       test_case "mutual recursion universal eval and existential calc"
"newtype Term : type
newtype Num : num
newtype Calc

external is_zero : ∀i. Num i → Bool = \"(=) 0\"
external cond : ∀i,j. Bool → Num i → Num j → ∃k. Num k = \"fun c a b -> if c then a else b\"

newcons Lit : ∀k. Num k ⟶ Calc
newcons Cond : Term Bool * Calc * Calc ⟶ Calc

newcons IsZero : Calc ⟶ Term Bool
newcons If : ∀a. Term Bool * Term a * Term a ⟶ Term a
newcons Pair : ∀a, b. Term a * Term b ⟶ Term (a, b)

let rec eval =
  let rec calc =
    efunction
    | Lit i -> i
    | Cond (b, t, e) ->
      let rt = calc t in
      let re = calc e in
      cond (eval b) rt re in
  function
  | IsZero x -> let r = calc x in is_zero r
  | If (b, t, e) -> (match eval b with True -> eval t | False -> eval e)
  | Pair (x, y) -> eval x, eval y"

        [2, "∃a. δ = (Term a → a)";
        3, "∃. δ = (Calc → ∃2:n.Num n)"]
    );

  "mutual recursion calc" >::
    (fun () ->
       skip_if !debug "debug";
       test_case "mutual recursion universal eval and existential calc"
"newtype Term : type
newtype Num : num
newtype Calc

external let mult : ∀i,j. Num i → Num j → ∃k. Num k = \"(*)\"
external let is_zero : ∀i. Num i → Bool = \"(=) 0\"
external cond : ∀i,j. Bool → Num i → Num j → ∃k. Num k = \"fun c a b -> if c then a else b\"

newcons Lit : ∀k. Num k ⟶ Calc
newcons Plus : Calc * Calc ⟶ Calc
newcons Mult : Calc * Calc ⟶ Calc
newcons Cond : Term Bool * Calc * Calc ⟶ Calc

newcons IsZero : Calc ⟶ Term Bool
newcons If : ∀a. Term Bool * Term a * Term a ⟶ Term a
newcons Pair : ∀a, b. Term a * Term b ⟶ Term (a, b)
newcons Fst : ∀a, b. Term (a, b) ⟶ Term a
newcons Snd : ∀a, b. Term (a, b) ⟶ Term b

let rec eval =
  let rec calc =
    efunction
    | Lit i -> i
    | Plus (x, y) ->
      let rx = calc x in
      let ry = calc y in
      rx + ry
    | Mult (x, y) ->
      let rx = calc x in
      let ry = calc y in
      mult rx ry
    | Cond (b, t, e) ->
      let rt = calc t in
      let re = calc e in
      cond (eval b) rt re in
  function
  | IsZero x -> let r = calc x in is_zero r
  | If (b, t, e) -> (match eval b with True -> eval t | False -> eval e)
  | Pair (x, y) -> eval x, eval y
  | Fst p -> (match eval p with x, y -> x)
  | Snd p -> (match eval p with x, y -> y)"

        [2, "∃a. δ = (Term a → a)";
        3, "∃. δ = (Calc → ∃3:n.Num n)"]
    );

  (* TODO: mutual recursion where the nested function has nontrivial
     postcondition, which needs to be bootstrapped from its
     non-recursive part. *)

  "nonrec simple" >::
    (fun () ->
       skip_if !debug "debug";
       test_nonrec_case "nonrec simple"
"newtype Order : num * num
external compare : ∀i, j. Num i → Num j → (Order (i, j), Int) = \"compare\"
let cmp7and8, res = compare 7 8
"
        [1, "(Order (7, 8), Int)"];

    );

  (* More non-recursive [let] tests are performed in {!InvarGenTTest}. *)

  "binomial heap--rank" >::
    (fun () ->
       skip_if !debug "debug";
       (* Here [rank] is defined using [let rec], the correct [let]
          forms are tested from {!InvarGenTTest}. *)
       test_case "binomial heap--rank"
"newtype Tree : type * num
newtype Forest : type * num

newcons Node : ∀a, k [0≤k]. Num k * a * Forest (a, k) ⟶ Tree (a, k)
newcons TCons :
  ∀a, n [0≤n]. Tree (a, n) * Forest (a, n) ⟶ Forest (a, n+1)
newcons TNil : ∀a. Forest (a, 0)

let rec rank = function Node (r, _, _) -> r
"
        [1,"∃n, a. δ = (Tree (a, n) → Num n)"];
    );

  "binomial heap--link" >::
    (fun () ->
       skip_if !debug "debug";
       (* Here [link] is defined using [let rec], the correct [let]
          forms are tested from {!InvarGenTTest}. *)
       test_case "binomial heap--link"
"newtype Tree : type * num
newtype Forest : type * num

newcons Node : ∀a, k [0≤k]. Num k * a * Forest (a, k) ⟶ Tree (a, k)
newcons TCons :
  ∀a, n [0≤n]. Tree (a, n) * Forest (a, n) ⟶ Forest (a, n+1)
newcons TNil : ∀a. Forest (a, 0)

external let leq : ∀a. a → a → Bool = \"(<=)\"

let rec link = function
  | (Node (r, x1, c1) as t1), (Node (_, x2, c2) as t2) ->
    match leq x1 x2 with
    | True -> Node (r+1, x1, TCons (t2, c1))
    | False -> Node (r+1, x2, TCons (t1, c2))
"
        [1,"∃n, a. δ = ((Tree (a, n), Tree (a, n)) → Tree (a, n + 1))"];
    );

  "unary minimum expanded" >::
    (fun () ->
       skip_if !debug "debug";
       test_case "unary minimum expanded"
"newtype Unary : num
newcons UNil : Unary 0
newcons UCons : ∀n [0≤n]. Unary n ⟶ Unary (n+1)

let rec zip =
  efunction
    | UNil, UNil -> UNil
    | UNil, UCons _ -> UNil
    | UCons _, UNil -> UNil
    | UCons xs, UCons ys ->
      let zs = zip (xs, ys) in
      UCons zs"
        [2,"∃n, k.
  δ =
    ((Unary n, Unary k) → ∃1:i[i=min (n, k) ∧ 0 ≤ i ∧ 0 ≤ k ∧
       0 ≤ n].Unary i)"]
    );

  "list zip prefix expanded" >::
    (fun () ->
       skip_if !debug "debug";
       test_case "list zip prefix expanded"
"newtype List : type * num
newcons LNil : ∀a. List(a, 0)
newcons LCons : ∀n, a [0≤n]. a * List(a, n) ⟶ List(a, n+1)

let rec zip =
  efunction
    | LNil, LNil -> LNil
    | LNil, LCons (_, _) -> LNil
    | LCons (_, _), LNil -> LNil
    | LCons (x, xs), LCons (y, ys) ->
      let zs = zip (xs, ys) in
      LCons ((x, y), zs)"
        [2,"∃n, k, a, b.
  δ =
    ((List (a, n), List (b, k)) → ∃1:i[i=min (n, k) ∧ 0 ≤ i ∧
       0 ≤ k ∧ 0 ≤ n].List ((a, b), i))"]
    );

  "unary maximum" >::
    (fun () ->
       skip_if !debug "debug";
       test_case "unary minimum expanded"
"newtype Unary : num
newcons UNil : Unary 0
newcons UCons : ∀n [0≤n]. Unary n ⟶ Unary (n+1)

let rec map2 =
  efunction
    | UNil, UNil -> UNil
    | UNil, (UCons _ as l) -> l
    | (UCons _ as l), UNil -> l
    | UCons xs, UCons ys ->
      let zs = map2 (xs, ys) in
      UCons zs"
        [2,"∃n, k.
  δ =
    ((Unary n, Unary k) → ∃1:i[i=max (n, k) ∧ i ≤ n + k ∧
       0 ≤ k ∧ 0 ≤ n].Unary i)"]
    );

  "list map2 with postfix too existential" >::
    (fun () ->
       skip_if !debug "debug";
       test_case "list map2 with postfix too existential"
"newtype List : type * num
newcons LNil : ∀a. List(a, 0)
newcons LCons : ∀n, a [0≤n]. a * List(a, n) ⟶ List(a, n+1)

let rec map2 = fun f ->
  efunction
    | LNil, LNil -> LNil
    | LNil, (LCons (_, _) as l) -> l
    | (LCons (_, _) as l), LNil -> l
    | LCons (x, xs), LCons (y, ys) ->
      let zs = map2 f (xs, ys) in
      LCons (f x y, zs)"
        [2,"∃n, k, a.
  δ =
    ((a → a → a) → (List (a, n), List (a, k)) →
       ∃1:i[i=max (n, k) ∧ i ≤ n + k ∧ 0 ≤ k ∧
       0 ≤ n].List (a, i))"]
    );

  "avl_tree--height" >::
    (fun () ->
       skip_if !debug "debug";
       test_case "avl_tree--height"
"newtype Avl : type * num
newcons Empty : ∀a. Avl (a, 0)
newcons Node :
  ∀a,k,m,n [k=max(m,n) ∧ 0≤m ∧ 0≤n ∧ n≤m+2 ∧ m≤n+2].
     Avl (a, m) * a * Avl (a, n) * Num (k+1) ⟶ Avl (a, k+1)

let height = function
  | Empty -> 0
  | Node (_, _, _, k) -> k"
        [1,"∃n, a. δ = (Avl (a, n) → Num n)"];
    );

  "avl_tree--create" >::
    (fun () ->
       skip_if !debug "debug";
       test_case "avl_tree--height"
"newtype Avl : type * num
newcons Empty : ∀a. Avl (a, 0)
newcons Node :
  ∀a,k,m,n [k=max(m,n) ∧ 0≤m ∧ 0≤n ∧ n≤m+2 ∧ m≤n+2].
     Avl (a, m) * a * Avl (a, n) * Num (k+1) ⟶ Avl (a, k+1)

external height : ∀a,n. Avl (a, n) → Num n = \"height\"

let create = fun l x r ->
  ematch height l, height r with
  | i, j when j <= i -> Node (l, x, r, i+1)
  | i, j when i <= j -> Node (l, x, r, j+1)"
        (* A bit ugly (too much info), but correct. *)
        [2,"∃n, k, a.
  δ =
    (Avl (a, k) → a → Avl (a, n) → ∃1:i[i=max (k + 1, n + 1) ∧
       i ≤ n + k + 1 ∧ i ≤ n + 3 ∧ i ≤ k + 3 ∧ k ≤ n + 2 ∧
       n ≤ k + 2 ∧ 0 ≤ k ∧ 0 ≤ n].Avl (a, i)) ∧
  k ≤ n + 2 ∧ n ≤ k + 2 ∧ 0 ≤ k ∧ 0 ≤ n"];
    );

  "avl_tree--singleton" >::
    (fun () ->
       skip_if !debug "debug";
       test_case "avl_tree--height"
"newtype Avl : type * num
newcons Empty : ∀a. Avl (a, 0)
newcons Node :
  ∀a,k,m,n [k=max(m,n) ∧ 0≤m ∧ 0≤n ∧ n≤m+2 ∧ m≤n+2].
     Avl (a, m) * a * Avl (a, n) * Num (k+1) ⟶ Avl (a, k+1)

let singleton = fun x -> Node (Empty, x, Empty, 1)"
        [1,"∃a. δ = (a → Avl (a, 1))"];
    );

  "avl_tree--min_binding" >::
    (fun () ->
       skip_if !debug "debug";
       test_case "avl_tree--height"
"newtype Avl : type * num
newcons Empty : ∀a. Avl (a, 0)
newcons Node :
  ∀a,k,m,n [k=max(m,n) ∧ 0≤m ∧ 0≤n ∧ n≤m+2 ∧ m≤n+2].
     Avl (a, m) * a * Avl (a, n) * Num (k+1) ⟶ Avl (a, k+1)

let rec min_binding = function
  | Empty -> assert false
  | Node (Empty, x, r, _) -> x
  | Node ((Node (_,_,_,_) as l), x, r, _) -> min_binding l"
        [1,"∃n, a. δ = (Avl (a, n) → a) ∧ 1 ≤ n"];
    );

  "avl_tree--bal" >::
    (fun () ->
       todo "hard for numerical solve";
       (* skip_if !debug "debug"; *)
       test_case "avl_tree--height"
"newtype Avl : type * num
newcons Empty : ∀a. Avl (a, 0)
newcons Node :
  ∀a,k,m,n [k=max(m,n) ∧ 0≤m ∧ 0≤n ∧ n≤m+2 ∧ m≤n+2].
     Avl (a, m) * a * Avl (a, n) * Num (k+1) ⟶ Avl (a, k+1)

external height : ∀a,n. Avl (a, n) → Num n = \"height\"
external create :
  ∀a,n,k[k ≤ n + 2 ∧ n ≤ k + 2 ∧ 0 ≤ k ∧ 0 ≤ n].
      Avl (a, k) → a → Avl (a, n) → ∃i[i=max (k + 1, n + 1) ∧
       i ≤ n + k + 1 ∧ i ≤ k + 3 ∧ i ≤ n + 3].Avl (a, i) = \"create\"
external singleton : ∀a. a → Avl (a, 1) = \"singleton\"
external min_binding : ∀a,n[1 ≤ n]. Avl (a, n) → a = \"min_binding\"

let bal = fun l x r ->
  ematch height l, height r with
  | i, j when j+3 <= i ->
    (ematch l with
    | Empty -> assert false
    | Node (ll, lx, lr, _) ->
      (ematch height ll, height lr with
      | m, n when n <= m ->
        let r' = create lr x r in
        create ll lx r'
      | m, n when m+1 <= n ->
        (ematch lr with
        | Empty -> assert false
        | Node (lrl, lrx, lrr, _) ->
          let l' = create ll lx lrl in
          let r' = create lrr x r in
          create l' lrx r')))
  | i, j when i+3 <= j ->
    (ematch r with
    | Empty -> assert false
    | Node (rl, rx, rr, _) ->
      (ematch height rr, height rl with
      | m, n when n <= m ->
        let l' = create l x rl in
        create l' rx rr
      | m, n when m+1 <= n ->
        (ematch rl with
        | Empty -> assert false
        | Node (rll, rlx, rlr, _) ->
          let l' = create l x rll in
          let r' = create rlr rx rr in
          create l' rlx r')))"
        [1,""];
    );

]


let () =
  let executable = Filename.basename Sys.executable_name in
  let chop f =
    try Filename.chop_extension f with Invalid_argument _ -> f in
  let executable = chop (chop executable) in
  if executable = "InvariantsTest"
  then ignore (OUnit.run_test_tt ~verbose:true tests)
