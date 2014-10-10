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

let test_common more_general more_existential no_num_abduction
    nodeadcode prefer_guess msg test =
  let ntime = Sys.time () in
  Terms.reset_state ();
  Infer.reset_state ();
  let old_nodeadcode = !Defs.nodeadcode in
  Defs.nodeadcode := nodeadcode;
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
  let old_more_general = !Abduction.more_general in
  Abduction.more_general := more_general;
  let old_no_num_abduction = !Abduction.no_num_abduction in
  Abduction.no_num_abduction := no_num_abduction;
  let old_more_existential = !DisjElim.more_existential in
  DisjElim.more_existential := more_existential;
  let old_prefer_guess = !Abduction.prefer_guess in
  Abduction.prefer_guess := prefer_guess;
  let _, res, sol =
    Invariants.solve q_ops new_ex_types exty_res_of_chi brs in
  Defs.nodeadcode := old_nodeadcode;
  Abduction.more_general := old_more_general;
  Abduction.no_num_abduction := old_no_num_abduction;
  Abduction.prefer_guess := old_prefer_guess;
  DisjElim.more_existential := old_more_existential;
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
    ?(no_num_abduction=false)
    ?(nodeadcode=false) ?(prefer_guess=false) msg test answers =
  let old_nodeadcode = !Defs.nodeadcode in
  let old_more_general = !Abduction.more_general in
  let old_no_num_abduction = !Abduction.no_num_abduction in
  let old_prefer_guess = !Abduction.prefer_guess in
  let old_more_existential = !DisjElim.more_existential in
  if !debug then Printexc.record_backtrace true;
  try
    let q, res, sol =
      test_common more_general more_existential no_num_abduction
        nodeadcode prefer_guess msg test in
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
    Defs.nodeadcode := old_nodeadcode;
    Abduction.more_general := old_more_general;
    Abduction.no_num_abduction := old_no_num_abduction;
    Abduction.prefer_guess := old_prefer_guess;
    DisjElim.more_existential := old_more_existential;
    assert_failure (Format.flush_str_formatter ())

let test_nonrec_case ?(more_general=false) ?(more_existential=false)
    ?(no_num_abduction=false) ?(nodeadcode=false)
    ?(prefer_guess=false) msg test answers =
  if !debug then Printexc.record_backtrace true;
  try
    let q, res, sol =
      test_common more_general more_existential no_num_abduction
        nodeadcode prefer_guess msg test in
    let test_sol (v, result) =
      let res_sb, _ = Infer.separate_subst q res in
      let ty = fst (List.assoc (VId (Type_sort, v)) res_sb) in
      ignore (Format.flush_str_formatter ());
      Format.fprintf Format.str_formatter "%a" pr_ty ty;
      assert_equal ~printer:(fun x -> x)
        result
        (Format.flush_str_formatter ()) in
    List.iter test_sol answers
  with (Report_toplevel _ | Contradiction _ | NoAnswer _) as exn ->
    ignore (Format.flush_str_formatter ());
    Terms.pr_exception Format.str_formatter exn;
    Abduction.more_general := false;
    Abduction.no_num_abduction := false;
    DisjElim.more_existential := false;
    assert_failure (Format.flush_str_formatter ())

let test_case_fail ?(more_general=false) ?(more_existential=false)
    ?(no_num_abduction=false)
    ?(nodeadcode=false) ?(prefer_guess=false) msg test answer =
  if !debug then Printexc.record_backtrace true;
  try
    let q, res, sol =
      test_common more_general more_existential no_num_abduction
        nodeadcode prefer_guess msg test in
    let _, (vs, ans) = nice_ans (snd (List.hd sol)) in
    ignore (Format.flush_str_formatter ());
    Format.fprintf Format.str_formatter "@[<2>∃%a.@ %a@]"
      (pr_sep_list "," pr_tyvar) vs pr_formula ans;
    assert_failure (Format.flush_str_formatter ())
  with (Defs.Report_toplevel _ | Terms.Contradiction _ |
        Terms.NoAnswer _) as exn ->
    ignore (Format.flush_str_formatter ());
    Terms.pr_exception Format.str_formatter exn;
    Defs.nodeadcode := false;
    Abduction.more_general := false;
    Abduction.no_num_abduction := false;
    DisjElim.more_existential := false;
    assert_equal ~printer:(fun x->x) answer (Format.flush_str_formatter ())

let tests = "Invariants" >::: [

  "simple eval" >::
    (fun () ->
      skip_if !debug "debug";
      test_case "eval term"
"datatype Term : type
external let plus : Int → Int → Int = \"(+)\"
external let is_zero : Int → Bool = \"(=) 0\"
datacons Lit : Int ⟶ Term Int
datacons Plus : Term Int * Term Int ⟶ Term Int
datacons IsZero : Term Int ⟶ Term Bool
datacons If : ∀a. Term Bool * Term a * Term a ⟶ Term a

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
"datatype Term : type
datacons Lit : Int ⟶ Term Int
datacons IsZero : Term Int ⟶ Term Bool
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
"datatype Positive : num
datacons Pos : ∀n [0 ≤ n]. Num n ⟶ Positive n

let rec foo = function i -> Pos (i + -7)"

        [1, "∃n. δ = (Num (n + 7) → Positive n) ∧ 0 ≤ n"]
    );

  "foo without when 2" >::
    (fun () ->
      skip_if !debug "debug";
      test_case "foo without when, non-negative and non-positive"
"datatype Signed : num
datacons Pos : ∀n [0 ≤ n]. Num n ⟶ Signed n
datacons Neg : ∀n [n ≤ 0]. Num n ⟶ Signed n

let rec foo = function
  | i -> Pos (i + -7)
  | i -> Neg (i + -7)"

        [1, "∃. δ = (Num 7 → Signed 0)"]
    );

  "foo with when 1" >::
    (fun () ->
      skip_if !debug "debug";
      test_case "foo with when"
"datatype Signed : num
datacons Pos : ∀n [0 ≤ n]. Num n ⟶ Signed n
datacons Neg : ∀n [n ≤ 0]. Num n ⟶ Signed n

let rec foo = function
  | i when 7 <= i -> Pos (i + -7)
  | i when i <= 7 -> Neg (i + -7)"

        [1, "∃n. δ = (Num (n + 7) → Signed n)"]
    );

  "foo with when 2" >::
    (fun () ->
      skip_if !debug "debug";
      test_case "foo with when, unsafe positive"
"datatype Positive : num
datacons Pos : ∀n [0 ≤ n]. Num n ⟶ Positive n

let rec foo = function
  | i when 7 <= i -> Pos (i + -7)"

        [1, "∃n. δ = (Num (n + 7) → Positive n)"]
    );

  "deadcode foo" >::
    (fun () ->
      skip_if !debug "debug";
      test_case "foo without when, positive"
"datatype Positive : num
datacons Pos : ∀n [0 ≤ n]. Num n ⟶ Positive n

let rec foo =
  function
  | Pos i when i <= -1 -> 7
  | Pos i -> i"

        [1, "∃n. δ = (Positive n → Num n)"]
    );

  "deadcode foo fail" >::
    (fun () ->
      skip_if !debug "debug";
      test_case_fail ~nodeadcode:true "foo without when, positive"
"datatype Positive : num
datacons Pos : ∀n [0 ≤ n]. Num n ⟶ Positive n

let rec foo =
  function
  | Pos i when i <= -1 -> 7
  | Pos i -> i"

        "File \"\", line 2, characters 21-28:
Contradiction in num: Failed numeric inequality
types involved:
1
n23
"
    );

  "eval" >::
    (fun () ->
       skip_if !debug "debug";
       test_case "eval term"
"datatype Term : type

external let plus : Int → Int → Int = \"(+)\"
external let is_zero : Int → Bool = \"(=) 0\"

datacons Lit : Int ⟶ Term Int
datacons Plus : Term Int * Term Int ⟶ Term Int
datacons IsZero : Term Int ⟶ Term Bool
datacons If : ∀a. Term Bool * Term a * Term a ⟶ Term a
datacons Pair : ∀a, b. Term a * Term b ⟶ Term (a, b)
datacons Fst : ∀a, b. Term (a, b) ⟶ Term a
datacons Snd : ∀a, b. Term (a, b) ⟶ Term b

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

  "eval hard" >::
    (fun () ->
       skip_if !debug "debug";
       test_case "eval term"
"datatype Term : type

datacons If : ∀a. Term Bool * Term a * Term a ⟶ Term a
datacons Pair : ∀a, b. Term a * Term b ⟶ Term (a, b)
datacons Fst : ∀a, b. Term (a, b) ⟶ Term a
datacons Snd : ∀a, b. Term (a, b) ⟶ Term b

let rec eval = function
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
"datatype Ty : type
datatype List : type
datacons Zero : Int
datacons Nil : ∀a. List a
datacons TInt : Ty Int
datacons TPair : ∀a, b. Ty a * Ty b ⟶ Ty (a, b)
datacons TList : ∀a. Ty a ⟶ Ty (List a)
external let eq_int : Int → Int → Bool = \"(=)\"
external let b_and : Bool → Bool → Bool = \"(&&)\"
external let b_not : Bool → Bool = \"not\"
external forall2 : ∀a, b. (a → b → Bool) → List a → List b → Bool

let rec equal1 = function
  | TInt, TInt -> fun x y -> eq_int x y
  | TPair (t1, t2), TPair (u1, u2) ->  
    (fun (x1, x2) (y1, y2) ->
        b_and (equal1 (t1, u1) x1 y1)
              (equal1 (t2, u2) x2 y2))
  | TList t, TList u -> forall2 (equal1 (t, u))
  | _ -> fun _ _ -> False"
        [1, "∃a, b. δ = ((Ty a, Ty b) → b → b → Bool)"]
    );

  "equal with test" >::
    (fun () ->
       skip_if !debug "debug";
       test_case "equal terms"
"datatype Ty : type
datatype List : type
datacons Zero : Int
datacons Nil : ∀a. List a
datacons TInt : Ty Int
datacons TPair : ∀a, b. Ty a * Ty b ⟶ Ty (a, b)
datacons TList : ∀a. Ty a ⟶ Ty (List a)
external let eq_int : Int → Int → Bool = \"(=)\"
external let b_and : Bool → Bool → Bool = \"(&&)\"
external let b_not : Bool → Bool = \"not\"
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
        [1, "∃a, b. δ = ((Ty a, Ty b) → a → b → Bool)"]
    );

  "equal with assert" >::
    (fun () ->
       skip_if !debug "debug";
       test_case "equal terms"
"datatype Ty : type
datatype List : type
datacons Zero : Int
datacons Nil : ∀a. List a
datacons TInt : Ty Int
datacons TPair : ∀a, b. Ty a * Ty b ⟶ Ty (a, b)
datacons TList : ∀a. Ty a ⟶ Ty (List a)
external let eq_int : Int → Int → Bool = \"(=)\"
external let b_and : Bool → Bool → Bool = \"(&&)\"
external let b_not : Bool → Bool = \"not\"
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
        [1, "∃a, b. δ = ((Ty a, Ty b) → a → b → Bool)"]
    );

  "equal with assert and test" >::
    (fun () ->
       skip_if !debug "debug";
       test_case "equal terms"
"datatype Ty : type
datatype List : type
datacons Zero : Int
datacons Nil : ∀a. List a
datacons TInt : Ty Int
datacons TPair : ∀a, b. Ty a * Ty b ⟶ Ty (a, b)
datacons TList : ∀a. Ty a ⟶ Ty (List a)
external let eq_int : Int → Int → Bool = \"(=)\"
external let b_and : Bool → Bool → Bool = \"(=)\"
external let b_not : Bool → Bool = \"not\"
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
        [1, "∃a, b. δ = ((Ty a, Ty b) → a → b → Bool)"]
    );

  "SPJ non-principal 1" >::
    (fun () ->
       skip_if !debug "debug";
       test_case "SPJ non-principal"
"datatype T : type
datacons T1 : Bool ⟶ T Bool
datacons T2 : ∀a. T a

let f = fun y -> function
  | T1 z -> True
  | T2 -> y"
        [1, "∃a. δ = (a → T a → a)"]
    );

  "SPJ non-principal 2" >::
    (fun () ->
       skip_if !debug "debug";
       test_case "SPJ non-principal"
"datatype T : type
datacons T1 : Bool ⟶ T Bool
datacons T2 : ∀a. T a
external c : T Int

let rec f = fun y -> function
  | T1 z -> True
  | T2 -> y
test f False c"
        [1, "∃a. δ = (Bool → T a → Bool)"]
    );


  "TS infinitely non-principal" >::
    (fun () ->
       skip_if !debug "debug";
       test_case "TS non-principal"
"datatype Char
datatype List : type
datacons LCons : ∀a. a * List a ⟶ List a
datatype Erk : type * type * type
datacons K : ∀a, b. a * b ⟶ Erk (a, b, Char)

let f = function K (x, y) -> LCons (x, y)
"
        [1, "∃a, b. δ = (Erk (a, List a, b) → List a)"]
    );

  "TS non-principal subexpr" >::
    (fun () ->
       skip_if !debug "debug";
       test_case "TS non-principal"
"datatype List : type
datacons LNil : ∀a. List a
datacons LCons : ∀a. a * List a ⟶ List a
datatype Erk : type * type * type
datacons K : ∀a, b. a * b ⟶ Erk (a, b, String)
datacons L : ∀a, b. a * b ⟶ Erk (a, b, Bool)

let rec g = function
  | K (x, y) -> LCons (x, y)
  | L (x, y) -> y
"
        [1, "∃a, b. δ = (Erk (a, List a, b) → List a)"]
    );

  "TS non-principal subexpr 2" >::
    (fun () ->
       skip_if !debug "debug";
       test_case_fail "TS non-principal"
"datatype List : type
datacons LNil : ∀a. List a
datacons LCons : ∀a. a * List a ⟶ List a
datatype Erk : type * type * type
datacons K : ∀a, b. a * b ⟶ Erk (a, b, String)
datacons L : ∀a, b. a * b ⟶ Erk (a, b, Bool)

let rec g = function
  | K (x, y) -> LCons (x, y)
  | L (x, y) -> y
test g (L (LCons (True, LNil), LCons (\"a\", LNil)))
"
     "File \"\", line 9, characters 16-28:
No answer in type: term abduction failed
"
     (* possible type if abduction gets "too good":
        "δ = (Erk (List a, List (List String), a) → List (List String))" *)
    );


  "map mono" >::
    (fun () ->
       skip_if !debug "debug";
       test_case "list map simplest numeric"
"datatype Elem
datatype List : num
datacons LNil : List 0
datacons LCons : ∀n [0≤n]. Elem * List n ⟶ List (n+1)

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
"datatype Elem
datatype List : num
datacons LNil : List 0
datacons LCons : ∀n [0≤n]. Elem * List n ⟶ List (n+1)

let rec append =
  function LNil -> (function LNil -> LNil | LCons (_,_) as l -> l)
    | LCons (x, xs) ->
      (function LNil -> LCons (x, append xs LNil)
        | LCons (_,_) as l -> LCons (x, append xs l))"
        [1,"∃n, k. δ = (List k → List n → List (n + k))"];
    );

  "append asserted" >::
    (fun () ->
       todo "too hard for current numerical abduction";
       skip_if !debug "debug";
       (* Too hard for the current abduction algo: when it discovers
          that the result is [n + k], rather than [n], it is already
          committed to requiring that the result is no less than [1],
          which on following iterations blows up. *)
       test_case "list append simple numeric"
"datatype Elem
datatype List : num
datacons LNil : List 0
datacons LCons : ∀n [0≤n]. Elem * List n ⟶ List (n+1)
external length : ∀n. List n → Num n

let rec append =
  function
    | LNil ->
      (function l when (length l + 1) <= 0 -> assert false | l -> l)
    | LCons (x, xs) ->
      (function l when (length l + 1) <= 0 -> assert false
      | l -> LCons (x, append xs l))"
        [1,"∃n, k. δ = (List k → List n → List (n + k)) ∧ 0 ≤ n ∧
  0 ≤ n + k"];
    );

  "interleave" >::
    (fun () ->
       skip_if !debug "debug";
       test_case "list interleave simple numeric"
"datatype Elem
datatype List : num
datacons LNil : List 0
datacons LCons : ∀n [0≤n]. Elem * List n ⟶ List (n+1)

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
"datatype Elem
datatype List : num
datacons LNil : List 0
datacons LCons : ∀n [0≤n]. Elem * List n ⟶ List (n+1)

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
"datatype Elem
datatype List : num
datacons LNil : List 0
datacons LCons : ∀n [0≤n]. Elem * List n ⟶ List (n+1)

let rec append =
  function LNil -> (function (LNil | LCons (_,_)) as l -> l)
    | LCons (x, xs) -> (fun l -> LCons (x, append xs l))"
        [1,"∃n, k. δ = (List n → List k → List (n + k))"];
    );

  "binary increment simple" >::
    (fun () ->
       skip_if !debug "debug";
       test_case ~nodeadcode:true "binary increment simple"
"datatype Binary : num

datacons Zero : Binary 0
datacons PZero : ∀n [0≤n]. Binary n ⟶ Binary(2 n)
datacons POne : ∀n [0≤n]. Binary n ⟶ Binary(2 n + 1)

let rec increment =
  function Zero -> POne Zero
    | PZero a1 -> POne a1
    | POne a1 -> PZero (increment a1)"
        [1,"∃n. δ = (Binary n → Binary (n + 1))"]
    );

  "binary increment" >::
    (fun () ->
       todo "num abduction: eliminate constants in initial candidates";
       skip_if !debug "debug";
       test_case "binary increment"
"datatype Binary : num

datacons Zero : Binary 0
datacons PZero : ∀n [0≤n]. Binary n ⟶ Binary(2 n)
datacons POne : ∀n [0≤n]. Binary n ⟶ Binary(2 n + 1)

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
"datatype Binary : num
datatype Carry : num

datacons Zero : Binary 0
datacons PZero : ∀n [0≤n]. Binary n ⟶ Binary(2 n)
datacons POne : ∀n [0≤n]. Binary n ⟶ Binary(2 n + 1)

datacons CZero : Carry 0
datacons COne : Carry 1

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

  "binary plus asserted" >::
    (fun () ->
       todo "too hard for current numerical abduction";
       skip_if !debug "debug";
       test_case "binary plus"
"datatype Binary : num
datatype Carry : num

datacons Zero : Binary 0
datacons PZero : ∀n [0≤n]. Binary n ⟶ Binary(2 n)
datacons POne : ∀n [0≤n]. Binary n ⟶ Binary(2 n + 1)
datacons CZero : Carry 0
datacons COne : Carry 1

external num_of_binary : ∀n. Binary n → Num n

let rec plus =
  function CZero ->
    (function Zero ->
        (function b when num_of_binary b+1 <= 0 -> assert false
           | b (* when 0 <= num_of_binary b *) -> b)
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
"datatype Binary : num
datatype Carry : num

datacons Zero : Binary 0
datacons PZero : ∀n [0≤n]. Binary n ⟶ Binary(2 n)
datacons POne : ∀n [0≤n]. Binary n ⟶ Binary(2 n + 1)

datacons CZero : Carry 0
datacons COne : Carry 1

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
"datatype Binary : num
datatype Carry : num

datacons Zero : Binary 0
datacons PZero : ∀n [0≤n]. Binary n ⟶ Binary(2 n)
datacons POne : ∀n [0≤n]. Binary n ⟶ Binary(2 n + 1)
datacons CZero : Carry 0
datacons COne : Carry 1

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
"datatype List : type * num
datacons LNil : ∀a. List(a, 0)
datacons LCons : ∀n, a [0≤n]. a * List(a, n) ⟶ List(a, n+1)

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
"datatype Room
datatype Yard
datatype Outside

datatype Placement : type
datacons Room : Room ⟶ Placement Room
datacons Yard : Yard ⟶ Placement Yard
datacons Outside : Outside ⟶ Placement Outside

external leave : Room → ∃t. Placement t
external enter : Yard → Room

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
"datatype Place : type
datatype Nearby : type * type
datacons Transitive : ∀a,b,c. Nearby (a, b) * Nearby (b, c) ⟶ Nearby (a, c)
external wander : ∀a. Place a → ∃b. (Place b, Nearby (a, b))
datatype Meet : type * type
datacons Close : ∀a,b. Nearby (a, b) ⟶ Meet (a, b)
datacons NotClose : ∀a, b. Meet (a, b)
external compare : ∀a,b. Place a → Place b → Meet (a, b)
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
"datatype Place : type
datatype Nearby : type * type
datatype A
datatype B
datacons LocA : Place A
datacons LocB : Place B
external is_nearby : ∀a,b. Nearby (a, b) → Bool
datacons Here : ∀a. Place a * Place a ⟶ Nearby (a, a)
datacons Transitive : ∀a,b,c. Nearby (a, b) * Nearby (b, c) ⟶ Nearby (a, c)
external wander : ∀a. Place a → ∃b. (Place b, Nearby (a, b))
datatype Meet : type * type
datacons Same : ∀a,b [a=b]. Meet (a, b)
datacons NotSame : ∀a, b. Meet (a, b)
external compare : ∀a,b. Place a → Place b → Meet (a, b)
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
"datatype Place : type
datatype Nearby : type * type
datatype A
datatype B
datacons LocA : Place A
datacons LocB : Place B
external is_nearby : ∀a,b. Nearby (a, b) → Bool
datacons Transitive : ∀a,b,c. Nearby (a, b) * Nearby (b, c) ⟶ Nearby (a, c)
external wander : ∀a. Place a → ∃b. (Place b, Nearby (a, b))
datatype Meet : type * type
datacons Close : ∀a,b. Nearby (a, b) ⟶ Meet (a, b)
datacons NotClose : ∀a, b. Meet (a, b)
external compare : ∀a,b. Place a → Place b → Meet (a, b)
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
"datatype Room
datatype Yard
datatype Village

datatype Castle : type
datatype Placement : type
datacons Room : Room ⟶ Castle Room
datacons Yard : Yard ⟶ Castle Yard
datacons CastleRoom : Room ⟶ Placement Room
datacons CastleYard : Yard ⟶ Placement Yard
datacons Village : Village ⟶ Placement Village

external wander : ∀a. Placement a → ∃b. Placement b

let rec find_castle = efunction
  | CastleRoom x -> Room x
  | CastleYard x -> Yard x
  | Village _ as x ->
    let y = wander x in
    find_castle y"
        [2,"∃a. δ = (Placement a → ∃a.Castle a)"];
    );

  "find castle big" >::
    (fun () ->
       skip_if !debug "debug";
       test_case "find castle big"
"datatype Room
datatype Yard
datatype Garden
datatype Village

datatype Castle : type
datatype Placement : type
datacons Room : Room ⟶ Castle Room
datacons Yard : Yard ⟶ Castle Yard
datacons CastleRoom : Room ⟶ Placement Room
datacons CastleYard : Yard ⟶ Placement Yard
datacons Garden : Garden ⟶ Placement Garden
datacons Village : Village ⟶ Placement Village

external wander : ∀a. Placement a → ∃b. Placement b

let rec find = efunction
  | CastleRoom x -> Room x
  | CastleYard x -> Yard x
  | Garden _ as x ->
    let y = wander x in
    find y
  | Village _ as x ->
    let y = wander x in
    find y"
        [2,"∃a. δ = (Placement a → ∃a.Castle a)"];
    );

  "search castle shortcut" >::
    (fun () ->
       skip_if !debug "debug";
       test_case "search castle shortcut"
"datatype Room
datatype Yard
datatype Village

datatype Castle : type
datatype Placement : type
datacons Room : Room ⟶ Castle Room
datacons Yard : Yard ⟶ Castle Yard
datacons CastleRoom : Room ⟶ Placement Room
datacons Village : Village ⟶ Placement Village

datatype Explore
datacons Ordinary : Explore
datacons Shortcut : Yard ⟶ Explore

external wander : ∀a. Placement a → ∃b. Placement b
external check : ∀a. Placement a → Explore

let rec search = efunction
  | CastleRoom x -> Room x
  | Village _ as x ->
    let y = wander x in
    ematch check y with
    | Ordinary -> search y
    | Shortcut z -> Yard z"
        [2,"∃a. δ = (Placement a → ∃a.Castle a)"];
    );

  "search castle distance" >::
    (fun () ->
       skip_if !debug "debug";
       test_case "find castle distance"
"datatype Room
datatype Yard
datatype Village

datatype Castle : type
datatype Placement : type
datacons Room : Room ⟶ Castle Room
datacons Yard : Yard ⟶ Castle Yard
datacons CastleRoom : Room ⟶ Placement Room
datacons CastleYard : Yard ⟶ Placement Yard
datacons Village : Village ⟶ Placement Village

external wander : ∀a. Placement a → ∃b. Placement b
external closer : ∀a. Placement a → Bool

let rec search = efunction
  | CastleRoom x -> Room x
  | CastleYard x -> Yard x
  | Village _ as x ->
    let y = wander x in
    ematch closer y with
    | True -> search y
    | False -> search x"
        [2,"∃a. δ = (Placement a → ∃a.Castle a)"];
    );

  "search castle distance A/B" >::
    (fun () ->
       skip_if !debug "debug";
       test_case "find castle distance A/B"
"datatype Boolean : type
datatype A
datatype B
datacons True : Boolean A
datacons False : Boolean B
datatype Room
datatype Yard
datatype Village

datatype Castle : type
datatype Placement : type
datacons Room : Room ⟶ Castle Room
datacons Yard : Yard ⟶ Castle Yard
datacons CastleRoom : Room ⟶ Placement Room
datacons CastleYard : Yard ⟶ Placement Yard
datacons Village : Village ⟶ Placement Village

external wander : ∀a. Placement a → ∃b. Placement b
external closer : ∀a. Placement a → ∃b. Boolean b

let rec search = efunction
  | CastleRoom x -> Room x
  | CastleYard x -> Yard x
  | Village _ as x ->
    let y = wander x in
    let b = closer y in
    ematch b with
    | True -> search y
    | False -> search x"
        [2,"∃a. δ = (Placement a → ∃a.Castle a)"];
    );

  "castle not existential" >::
    (fun () ->
       skip_if !debug "debug";
       test_case "castle not existential"
"datatype Yard
datatype Village

datatype Castle : type
datatype Placement : type
datacons Yard : Yard ⟶ Castle Yard
datacons CastleYard : Yard ⟶ Placement Yard
datacons Village : Village ⟶ Placement Village

external wander : Village → ∃b. Placement b

let rec search = efunction
  | CastleYard x -> Yard x
  | Village x ->
    let y = wander x in
    search y"
        [2,"∃a. δ = (Placement a → ∃.Castle Yard)"];
    );

  "castle nested not existential" >::
    (fun () ->
       skip_if !debug "debug";
       test_case "castle nested not existential"
"datatype Answer
datacons No : Answer
datacons Nearby : Answer
datatype Yard
datatype Village

datatype Castle : type
datatype Placement : type
datacons Closeby : Castle Yard
datacons Yard : Yard ⟶ Castle Yard
datacons CastleYard : Yard ⟶ Placement Yard
datacons Village : Village ⟶ Placement Village

external wander : Village → ∃b. Placement b
external entrance : Village → Answer

let rec search = efunction
  | CastleYard x -> Yard x
  | Village x ->
    ematch entrance x with
    | Nearby -> Closeby
    | No ->
      let y = wander x in
      search y"
        [2,"∃a. δ = (Placement a → ∃.Castle Yard)"];
    );

  "castle nested existential factored" >::
    (fun () ->
       skip_if !debug "debug";
       test_case "castle nested existential factored"
"datatype Answer
datacons Yes : Answer
datacons No : Answer
datatype Room
datatype Yard
datatype Village

datatype Castle : type
datatype Placement : type
datacons Yard : Yard ⟶ Castle Yard
datacons CastleYard : Yard ⟶ Placement Yard
datacons Village : Village ⟶ Placement Village

external wander : Village → ∃b. Placement b
external entrance : Village → Answer
external enter : ∀a. Placement a → Castle a

let rec search = efunction
  | CastleYard x -> Yard x
  | Village x ->
    let y = wander x in
    ematch entrance x with
    | Yes ->
      enter y
    | No ->
      search y"
        [2,"∃a. δ = (Placement a → ∃a.Castle a)"];
    );

  "castle nested existential" >::
    (fun () ->
       skip_if !debug "debug";
       test_case "castle nested existential"
"datatype Answer
datacons Yes : Answer
datacons No : Answer
datatype Yard
datatype Village
datatype Room
datatype Castle : type
datatype Placement : type
datacons Yard : Yard ⟶ Castle Yard
datacons CastleYard : Yard ⟶ Placement Yard
datacons Village : Village ⟶ Placement Village

external wander : Village → ∃b. Placement b
external entrance : Village → Answer
external enter : ∀a. Placement a → Castle Room

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
        [2,"∃a. δ = (Placement a → ∃a.Castle a)"];
    );

  "existential by hand" >::
    (fun () ->
       skip_if !debug "debug";
       test_case "existential by hand"
"datatype Place : type
datatype Nearby : type * type
datatype Near : type
datacons Here : ∀a. Place a ⟶ Nearby (a, a)
datacons Near : ∀a,b. Nearby (a, b) ⟶ Near a
datacons Transitive : ∀a,b,c. Nearby (a, b) * Nearby (b, c) ⟶ Nearby (a, c)
external wander : ∀a. Place a → ∃b. (Place b, Nearby (a, b))
external finish : ∀a. Place a → Bool
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
"datatype Place : type
datatype Nearby : type * type
datacons Here : ∀a. Place a ⟶ Nearby (a, a)
datacons Transitive : ∀a,b,c. Nearby (a, b) * Nearby (b, c) ⟶ Nearby (a, c)
external wander : ∀a. Place a → ∃b. (Place b, Nearby (a, b))
external finish : ∀a. Place a → Bool
let rec walk = fun x ->
  ematch finish x with
  | True -> Here x
  | False ->
    let y, to_y = wander x in
    let to_z = walk y in
    Transitive (to_y, to_z)"
        [2,"∃a. δ = (Place a → ∃b.Nearby (a, b))"];
    );

  "universal option" >::
    (fun () ->
       skip_if !debug "debug";
       test_case "universal option"
"datatype Option : type
datacons None : ∀a. Option a
datacons Some : ∀a. a ⟶ Option a

let rec one_of =
  function (Some _ as a) -> (function _ -> a)
  | None -> (function None -> None | (Some _ as b) -> b)"
        [1,"∃a. δ = (Option a → Option a → Option a)"];
    );

  "existential option" >::
    (fun () ->
       todo "FIXME";
       skip_if !debug "debug";
       test_case ~more_existential:true "existential option"
"datatype Option : type
datacons None : ∀a. Option a
datacons Some : ∀a. a ⟶ Option a

let rec one_of =
  efunction (Some _ as a) -> (efunction _ -> a)
  | None -> (efunction None -> None | (Some _ as b) -> b)"
        [2,"∃a, b. δ = (Option a → Option b → ∃a.Option a)"];
    );

  "not existential option" >::
    (fun () ->
       skip_if !debug "debug";
       test_case "not existential option"
"datatype Option : type
datacons None : ∀a. Option a
datacons Some : ∀a. a ⟶ Option a
external f : ∀a. a → a → a

let rec one_of =
  efunction (Some a) -> (efunction None -> a | (Some b) -> f a b)
  | None -> (efunction (Some b) -> b)"
        [2,"∃a. δ = (Option a → Option a → ∃.a)"];
    );

  "non-num map not existential poly" >::
    (fun () ->
       skip_if !debug "debug";
       test_case "list without length map not existential poly"
"datatype List : type
datacons LNil : ∀a. List a
datacons LCons : ∀a. a * List a ⟶ List a

let rec map = fun f ->
  efunction LNil -> LNil
    | LCons (x, xs) ->
      let ys = map f xs in
      LCons (f x, ys)"
        [2,"∃a, b. δ = ((a → b) → List a → ∃.List b)"];
    );

  "non-num map not existential mono" >::
    (fun () ->
       skip_if !debug "debug";
       test_case "list without length map not existential mono"
"datatype List : type
datacons LNil : ∀a. List a
datacons LCons : ∀a. a * List a ⟶ List a
datatype Foo
datatype Bar

external f : Foo → Bar

let rec map =
  efunction LNil -> LNil
    | LCons (x, xs) ->
      let ys = map xs in
      LCons (f x, ys)"
        [2,"∃. δ = (List Foo → ∃.List Bar)"];
    );

  "map not existential mono" >::
    (fun () ->
       skip_if !debug "debug";
       test_case "list map not existential mono"
"datatype Elem
datatype List : num
datacons LNil : List 0
datacons LCons : ∀n [0≤n]. Elem * List n ⟶ List(n+1)

external f : Elem → Elem

let rec map =
  efunction LNil -> LNil
    | LCons (x, xs) ->
      let ys = map xs in
      LCons (f x, ys)"
        [2,"∃n. δ = (List n → ∃.List n)"];
    );

  "map not existential poly" >::
    (fun () ->
       skip_if !debug "debug";
       test_case "list map not existential poly"
"datatype List : type * num
datacons LNil : ∀a. List(a, 0)
datacons LCons : ∀n, a [0≤n]. a * List(a, n) ⟶ List(a, n+1)

let rec map = fun f ->
  efunction LNil -> LNil
    | LCons (x, xs) ->
      let ys = map f xs in
      LCons (f x, ys)"
        [2,"∃n, a, b. δ = ((a → b) → List (a, n) → ∃.List (b, n))"];
    );

  "map not existential instance" >::
    (fun () ->
       skip_if !debug "debug";
       test_case "list map not existential instance"
"datatype List : type * num
datacons LNil : ∀a. List(a, 0)
datacons LCons : ∀n, a [0≤n]. a * List(a, n) ⟶ List(a, n+1)
datatype Foo
datatype Bar

external f : Foo → Bar

let rec map =
  efunction LNil -> LNil
    | LCons (x, xs) ->
      let ys = map xs in
      LCons (f x, ys)"
        [2,"∃n. δ = (List (Foo, n) → ∃.List (Bar, n))"];
    );

  "filter mono" >::
    (fun () ->
       skip_if !debug "debug";
       test_case "monomorphic list filter"
"datatype Bar
datatype List : num
datacons LNil : List 0
datacons LCons : ∀n [0≤n]. Bar * List n ⟶ List(n+1)
external f : Bar → Bool

let rec filter =
  efunction LNil -> LNil
    | LCons (x, xs) ->
      ematch f x with
        | True ->
          let ys = filter xs in
          LCons (x, ys)
	| False ->
          filter xs"
        [2,"∃n. δ = (List n → ∃k[0 ≤ k ∧ k ≤ n].List k)"];

    );

  "filter Bar" >::
    (fun () ->
       skip_if !debug "debug";
       test_case "list filter: Bar"
"datatype List : type * num
datacons LNil : ∀a. List(a, 0)
datacons LCons : ∀n, a [0≤n]. a * List(a, n) ⟶ List(a, n+1)

datatype Bar
external f : Bar → Bool

let rec filter =
  efunction LNil -> LNil
    | LCons (x, xs) ->
      ematch f x with
        | True ->
          let ys = filter xs in
          LCons (x, ys)
	| False ->
          filter xs"
        [2,"∃n. δ = (List (Bar, n) → ∃k[0 ≤ k ∧ k ≤ n].List (Bar, k))"];
    );

  "filter poly" >::
    (fun () ->
       skip_if !debug "debug";
       test_case "polymorphic list filter"
"datatype List : type * num
datacons LNil : ∀a. List(a, 0)
datacons LCons : ∀n, a [0≤n]. a * List(a, n) ⟶ List(a, n+1)

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
    ((a → Bool) → List (a, n) → ∃k[0 ≤ k ∧ k ≤ n].List (a, k))"];
    );

  "poly filter map" >::
    (fun () ->
       skip_if !debug "debug";
       test_case "list filter map"
"datatype List : type * num
datacons LNil : ∀a. List(a, 0)
datacons LCons : ∀n, a [0≤n]. a * List(a, n) ⟶ List(a, n+1)

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
    ((a → Bool) → (a → b) → List (a, n) → ∃k[0 ≤ k ∧
       k ≤ n].List (b, k))"];

    );

  "binary upper bound-wrong" >::
    (fun () ->
       skip_if !debug "debug";
       (* We need to expand the branch when the first argument is
          [Zero] from [efunction b -> b] to the cases as below, to
          convey the fact that the numerical parameter is non-negative. *)
       test_case "binary upper bound -- bitwise or"
"datatype Binary : num
datacons Zero : Binary 0
datacons PZero : ∀n [0≤n]. Binary n ⟶ Binary(2 n)
datacons POne : ∀n [0≤n]. Binary n ⟶ Binary(2 n + 1)

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
  δ = (Binary k → Binary n → ∃i[i ≤ n + k ∧ n ≤ i].Binary i)"]
    );

  "binary upper bound expanded" >::
    (fun () ->
       skip_if !debug "debug";
       (* We need to expand the branch when the first argument is
          [Zero] from [efunction b -> b] to the cases as below, to
          convey the fact that the numerical parameter is non-negative. *)
       test_case "binary upper bound -- bitwise or"
"datatype Binary : num
datacons Zero : Binary 0
datacons PZero : ∀n [0≤n]. Binary(n) ⟶ Binary(n+n)
datacons POne : ∀n [0≤n]. Binary(n) ⟶ Binary(n+n+1)

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
    (Binary k → Binary n → ∃i[k ≤ i ∧ i ≤ n + k ∧
       n ≤ i].Binary i)"]
    );

  "binary upper bound" >::
    (fun () ->
       todo "disjunctive patterns";
       skip_if !debug "debug";
       (* We need to expand the branch when the first argument is
          [Zero] from [efunction b -> b] to the cases as below, to
          convey the fact that the numerical parameter is non-negative. *)
       test_case "binary upper bound -- bitwise or"
"datatype Binary : num
datacons Zero : Binary 0
datacons PZero : ∀n [0≤n]. Binary n ⟶ Binary(2 n)
datacons POne : ∀n [0≤n]. Binary n ⟶ Binary(2 n + 1)

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
    (Binary k → Binary n → ∃i[n ≤ i ∧ k ≤ i ∧
       i ≤ n + k].Binary i)"]
    );

  "nested recursion simple eval" >::
    (fun () ->
       skip_if !debug "debug";
       test_case "nested recursion eval with literal numbers only"
"datatype Term : type
datatype Num : num
datatype Calc : num

external let is_zero : ∀i. Num i → Bool = \"(=) 0\"

datacons Lit : ∀k. Num k ⟶ Calc k

datacons IsZero : ∀k. Calc k ⟶ Term Bool
datacons If : ∀a. Term Bool * Term a * Term a ⟶ Term a

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
"datatype Term : type
datatype Num : num
datatype Calc : num

external let is_zero : ∀i. Num i → Bool = \"(=) 0\"

datacons Lit : ∀k. Num k ⟶ Calc k
datacons Plus : ∀i,j. Calc i * Calc j ⟶ Calc (i+j)

datacons IsZero : ∀k. Calc k ⟶ Term Bool
datacons If : ∀a. Term Bool * Term a * Term a ⟶ Term a
datacons Pair : ∀a, b. Term a * Term b ⟶ Term (a, b)
datacons Fst : ∀a, b. Term (a, b) ⟶ Term a
datacons Snd : ∀a, b. Term (a, b) ⟶ Term b

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
"datatype Term : type
datatype Num : num
datatype Calc

external let is_zero : ∀i. Num i → Bool = \"(=) 0\"
external let cond : ∀i,j. Bool → Num i → Num j → ∃k. Num k = \"fun c a b -> if c then a else b\"

datacons Lit : ∀k. Num k ⟶ Calc
datacons Cond : Term Bool * Calc * Calc ⟶ Calc

datacons IsZero : Calc ⟶ Term Bool
datacons If : ∀a. Term Bool * Term a * Term a ⟶ Term a

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
        3, "∃. δ = (Calc → ∃n.Num n)"]
    );

  "mutual recursion medium calc" >::
    (fun () ->
       skip_if !debug "debug";
       test_case "mutual recursion universal eval and existential calc"
"datatype Term : type
datatype Num : num
datatype Calc

external let is_zero : ∀i. Num i → Bool = \"(=) 0\"
external let cond : ∀i,j. Bool → Num i → Num j → ∃k. Num k = \"fun c a b -> if c then a else b\"

datacons Lit : ∀k. Num k ⟶ Calc
datacons Cond : Term Bool * Calc * Calc ⟶ Calc

datacons IsZero : Calc ⟶ Term Bool
datacons If : ∀a. Term Bool * Term a * Term a ⟶ Term a
datacons Pair : ∀a, b. Term a * Term b ⟶ Term (a, b)

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
        3, "∃. δ = (Calc → ∃n.Num n)"]
    );

  "mutual recursion calc" >::
    (fun () ->
       skip_if !debug "debug";
       test_case "mutual recursion universal eval and existential calc"
"datatype Term : type
datatype Num : num
datatype Calc

external let mult : ∀i,j. Num i → Num j → ∃k. Num k = \"(*)\"
external let is_zero : ∀i. Num i → Bool = \"(=) 0\"
external let cond : ∀i,j. Bool → Num i → Num j → ∃k. Num k = \"fun c a b -> if c then a else b\"

datacons Lit : ∀k. Num k ⟶ Calc
datacons Plus : Calc * Calc ⟶ Calc
datacons Mult : Calc * Calc ⟶ Calc
datacons Cond : Term Bool * Calc * Calc ⟶ Calc

datacons IsZero : Calc ⟶ Term Bool
datacons If : ∀a. Term Bool * Term a * Term a ⟶ Term a
datacons Pair : ∀a, b. Term a * Term b ⟶ Term (a, b)
datacons Fst : ∀a, b. Term (a, b) ⟶ Term a
datacons Snd : ∀a, b. Term (a, b) ⟶ Term b

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
        3, "∃. δ = (Calc → ∃n.Num n)"]
    );

  (* TODO: mutual recursion where the nested function has nontrivial
     postcondition, which needs to be bootstrapped from its
     non-recursive part. *)

  "local defs simple" >::
    (fun () ->
       skip_if !debug "debug";
       test_case "local defs simple"
"datatype Box : type
datacons Int : Int ⟶ Box Int
datacons String : String ⟶ Box String
external let fI : Int → Int → Int = \"(*)\"
external let fS : String → String → String = \"(@)\"

let rec foo =
  function
  | Int x -> let rec bar = fun y -> fI x y in bar x
  | String x -> let rec baz = fun y -> fS x y in baz x"

        [1, "∃a. δ = (Box a → a)"]
    );

  "local recursion simple" >::
    (fun () ->
       skip_if !debug "debug";
       test_case "local defs simple"
"datatype Box : type
datacons Int : Int ⟶ Box Int
datacons String : String ⟶ Box String
external let fI : Int → Int → Int = \"(*)\"
external let decrI : Int → Int = \"fun i -> i - 1\"
external let zero_p : Int → Bool = \"(=) 0\"
external let one : Int = \"1\"
external let fS : String → String → String = \"(@)\"
external let decrS : String → String =
  \"fun s -> String.sub s 1 (String.length s - 1)\"
external let empty_p : String → Bool = \"fun s -> String.length s = 0\"

let rec foo =
  function
  | Int x ->
    let rec bar = fun y ->
      match zero_p y with
      | True -> one
      | False -> fI y (bar (decrI y)) in
    bar x
  | String x ->
    let rec baz = fun y ->
      match empty_p y with
      | True -> \"\"
      | False -> fS y (baz (decrS y)) in
    baz x"

        [1, "∃a. δ = (Box a → a)"]
    );

  "nonrec simple" >::
    (fun () ->
       skip_if !debug "debug";
       test_nonrec_case "nonrec simple"
"datatype Order : num * num
external compare : ∀i, j. Num i → Num j → (Order (i, j), Int)
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
"datatype Tree : type * num
datatype Forest : type * num

datacons Node : ∀a, k [0≤k]. Num k * a * Forest (a, k) ⟶ Tree (a, k)
datacons TCons :
  ∀a, n [0≤n]. Tree (a, n) * Forest (a, n) ⟶ Forest (a, n+1)
datacons TNil : ∀a. Forest (a, 0)

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
"datatype Tree : type * num
datatype Forest : type * num

datacons Node : ∀a, k [0≤k]. Num k * a * Forest (a, k) ⟶ Tree (a, k)
datacons TCons :
  ∀a, n [0≤n]. Tree (a, n) * Forest (a, n) ⟶ Forest (a, n+1)
datacons TNil : ∀a. Forest (a, 0)

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
"datatype Unary : num
datacons UNil : Unary 0
datacons UCons : ∀n [0≤n]. Unary n ⟶ Unary (n+1)

let rec zip =
  efunction
    | UNil, UNil -> UNil
    | UNil, UCons _ -> UNil
    | UCons _, UNil -> UNil
    | UCons xs, UCons ys ->
      let zs = zip (xs, ys) in
      UCons zs"
        [2,"∃n, k. δ = ((Unary n, Unary k) → ∃i[i=min (n, k)].Unary i)"]
    );

  "unary minimum asserted" >::
    (fun () ->
       skip_if !debug "debug";
       test_case "unary minimum asserted"
"datatype Unary : num
datacons UNil : Unary 0
datacons UCons : ∀n [0≤n]. Unary n ⟶ Unary (n+1)
external num_of_unary : ∀n. Unary n → Num n

let rec zip =
  efunction
    | UNil, u when num_of_unary u + 1 <= 0 -> assert false
    | UNil, u when 0 <= num_of_unary u -> UNil
    | UCons _, UNil -> UNil
    | UCons xs, UCons ys ->
      let zs = zip (xs, ys) in
      UCons zs"
        [2,"∃n, k. δ = ((Unary n, Unary k) → ∃i[i=min (k, n)].Unary i) ∧ 0 ≤ k"]
    );

  "list zip prefix expanded" >::
    (fun () ->
       skip_if !debug "debug";
       test_case "list zip prefix expanded"
"datatype List : type * num
datacons LNil : ∀a. List(a, 0)
datacons LCons : ∀n, a [0≤n]. a * List(a, n) ⟶ List(a, n+1)

let rec zip =
  efunction
    | LNil, LNil -> LNil
    | LNil, LCons (_, _) -> LNil
    | LCons (_, _), LNil -> LNil
    | LCons (x, xs), LCons (y, ys) ->
      let zs = zip (xs, ys) in
      LCons ((x, y), zs)"
        [2,"∃n, k, a, b.
  δ = ((List (a, n), List (b, k)) → ∃i[i=min (k, n)].List ((a, b), i))"]
    );

  "unary maximum expanded" >::
    (fun () ->
       skip_if !debug "debug";
       test_case "unary maximum"
"datatype Unary : num
datacons UNil : Unary 0
datacons UCons : ∀n [0≤n]. Unary n ⟶ Unary (n+1)

let rec map2 =
  efunction
    | UNil, UNil -> UNil
    | UNil, (UCons _ as l) -> l
    | (UCons _ as l), UNil -> l
    | UCons xs, UCons ys ->
      let zs = map2 (xs, ys) in
      UCons zs"
        [2,"∃n, k. δ = ((Unary n, Unary k) → ∃i[i=max (k, n)].Unary i)"]
    );

  "list map2 with postfix expanded" >::
    (fun () ->
       todo "keep separate bvs variables";
       skip_if !debug "debug";
       test_case "list map2 with postfix"
"datatype List : type * num
datacons LNil : ∀a. List(a, 0)
datacons LCons : ∀n, a [0≤n]. a * List(a, n) ⟶ List(a, n+1)

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
       ∃i[i=max (k, n)].List (a, i))"]
    );


  "list filter-zip prefix" >::
    (fun () ->
       skip_if !debug "debug";
       test_case "list filter-zip prefix"
"datatype List : type * num
datacons LNil : ∀a. List(a, 0)
datacons LCons : ∀n, a [0≤n]. a * List(a, n) ⟶ List(a, n+1)

let rec filter_zip = fun f ->
  efunction
    | LNil, LNil -> LNil
    | LNil, LCons (_, _) -> LNil
    | LCons (_, _), LNil -> LNil
    | LCons (x, xs), LCons (y, ys) ->
      let zs = filter_zip f (xs, ys) in
      ematch f x y with
      | True -> LCons ((x, y), zs)
      | False -> zs"
        [2,"∃n, k, a, b.
  δ =
    ((a → b → Bool) → (List (a, n), List (b, k)) → ∃i[i ≤ k ∧
       i ≤ n ∧ 0 ≤ i].List ((a, b), i))"]
    );

  "list filter-map2 with postfix" >::
    (fun () ->
       todo "keep separate bvs variables";
       skip_if !debug "debug";
       test_case "list filter-map2 with postfix"
"datatype List : type * num
datacons LNil : ∀a. List(a, 0)
datacons LCons : ∀n, a [0≤n]. a * List(a, n) ⟶ List(a, n+1)

let rec filter_map2 = fun p f ->
  efunction
    | LNil, LNil -> LNil
    | LNil, (LCons (_, _) as l) -> l
    | (LCons (_, _) as l), LNil -> l
    | LCons (x, xs), LCons (y, ys) ->
      let zs = filter_map2 p f (xs, ys) in
      ematch p x y with
      | True -> LCons (f x y, zs)
      | False -> zs"
        [2,"∃n, k, a.
  δ =
    ((a → a → Bool) → (a → a → a) →
       (List (a, n), List (a, k)) → ∃i[0 ≤ i ∧ n ≤ i + k ∧
       k ≤ i + n ∧ i≤max (n, k)].List (a, i))"]
    );

  "list filter-map2 with filter postfix mono" >::
    (fun () ->
       skip_if !debug "debug";
       test_case "list filter-map2 with filter postfix mono"
"datatype Bar
datatype List : num
datacons LNil : ∀a. List 0
datacons LCons : ∀n [0≤n]. Bar * List n ⟶ List(n+1)
external p : Bar → Bar → Bool
external q : Bar → Bool
external f : Bar → Bar → Bar

let rec filter_map2 =
  efunction
    | LNil, LNil -> LNil
    | LNil, LCons (y, ys) ->
      let zs = filter_map2 (LNil, ys) in
      (ematch q y with
      | True -> LCons (y, zs)
      | False -> zs)
    | LCons (x, xs), LNil ->
      let zs = filter_map2 (xs, LNil) in
      (ematch q x with
      | True -> LCons (x, zs)
      | False -> zs)
    | LCons (x, xs), LCons (y, ys) ->
      let zs = filter_map2 (xs, ys) in
      ematch p x y with
      | True -> LCons (f x y, zs)
      | False -> zs"
        [2,"∃n, k. δ = ((List n, List k) → ∃i[i≤max (n, k) ∧ 0 ≤ i].List i)"]
    );

  "non-num no postcond list filter-map2 with filter postfix" >::
    (fun () ->
       skip_if !debug "debug";
       test_case "non-num no postcond list filter-map2 with filter postfix"
"datatype List : type
datacons LNil : ∀a. List a
datacons LCons : ∀a. a * List a ⟶ List a

let rec filter_map2 = fun p q r f g h ->
  function
    | LNil, LNil -> LNil
    | LNil, LCons (y, ys) ->
      let zs = filter_map2 p q r f g h (LNil, ys) in
      (match r y with
      | True -> LCons (h y, zs)
      | False -> zs)
    | LCons (x, xs), LNil ->
      let zs = filter_map2 p q r f g h (xs, LNil) in
      (match q x with
      | True -> LCons (g x, zs)
      | False -> zs)
    | LCons (x, xs), LCons (y, ys) ->
      let zs = filter_map2 p q r f g h (xs, ys) in
      match p x y with
      | True -> LCons (f x y, zs)
      | False -> zs"
        [1,"∃a, b, c.
  δ =
    ((a → b → Bool) → (a → Bool) → (b → Bool) →
       (a → b → c) → (a → c) → (b → c) → (List a, List b) →
       List c)"]
    );

  "non-num list filter-map2 with filter postfix" >::
    (fun () ->
       skip_if !debug "debug";
       test_case "non-num list filter-map2 with filter postfix"
"datatype List : type
datacons LNil : ∀a. List a
datacons LCons : ∀a. a * List a ⟶ List a

let rec filter_map2 = fun p q r f g h ->
  efunction
    | LNil, LNil -> LNil
    | LNil, LCons (y, ys) ->
      let zs = filter_map2 p q r f g h (LNil, ys) in
      (ematch r y with
      | True -> LCons (h y, zs)
      | False -> zs)
    | LCons (x, xs), LNil ->
      let zs = filter_map2 p q r f g h (xs, LNil) in
      (ematch q x with
      | True -> LCons (g x, zs)
      | False -> zs)
    | LCons (x, xs), LCons (y, ys) ->
      let zs = filter_map2 p q r f g h (xs, ys) in
      ematch p x y with
      | True -> LCons (f x y, zs)
      | False -> zs"
        [2,"∃a, b, c.
  δ =
    ((b → c → Bool) → (b → Bool) → (c → Bool) →
       (b → c → a) → (b → a) → (c → a) → (List b, List c) →
       ∃.List a)"]
    );

  "list filter-map2 with filter postfix" >::
    (fun () ->
       skip_if !debug "debug";
       test_case "list filter-map2 with filter postfix"
"datatype List : type * num
datacons LNil : ∀a. List(a, 0)
datacons LCons : ∀n, a [0≤n]. a * List(a, n) ⟶ List(a, n+1)

let rec filter_map2 = fun p q r f g h ->
  efunction
    | LNil, LNil -> LNil
    | LNil, LCons (y, ys) ->
      let zs = filter_map2 p q r f g h (LNil, ys) in
      (ematch r y with
      | True -> LCons (h y, zs)
      | False -> zs)
    | LCons (x, xs), LNil ->
      let zs = filter_map2 p q r f g h (xs, LNil) in
      (ematch q x with
      | True -> LCons (g x, zs)
      | False -> zs)
    | LCons (x, xs), LCons (y, ys) ->
      let zs = filter_map2 p q r f g h (xs, ys) in
      ematch p x y with
      | True -> LCons (f x y, zs)
      | False -> zs"
        [2,"∃n, k, a, b, c.
  δ =
    ((b → c → Bool) → (b → Bool) → (c → Bool) →
       (b → c → a) → (b → a) → (c → a) →
       (List (b, n), List (c, k)) → ∃i[i≤max (n, k) ∧
       0 ≤ i].List (a, i))"]
    );

  "list map2 with filter postfix" >::
    (fun () ->
       skip_if !debug "debug";
       test_case "list map2 with filter postfix"
"datatype List : type * num
datacons LNil : ∀a. List(a, 0)
datacons LCons : ∀n, a [0≤n]. a * List(a, n) ⟶ List(a, n+1)

let rec map2_filter = fun q r f g h ->
  efunction
    | LNil, LNil -> LNil
    | LNil, LCons (y, ys) ->
      let zs = map2_filter q r f g h (LNil, ys) in
      (ematch r y with
      | True -> LCons (h y, zs)
      | False -> zs)
    | LCons (x, xs), LNil ->
      let zs = map2_filter q r f g h (xs, LNil) in
      (ematch q x with
      | True -> LCons (g x, zs)
      | False -> zs)
    | LCons (x, xs), LCons (y, ys) ->
      let zs = map2_filter q r f g h (xs, ys) in
      LCons (f x y, zs)"
        [2,"∃n, k, a, b, c.
  δ =
    ((b → Bool) → (c → Bool) → (b → c → a) → (b → a) →
       (c → a) → (List (b, n), List (c, k)) → ∃i[i≤max (n, k) ∧
       min (k, n)≤i].List (a, i))"]
    );

  "avl_tree--height" >::
    (fun () ->
       skip_if !debug "debug";
       test_case "avl_tree--height"
"datatype Avl : type * num
datacons Empty : ∀a. Avl (a, 0)
datacons Node :
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
"datatype Avl : type * num
datacons Empty : ∀a. Avl (a, 0)
datacons Node :
  ∀a,k,m,n [k=max(m,n) ∧ 0≤m ∧ 0≤n ∧ n≤m+2 ∧ m≤n+2].
     Avl (a, m) * a * Avl (a, n) * Num (k+1) ⟶ Avl (a, k+1)

external height : ∀a,n. Avl (a, n) → Num n

let create = fun l x r ->
  ematch height l, height r with
  | i, j when j <= i -> Node (l, x, r, i+1)
  | i, j when i <= j -> Node (l, x, r, j+1)"
        [2,"∃n, k, a.
  δ =
    (Avl (a, k) → a → Avl (a, n) →
       ∃i[i=max (k + 1, n + 1)].Avl (a, i)) ∧
  0 ≤ n ∧ 0 ≤ k ∧ n ≤ k + 2 ∧ k ≤ n + 2"];
    );

  "avl_tree--singleton" >::
    (fun () ->
       skip_if !debug "debug";
       test_case "avl_tree--height"
"datatype Avl : type * num
datacons Empty : ∀a. Avl (a, 0)
datacons Node :
  ∀a,k,m,n [k=max(m,n) ∧ 0≤m ∧ 0≤n ∧ n≤m+2 ∧ m≤n+2].
     Avl (a, m) * a * Avl (a, n) * Num (k+1) ⟶ Avl (a, k+1)

let singleton = fun x -> Node (Empty, x, Empty, 1)"
        [1,"∃a. δ = (a → Avl (a, 1))"];
    );

  "avl_tree--min_binding" >::
    (fun () ->
       skip_if !debug "debug";
       test_case "avl_tree--height"
"datatype Avl : type * num
datacons Empty : ∀a. Avl (a, 0)
datacons Node :
  ∀a,k,m,n [k=max(m,n) ∧ 0≤m ∧ 0≤n ∧ n≤m+2 ∧ m≤n+2].
     Avl (a, m) * a * Avl (a, n) * Num (k+1) ⟶ Avl (a, k+1)

let rec min_binding = function
  | Empty -> assert false
  | Node (Empty, x, r, _) -> x
  | Node ((Node (_,_,_,_) as l), x, r, _) -> min_binding l"
        [1,"∃n, a. δ = (Avl (a, n) → a) ∧ 1 ≤ n"];
    );

  "avl_tree--rotr-simple" >::
    (fun () ->
       skip_if !debug "debug";
       test_case "avl_tree--rotr-simple"
"datatype Avl : type * num
datacons Empty : ∀a. Avl (a, 0)
datacons Node :
  ∀a,k,m,n [k=max(m,n) ∧ 0≤m ∧ 0≤n ∧ n≤m+2 ∧ m≤n+2].
     Avl (a, m) * a * Avl (a, n) * Num (k+1) ⟶ Avl (a, k+1)

external height : ∀a,n. Avl (a, n) → Num n
external create :
  ∀a,n,k[k ≤ n + 2 ∧ n ≤ k + 2 ∧ 0 ≤ k ∧ 0 ≤ n].
      Avl (a, k) → a → Avl (a, n) → ∃i[i=max (k + 1, n + 1) ∧
       0 ≤ i].Avl (a, i)
external singleton : ∀a. a → Avl (a, 1)

let rotr = efunction (* hl = hr + 3 *)
    | Empty, x, r -> assert false
    | Node (ll, lx, lr, hl), x, r ->
      (ematch height ll, height lr, height r with
      | _, _, hr when hr+1 <= 0 -> assert false
      | _, _, hr when hl <= hr+2 -> assert false
      | _, _, hr when hr+4 <= hl -> assert false
      | m, n, _ when n <= m ->
        let r' = create lr x r in
        create ll lx r'
      | m, n, _ when m+1 <= n ->
        (ematch lr with
        | Empty -> assert false
        | Node (lrl, lrx, lrr, _) ->
          let l' = create ll lx lrl in
          let r' = create lrr x r in
          create l' lrx r'))
"
        [2,"∃n, a.
  δ =
    ((Avl (a, n + 3), a, Avl (a, n)) → ∃k[n + 3 ≤ k ∧
       k ≤ n + 4].Avl (a, k)) ∧
  0 ≤ n"];
    );

  "avl_tree--rotr-simple2" >::
    (fun () ->
       skip_if !debug "debug";
       test_case "avl_tree--rotr-simple2"
"datatype Avl : type * num
datacons Empty : ∀a. Avl (a, 0)
datacons Node :
  ∀a,k,m,n [k=max(m,n) ∧ 0≤m ∧ 0≤n ∧ n≤m+2 ∧ m≤n+2].
     Avl (a, m) * a * Avl (a, n) * Num (k+1) ⟶ Avl (a, k+1)

external height : ∀a,n. Avl (a, n) → Num n
external create :
  ∀a,n,k[k ≤ n + 2 ∧ n ≤ k + 2 ∧ 0 ≤ k ∧ 0 ≤ n].
      Avl (a, k) → a → Avl (a, n) → ∃i[i=max (k + 1, n + 1) ∧
       0 ≤ i].Avl (a, i)
external singleton : ∀a. a → Avl (a, 1)

let rotr = efunction
    | Empty, x, r -> assert false
    | Node (ll, lx, lr, hl), x, r ->
      assert num 0 <= height r;
      assert type hl = height r + 3;
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
          create l' lrx r'))
"
        [2,"∃n, a.
  δ =
    ((Avl (a, n + 3), a, Avl (a, n)) → ∃k[n + 3 ≤ k ∧
       k ≤ n + 4].Avl (a, k)) ∧
  0 ≤ n"];
    );

  "avl_tree--rotr-simple3" >::
    (fun () ->
       skip_if !debug "debug";
       test_case "avl_tree--rotr-simple2"
"datatype Avl : type * num
datacons Empty : ∀a. Avl (a, 0)
datacons Node :
  ∀a,k,m,n [k=max(m,n) ∧ 0≤m ∧ 0≤n ∧ n≤m+2 ∧ m≤n+2].
     Avl (a, m) * a * Avl (a, n) * Num (k+1) ⟶ Avl (a, k+1)

external height : ∀a,n. Avl (a, n) → Num n
external create :
  ∀a,n,k[k ≤ n + 2 ∧ n ≤ k + 2 ∧ 0 ≤ k ∧ 0 ≤ n].
      Avl (a, k) → a → Avl (a, n) → ∃i[i=max (k + 1, n + 1) ∧
       0 ≤ i].Avl (a, i)
external singleton : ∀a. a → Avl (a, 1)

let rotr = efunction
    | Empty, x, r -> assert false
    | Node (ll, lx, lr, hl), x, r ->
      let hr = height r in
      assert num 0 <= hr;
      assert type hl = hr + 3;
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
          create l' lrx r'))
"
        [2,"∃n, a.
  δ =
    ((Avl (a, n + 3), a, Avl (a, n)) → ∃k[n + 3 ≤ k ∧
       k ≤ n + 4].Avl (a, k)) ∧
  0 ≤ n"];
    );

  "avl_tree--rotr" >::
    (fun () ->
       todo "too hard for current numerical abduction";
       skip_if !debug "debug";
       test_case "avl_tree--rotr"
"datatype Avl : type * num
datacons Empty : ∀a. Avl (a, 0)
datacons Node :
  ∀a,k,m,n [k=max(m,n) ∧ 0≤m ∧ 0≤n ∧ n≤m+2 ∧ m≤n+2].
     Avl (a, m) * a * Avl (a, n) * Num (k+1) ⟶ Avl (a, k+1)

external height : ∀a,n. Avl (a, n) → Num n
external create :
  ∀a,n,k[k ≤ n + 2 ∧ n ≤ k + 2 ∧ 0 ≤ k ∧ 0 ≤ n].
      Avl (a, k) → a → Avl (a, n) → ∃i[i=max (k + 1, n + 1) ∧
       0 ≤ i].Avl (a, i)
external singleton : ∀a. a → Avl (a, 1)

let rotr = fun l x r -> (* hl = hr + 3 *)
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
"
        [2,""];
    );

  (* The [rotl] functions are symmetrical to [rotr]. *)
  "avl_tree--rotl-simple" >::
    (fun () ->
       skip_if !debug "debug";
       test_case "avl_tree--rotl"
"datatype Avl : type * num
datacons Empty : ∀a. Avl (a, 0)
datacons Node :
  ∀a,k,m,n [k=max(m,n) ∧ 0≤m ∧ 0≤n ∧ n≤m+2 ∧ m≤n+2].
     Avl (a, m) * a * Avl (a, n) * Num (k+1) ⟶ Avl (a, k+1)

external height : ∀a,n. Avl (a, n) → Num n
external create :
  ∀a,n,k[k ≤ n + 2 ∧ n ≤ k + 2 ∧ 0 ≤ k ∧ 0 ≤ n].
      Avl (a, k) → a → Avl (a, n) → ∃i[i=max (k + 1, n + 1) ∧
       0 ≤ i].Avl (a, i)
external singleton : ∀a. a → Avl (a, 1)

let rotl = efunction (* hl + 3 = hr *)
    | l, x, Empty -> assert false
    | l, x, Node (rl, rx, rr, hr) ->
      (ematch height rr, height rl, height l with
      | _, _, hl when hl+1 <= 0 -> assert false
      | _, _, hl when hr <= hl+2 -> assert false
      | _, _, hl when hl+4 <= hr -> assert false
      | m, n, _ when n <= m ->
        let l' = create l x rl in
        create l' rx rr
      | m, n, _ when m+1 <= n ->
        (ematch rl with
        | Empty -> assert false
        | Node (rll, rlx, rlr, _) ->
          let l' = create l x rll in
          let r' = create rlr rx rr in
          create l' rlx r'))
"
        [2,"∃n, a.
  δ =
    ((Avl (a, n), a, Avl (a, n + 3)) → ∃k[n + 3 ≤ k ∧
       k ≤ n + 4].Avl (a, k)) ∧
  0 ≤ n"];
    );

  "avl_tree--rotl-simple2" >::
    (fun () ->
       skip_if !debug "debug";
       test_case "avl_tree--rotl"
"datatype Avl : type * num
datacons Empty : ∀a. Avl (a, 0)
datacons Node :
  ∀a,k,m,n [k=max(m,n) ∧ 0≤m ∧ 0≤n ∧ n≤m+2 ∧ m≤n+2].
     Avl (a, m) * a * Avl (a, n) * Num (k+1) ⟶ Avl (a, k+1)

external height : ∀a,n. Avl (a, n) → Num n
external create :
  ∀a,n,k[k ≤ n + 2 ∧ n ≤ k + 2 ∧ 0 ≤ k ∧ 0 ≤ n].
      Avl (a, k) → a → Avl (a, n) → ∃i[i=max (k + 1, n + 1) ∧
       0 ≤ i].Avl (a, i)
external singleton : ∀a. a → Avl (a, 1)

let rotl = efunction
    | l, x, Empty -> assert false
    | l, x, Node (rl, rx, rr, hr) ->
      assert num 0 <= height l;
      assert type hr = height l + 3;
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
          create l' rlx r'))
"
        [2,"∃n, a.
  δ =
    ((Avl (a, n), a, Avl (a, n + 3)) → ∃k[n + 3 ≤ k ∧
       k ≤ n + 4].Avl (a, k)) ∧
  0 ≤ n"];
    );

  "avl_tree--rotl" >::
    (fun () ->
       todo "too hard for current numerical abduction";
       skip_if !debug "debug";
       test_case "avl_tree--rotl"
"datatype Avl : type * num
datacons Empty : ∀a. Avl (a, 0)
datacons Node :
  ∀a,k,m,n [k=max(m,n) ∧ 0≤m ∧ 0≤n ∧ n≤m+2 ∧ m≤n+2].
     Avl (a, m) * a * Avl (a, n) * Num (k+1) ⟶ Avl (a, k+1)

external height : ∀a,n. Avl (a, n) → Num n
external create :
  ∀a,n,k[k ≤ n + 2 ∧ n ≤ k + 2 ∧ 0 ≤ k ∧ 0 ≤ n].
      Avl (a, k) → a → Avl (a, n) → ∃i[i=max (k + 1, n + 1) ∧
       0 ≤ i].Avl (a, i)
external singleton : ∀a. a → Avl (a, 1)

let rotl = fun l x r -> (* hl + 3 = hr *)
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
          create l' rlx r')))
"
        [2,""];
    );

  "avl_tree--add-simple" >::
    (fun () ->
       skip_if !debug "debug";
       test_case ~no_num_abduction:true "avl_tree--add"
"datatype Avl : type * num
datacons Empty : ∀a. Avl (a, 0)
datacons Node :
  ∀a,k,m,n [k=max(m,n) ∧ 0≤m ∧ 0≤n ∧ n≤m+2 ∧ m≤n+2].
     Avl (a, m) * a * Avl (a, n) * Num (k+1) ⟶ Avl (a, k+1)
datatype LinOrder
datacons LT : LinOrder
datacons EQ : LinOrder
datacons GT : LinOrder
external let compare : ∀a. a → a → LinOrder =
  \"fun x y -> let c=Pervasives.compare x y in
              if c<0 then LT else if c=0 then EQ else GT\"

external height : ∀a,n. Avl (a, n) → Num n
external create :
  ∀a,n,k[k ≤ n + 2 ∧ n ≤ k + 2 ∧ 0 ≤ k ∧ 0 ≤ n].
      Avl (a, k) → a → Avl (a, n) → ∃i[i=max (k + 1, n + 1) ∧
       0 ≤ i].Avl (a, i)
external rotr :
  ∀n, a. Avl (a, n+3) → a → Avl (a, n) →
       ∃i[n+3 ≤ i ∧ i ≤ n+4].Avl (a, i)
external rotl :
  ∀n, a. Avl (a, n) → a → Avl (a, n+3) →
       ∃i[n+3 ≤ i ∧ i ≤ n+4].Avl (a, i)

let rec add = fun x -> efunction
  | Empty -> Node (Empty, x, Empty, 1)
  | Node (l, y, r, h) ->
    ematch compare x y, height l, height r with
    | EQ, _, _ -> Node (l, x, r, h)
    | LT, hl, hr ->
      let l' = add x l in
      (ematch height l' with
       | hl' when hl' <= hr+2 -> create l' y r
       | hl' when hr+3 <= hl' -> rotr l' y r)
    | GT, hl, hr ->
      let r' = add x r in
      (ematch height r' with
       | hr' when hr' <= hl+2 -> create l y r'
       | hr' when hl+3 <= hr' -> rotl l y r')
"
        [2,"∃n, a.
  δ =
    (a → Avl (a, n) → ∃k[1 ≤ k ∧ n ≤ k ∧
       k ≤ n + 1].Avl (a, k))"];
    );

  "avl_tree--add-simple2" >::
    (fun () ->
       skip_if !debug "debug";
       test_case ~no_num_abduction:true "avl_tree--add"
"datatype Avl : type * num
datacons Empty : ∀a. Avl (a, 0)
datacons Node :
  ∀a,k,m,n [k=max(m,n) ∧ 0≤m ∧ 0≤n ∧ n≤m+2 ∧ m≤n+2].
     Avl (a, m) * a * Avl (a, n) * Num (k+1) ⟶ Avl (a, k+1)
datatype LinOrder
datacons LT : LinOrder
datacons EQ : LinOrder
datacons GT : LinOrder
external let compare : ∀a. a → a → LinOrder =
  \"fun x y -> let c=Pervasives.compare x y in
              if c<0 then LT else if c=0 then EQ else GT\"

external height : ∀a,n. Avl (a, n) → Num n
external create :
  ∀a,n,k[k ≤ n + 2 ∧ n ≤ k + 2 ∧ 0 ≤ k ∧ 0 ≤ n].
      Avl (a, k) → a → Avl (a, n) → ∃i[i=max (k + 1, n + 1) ∧
       0 ≤ i].Avl (a, i)
external rotr :
  ∀n, a. Avl (a, n+3) → a → Avl (a, n) →
       ∃i[n+3 ≤ i ∧ i ≤ n+4].Avl (a, i)
external rotl :
  ∀n, a. Avl (a, n) → a → Avl (a, n+3) →
       ∃i[n+3 ≤ i ∧ i ≤ n+4].Avl (a, i)

let rec add = fun x -> efunction
  | Empty -> Node (Empty, x, Empty, 1)
  | Node (l, y, r, h) ->
    ematch compare x y with
    | EQ -> Node (l, x, r, h)
    | LT ->
      let l' = add x l in
      (ematch height l', height r with
       | hl', hr when hl' <= hr+2 -> create l' y r
       | hl', hr when hr+3 <= hl' -> rotr l' y r)
    | GT ->
      let r' = add x r in
      (ematch height r', height l with
       | hr', hl when hr' <= hl+2 -> create l y r'
       | hr', hl when hl+3 <= hr' -> rotl l y r')
"
(* Tricky! The weaker result is due to lack of sharing of information
   about [l] due to facts about [l' = add x l], resp. about [r] due
   to facts about [r' = add x r], with the other branch. *)
        [2,"∃n, a.
  δ =
    (a → Avl (a, n) → ∃k[1 ≤ k ∧ n ≤ k ∧
       k ≤ n + 1].Avl (a, k))"];
    );

  "avl_tree--add" >::
    (fun () ->
       skip_if !debug "debug";
       test_case "avl_tree--add"
"datatype Avl : type * num
datacons Empty : ∀a. Avl (a, 0)
datacons Node :
  ∀a,k,m,n [k=max(m,n) ∧ 0≤m ∧ 0≤n ∧ n≤m+2 ∧ m≤n+2].
     Avl (a, m) * a * Avl (a, n) * Num (k+1) ⟶ Avl (a, k+1)
datatype LinOrder
datacons LT : LinOrder
datacons EQ : LinOrder
datacons GT : LinOrder
external let compare : ∀a. a → a → LinOrder =
  \"fun x y -> let c=Pervasives.compare x y in
              if c<0 then LT else if c=0 then EQ else GT\"

external height : ∀a,n. Avl (a, n) → Num n
external create :
  ∀a,n,k[k ≤ n + 2 ∧ n ≤ k + 2 ∧ 0 ≤ k ∧ 0 ≤ n].
      Avl (a, k) → a → Avl (a, n) → ∃i[i=max (k + 1, n + 1) ∧
       0 ≤ i].Avl (a, i)
external rotr :
  ∀n, a. Avl (a, n+3) → a → Avl (a, n) →
       ∃i[n+3 ≤ i ∧ i ≤ n+4].Avl (a, i)
external rotl :
  ∀n, a. Avl (a, n) → a → Avl (a, n+3) →
       ∃i[n+3 ≤ i ∧ i ≤ n+4].Avl (a, i)

let rec add = fun x -> efunction
  | Empty -> Node (Empty, x, Empty, 1)
  | Node (l, y, r, h) ->
    ematch compare x y, height l, height r with
    | EQ, _, _ -> Node (l, x, r, h)
    | LT, hl, hr ->
      let l' = add x l in
      (ematch height l' with
       | hl' when hl' <= hr+2 -> create l' y r
       | hl' when hr+3 <= hl' -> rotr l' y r)
    | GT, hl, hr ->
      let r' = add x r in
      (ematch height r' with
       | hr' when hr' <= hl+2 -> create l y r'
       | hr' when hl+3 <= hr' -> rotl l y r')
"
        [2,"∃n, a.
  δ =
    (a → Avl (a, n) → ∃k[1 ≤ k ∧ n ≤ k ∧
       k ≤ n + 1].Avl (a, k))"];
    );

  "avl_tree--add2" >::
    (fun () ->
       todo "too hard for current numerical abduction";
       skip_if !debug "debug";
       test_case "avl_tree--add"
"datatype Avl : type * num
datacons Empty : ∀a. Avl (a, 0)
datacons Node :
  ∀a,k,m,n [k=max(m,n) ∧ 0≤m ∧ 0≤n ∧ n≤m+2 ∧ m≤n+2].
     Avl (a, m) * a * Avl (a, n) * Num (k+1) ⟶ Avl (a, k+1)
datatype LinOrder
datacons LT : LinOrder
datacons EQ : LinOrder
datacons GT : LinOrder
external let compare : ∀a. a → a → LinOrder =
  \"fun x y -> let c=Pervasives.compare x y in
              if c<0 then LT else if c=0 then EQ else GT\"

external height : ∀a,n. Avl (a, n) → Num n
external create :
  ∀a,n,k[k ≤ n + 2 ∧ n ≤ k + 2 ∧ 0 ≤ k ∧ 0 ≤ n].
      Avl (a, k) → a → Avl (a, n) → ∃i[i=max (k + 1, n + 1) ∧
       0 ≤ i].Avl (a, i)
external rotr :
  ∀n, a. Avl (a, n+3) → a → Avl (a, n) →
       ∃i[n+3 ≤ i ∧ i ≤ n+4].Avl (a, i)
external rotl :
  ∀n, a. Avl (a, n) → a → Avl (a, n+3) →
       ∃i[n+3 ≤ i ∧ i ≤ n+4].Avl (a, i)

let rec add = fun x -> efunction
  | Empty -> Node (Empty, x, Empty, 1)
  | Node (l, y, r, h) ->
    ematch compare x y with
    | EQ -> Node (l, x, r, h)
    | LT ->
      let l' = add x l in
      (ematch height l', height r with
       | hl', hr when hl' <= hr+2 -> create l' y r
       | hl', hr when hr+3 <= hl' -> rotr l' y r)
    | GT ->
      let r' = add x r in
      (ematch height r', height l with
       | hr', hl when hr' <= hl+2 -> create l y r'
       | hr', hl when hl+3 <= hr' -> rotl l y r')
"
(* Tricky because of lack of sharing of information
   about [l] due to facts about [l' = add x l], resp. about [r] due
   to facts about [r' = add x r], with the other branch. *)
        [2,"∃n, a.
  δ =
    (a → Avl (a, n) → ∃k[k ≤ n + 1 ∧ 1 ≤ k ∧
       n ≤ k].Avl (a, k))"];
    );

  "avl_tree--remove_min_binding-simple" >::
    (fun () ->
       skip_if !debug "debug";
       test_case ~no_num_abduction:true
         "avl_tree--remove_min_binding-simple"
"datatype Avl : type * num
datacons Empty : ∀a. Avl (a, 0)
datacons Node :
  ∀a,k,m,n [k=max(m,n) ∧ 0≤m ∧ 0≤n ∧ n≤m+2 ∧ m≤n+2].
     Avl (a, m) * a * Avl (a, n) * Num (k+1) ⟶ Avl (a, k+1)
datatype LinOrder
datacons LT : LinOrder
datacons EQ : LinOrder
datacons GT : LinOrder
external let compare : ∀a. a → a → LinOrder =
  \"fun x y -> let c=Pervasives.compare x y in
              if c<0 then LT else if c=0 then EQ else GT\"

external height : ∀a,n. Avl (a, n) → Num n
external create :
  ∀a,n,k[k ≤ n + 2 ∧ n ≤ k + 2 ∧ 0 ≤ k ∧ 0 ≤ n].
      Avl (a, k) → a → Avl (a, n) → ∃i[i=max (k + 1, n + 1) ∧
       0 ≤ i].Avl (a, i)
external rotr :
  ∀n, a. Avl (a, n+3) → a → Avl (a, n) →
       ∃i[n+3 ≤ i ∧ i ≤ n+4].Avl (a, i)
external rotl :
  ∀n, a. Avl (a, n) → a → Avl (a, n+3) →
       ∃i[n+3 ≤ i ∧ i ≤ n+4].Avl (a, i)

let rec remove_min_binding = efunction
  | Empty -> assert false
  | Node (Empty, x, r, _) -> r
  | Node ((Node (_,_,_,_) as l), x, r, _) ->
    let l' = remove_min_binding l in
    (ematch height l', height r with
     | hl', hr when hl' <= hr+2 && hr <= hl'+2 -> create l' x r
     | hl', hr when hl'+3 <= hr -> rotl l' x r)
"
(* The inequality [k + 2 ≤ 2 n] corresponds to the fact [n=1 ==> k=0]. *)
        [2,"∃n, a.
  δ =
    (Avl (a, n) → ∃k[n ≤ k + 1 ∧ k ≤ n ∧
       k + 2 ≤ 2 n].Avl (a, k)) ∧
  1 ≤ n"];
    );

  "avl_tree--remove_min_binding" >::
    (fun () ->
       skip_if !debug "debug";
       test_case "avl_tree--remove_min_binding"
"datatype Avl : type * num
datacons Empty : ∀a. Avl (a, 0)
datacons Node :
  ∀a,k,m,n [k=max(m,n) ∧ 0≤m ∧ 0≤n ∧ n≤m+2 ∧ m≤n+2].
     Avl (a, m) * a * Avl (a, n) * Num (k+1) ⟶ Avl (a, k+1)
datatype LinOrder
datacons LT : LinOrder
datacons EQ : LinOrder
datacons GT : LinOrder
external let compare : ∀a. a → a → LinOrder =
  \"fun x y -> let c=Pervasives.compare x y in
              if c<0 then LT else if c=0 then EQ else GT\"

external height : ∀a,n. Avl (a, n) → Num n
external create :
  ∀a,n,k[k ≤ n + 2 ∧ n ≤ k + 2 ∧ 0 ≤ k ∧ 0 ≤ n].
      Avl (a, k) → a → Avl (a, n) → ∃i[i=max (k + 1, n + 1) ∧
       0 ≤ i].Avl (a, i)
external rotr :
  ∀n, a. Avl (a, n+3) → a → Avl (a, n) →
       ∃i[n+3 ≤ i ∧ i ≤ n+4].Avl (a, i)
external rotl :
  ∀n, a. Avl (a, n) → a → Avl (a, n+3) →
       ∃i[n+3 ≤ i ∧ i ≤ n+4].Avl (a, i)

let rec remove_min_binding = efunction
  | Empty -> assert false
  | Node (Empty, x, r, _) -> r
  | Node ((Node (_,_,_,_) as l), x, r, _) ->
    let l' = remove_min_binding l in
    (ematch height l', height r with
     | hl', hr when hl' <= hr+2 && hr <= hl'+2 -> create l' x r
     | hl', hr when hl'+3 <= hr -> rotl l' x r)
"
(* The inequality [k + 2 ≤ 2 n] corresponds to the fact [n=1 ==> k=0]. *)
        [2,"∃n, a.
  δ =
    (Avl (a, n) → ∃k[n ≤ k + 1 ∧ k ≤ n ∧
       k + 2 ≤ 2 n].Avl (a, k)) ∧
  1 ≤ n"];
    );

  "avl_tree--merge-simple" >::
    (fun () ->
       skip_if !debug "debug";
       test_case ~no_num_abduction:true "avl_tree--merge-simple"
"datatype Avl : type * num
datacons Empty : ∀a. Avl (a, 0)
datacons Node :
  ∀a,k,m,n [k=max(m,n) ∧ 0≤m ∧ 0≤n ∧ n≤m+2 ∧ m≤n+2].
     Avl (a, m) * a * Avl (a, n) * Num (k+1) ⟶ Avl (a, k+1)
datatype LinOrder
datacons LT : LinOrder
datacons EQ : LinOrder
datacons GT : LinOrder
external let compare : ∀a. a → a → LinOrder =
  \"fun x y -> let c=Pervasives.compare x y in
              if c<0 then LT else if c=0 then EQ else GT\"

external height : ∀a,n. Avl (a, n) → Num n
external create :
  ∀a,n,k[k ≤ n + 2 ∧ n ≤ k + 2 ∧ 0 ≤ k ∧ 0 ≤ n].
      Avl (a, k) → a → Avl (a, n) → ∃i[i=max (k + 1, n + 1) ∧
       0 ≤ i].Avl (a, i)
external rotr :
  ∀n, a. Avl (a, n+3) → a → Avl (a, n) →
       ∃i[n+3 ≤ i ∧ i ≤ n+4].Avl (a, i)
external rotl :
  ∀n, a. Avl (a, n) → a → Avl (a, n+3) →
       ∃i[n+3 ≤ i ∧ i ≤ n+4].Avl (a, i)
external min_binding : ∀n, a [1 ≤ n]. Avl (a, n) → a
external remove_min_binding :
  ∀n, a [1 ≤ n]. Avl (a, n) →
    ∃k[k + 2 ≤ 2 n ∧ n ≤ k + 1 ∧ k ≤ n].Avl (a, k)
  

let merge = efunction
  | Empty, Empty -> Empty
  | Empty, (Node (_,_,_,_) as t) -> t
  | (Node (_,_,_,_) as t), Empty -> t
  | Node (_,_,_,ht1), Node (_,_,_,ht2) when ht1+3 <= ht2 -> assert false
  | Node (_,_,_,ht1), Node (_,_,_,ht2) when ht2+3 <= ht1 -> assert false
  | (Node (_,_,_,_) as t1), (Node (_,_,_,_) as t2) ->
    let x = min_binding t2 in
    let t2' = remove_min_binding t2 in
    (ematch height t1, height t2' with
     | ht1, ht2' when ht1 <= ht2'+2 && ht2' <= ht1+2 -> create t1 x t2'
     | ht1, ht2' when ht2'+3 <= ht1 -> rotr t1 x t2')
"
        [2,"∃n, k, a.
  δ =
    ((Avl (a, n), Avl (a, k)) → ∃i[i≤max (k + 1, n + 1) ∧ k ≤ i ∧
       n ≤ i ∧ i ≤ n + k].Avl (a, i)) ∧
  n ≤ k + 2 ∧ k ≤ n + 2"];
    );

  "avl_tree--merge" >::
    (fun () ->
       skip_if !debug "debug";
       test_case "avl_tree--remove_min_binding"
"datatype Avl : type * num
datacons Empty : ∀a. Avl (a, 0)
datacons Node :
  ∀a,k,m,n [k=max(m,n) ∧ 0≤m ∧ 0≤n ∧ n≤m+2 ∧ m≤n+2].
     Avl (a, m) * a * Avl (a, n) * Num (k+1) ⟶ Avl (a, k+1)
datatype LinOrder
datacons LT : LinOrder
datacons EQ : LinOrder
datacons GT : LinOrder
external let compare : ∀a. a → a → LinOrder =
  \"fun x y -> let c=Pervasives.compare x y in
              if c<0 then LT else if c=0 then EQ else GT\"

external height : ∀a,n. Avl (a, n) → Num n
external create :
  ∀a,n,k[k ≤ n + 2 ∧ n ≤ k + 2 ∧ 0 ≤ k ∧ 0 ≤ n].
      Avl (a, k) → a → Avl (a, n) → ∃i[i=max (k + 1, n + 1) ∧
       0 ≤ i].Avl (a, i)
external rotr :
  ∀n, a. Avl (a, n+3) → a → Avl (a, n) →
       ∃i[n+3 ≤ i ∧ i ≤ n+4].Avl (a, i)
external rotl :
  ∀n, a. Avl (a, n) → a → Avl (a, n+3) →
       ∃i[n+3 ≤ i ∧ i ≤ n+4].Avl (a, i)
external min_binding : ∀n, a [1 ≤ n]. Avl (a, n) → a
external remove_min_binding :
  ∀n, a [1 ≤ n]. Avl (a, n) →
    ∃k[k + 2 ≤ 2 n ∧ n ≤ k + 1 ∧ k ≤ n].Avl (a, k)
  

let merge = efunction
  | Empty, Empty -> Empty
  | Empty, (Node (_,_,_,_) as t) -> t
  | (Node (_,_,_,_) as t), Empty -> t
  | Node (_,_,_,ht1), Node (_,_,_,ht2) when ht1+3 <= ht2 -> assert false
  | Node (_,_,_,ht1), Node (_,_,_,ht2) when ht2+3 <= ht1 -> assert false
  | (Node (_,_,_,_) as t1), (Node (_,_,_,_) as t2) ->
    let x = min_binding t2 in
    let t2' = remove_min_binding t2 in
    (ematch height t1, height t2' with
     | ht1, ht2' when ht1 <= ht2'+2 && ht2' <= ht1+2 -> create t1 x t2'
     | ht1, ht2' when ht2'+3 <= ht1 -> rotr t1 x t2')
"
        [2,"∃n, k, a.
  δ =
    ((Avl (a, n), Avl (a, k)) → ∃i[i≤max (k + 1, n + 1) ∧ k ≤ i ∧
       n ≤ i ∧ i ≤ n + k].Avl (a, i)) ∧
  n ≤ k + 2 ∧ k ≤ n + 2"];
    );

  "avl_tree--merge2" >::
    (fun () ->
       skip_if !debug "debug";
       test_case "avl_tree--remove_min_binding"
"datatype Avl : type * num
datacons Empty : ∀a. Avl (a, 0)
datacons Node :
  ∀a,k,m,n [k=max(m,n) ∧ 0≤m ∧ 0≤n ∧ n≤m+2 ∧ m≤n+2].
     Avl (a, m) * a * Avl (a, n) * Num (k+1) ⟶ Avl (a, k+1)
datatype LinOrder
datacons LT : LinOrder
datacons EQ : LinOrder
datacons GT : LinOrder
external let compare : ∀a. a → a → LinOrder =
  \"fun x y -> let c=Pervasives.compare x y in
              if c<0 then LT else if c=0 then EQ else GT\"

external height : ∀a,n. Avl (a, n) → Num n
external create :
  ∀a,n,k[k ≤ n + 2 ∧ n ≤ k + 2 ∧ 0 ≤ k ∧ 0 ≤ n].
      Avl (a, k) → a → Avl (a, n) → ∃i[i=max (k + 1, n + 1) ∧
       0 ≤ i].Avl (a, i)
external rotr :
  ∀n, a. Avl (a, n+3) → a → Avl (a, n) →
       ∃i[n+3 ≤ i ∧ i ≤ n+4].Avl (a, i)
external rotl :
  ∀n, a. Avl (a, n) → a → Avl (a, n+3) →
       ∃i[n+3 ≤ i ∧ i ≤ n+4].Avl (a, i)
external min_binding : ∀n, a [1 ≤ n]. Avl (a, n) → a
external remove_min_binding :
  ∀n, a [1 ≤ n]. Avl (a, n) →
    ∃k[k + 2 ≤ 2 n ∧ n ≤ k + 1 ∧ k ≤ n].Avl (a, k)
  

let merge = efunction
  | Empty, Empty -> Empty
  | Empty, (Node (_,_,_,_) as t) -> t
  | (Node (_,_,_,_) as t), Empty -> t
  | (Node (_,_,_,ht1) as t1), (Node (_,_,_,ht2) as t2) ->
    assert num ht1 <= ht2+2;
    assert num ht2 <= ht1+2;
    let x = min_binding t2 in
    let t2' = remove_min_binding t2 in
    (ematch height t1, height t2' with
     | ht1, ht2' when ht1 <= ht2'+2 && ht2' <= ht1+2 -> create t1 x t2'
     | ht1, ht2' when ht2'+3 <= ht1 -> rotr t1 x t2')
"
        [2,"∃n, k, a.
  δ =
    ((Avl (a, n), Avl (a, k)) → ∃i[i≤max (k + 1, n + 1) ∧ k ≤ i ∧
       n ≤ i ∧ i ≤ n + k].Avl (a, i)) ∧
  n ≤ k + 2 ∧ k ≤ n + 2"];
    );

  "avl_tree--merge3" >::
    (fun () ->
       todo "too hard for current numerical abduction";
       skip_if !debug "debug";
       test_case "avl_tree--remove_min_binding"
"datatype Avl : type * num
datacons Empty : ∀a. Avl (a, 0)
datacons Node :
  ∀a,k,m,n [k=max(m,n) ∧ 0≤m ∧ 0≤n ∧ n≤m+2 ∧ m≤n+2].
     Avl (a, m) * a * Avl (a, n) * Num (k+1) ⟶ Avl (a, k+1)
datatype LinOrder
datacons LT : LinOrder
datacons EQ : LinOrder
datacons GT : LinOrder
external let compare : ∀a. a → a → LinOrder =
  \"fun x y -> let c=Pervasives.compare x y in
              if c<0 then LT else if c=0 then EQ else GT\"

external height : ∀a,n. Avl (a, n) → Num n
external create :
  ∀a,n,k[k ≤ n + 2 ∧ n ≤ k + 2 ∧ 0 ≤ k ∧ 0 ≤ n].
      Avl (a, k) → a → Avl (a, n) → ∃i[i=max (k + 1, n + 1) ∧
       0 ≤ i].Avl (a, i)
external rotr :
  ∀n, a. Avl (a, n+3) → a → Avl (a, n) →
       ∃i[n+3 ≤ i ∧ i ≤ n+4].Avl (a, i)
external rotl :
  ∀n, a. Avl (a, n) → a → Avl (a, n+3) →
       ∃i[n+3 ≤ i ∧ i ≤ n+4].Avl (a, i)
external min_binding : ∀n, a [1 ≤ n]. Avl (a, n) → a
external remove_min_binding :
  ∀n, a [1 ≤ n]. Avl (a, n) →
    ∃k[k + 2 ≤ 2 n ∧ n ≤ k + 1 ∧ k ≤ n].Avl (a, k)
  

let merge = efunction
  | Empty, Empty -> Empty
  | Empty, (Node (_,_,_,_) as t) -> t
  | (Node (_,_,_,_) as t), Empty -> t
  | (Node (_,_,_,_) as t1), (Node (_,_,_,_) as t2) ->
    let x = min_binding t2 in
    let t2' = remove_min_binding t2 in
    (ematch height t1, height t2' with
     | ht1, ht2' when ht1 <= ht2'+2 && ht2' <= ht1+2 -> create t1 x t2'
     | ht1, ht2' when ht2'+3 <= ht1 -> rotr t1 x t2'
     | ht1, ht2' when ht1+3 <= ht2' -> assert false)
"
        [2,"∃n, k, a.
  δ =
    ((Avl (a, n), Avl (a, k)) → ∃i[i ≤ n + k ∧ k ≤ i ∧
       n ≤ i ∧ i≤max (k + 1, n + 1)].Avl (a, i)) ∧
  n ≤ k + 2 ∧ k ≤ n + 2"];
    );

  "avl_tree--remove-simple" >::
    (fun () ->
       skip_if !debug "debug";
       test_case ~no_num_abduction:true "avl_tree--remove"
"datatype Avl : type * num
datacons Empty : ∀a. Avl (a, 0)
datacons Node :
  ∀a,k,m,n [k=max(m,n) ∧ 0≤m ∧ 0≤n ∧ n≤m+2 ∧ m≤n+2].
     Avl (a, m) * a * Avl (a, n) * Num (k+1) ⟶ Avl (a, k+1)
datatype LinOrder
datacons LT : LinOrder
datacons EQ : LinOrder
datacons GT : LinOrder
external let compare : ∀a. a → a → LinOrder =
  \"fun x y -> let c=Pervasives.compare x y in
              if c<0 then LT else if c=0 then EQ else GT\"

external height : ∀a,n. Avl (a, n) → Num n
external create :
  ∀a,n,k[k ≤ n + 2 ∧ n ≤ k + 2 ∧ 0 ≤ k ∧ 0 ≤ n].
      Avl (a, k) → a → Avl (a, n) → ∃i[i=max (k + 1, n + 1) ∧
       0 ≤ i].Avl (a, i)
external rotr :
  ∀n, a. Avl (a, n+3) → a → Avl (a, n) →
       ∃i[n+3 ≤ i ∧ i ≤ n+4].Avl (a, i)
external rotl :
  ∀n, a. Avl (a, n) → a → Avl (a, n+3) →
       ∃i[n+3 ≤ i ∧ i ≤ n+4].Avl (a, i)
external min_binding : ∀n, a [1 ≤ n]. Avl (a, n) → a
external remove_min_binding :
  ∀n, a [1 ≤ n]. Avl (a, n) →
    ∃k[k + 2 ≤ 2 n ∧ n ≤ k + 1 ∧ k ≤ n].Avl (a, k)
external merge :
  ∀n, k, a [n ≤ k + 2 ∧ k ≤ n + 2].
    (Avl (a, n), Avl (a, k)) → ∃i[i ≤ n + k ∧ k ≤ i ∧
       n ≤ i ∧ i≤max (k + 1, n + 1)].Avl (a, i)
  
  
let rec remove = fun x -> efunction
  | Empty -> Empty
  | Node (l, y, r, h) ->
    ematch compare x y with
    | EQ -> merge (l, r)
    | LT ->
      let l' = remove x l in
      (ematch height l', height r with
       | hl', hr when hl' <= hr+2 && hr <= hl'+2 -> create l' y r
       | hl', hr when hl'+3 <= hr -> rotl l' y r)
    | GT ->
      let r' = remove x r in
      (ematch height l, height r' with
       | hl, hr' when hl <= hr'+2 && hr' <= hl+2 -> create l y r'
       | hl, hr' when hr'+3 <= hl -> rotr l y r')
"
        [2,"∃n, a.
  δ =
    (a → Avl (a, n) → ∃k[0 ≤ k ∧ n ≤ k + 1 ∧
       k ≤ n].Avl (a, k))"];
    );

  "avl_tree--remove" >::
    (fun () ->
       skip_if !debug "debug";
       test_case "avl_tree--remove_min_binding"
"datatype Avl : type * num
datacons Empty : ∀a. Avl (a, 0)
datacons Node :
  ∀a,k,m,n [k=max(m,n) ∧ 0≤m ∧ 0≤n ∧ n≤m+2 ∧ m≤n+2].
     Avl (a, m) * a * Avl (a, n) * Num (k+1) ⟶ Avl (a, k+1)
datatype LinOrder
datacons LT : LinOrder
datacons EQ : LinOrder
datacons GT : LinOrder
external let compare : ∀a. a → a → LinOrder =
  \"fun x y -> let c=Pervasives.compare x y in
              if c<0 then LT else if c=0 then EQ else GT\"

external height : ∀a,n. Avl (a, n) → Num n
external create :
  ∀a,n,k[k ≤ n + 2 ∧ n ≤ k + 2 ∧ 0 ≤ k ∧ 0 ≤ n].
      Avl (a, k) → a → Avl (a, n) → ∃i[i=max (k + 1, n + 1) ∧
       0 ≤ i].Avl (a, i)
external rotr :
  ∀n, a. Avl (a, n+3) → a → Avl (a, n) →
       ∃i[n+3 ≤ i ∧ i ≤ n+4].Avl (a, i)
external rotl :
  ∀n, a. Avl (a, n) → a → Avl (a, n+3) →
       ∃i[n+3 ≤ i ∧ i ≤ n+4].Avl (a, i)
external min_binding : ∀n, a [1 ≤ n]. Avl (a, n) → a
external remove_min_binding :
  ∀n, a [1 ≤ n]. Avl (a, n) →
    ∃k[k + 2 ≤ 2 n ∧ n ≤ k + 1 ∧ k ≤ n].Avl (a, k)
external merge :
  ∀n, k, a [n ≤ k + 2 ∧ k ≤ n + 2].
    (Avl (a, n), Avl (a, k)) → ∃i[i ≤ n + k ∧ k ≤ i ∧
       n ≤ i ∧ i≤max (k + 1, n + 1)].Avl (a, i)
  
  
let rec remove = fun x -> efunction
  | Empty -> Empty
  | Node (l, y, r, h) ->
    ematch compare x y with
    | EQ -> merge (l, r)
    | LT ->
      let l' = remove x l in
      (ematch height l', height r with
       | hl', hr when hl' <= hr+2 && hr <= hl'+2 -> create l' y r
       | hl', hr when hl'+3 <= hr -> rotl l' y r)
    | GT ->
      let r' = remove x r in
      (ematch height l, height r' with
       | hl, hr' when hl <= hr'+2 && hr' <= hl+2 -> create l y r'
       | hl, hr' when hr'+3 <= hl -> rotr l y r')
"
        [2,"∃n, a.
  δ =
    (a → Avl (a, n) → ∃k[0 ≤ k ∧ n ≤ k + 1 ∧
       k ≤ n].Avl (a, k))"];
    );


]

let () =
  let executable = Filename.basename Sys.executable_name in
  let chop f =
    try Filename.chop_extension f with Invalid_argument _ -> f in
  let executable = chop (chop executable) in
  if executable = "InvariantsTest"
  then ignore (OUnit.run_test_tt ~verbose:true tests)
