(** Solving second-order i.e. formula variables tests for InvarGenT.

    Released under the GNU General Public Licence (version 2 or
    higher), NO WARRANTY of correctness etc. (C) Lukasz Stafiniak 2013
    @author Lukasz Stafiniak lukstafi (AT) gmail.com
    @since Mar 2013
*)
open OUnit
open Terms
open Aux

let debug = ref false(* true *)

let test_common more_general msg test =
  let ntime = Sys.time () in
  Terms.reset_state ();
  Infer.reset_state ();
  let prog = (Infer.normalize_program % Parser.program Lexer.token)
      (Lexing.from_string test) in
  let preserve, orig_cn = Infer.infer_prog_mockup prog in
  (* Format.printf "orig_cn: %s@\n%a@\n%!" msg
    Infer.pr_cnstrnt orig_cn; * *)
  let q_ops, cn = Infer.prenexize orig_cn in
  let exty_res_of_chi, brs = Infer.normalize q_ops cn in
  (* Format.printf "brs: %s@\n%a@\n%!" msg Infer.pr_brs brs; * *)
  let brs = Infer.simplify preserve q_ops brs in
  (* Format.printf "simpl-brs: %s@\n%a@\nex_types:@\n%!"
    msg Infer.pr_brs brs;
  List.iter
    (fun (i,loc) ->
       let (allvs, phi, ty, n, pvs) =
         Hashtbl.find sigma (Extype i) in
       let ty = match ty with [ty] -> ty | _ -> assert false in
       Format.printf "∃%d: pvs=%a@ allvs=%a@ t=%a@ phi=%a@\n%!"
         i pr_vars (vars_of_list pvs) pr_vars (vars_of_list allvs)
         (pr_ty false) ty pr_formula phi)
    !all_ex_types;
  * *)
  Abduction.more_general := more_general;
  let _, res, sol =
    Invariants.solve q_ops exty_res_of_chi brs in
  (* Format.printf
    "Test: res=@\n%a@\n%!" pr_formula res;
  List.iter
    (fun (i,loc) ->
       let (allvs, phi, ty, n, pvs) =
         Hashtbl.find sigma (Extype i) in
       let ty = match ty with [ty] -> ty | _ -> assert false in
       Format.printf "so∃%d: pvs=%a@ allvs=%a@ t=%a@ phi=%a@\n%!"
         i pr_vars (vars_of_list pvs) pr_vars (vars_of_list allvs)
         (pr_ty false) ty pr_formula phi)
    !all_ex_types;
  * *)
  Format.printf " t=%.3fs " (Sys.time () -. ntime);
  q_ops, res, sol

let test_case ?(more_general=false) msg test answers =
  try
    let q, res, sol = test_common more_general msg test in
    let test_sol (chi, result) =
      let vs, ans = nice_ans (List.assoc chi sol) in
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

let test_nonrec_case ?(more_general=false) msg test answers =
  try
    let q, res, sol = test_common more_general msg test in
    let test_sol (v, result) =
      let res_sb, _ = Infer.separate_subst q res in
      let ty = fst (List.assoc (VId (Type_sort, v)) res_sb) in
      ignore (Format.flush_str_formatter ());
      Format.fprintf Format.str_formatter "%a" (pr_ty false) ty;
      assert_equal ~printer:(fun x -> x)
        result
        (Format.flush_str_formatter ()) in
    List.iter test_sol answers
  with (Terms.Report_toplevel _ | Terms.Contradiction _) as exn ->
    ignore (Format.flush_str_formatter ());
    Terms.pr_exception Format.str_formatter exn;
    assert_failure (Format.flush_str_formatter ())

let tests = "Invariants" >::: [

  "simple eval" >::
    (fun () ->
      skip_if !debug "debug";
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

let rec eval = function
  | Lit i -> i
  | IsZero x -> is_zero (eval x)
  | Plus (x, y) -> plus (eval x) (eval y)
  | If (b, t, e) -> if (eval b) (eval t) (eval e)"

        [1, "∃a. δ = (Term a → a)"]
    );

  "eval" >::
    (fun () ->
       skip_if !debug "debug";
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

        [1, "∃a. δ = (Term a → a)"]
    );

  "equal1 wrong type" >::
    (fun () ->
       skip_if !debug "debug";
       test_case "equal1 wrong type"
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
        [1, "∃a, b. δ = ((Ty a, Ty b) → a → b → Bool)"]
    );

  "equal with assert" >::
    (fun () ->
       skip_if !debug "debug";
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
        [1, "∃a, b. δ = ((Ty a, Ty b) → a → b → Bool)"]
    );

  "equal with assert and test" >::
    (fun () ->
       skip_if !debug "debug";
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
        [1, "∃a, b. δ = ((Ty a, Ty b) → a → b → Bool)"]
    );

  "binary plus" >::
    (fun () ->
       skip_if !debug "debug";
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
        [1,"∃n, k, i, j. δ = (Carry j → Binary i → Binary k → Binary n) ∧
  n = (j + i + k)"]
    );

  "binary plus with test" >::
    (fun () ->
       skip_if !debug "debug";
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
        [1,"∃n, k, i, j. δ = (Carry j → Binary i → Binary k → Binary n) ∧
  n = (j + i + k)"]
    );

  "flatten_pairs" >::
    (fun () ->
       skip_if !debug "debug";
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
        [1,"∃n, k, a. δ = (List ((a, a), k) → List (a, n)) ∧ n = (k + k)"];
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
"newtype Place : type
newtype Nearby : type * type
newcons Transitive : ∀a,b,c. Nearby (a, b) * Nearby (b, c) ⟶ Nearby (a, c)
external wander : ∀a. Place a → ∃b. (Place b, Nearby (a, b))
newtype Meet : type * type
newcons Close : ∀a,b. Nearby (a, b) ⟶ Meet (a, b)
newcons NotClose : ∀a, b. Meet (a, b)
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
"newtype Place : type
newtype Nearby : type * type
newtype A
newtype B
newcons LocA : Place A
newcons LocB : Place B
newtype Bool
external is_nearby : ∀a,b. Nearby (a, b) → Bool
newcons Here : ∀a. Place a * Place a ⟶ Nearby (a, a)
newcons Transitive : ∀a,b,c. Nearby (a, b) * Nearby (b, c) ⟶ Nearby (a, c)
external wander : ∀a. Place a → ∃b. (Place b, Nearby (a, b))
newtype Meet : type * type
newcons Same : ∀a,b [a=b]. Meet (a, b)
newcons NotSame : ∀a, b. Meet (a, b)
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
"newtype Place : type
newtype Nearby : type * type
newtype A
newtype B
newcons LocA : Place A
newcons LocB : Place B
newtype Bool
external is_nearby : ∀a,b. Nearby (a, b) → Bool
newcons Transitive : ∀a,b,c. Nearby (a, b) * Nearby (b, c) ⟶ Nearby (a, c)
external wander : ∀a. Place a → ∃b. (Place b, Nearby (a, b))
newtype Meet : type * type
newcons Close : ∀a,b. Nearby (a, b) ⟶ Meet (a, b)
newcons NotClose : ∀a, b. Meet (a, b)
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

let rec find_castle = efunction
  | CastleRoom x -> Room x
  | CastleYard x -> Yard x
  | Village _ as x ->
    let y = wander x in
    find_castle y"
        [2,"∃a. δ = (Placement a → ∃2:a[].Castle a)"];
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
        [2,"∃a. δ = (Placement a → ∃2:a[].Castle a)"];
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

external wander : ∀a. Placement a → ∃b. Placement b
external check : ∀a. Placement a → Explore

let rec search = efunction
  | CastleRoom x -> Room x
  | Village _ as x ->
    let y = wander x in
    ematch check y with
    | Ordinary -> search y
    | Shortcut z -> Yard z"
        [2,"∃a. δ = (Placement a → ∃3:a[].Castle a)"];
    );

  "search castle distance" >::
    (fun () ->
       skip_if !debug "debug";
       test_case "find castle distance"
"newtype Bool
newcons True : Bool
newcons False : Bool
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
        [2,"∃a. δ = (Placement a → ∃3:a[].Castle a)"];
    );

  "search castle distance A/B" >::
    (fun () ->
       skip_if !debug "debug";
       test_case "find castle distance A/B"
"newtype Bool : type
newtype A
newtype B
newcons True : Bool A
newcons False : Bool B
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

external wander : ∀a. Placement a → ∃b. Placement b
external closer : ∀a. Placement a → ∃b. Bool b

let rec search = efunction
  | CastleRoom x -> Room x
  | CastleYard x -> Yard x
  | Village _ as x ->
    let y = wander x in
    let b = closer y in
    ematch b with
    | True -> search y
    | False -> search x"
        [2,"∃a. δ = (Placement a → ∃4:a[].Castle a)"];
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

external wander : Village → ∃b. Placement b

let rec search = efunction
  | CastleYard x -> Yard x
  | Village x ->
    let y = wander x in
    search y"
        [2,"∃a. δ = (Placement a → ∃2:[].Castle Yard)"];
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
        [2,"∃a. δ = (Placement a → ∃3:[].Castle Yard)"];
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
        [2,"∃a. δ = (Placement a → ∃3:a[].Castle a)"];
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
        [2,"∃a. δ = (Placement a → ∃3:a[].Castle a)"];
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
external wander : ∀a. Place a → ∃b. (Place b, Nearby (a, b))
newtype Bool
newcons True : Bool
newcons False : Bool
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
       test_case "existential with param"
"newtype Place : type
newtype Nearby : type * type
newcons Here : ∀a. Place a ⟶ Nearby (a, a)
newcons Transitive : ∀a,b,c. Nearby (a, b) * Nearby (b, c) ⟶ Nearby (a, c)
external wander : ∀a. Place a → ∃b. (Place b, Nearby (a, b))
newtype Bool
newcons True : Bool
newcons False : Bool
external finish : ∀a. Place a → Bool
let rec walk = fun x ->
  ematch finish x with
  | True -> Here x
  | False ->
    let y, to_y = wander x in
    let to_z = walk y in
    Transitive (to_y, to_z)"
        [2,"∃a. δ = (Place a → ∃2:b[].Nearby (a, b))"];
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
        [2,"∃a, b. δ = ((a → b) → List a → ∃1:[].List b)"];
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

external f : Foo → Bar

let rec map =
  efunction LNil -> LNil
    | LCons (x, xs) ->
      let ys = map xs in
      LCons (f x, ys)"
        [2,"∃. δ = (List Foo → ∃1:[].List Bar)"];
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
        [2,"∃n, a, b. δ = ((a → b) → List (a, n) → ∃1:[].List (b, n))"];
    );

  "non-num map universal mono" >::
    (fun () ->
       skip_if !debug "debug";
       test_case "list map not existential mono"
"newtype List : type
newcons LNil : ∀a. List a
newcons LCons : ∀a. a * List a ⟶ List a
newtype Foo
newtype Bar

external f : Foo → Bar

let rec map =
  function LNil -> LNil
    | LCons (x, xs) ->
      let ys = map xs in
      LCons (f x, ys)"
        [1,"∃. δ = (List Foo → List Bar)"];
    );

  "non-num map not existential mono" >::
    (fun () ->
       skip_if !debug "debug";
       test_case "list map not existential mono"
"newtype List : type
newcons LNil : ∀a. List a
newcons LCons : ∀a. a * List a ⟶ List a
newtype Foo
newtype Bar

external f : Foo → Bar

let rec map =
  efunction LNil -> LNil
    | LCons (x, xs) ->
      let ys = map xs in
      LCons (f x, ys)"
        [2,"∃. δ = (List Foo → ∃1:[].List Bar)"];
    );

  "map not existential mono" >::
    (fun () ->
       skip_if !debug "debug";
       test_case "list map not existential mono"
"newtype List : type * num
newcons LNil : ∀a. List(a, 0)
newcons LCons : ∀n, a [0≤n]. a * List(a, n) ⟶ List(a, n+1)
newtype Foo
newtype Bar

external f : Foo → Bar

let rec map =
  efunction LNil -> LNil
    | LCons (x, xs) ->
      let ys = map xs in
      LCons (f x, ys)"
        [2,"∃n. δ = (List (Foo, n) → ∃1:[].List (Bar, n))"];
    );

  "filter mono" >::
    (fun () ->
       skip_if !debug "debug";
       test_case "monomorphic list filter"
"newtype Bool
newtype Bar
newtype List : num
newcons True : Bool
newcons False : Bool
newcons LNil : List 0
newcons LCons : ∀n [0≤n]. Bar * List n ⟶ List(n+1)
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
        [2,"∃n. δ = (List n → ∃2:k[k ≤ n ∧ 0 ≤ n ∧ 0 ≤ k].List k)"];

    );

  "filter Bar" >::
    (fun () ->
       skip_if !debug "debug";
       test_case "list filter: Bar"
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
    | LCons (x, xs) ->
      ematch f x with
        | True ->
          let ys = filter xs in
          LCons (x, ys)
	| False ->
          filter xs"
        [2,"∃n.
  δ =
    (List (Bar, n) → ∃2:k[k ≤ n ∧ 0 ≤ n ∧ 0 ≤ k].List (Bar, k))"];

    );

  "filter poly" >::
    (fun () ->
       skip_if !debug "debug";
       test_case "polymorphic list filter"
"newtype Bool
newtype List : type * num
newcons True : Bool
newcons False : Bool
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
    ((a → Bool) → List (a, n) → ∃2:k[k ≤ n ∧ 0 ≤ n ∧
       0 ≤ k].List (a, k))"];

    );

  "poly filter map" >::
    (fun () ->
       skip_if !debug "debug";
       test_case "list filter map"
"newtype Bool
newtype List : type * num
newcons True : Bool
newcons False : Bool
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
       0 ≤ n ∧ 0 ≤ k].List (b, k))"];

    );


  "binary upper bound" >::
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
    (Binary k → Binary n → ∃4:i[n ≤ i ∧ k ≤ i ∧
       i ≤ (k + n) ∧ 0 ≤ n ∧ 0 ≤ k].Binary i)"]
    );

  "nested recursion simple eval" >::
    (fun () ->
       skip_if !debug "debug";
       test_case "nested recursion eval with literal numbers only"
"newtype Term : type
newtype Num : num
newtype Calc : num
newtype Bool

external is_zero : ∀i. Num i → Bool
external if : ∀a. Bool → a → a → a

newcons Lit : ∀k. Num k ⟶ Calc k

newcons IsZero : ∀k. Calc k ⟶ Term Bool
newcons If : ∀a. Term Bool * Term a * Term a ⟶ Term a

let rec eval =
  let rec calc =
    function
    | Lit i -> i in
  function
  | IsZero x -> is_zero (calc x)
  | If (b, t, e) -> if (eval b) (eval t) (eval e)"

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
newtype Bool

external plus : ∀i,j. Num i → Num j → Num (i+j)
external is_zero : ∀i. Num i → Bool
external if : ∀a. Bool → a → a → a

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
    | Plus (i, j) -> plus (calc i) (calc j) in
  function
  | IsZero x -> is_zero (calc x)
  | If (b, t, e) -> if (eval b) (eval t) (eval e)
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
newtype Bool

external is_zero : ∀i. Num i → Bool
external cond : ∀i,j. Bool → Num i → Num j → ∃k. Num k
external if : ∀a. Bool → a → a → a

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
  | If (b, t, e) -> if (eval b) (eval t) (eval e)"

        [2, "∃a. δ = (Term a → a)";
        3, "∃. δ = (Calc → ∃2:n[].Num n)"]
    );

  "mutual recursion medium calc" >::
    (fun () ->
       skip_if !debug "debug";
       test_case "mutual recursion universal eval and existential calc"
"newtype Term : type
newtype Num : num
newtype Calc
newtype Bool

external is_zero : ∀i. Num i → Bool
external cond : ∀i,j. Bool → Num i → Num j → ∃k. Num k
external if : ∀a. Bool → a → a → a

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
  | If (b, t, e) -> if (eval b) (eval t) (eval e)
  | Pair (x, y) -> eval x, eval y"

        [2, "∃a. δ = (Term a → a)";
        3, "∃. δ = (Calc → ∃2:n[].Num n)"]
    );

  "mutual recursion calc" >::
    (fun () ->
       skip_if !debug "debug";
       test_case "mutual recursion universal eval and existential calc"
"newtype Term : type
newtype Num : num
newtype Calc
newtype Bool

external plus : ∀i,j. Num i → Num j → Num (i+j)
external mult : ∀i,j. Num i → Num j → ∃k. Num k
external is_zero : ∀i. Num i → Bool
external cond : ∀i,j. Bool → Num i → Num j → ∃k. Num k
external if : ∀a. Bool → a → a → a

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
      plus rx ry
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
  | If (b, t, e) -> if (eval b) (eval t) (eval e)
  | Pair (x, y) -> eval x, eval y
  | Fst p -> (match eval p with x, y -> x)
  | Snd p -> (match eval p with x, y -> y)"

        [2, "∃a. δ = (Term a → a)";
        3, "∃. δ = (Calc → ∃3:n[].Num n)"]
    );

  (* TODO: mutual recursion where the nested function has nontrivial
     postcondition, which needs to be bootstrapped from its
     non-recursive part. *)

  "nonrec simple" >::
    (fun () ->
       skip_if !debug "debug";
       test_nonrec_case "nonrec simple"
"newtype Order : num * num
external compare : ∀i, j. Num i → Num j → Order (i, j)
let cmp7and8 = compare 7 8
"
        [1, "Order (7, 8)"];

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
newtype Bool
newcons True : Bool
newcons False : Bool

newcons Node : ∀a, k [0≤k]. Num k * a * Forest (a, k) ⟶ Tree (a, k)
newcons TCons :
  ∀a, n [0≤n]. Tree (a, n) * Forest (a, n) ⟶ Forest (a, n+1)
newcons TNil : ∀a. Forest (a, 0)

external leq : ∀a. a → a → Bool
external incr : ∀i. Num i → Num (i+1)

let rec link = function
  | (Node (r, x1, c1) as t1), (Node (_, x2, c2) as t2) ->
    match leq x1 x2 with
    | True -> Node (incr r, x1, TCons (t2, c1))
    | False -> Node (incr r, x2, TCons (t1, c2))
"
        [1,"∃n, k, i, a. δ = ((Tree (a, k), Tree (a, i)) → Tree (a, n)) ∧
  n = (1 + k) ∧ n = (1 + i)"];
    );

  "binomial heap--ins_tree" >::
    (fun () ->
       todo "requires `min` and `max`";
       (* [Heap (a, i, j)] is a list of trees of increasing rank,
          starting with rank [i] and finishing with rank [j-1] -- for
          "technical reasons" the singleton heap at the end of
          [Heap (a, i, j)] is [Heap (a, j-1, j)] and the empty heap is
          [Heap (a, j, j)]. *)
       test_case "binomial heap--ins_tree"
"newtype Tree : type * num
newtype Forest : type * num
newtype Heap : type * num * num
newtype Order : num * num
newtype Bool
newcons Le : ∀i, j [i≤j+1]. Order (i, j)
newcons Gt : ∀i, j [j≤i+1]. Order (i, j)
newcons Eq : ∀i. Order (i, i)
newcons True : Bool
newcons False : Bool

newcons Node : ∀a, k [0≤k]. Num k * a * Forest (a, k) ⟶ Tree (a, k)
newcons TCons :
  ∀a, n [0≤n]. Tree (a, n) * Forest (a, n) ⟶ Forest (a, n+1)
newcons TNil : ∀a. Forest (a, 0)
newcons HCons :
  ∀a, k, m, n [0≤k ∧ k+1≤m ∧ m≤n].
    Tree (a, k) * Heap (a, m, n) ⟶ Heap (a, k, n)
newcons HNil : ∀a, n. Heap (a, n, n)

external compare : ∀i, j. Num i → Num j → Order (i, j)
external leq : ∀a. a → a → Bool
external incr : ∀i. Num i → Num (i+1)

external rank : ∀a, n. Tree (a, n) → Num n
external link : ∀a, n. (Tree (a, n), Tree (a, n)) → Tree (a, n+1)

let rec ins_tree = fun t ->
  efunction
  | HNil -> HCons (t, HNil)
  | HCons (t', ts') as ts ->
    ematch compare (rank t) (rank t') with
    | Le -> HCons (t, ts)
    | Eq -> ins_tree (link (t, t')) ts'
    | Gt ->
      let rts = ins_tree t ts' in
      HCons (t', rts)
"
        [1,"∃a, k, m, n.
  δ =
    (Tree (a, k) → Heap (a, m, n) →
            ∃4:i, j[min (i, k, m) ∧ max (j, k, n) ∧ 0 ≤ i ∧ 0 ≤ j].
               Heap (a, i, j))"];
    );

]
