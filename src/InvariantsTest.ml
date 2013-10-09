(** Solving second-order i.e. formula variables tests for InvarGenT.

    Released under the GNU General Public Licence (version 2 or
    higher), NO WARRANTY of correctness etc. (C) Lukasz Stafiniak 2013
    @author Lukasz Stafiniak lukstafi (AT) gmail.com
    @since Mar 2013
*)
open OUnit
open Terms
open Aux

let debug = ref true

let test_case ?(more_general=false) msg test answers =
      Terms.reset_state ();
      Infer.reset_state ();
      let prog = (Infer.normalize_program % Parser.program Lexer.token)
	(Lexing.from_string test) in
      try
        let preserve, cn = Infer.infer_prog_mockup prog in
        Format.printf "cn: %s@\n%a@\n%!" msg Infer.pr_cnstrnt cn; (* *)
        let cmp_v, uni_v, brs = Infer.normalize cn in
        Format.printf "brs: %s@\n%a@\n%!" msg Infer.pr_brs brs; (* *)
        let uni_v v =
          try Hashtbl.find uni_v v with Not_found -> false in
        let pruned = Infer.prune_cn cn in
        Format.printf "pruned_cn: %s@\n%a@\n%!"
          msg Infer.pr_cnstrnt pruned; (* *)
        let brs = Infer.simplify preserve cmp_v uni_v brs in
        Format.printf "simpl-brs: %s@\n%a@\nex_types:@\n%!"
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
        (* *)
        Abduction.more_general := more_general;
        let _, _, (res, rol, sol) =
          Invariants.solve cmp_v uni_v brs in
        List.iter
          (fun (i,loc) ->
            let (allvs, phi, ty, n, pvs) =
              Hashtbl.find sigma (Extype i) in
            let ty = match ty with [ty] -> ty | _ -> assert false in
            Format.printf "so∃%d: pvs=%a@ allvs=%a@ t=%a@ phi=%a@\n%!"
              i pr_vars (vars_of_list pvs) pr_vars (vars_of_list allvs)
              (pr_ty false) ty pr_formula phi)
          !all_ex_types;
        (* *)
        let test_sol (chi, result) =
          let vs, ans = List.assoc chi sol in
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

        [1, "∃t43. δ = (Term t43 → t43)"]
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

        [1, "∃t94. δ = (Term t94 → t94)"]
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
        [1, "∃t106, t107. δ = (Ty t106, Ty t107 → t107 → t107 → Bool)"]
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
        [1, "∃t201, t202. δ = (Ty t201, Ty t202 → t201 → t202 → Bool)"]
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
        [1, "∃t264, t265. δ = (Ty t264, Ty t265 → t264 → t265 → Bool)"]
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
        [1, "∃t231, t232. δ = (Ty t231, Ty t232 → t231 → t232 → Bool)"]
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
        [1,"∃n263, n264, n265, n266.
  δ = (Carry n266 → Binary n265 → Binary n264 → Binary n263) ∧
  n263 = (n266 + n265 + n264)"]
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
        [1,"∃n285, n286, n287, n288.
  δ = (Carry n288 → Binary n287 → Binary n286 → Binary n285) ∧
  n285 = (n288 + n287 + n286)"]
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
        [1,"∃n41, n42, t44. δ = (List ((t44, t44), n42) → List (t44, n41)) ∧
  n41 = (n42 + n42)"];
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
        [1,"∃t35. δ = (Placement t35 → Outside)"]

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
        [1,"∃t63, t65. δ = (Place t63 → Place t65 → Nearby (t63, t65))"];
    );

  "equational nested universal" >::
    (fun () ->
      skip_if !debug "debug";
      test_case "less nested universal"
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
        [1,"∃t74, t75. δ = (Place t75 → Place t74 → Nearby (t75, t74))"];
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
        [1,"∃t89, t91. δ = (Place t89 → Place t91 → Nearby (t89, t91))"];
    );

  "find castle" >::
    (fun () ->
       (* skip_if !debug "debug"; *)
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

let rec find_castle = efunction
  | CastleRoom x -> Room x
  | CastleYard x -> Yard x
  | Village _ as x ->
    let y = wander x in
    find_castle y"
        [1,"∃t51, t52. δ = (Placement t52 → ∃2:t40[].Castle t40)"];

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
        [1,"∃t78, t79. δ = (Placement t79 → ∃2:t61[].Castle t61)"];
    );

  "search castle shortcut" >::
    (fun () ->
      (* skip_if !debug "debug"; *)
       todo "existential";
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
        [1,"∃t67, t68. δ = (Placement t68 → ∃3:t88[].Castle t88)"];
    );

  "search castle distance" >::
    (fun () ->
      todo "existential";
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
        [1,"∃t81, t82. δ = (Placement t82 → ∃3:t65[].Castle t65)"];
    );

  "search castle distance A/B" >::
    (fun () ->
      todo "existential";
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
        [1,"∃t214, t215. δ = (Placement t215 → ∃4:t216[].Castle t216)"];
    );

  "castle not existential" >::
    (fun () ->
       (* skip_if !debug "debug"; *)
       todo "existential";
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
        [1,"∃t56, t57. δ = (Placement t57 → ∃2:[].Castle Yard)"];
    );

  "castle nested not existential" >::
    (fun () ->
       (* skip_if !debug "debug"; *)
       todo "existential";
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
        [1,"∃t74, t75. δ = (Placement t75 → ∃3:[].Castle Yard)"];
    );

  "castle nested existential factored" >::
    (fun () ->
       (* skip_if !debug "debug"; *)
       todo "existential";
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
        [1,"∃t90, t91. δ = (Placement t91 → ∃3:t107[].Castle t107)"];
    );

  "castle nested existential" >::
    (fun () ->
       (* skip_if !debug "debug"; *)
       todo "existential";
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
        [1,"∃t99, t100. δ = (Placement t100 → ∃3:t87[].Castle t87)"];
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
        [1,"∃t70. δ = (Place t70 → Near t70)"];
    );

  "existential with param" >::
    (fun () ->
       todo "existential";
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
        [1,"∃t1. δ = (Place t1 → ∃3:t2[].Nearby (t1,t2)"];
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
    | LCons (x, xs) ->
      ematch f x with
        | True ->
          let ys = filter xs in
          LCons (x, ys)
	| False ->
          filter xs"
        [1,""];

    );

  "poly filter" >::
    (fun () ->
      todo "existential";
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
        [1,""];

    );


]
