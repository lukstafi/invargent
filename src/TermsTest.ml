(** Data structures, parsing and printing tests for InvarGenT.

    Released under the GNU General Public Licence (version 2 or
    higher), NO WARRANTY of correctness etc. (C) Lukasz Stafiniak 2013
    @author Lukasz Stafiniak lukstafi (AT) gmail.com
    @since Mar 2013
*)
open OUnit
open Terms

let tests = "Terms" >::: [
  "parsing and printing" >::
    (fun () ->
      extype_id := 0;
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
      ignore (Format.flush_str_formatter ());
      pr_program Format.str_formatter prog;

      assert_equal ~printer:(fun x -> x)
"newtype Term : type

newtype Int

newtype Bool

external plus : Int → Int → Int

external is_zero : Int → Bool

external if : ∀a. Bool → a → a → a

newcons Lit : ∀a[Int = a].Int ⟶ Term a

newcons Plus : ∀a[Int = a].Term Int * Term Int ⟶ Term a

newcons IsZero : ∀a[Bool = a].Term Int ⟶ Term a

newcons If : ∀a.Term Bool * Term a * Term a ⟶ Term a

newcons Pair : ∀a, a, b[(a, b) = a].Term a * Term b ⟶ Term a

newcons Fst : ∀a, b.Term (a, b) ⟶ Term a

newcons Snd : ∀a, b.Term (a, b) ⟶ Term b

let rec eval =
   function Lit i -> i | IsZero x -> is_zero (eval x)
   | Plus (x, y) -> plus (eval x) (eval y)
   | If (b, t, e) -> if (eval b) (eval t) (eval e)
   | Pair (x, y) -> eval x, eval y | Fst p -> let x, y = eval p in x
   | Snd p -> let x, y = eval p in y"
        (Format.flush_str_formatter ());
    );

  "parsing existentials" >::
    (fun () ->
      extype_id := 0;
      let prog = Parser.program Lexer.token
	(Lexing.from_string
"newtype List : type * num
newcons LNil : all a. List(a, 0)
newcons LCons : ∀n, a. a * List(a, n) ⟶ List(a, n+1)
external filter : ∀n, a. List (a, n) → ∃k [k≤n]. List (a, k)") in
      let prog = infer_sorts prog in
      ignore (Format.flush_str_formatter ());
      pr_program Format.str_formatter prog;

      assert_equal ~printer:(fun x -> x)
"newtype List : type * num

newcons LNil : ∀a. List (a, 0)

newcons LCons : ∀n, a.a * List (a, n) ⟶ List (a, n + 1)

newtype Ex1 : type * num

newcons Ex1 : ∀a, k, n[k ≤ n].List (a, k) ⟶ Ex1 (a, n)

external filter : ∀n * a. List (a, n) → Ex1 (a, n)"
        (Format.flush_str_formatter ());
    );

  "sort inference" >::
    (fun () ->
      let prog = Parser.program Lexer.token
	(Lexing.from_string
"newtype N : num
newtype T : type
external foo : ∀a,b. T a → N b → a") in
      let prog = infer_sorts prog in
      assert_equal ~msg:"a in ∀a,b. T a → N b → a" ~printer:sort_str
        Type_sort (match List.rev prog with
        | PrimVal (_, ([v1;v2], _, _), _) :: _ -> var_sort v1
        | _ -> assert false);
      assert_equal ~msg:"b in ∀a,b. T a → N b → a" ~printer:sort_str
        Num_sort (match List.rev prog with
        | PrimVal (_, ([v1;v2], _, _), _) :: _ -> var_sort v2
        | _ -> assert false);
    );

]

