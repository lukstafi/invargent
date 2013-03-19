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
        (Format.flush_str_formatter ())
"newtype Term : type

newtype Int

newtype Bool

external plus : Int → Int → Int

external is_zero : Int → Bool

external if : ∀a. Bool → a → a → a

newcons Lit : Int ⟶ Term Int

newcons Plus : Term Int * Term Int ⟶ Term Int

newcons IsZero : Term Int ⟶ Term Bool

newcons If : ∀a.Term Bool * Term a * Term a ⟶ Term a

newcons Pair : ∀a, b.Term a * Term b ⟶ Term (a, b)

newcons Fst : ∀a, b.Term (a, b) ⟶ Term a

newcons Snd : ∀a, b.Term (a, b) ⟶ Term b

let rec eval =
   function Lit i -> i | IsZero x -> is_zero (eval x)
   | Plus (x, y) -> plus (eval x) (eval y)
   | If (b, t, e) -> if (eval b) (eval t) (eval e)
   | Pair (x, y) -> eval x, eval y | Fst p -> let x, y = eval p in x
   | Snd p -> let x, y = eval p in y";
    );

  "sort inference" >::
    (fun () ->
      let prog = Parser.program Lexer.token
	(Lexing.from_string
"newtype N : num
newtype T : type
external test : ∀a,b. T a → N b → a") in
      assert_equal ~msg:"a in ∀a,b. T a → N b → a" ~printer:sort_str
        (match List.rev prog with
        | PrimVal (_, ([s1,_;s2,_], _, _), _) :: _ -> s1
        | _ -> assert false) Type_sort;
      assert_equal ~msg:"b in ∀a,b. T a → N b → a" ~printer:sort_str
        (match List.rev prog with
        | PrimVal (_, ([s1,_;s2,_], _, _), _) :: _ -> s2
        | _ -> assert false) Num_sort;
    );

]

