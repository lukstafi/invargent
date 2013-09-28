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

newcons Pair : ∀a, b, c[(a, b) = c].Term a * Term b ⟶ Term c

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
      ignore (Format.flush_str_formatter ());
      pr_program Format.str_formatter prog;

      assert_equal ~printer:(fun x -> x)
"newtype List : type * num

newcons LNil : ∀n, a[0 = n]. List (a, n)

newcons LCons : ∀k, n, a[(n + 1) = k].a * List (a, n) ⟶ List (a, k)

newtype Ex1 : num * type

newcons Ex1 : ∀k, n, a[k ≤ n].List (a, k) ⟶
   ∃1:k[k ≤ n].List (a, k)

external filter : ∀n, a. List (a, n) → ∃1:k[k ≤ n].List (a, k)"
        (Format.flush_str_formatter ());
    );

  "zipper" >::
    (fun () ->
      let t = TCons (CNam "f", [TVar (VNam (Type_sort, "x"));
                                Nadd [NCst 1; NCst 2]]) in
      let loc1 = Aux.unsome
        (Aux.bind_opt (typ_up {typ_sub=t; typ_ctx=[]}) typ_next) in
      let loc2 = Aux.unsome
        (Aux.bind_opt (typ_up loc1) typ_next) in
      assert_equal ~msg:"next (up `f (x, 1+2)`)"
        ~printer:(pr_to_str pr_typ_loc)
        {typ_sub=Nadd [NCst 1; NCst 2];
         typ_ctx=[TCons_dir (CNam "f", [TVar (VNam (Type_sort, "x"))],
                             [])]}
        loc1;
      assert_equal ~msg:"next (up (next (up `f (x, 1+2)`)))"
        ~printer:(pr_to_str pr_typ_loc)
        {typ_sub=NCst 2;
         typ_ctx=[Nadd_dir ([NCst 1], []);
                  TCons_dir (CNam "f", [TVar (VNam (Type_sort, "x"))],
                             [])]}
        loc2;
        ;
    );


]

