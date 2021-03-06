(** Data structures, parsing and printing tests for InvarGenT.

    Released under the GNU General Public Licence (version 2 or
    higher), NO WARRANTY of correctness etc. (C) Lukasz Stafiniak 2013
    @author Lukasz Stafiniak lukstafi (AT) gmail.com
    @since Mar 2013
*)
open OUnit
open Defs
open NumDefs
open Terms

let tests = "Terms" >::: [
  "parsing and printing" >::
    (fun () ->
      extype_id := 0;
      let prog = Parser.program Lexer.token
	(Lexing.from_string
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
  | Snd p -> (match eval p with x, y -> y)") in
      ignore (Format.flush_str_formatter ());
      pr_program Format.str_formatter prog;

      assert_equal ~printer:(fun x -> x)
"datatype Term : type

external let plus : Int → Int → Int = \"(+)\"

external let is_zero : Int → Bool = \"(=) 0\"

datacons Lit : ∀a[Int = a].Int ⟶ Term a

datacons Plus : ∀a[Int = a].Term Int * Term Int ⟶ Term a

datacons IsZero : ∀a[Bool = a].Term Int ⟶ Term a

datacons If : ∀a.Term Bool * Term a * Term a ⟶ Term a

datacons Pair : ∀a, b, c[((a, b)) = c].Term a * Term b ⟶ Term c

datacons Fst : ∀a, b.Term ((a, b)) ⟶ Term a

datacons Snd : ∀a, b.Term ((a, b)) ⟶ Term b

let rec eval =
   (function Lit i -> i | IsZero x -> is_zero (eval x)
     | Plus (x, y) -> plus (eval x) (eval y)
     | If (b, t, e) -> (match eval b with True -> eval t | False -> eval e)
     | Pair (x, y) -> (eval x, eval y) | Fst p -> let (x, y) = eval p in x
     | Snd p -> let (x, y) = eval p in y)"
        (Format.flush_str_formatter ());
    );

  "parsing existentials" >::
    (fun () ->
      extype_id := 0;
      let prog = Parser.program Lexer.token
	(Lexing.from_string
"datatype List : type * num
datacons LNil : all a. List(a, 0)
datacons LCons : ∀n, a. a * List(a, n) ⟶ List(a, n+1)
external filter : ∀n, a. List (a, n) → ∃k [k≤n]. List (a, k) = \"filter\"") in
      ignore (Format.flush_str_formatter ());
      pr_program Format.str_formatter prog;

      assert_equal ~printer:(fun x -> x)
"datatype List : type * num

datacons LNil : ∀n, a[0 = n]. List (a, n)

datacons LCons : ∀k, n, a[n + 1 = k].a * List (a, n) ⟶ List (a, k)

external filter : ∀n, a. List (a, n) → ∃k[k ≤ n].List (a, k) =
   \"filter\""
        (Format.flush_str_formatter ());
    );

  "zipper" >::
    (fun () ->
      let t = TCons (CNam "f", [TVar (VNam (Type_sort, "x"));
                                num (Add [Cst (1,1); Cst (2,1)])]) in
      let loc1 = Aux.unsome
        (Aux.bind_opt (typ_up {typ_sub=t; typ_ctx=[]}) typ_next) in
      assert_equal ~msg:"next (up `f (x, 1+2)`)"
        ~printer:(pr_to_str pr_typ_loc)
        {typ_sub=num (Add [Cst (1,1); Cst (2,1)]);
         typ_ctx=[TCons_dir (CNam "f", [TVar (VNam (Type_sort, "x"))],
                             [])]}
        loc1;
    );


]

