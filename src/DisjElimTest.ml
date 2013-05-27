(** Disjunction elimination tests for InvarGenT.

    Released under the GNU General Public Licence (version 2 or
    higher), NO WARRANTY of correctness etc. (C) Lukasz Stafiniak 2013
    @author Lukasz Stafiniak lukstafi (AT) gmail.com
    @since Mar 2013
*)
open OUnit
open Terms
open Aux

let tests = "DisjElim" >::: [


  "abduction: binary plus" >::
    (fun () ->
      Terms.reset_state ();
      Infer.reset_state ();
      let prog = Parser.program Lexer.token
	(Lexing.from_string
"newtype Binary : num
newtype Carry : num

newcons Zero : Binary 0
newcons PZero : ∀n. Binary(n) ⟶ Binary(n+n)
newcons POne : ∀n. Binary(n) ⟶ Binary(n+n+1)

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
	  | POne b1 -> POne (plus COne a1 b1)))") in
      try
        let prog = Terms.infer_sorts prog in
        let preserve, cn = Infer.infer_prog_mockup prog in
        (* Format.printf "cn:@\n%a@\n" pr_cnstrnt cn; *)
        let cmp_v, uni_v, brs = Infer.normalize cn in
        (*let uni_v v =
          try Hashtbl.find uni_v v with Not_found -> false in*)
        (* FIXME: big problem with quantifiers! *)
        let uni_v v = false in
        let cmp_v v1 v2 = Same_quant in
        let brs = Infer.simplify preserve cmp_v uni_v brs in
        let vs, ans = DisjElim.disjelim cmp_v uni_v
          (List.map (uncurry (@) % Infer.br_to_formulas) brs) in
        ignore (Format.flush_str_formatter ());
        Format.fprintf Format.str_formatter "@[<2>∃%a.@ %a@]"
          (pr_sep_list "," pr_tyvar) vs pr_formula ans;
        assert_equal ~printer:(fun x -> x)
          ""
          (Format.flush_str_formatter ());
      with (Terms.Report_toplevel _ | Terms.Contradiction _) as exn ->
        ignore (Format.flush_str_formatter ());
        Terms.pr_exception Format.str_formatter exn;
        assert_failure (Format.flush_str_formatter ())
    );

  "abduction: filter" >::
    (fun () ->
      Terms.reset_state ();
      Infer.reset_state ();
      let prog = Parser.program Lexer.token
	(Lexing.from_string
"newtype Bool
newtype List : type * num
newcons True : Bool
newcons False : Bool
newcons LNil : ∀a. List(a, 0)
newcons LCons : ∀n, a. a * List(a, n) ⟶ List(a, n+1)

newtype Bar
external f : Bar → Bool

let rec filter =
  efunction LNil -> LNil
    | LCons (x, l) -> match f x with
          True -> LCons (x, filter l)
	| False -> filter l") in
      try
        let prog = Terms.infer_sorts prog in
        let preserve, cn = Infer.infer_prog_mockup prog in
        (* Format.printf "cn:@\n%a@\n" Infer.pr_cnstrnt cn; *)
        let cmp_v, uni_v, brs = Infer.normalize cn in
        (*let uni_v v =
          try Hashtbl.find uni_v v with Not_found -> false in*)
        (* FIXME: big problem with quantifiers! *)
        let uni_v v = false in
        let cmp_v v1 v2 = Same_quant in
        let brs = Infer.simplify preserve cmp_v uni_v brs in
        let vs, ans = DisjElim.disjelim cmp_v uni_v
          (List.map (uncurry (@) % Infer.br_to_formulas) brs) in
        ignore (Format.flush_str_formatter ());
        Format.fprintf Format.str_formatter "@[<2>∃%a.@ %a@]"
          (pr_sep_list "," pr_tyvar) vs pr_formula ans;
        assert_equal ~printer:(fun x -> x)
          ""
          (Format.flush_str_formatter ());
      with (Terms.Report_toplevel _ | Terms.Contradiction _) as exn ->
        ignore (Format.flush_str_formatter ());
        Terms.pr_exception Format.str_formatter exn;
        assert_failure (Format.flush_str_formatter ())
    );

]
