(** Abduction tests for InvarGenT.

    Released under the GNU General Public Licence (version 2 or
    higher), NO WARRANTY of correctness etc. (C) Lukasz Stafiniak 2013
    @author Lukasz Stafiniak lukstafi (AT) gmail.com
    @since Mar 2013
*)
open OUnit
open Terms
open Abduction

let cmp_v v1 v2 = Same_quant
let uni_v v = false

let p_formula s = Parser.formula Lexer.token (Lexing.from_string s)
let br_simple lhs rhs =
  let lhs, _, _ = unify ~use_quants:false cmp_v uni_v lhs in
  let rhs, _, _ = unify ~use_quants:false cmp_v uni_v rhs in
  lhs, rhs

let test_simple lhs_m rhs_m ?(validate=(fun _ _ -> ())) skip res =
  let lhs = p_formula lhs_m and rhs = p_formula rhs_m in
  let lhs, rhs = br_simple lhs rhs in
  let ans =
    match abd_simple cmp_v uni_v validate skip ([],[]) (lhs, rhs) with
    | None -> "none"
    | Some (vs, ans_typ) ->
      pr_to_str pr_formula
        (to_formula ans_typ) in
  assert_equal ~printer:(fun x -> x)
    ~msg:(string_of_int skip^":"^lhs_m^" ⟹ "^rhs_m) res ans

(*  *)
let rhs0 = "tres = (Term tc → tb) ∧ ta = (Term tc)"
let lhs1 = "(Term td) = ta ∧ Int = td" and rhs1 = "tb = Int"
let lhs2 = "(Term te) = ta ∧ Bool = te" and rhs2 = "tb = Bool ∧
    tf = (Term Int → Int)"
let lhs3 = "(Term tg) = ta ∧ Int = tg" and rhs3 = "tb = Int ∧
    ti = (Term Int → Int) ∧ th = (Term Int → Int)"
let lhs4 = "(Term tj) = ta" and rhs4 = "tm = (Term Bool → Bool) ∧
    tl = (Term tj → tb) ∧ tk = (Term tj → tb)"
let lhs5 = "(Term tn) = ta ∧ (to, tp) = tn" and rhs5 = "tb = (tq, tr) ∧
    ts = (Term to → tq) ∧ tt = (Term tp → tr)"
let lhs6 = "(Term tu) = ta" and rhs6 = "tL = (ty, tz) ∧ tx = tb ∧
    tw = (Term (tu, tv) → ty, tz)"
let lhs7 = "(tA, tB) = tL ∧ (Term tu) = ta" and rhs7 = "tA = tx"
let lhs8 = "(Term tD) = ta" and rhs8 = "tF = (tH, tI) ∧ tG = tb ∧
    tE = (Term (tC, tD) → tH, tI)"
let lhs9 = "(tJ, tK) = tF ∧ (Term tD) = ta" and rhs9 = "tK = tG"


let tests = "Abduction" >::: [

  "simple abduction: eval" >::
    (fun () ->
      Terms.reset_state ();
      Infer.reset_state ();
      try
        test_simple lhs1 rhs1 0 "tb = Int";
        test_simple lhs1 rhs1 1 "ta = (Term tb) ∧
td = Int";
        test_simple lhs1 rhs1 2 "ta = (Term tb)"; (* expected *)
      with (Terms.Report_toplevel _ | Terms.Contradiction _) as exn ->
        ignore (Format.flush_str_formatter ());
        Terms.pr_exception Format.str_formatter exn;
        assert_failure (Format.flush_str_formatter ())
    );

  "joint term abduction: eval" >::
    (fun () ->
      Terms.reset_state ();
      Infer.reset_state ();
      try
        let lhs0, rhs0 = [], p_formula rhs0 in
        let lhs1 = p_formula lhs1 and rhs1 = p_formula rhs1 in
        let lhs2 = p_formula lhs2 and rhs2 = p_formula rhs2 in
        let lhs4 = p_formula lhs4 and rhs4 = p_formula rhs4 in
        let lhs5 = p_formula lhs5 and rhs5 = p_formula rhs5 in
        let lhs6 = p_formula lhs6 and rhs6 = p_formula rhs6 in
        let lhs7 = p_formula lhs7 and rhs7 = p_formula rhs7 in
        let lhs8 = p_formula lhs8 and rhs8 = p_formula rhs8 in
        let lhs9 = p_formula lhs9 and rhs9 = p_formula rhs9 in
        let lhs0, rhs0 = br_simple lhs0 rhs0 in
        let lhs1, rhs1 = br_simple lhs1 rhs1 in
        let lhs2, rhs2 = br_simple lhs2 rhs2 in
        let lhs4, rhs4 = br_simple lhs4 rhs4 in
        let lhs5, rhs5 = br_simple lhs5 rhs5 in
        let lhs6, rhs6 = br_simple lhs6 rhs6 in
        let lhs7, rhs7 = br_simple lhs7 rhs7 in
        let lhs8, rhs8 = br_simple lhs8 rhs8 in
        let lhs9, rhs9 = br_simple lhs9 rhs9 in
        let ans =
          match abd_typ cmp_v uni_v
            [lhs0, rhs0; lhs1, rhs1;
             lhs2, rhs2; lhs4, rhs4;
             lhs5, rhs5; lhs6, rhs6;
             lhs7, rhs7; lhs8, rhs8;
             lhs9, rhs9] with
            | None -> "none"
            | Some (vs, ans_typ, _) ->
              pr_to_str pr_formula (to_formula ans_typ) in
        assert_equal ~printer:(fun x -> x)
          "tE = (Term (tC, tD) → tH, tD) ∧ tF = (tH, tD) ∧ tG = tD ∧ tI = tD ∧
tL = (tu, tz) ∧ ta = (Term tc) ∧ tb = tc ∧ te = Bool ∧
tf = (Term Int → Int) ∧ tk = (Term tj → tj) ∧
tl = (Term tj → tj) ∧ tm = (Term Bool → Bool) ∧ tn = (tq, tr) ∧
tres = (Term tc → tc) ∧ ts = (Term tq → tq) ∧
tt = (Term tr → tr) ∧ tw = (Term (tu, tv) → tu, tz) ∧ tx = tu ∧
ty = tu" ans
      with (Terms.Report_toplevel _ | Terms.Contradiction _) as exn ->
        ignore (Format.flush_str_formatter ());
        Terms.pr_exception Format.str_formatter exn;
        assert_failure (Format.flush_str_formatter ())
    );

  "constraint separation: binary plus" >::
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
        let brs = abd_mockup_num cmp_v uni_v
          (List.map Infer.br_to_formulas brs) in
        assert_bool "No abduction answer" (brs <> None);
        let brs = Aux.unsome brs in
        ignore (Format.flush_str_formatter ());
        pr_line_list "| "
          (fun ppf (prem,concl) -> Format.fprintf ppf
            "@[<2>%a@ ⟹@ %a@]" pr_formula prem pr_formula concl)
          Format.str_formatter brs;
        assert_equal ~printer:(fun x -> x)
          " ⟹ 
|  ⟹ 
| 0 = n6 ⟹ n6 = n5
| 0 = n10 ∧ 0 = n6 ⟹ n10 = n9 ∧ n6 = n5
| (n16 + n16) = n15 ∧ 0 = n6 ⟹ n15 = n9 ∧ n6 = n5
| 0 = n20 ∧ (n16 + n16) = n15 ∧ 0 = n6 ⟹ n20 = n19 ∧ n15 = n9 ∧
    n6 = n5 ∧ n19 = n15
| (n24 + n24) = n23 ∧ (n16 + n16) = n15 ∧ 0 = n6 ⟹ n23 = n19 ∧
    n15 = n9 ∧ n6 = n5 ∧ n19 = n25 ∧ (n26 + n26) = n25 ∧ 0 = n30
| (1 + n35 + n35) = n34 ∧ (n16 + n16) = n15 ∧ 0 = n6 ⟹ n34 = n19 ∧
    n15 = n9 ∧ n6 = n5 ∧ n19 = n36 ∧ (1 + n37 + n37) = n36 ∧ 
    0 = n41
| (1 + n46 + n46) = n45 ∧ 0 = n6 ⟹ n45 = n9 ∧ n6 = n5 ∧ n19 = n49
| 0 = n50 ∧ (1 + n46 + n46) = n45 ∧ 0 = n6 ⟹ n50 = n49 ∧ n45 = n9 ∧
    n6 = n5 ∧ n19 = n45
| (n54 + n54) = n53 ∧ (1 + n46 + n46) = n45 ∧ 0 = n6 ⟹ n53 = n49 ∧
    n45 = n9 ∧ n6 = n5 ∧ n19 = n55 ∧ (1 + n56 + n56) = n55 ∧ 
    0 = n60
| (1 + n65 + n65) = n64 ∧ (1 + n46 + n46) = n45 ∧ 0 = n6 ⟹
    n64 = n49 ∧ n45 = n9 ∧ n6 = n5 ∧ n19 = n66 ∧
    (n67 + n67) = n66 ∧ 1 = n71
| 1 = n74 ⟹ n74 = n5 ∧ n9 = n77
| 0 = n78 ∧ 1 = n74 ⟹ n78 = n77 ∧ n74 = n5 ∧ n19 = n81
| 0 = n82 ∧ 0 = n78 ∧ 1 = n74 ⟹ n82 = n81 ∧ n78 = n77 ∧
    n74 = n5 ∧ n19 = n83 ∧ n85 = n84 ∧ (1 + n84 + n84) = n83 ∧
    0 = n85
| (n89 + n89) = n88 ∧ 0 = n78 ∧ 1 = n74 ⟹ n88 = n81 ∧ n78 = n77 ∧
    n74 = n5 ∧ n19 = n90 ∧ n89 = n91 ∧ (1 + n91 + n91) = n90
| (1 + n95 + n95) = n94 ∧ 0 = n78 ∧ 1 = n74 ⟹ n94 = n81 ∧
    n78 = n77 ∧ n74 = n5 ∧ n19 = n96 ∧ (n97 + n97) = n96 ∧
    1 = n102 ∧ 0 = n100
| (n107 + n107) = n106 ∧ 1 = n74 ⟹ n106 = n77 ∧ n74 = n5 ∧ n19 = n110
| 0 = n111 ∧ (n107 + n107) = n106 ∧ 1 = n74 ⟹ n111 = n110 ∧
    n106 = n77 ∧ n74 = n5 ∧ n19 = n112 ∧ n107 = n113 ∧
    (1 + n113 + n113) = n112
| (n117 + n117) = n116 ∧ (n107 + n107) = n106 ∧ 1 = n74 ⟹
    n116 = n110 ∧ n106 = n77 ∧ n74 = n5 ∧ n19 = n118 ∧
    (1 + n119 + n119) = n118 ∧ 0 = n123
| (1 + n128 + n128) = n127 ∧ (n107 + n107) = n106 ∧ 1 = n74 ⟹
    n127 = n110 ∧ n106 = n77 ∧ n74 = n5 ∧ n19 = n129 ∧
    (n130 + n130) = n129 ∧ 1 = n134
| (1 + n139 + n139) = n138 ∧ 1 = n74 ⟹ n138 = n77 ∧ n74 = n5 ∧
    n19 = n142
| 0 = n143 ∧ (1 + n139 + n139) = n138 ∧ 1 = n74 ⟹ n143 = n142 ∧
    n138 = n77 ∧ n74 = n5 ∧ n19 = n144 ∧ (n145 + n145) = n144 ∧
    1 = n150 ∧ 0 = n147
| (n155 + n155) = n154 ∧ (1 + n139 + n139) = n138 ∧ 1 = n74 ⟹
    n154 = n142 ∧ n138 = n77 ∧ n74 = n5 ∧ n19 = n156 ∧
    (n157 + n157) = n156 ∧ 1 = n161
| (1 + n166 + n166) = n165 ∧ (1 + n139 + n139) = n138 ∧ 1 = n74 ⟹
    n165 = n142 ∧ n138 = n77 ∧ n74 = n5 ∧ n19 = n167 ∧
    (1 + n168 + n168) = n167 ∧ 1 = n172"
          (Format.flush_str_formatter ());
      with (Terms.Report_toplevel _ | Terms.Contradiction _) as exn ->
        ignore (Format.flush_str_formatter ());
        Terms.pr_exception Format.str_formatter exn;
        assert_failure (Format.flush_str_formatter ())
    );

  "constraint separation: filter" >::
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
        let brs = abd_mockup_num cmp_v uni_v
          (List.map Infer.br_to_formulas brs) in
        assert_bool "No abduction answer" (brs <> None);
        let brs = Aux.unsome brs in
        ignore (Format.flush_str_formatter ());
        pr_line_list "| "
          (fun ppf (prem,concl) -> Format.fprintf ppf
            "@[<2>%a@ ⟹@ %a@]" pr_formula prem pr_formula concl)
          Format.str_formatter brs;
        assert_equal ~printer:(fun x -> x)
          " ⟹ 
|  ⟹ 
| 0 = n7 ⟹ n7 = n5 ∧ 0 = n10
| (n17 + 1) = n15 ⟹ n15 = n5
| (n17 + 1) = n15 ⟹ n15 = n5 ∧ (n25 + 1) = n23
| (n17 + 1) = n15 ⟹ n15 = n5"
          (Format.flush_str_formatter ());
      with (Terms.Report_toplevel _ | Terms.Contradiction _) as exn ->
        ignore (Format.flush_str_formatter ());
        Terms.pr_exception Format.str_formatter exn;
        assert_failure (Format.flush_str_formatter ())
    );

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
        let ans = abd cmp_v uni_v
          (List.map Infer.br_to_formulas brs) in
        assert_bool "No abduction answer" (ans <> None);
        let vs, ans = Aux.unsome ans in
        ignore (Format.flush_str_formatter ());
        Format.fprintf Format.str_formatter "@[<2>∃%a.@ %a@]"
          (pr_sep_list "," pr_tyvar) vs pr_formula ans;
        assert_equal ~printer:(fun x -> x)
          "∃. t1 = (Carry n5 → Binary n9 → Binary n19 → Binary n19) ∧
  t3 = (Carry n5) ∧ t4 = (Binary n9 → Binary n19 → Binary n19) ∧
  t7 = (Binary n9) ∧ t8 = (Binary n19 → Binary n19) ∧
  t12 = (Binary n19) ∧ t17 = (Binary n19) ∧ t18 = (Binary n19) ∧
  t31 = (Carry n30 → Binary n16 → Binary n24 → Binary n26) ∧
  t42 = (Carry n41 → Binary n16 → Binary n35 → Binary n37) ∧
  t47 = (Binary n49) ∧ t48 = (Binary n19) ∧
  t61 = (Carry n60 → Binary n46 → Binary n54 → Binary n56) ∧
  t72 = (Carry n71 → Binary n46 → Binary n65 → Binary n67) ∧
  t75 = (Binary n77) ∧ t76 = (Binary n19 → Binary n19) ∧
  t79 = (Binary n81) ∧ t80 = (Binary n19) ∧
  t103 = (Carry n102 → Binary n100 → Binary n95 → Binary n97) ∧
  t108 = (Binary n110) ∧ t109 = (Binary n19) ∧
  t124 = (Carry n123 → Binary n107 → Binary n117 → Binary n119) ∧
  t135 = (Carry n134 → Binary n107 → Binary n128 → Binary n130) ∧
  t140 = (Binary n142) ∧ t141 = (Binary n19) ∧
  t151 = (Carry n150 → Binary n139 → Binary n147 → Binary n145) ∧
  t162 = (Carry n161 → Binary n139 → Binary n155 → Binary n157) ∧
  t173 = (Carry n172 → Binary n139 → Binary n166 → Binary n168) ∧
  0 = n172 ∧ (n168 + n168) = n167 ∧ n168 = n157 ∧
  (n166 + n166) = n142 ∧ 0 = n77 ∧ 0 = n5"
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
        let ans = abd cmp_v uni_v
          (List.map Infer.br_to_formulas brs) in
        assert_bool "No abduction answer" (ans <> None);
        let vs, ans = Aux.unsome ans in
        ignore (Format.flush_str_formatter ());
        Format.fprintf Format.str_formatter "@[<2>∃%a.@ %a@]"
          (pr_sep_list "," pr_tyvar) vs pr_formula ans;
        assert_equal ~printer:(fun x -> x)
          "∃. t1 = (List (Bar, n5) → Ex1 t4) ∧ t3 = (List (Bar, n5)) ∧
  t6 = Bar ∧ t9 = (List (t11, n10)) ∧ t18 = (List (Bar, n23)) ∧
  t21 = Bool ∧ t22 = (List (Bar, n23)) ∧
  t27 = (List (Bar, n17) → List (Bar, n25)) ∧
  t29 = (List (Bar, n17) → List (Bar, n23)) ∧ 0 = n17"
          (Format.flush_str_formatter ());
      with (Terms.Report_toplevel _ | Terms.Contradiction _) as exn ->
        ignore (Format.flush_str_formatter ());
        Terms.pr_exception Format.str_formatter exn;
        assert_failure (Format.flush_str_formatter ())
    );

]
