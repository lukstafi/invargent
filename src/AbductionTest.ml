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

let test_simple lhs_m rhs_m ?(validate=(fun _ _ _ -> ())) skip res =
  let lhs = p_formula lhs_m and rhs = p_formula rhs_m in
  let lhs, rhs = br_simple lhs rhs in
  let ans =
    match abd_simple cmp_v uni_v
      ~validate ~discard:[] skip ([],[]) (lhs, rhs) with
    | None _ -> "none"
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
        test_simple lhs1 rhs1 1 "tb = td";
        test_simple lhs1 rhs1 2 "ta = (Term tb)";
        test_simple lhs1 rhs1 3 "none";
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
          try let vs, ans_typ, _ = abd_typ cmp_v uni_v
                ~params:VarSet.empty
                ~bparams:[]
                ~zparams:[]
                ~validate:(fun _ _ _ -> ()) ~discard:[]
                [lhs0, rhs0; lhs1, rhs1;
                 lhs2, rhs2; lhs4, rhs4;
                 lhs5, rhs5; lhs6, rhs6;
                 lhs7, rhs7; lhs8, rhs8;
                 lhs9, rhs9] in
              pr_to_str pr_formula (to_formula ans_typ)
          with Suspect _ -> "none" in
        assert_equal ~printer:(fun x -> x) (* te = Bool *)
"tA = tu ∧ tE = (Term (tC, tD) → tH, tI) ∧ tF = (tH, tI) ∧ tG = tD ∧
tK = tD ∧ tL = (ty, tz) ∧ ta = (Term tc) ∧ tb = tc ∧
tf = (Term Int → Int) ∧ tk = (Term tj → tj) ∧
tl = (Term tj → tj) ∧ tm = (Term Bool → Bool) ∧ tq = to ∧
tr = tp ∧ tres = (Term tc → tc) ∧ ts = (Term to → to) ∧
tt = (Term tp → tp) ∧ tw = (Term (tu, tv) → ty, tz) ∧
tx = tu"
(* or  "tE = (Term (tC, tD) → tH, tD) ∧ tF = (tH, tD) ∧ tG = tD ∧ tI = tD ∧
tL = (tu, tz) ∧ ta = (Term tb) ∧ tc = tb ∧ td = Int ∧
tf = (Term Int → Int) ∧ tk = (Term tj → tj) ∧
tl = (Term tj → tj) ∧ tm = (Term Bool → Bool) ∧ tn = (tq, tr) ∧
tres = (Term tb → tb) ∧ ts = (Term tq → tq) ∧
tt = (Term tr → tr) ∧ tw = (Term (tu, tv) → tu, tz) ∧ tx = tu ∧
ty = tu" *) ans
      with (Terms.Report_toplevel _ | Terms.Contradiction _) as exn ->
        ignore (Format.flush_str_formatter ());
        Terms.pr_exception Format.str_formatter exn;
        assert_failure (Format.flush_str_formatter ())
    );

  "constraint separation: filter" >::
    (fun () ->
      todo "debug";
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
        let uni_v v =
          try Hashtbl.find uni_v v with Not_found -> false in
        (*let uni_v v = false in
        let cmp_v v1 v2 = Same_quant in*)
        todo "Test fails by looping inside abduction";
        let brs = Infer.simplify preserve cmp_v uni_v brs in
        let brs = abd_mockup_num cmp_v uni_v
          ~params:VarSet.empty
          ~bparams:[]
          ~zparams:[]
          (List.map Infer.br_to_formulas brs) in
        assert_bool "No abduction answer" (brs <> None);
        let brs = Aux.unsome brs in
        ignore (Format.flush_str_formatter ());
        pr_line_list "| "
          (fun ppf (prem,concl) -> Format.fprintf ppf
            "@[<2>%a@ ⟹@ %a@]" pr_formula prem pr_formula concl)
          Format.str_formatter brs;
        (* FIXME: really? *)
        assert_equal ~printer:(fun x -> x)
          " ⟹ 
|  ⟹ 
| n7 = n5 ∧ 0 = n7 ⟹ 0 = n10
| n15 = n5 ∧ (n17 + 1) = n15 ⟹ 
| n15 = n5 ∧ (n17 + 1) = n15 ⟹ (n25 + 1) = n23
| n15 = n5 ∧ (n17 + 1) = n15 ⟹ "
          (Format.flush_str_formatter ());
      with (Terms.Report_toplevel _ | Terms.Contradiction _) as exn ->
        ignore (Format.flush_str_formatter ());
        Terms.pr_exception Format.str_formatter exn;
        assert_failure (Format.flush_str_formatter ())
    );

  "abduction: filter" >::
    (fun () ->
      todo "debug";
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
        let uni_v v =
          try Hashtbl.find uni_v v with Not_found -> false in
        (*let uni_v v = false in
        let cmp_v v1 v2 = Same_quant in*)
        todo "Test fails by looping inside abduction";
        let brs = Infer.simplify preserve cmp_v uni_v brs in
        let brs = List.map Infer.br_to_formulas brs in
        let _, (vs, ans) =
          try abd cmp_v uni_v ~params:VarSet.empty
                ~bparams:[]
                ~zparams:[]
                ~discard:[] ~fallback:brs brs
          with Suspect _ -> assert_failure "No abduction answer" in
        ignore (Format.flush_str_formatter ());
        Format.fprintf Format.str_formatter "@[<2>∃%a.@ %a@]"
          (pr_sep_list "," pr_tyvar) vs pr_formula ans;
        assert_equal ~printer:(fun x -> x)
          (* FIXME *)
          "∃. t1 = (List (Bar, n5) → Ex1 t4) ∧ t3 = (List (Bar, n5)) ∧
  t6 = Bar ∧ t9 = (List (t11, n10)) ∧ t18 = (List (Bar, n23)) ∧
  t21 = Bool ∧ t22 = (List (Bar, n23)) ∧
  t27 = (List (Bar, n17) → List (Bar, n25)) ∧
  t29 = (List (Bar, n17) → List (Bar, n23)) ∧ n15 = (1 + n17)"
          (Format.flush_str_formatter ());
      with (Terms.Report_toplevel _ | Terms.Contradiction _) as exn ->
        ignore (Format.flush_str_formatter ());
        Terms.pr_exception Format.str_formatter exn;
        assert_failure (Format.flush_str_formatter ())
    );

  "term abduction: params" >::
    (fun () ->
      Terms.reset_state ();
      Infer.reset_state ();
      try
        let lhs0, rhs0 = [], p_formula "tA = ((Ty tB, Ty tC) → Bool)" in
        let lhs1 = [] and rhs1 = p_formula "tD = ((Ty Int, Ty Int) → Bool)" in
        let lhs0, rhs0 = br_simple lhs0 rhs0 in
        let lhs1, rhs1 = br_simple lhs1 rhs1 in
        let vA = VNam (Type_sort, "tA")
        and vB = VNam (Type_sort, "tB")
        and vC = VNam (Type_sort, "tC")
        and vD = VNam (Type_sort, "tD") in
        let pms = vars_of_list [vA; vB; vC; vD] in
        let ans =
          try let vs, ans_typ, _ =
                abd_typ cmp_v uni_v ~params:pms
                  ~bparams:[vA, VarSet.singleton vA]
                  ~zparams:[vA, vars_of_list [vA; vB; vC]]
                  ~validate:(fun _ _ _ -> ()) ~discard:[]
                [lhs0, rhs0; lhs1, rhs1] in
              pr_to_str pr_formula (to_formula ans_typ)
          with Suspect _ -> "none" in
        assert_equal ~printer:(fun x -> x)
          "tA = (Ty tB, Ty tC → Bool) ∧
tD = (Ty Int, Ty Int → Bool)" ans
      with (Terms.Report_toplevel _ | Terms.Contradiction _) as exn ->
        ignore (Format.flush_str_formatter ());
        Terms.pr_exception Format.str_formatter exn;
        assert_failure (Format.flush_str_formatter ())
    );


]

let tests = "Abduction Debug Off" >::: [ ]

