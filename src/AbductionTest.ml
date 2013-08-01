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

let prepare_brs = List.map
  (fun br ->
    let prem, concl = Infer.br_to_formulas br in
    List.for_all                        (* is_nonrec *)
      (function PredVarU _ -> false | _ -> true) concl,
    prem, concl)
    
let tests = "Abduction" >::: [

  "simple abduction: eval" >::
    (fun () ->
      todo "debug";
      let lhs1 = "(Term td) = ta ∧ Int = td" and rhs1 = "tb = Int" in
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

  "term abduction: params" >::
    (fun () ->
      todo "debug";
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
          try let alien_eqs, vs, ans_typ, _ =
                abd_typ cmp_v uni_v ~params:pms
                  ~bparams:[vA, VarSet.singleton vA]
                  ~zparams:[vA, vars_of_list [vA; vB; vC]]
                  ~validate:(fun _ _ _ -> ()) ~discard:[]
                [lhs0, rhs0; lhs1, rhs1] in
              pr_to_str pr_formula (to_formula ans_typ)
          with Suspect _ -> "none" in
        assert_equal ~printer:(fun x -> x)
          "tD = (Ty Int, Ty Int → Bool) ∧
tA = (Ty tB, Ty tC → Bool)" ans
      with (Terms.Report_toplevel _ | Terms.Contradiction _) as exn ->
        ignore (Format.flush_str_formatter ());
        Terms.pr_exception Format.str_formatter exn;
        assert_failure (Format.flush_str_formatter ())
    );


]
