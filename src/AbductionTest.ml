(** Abduction tests for InvarGenT.

    Released under the GNU General Public Licence (version 2 or
    higher), NO WARRANTY of correctness etc. (C) Lukasz Stafiniak 2013
    @author Lukasz Stafiniak lukstafi (AT) gmail.com
    @since Mar 2013
*)
open OUnit
open Terms
open Abduction

let debug = ref (* true *)false

let cmp_v v1 v2 = Same_quant
let uni_v v = v=VNam (Type_sort, "tx")
              || v=VNam (Type_sort, "ty")
let q = {cmp_v; uni_v; same_as = fun _ _ -> ()}

let p_formula s = Parser.formula Lexer.token (Lexing.from_string s)
let br_simple lhs rhs =
  let lhs, _, _ = unify ~use_quants:false q lhs in
  let rhs, _, _ = unify ~use_quants:false q rhs in
  lhs, rhs

let test_simple lhs_m rhs_m ?(validate=(fun _ _ -> ())) skip res =
  let lhs = p_formula lhs_m and rhs = p_formula rhs_m in
  let lhs, rhs = br_simple lhs rhs in
  let ans =
    match abd_simple q ~without_quant:()
      ~bvs:VarSet.empty
      ~validate ~discard:[] skip ([],[]) (lhs, rhs) with
    | None -> "none"
    | Some (bvs, (vs, ans_typ)) ->
      pr_to_str pr_formula
        (to_formula ans_typ) in
  assert_equal ~printer:(fun x -> x)
    ~msg:(string_of_int skip^":"^lhs_m^" ⟹ "^rhs_m) res ans

let prepare_brs (brs : Infer.branch list) = List.map
  (fun (prem, concl) ->
    List.for_all                        (* is_nonrec *)
      (function PredVarU _ -> false | _ -> true) concl,
    prem, concl) brs
    
let tests = "Abduction" >::: [

  "simple abduction: eval" >::
    (fun () ->
       skip_if !debug "debug";
      let lhs1 = "(Term td) = ta ∧ Int = td" and rhs1 = "tb = Int" in
      Terms.reset_state ();
      Infer.reset_state ();
      try
        test_simple lhs1 rhs1 0 "tb = td";
        test_simple lhs1 rhs1 1 "tb = Int ∧
td = Int"; 
        test_simple lhs1 rhs1 2 "tb = td";
        test_simple lhs1 rhs1 3 "tb = Int";
        test_simple lhs1 rhs1 4 "td = Int ∧
ta = (Term tb)";
        test_simple lhs1 rhs1 5 "ta = (Term tb)";
        test_simple lhs1 rhs1 6 "none";
      with (Terms.Report_toplevel _ | Terms.Contradiction _) as exn ->
        ignore (Format.flush_str_formatter ());
        Terms.pr_exception Format.str_formatter exn;
        assert_failure (Format.flush_str_formatter ())
    );

  "simple abduction: avoid subst" >::
    (fun () ->
       skip_if !debug "debug";
      let lhs1 = "tx = F(ty) ∧ ta = A" and rhs1 = "tb = G(ta)" in
      Terms.reset_state ();
      Infer.reset_state ();
      try
        test_simple lhs1 rhs1 0 "tb = (G ta)";
        test_simple lhs1 rhs1 1 "ta = A ∧
tb = (G A)"; 
        test_simple lhs1 rhs1 2 "tb = (G A)"; 
        test_simple lhs1 rhs1 3 "none";
      with (Terms.Report_toplevel _ | Terms.Contradiction _) as exn ->
        ignore (Format.flush_str_formatter ());
        Terms.pr_exception Format.str_formatter exn;
        assert_failure (Format.flush_str_formatter ())
    );

  "term abduction: params" >::
    (fun () ->
       skip_if !debug "debug";
      Terms.reset_state ();
      Infer.reset_state ();
      try
        let lhs0, rhs0 = [], p_formula "tA = ((Ty tB, Ty tC) → Bool)" in
        let lhs1 = [] and rhs1 = p_formula "tD = ((Ty Int, Ty Int) → Bool)" in
        let lhs0, rhs0 = br_simple lhs0 rhs0 in
        let lhs1, rhs1 = br_simple lhs1 rhs1 in
        let vA = VNam (Type_sort, "tA") in
        let bvs = VarSet.singleton vA in
        let ans =
          try let cand_bvs, alien_eqs, vs, ans_typ, _ =
                abd_typ q ~bvs
                  ~validate:(fun _ _ -> ()) ~discard:[]
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
