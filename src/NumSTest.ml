(** Numeric sort operations tests for InvarGenT.

    Released under the GNU General Public Licence (version 2 or
    higher), NO WARRANTY of correctness etc. (C) Lukasz Stafiniak 2013
    @author Lukasz Stafiniak lukstafi (AT) gmail.com
    @since Mar 2013
*)
open OUnit

let debug = ref (* true *)false

open Aux
open Defs
open NumDefs
(* open Terms *)
open NumS

let cmp_v v1 v2 = Same_quant
let uni_v v = v=VNam (Type_sort, "tx")
              || v=VNam (Type_sort, "ty")
let q = {cmp_v; uni_v; same_as = (fun _ _ -> ());
         upward_of = (fun _ _ -> false)}

let numeric_formula s =
  sort_formula (Parser.formula Lexer.token (Lexing.from_string s))

let tests = "NumS" >::: [
  "crossing guard bands preserve the best legal key in either order" >:: (fun () ->
    let var s = VNam (Num_sort,s) in
    let i = var "i" and j = var "j" and k = var "k" and r = var "l" in
    let v x = Lin (1,1,x) and c n = Cst (n,1) in
    let inputs = vars_of_list [i;j] in
    let band x = v x, add (v x) (c 3) in
    let post = numeric_formula "l=k" and pre = numeric_formula "(-10)<=k ∧ k<=5" in
    let at x n = Eq (v x,c n,dummy_loc) in
    let graphs = guarded_interval_call ~inputs ~key:k ~result:r ~bands:[band i;band j] ~post pre dummy_loc in
    let graph = match graphs with [g] -> g | _ -> assert_failure "missing guarded graph" in
    List.iter (fun (a,b,expected) ->
        let state = satisfiable_exn (at i a :: at j b :: graph) in
        assert_bool "greatest safe key, or legal lower endpoint when none is safe"
          (implies_cnj state [at k expected])) [3,-1,-2; -1,3,-2; 1,9,5; 4,2,1];
    let blocked = guarded_interval_call ~inputs ~key:k ~result:r ~bands:[c 0,c 6]
        ~post (numeric_formula "3<=k ∧ k<=5") dummy_loc in
    (match blocked with
     | [g] -> assert_bool "impossible avoidance still supplies a legal key"
         (implies_cnj (satisfiable_exn g) [at k 3])
     | _ -> assert_failure "missing covered fallback");
    assert_equal [] (guarded_interval_call ~inputs ~key:k ~result:r ~bands:[c 0,c 0]
      ~post (numeric_formula "1<=2 k ∧ 2 k<=3") dummy_loc);
    let post = numeric_formula "k<=l ∧ l<=k+2" and pre = numeric_formula "i+(-2)<=k ∧ k<=i" in
    let choose pre = guarded_interval_call ~inputs ~key:k ~result:r ~bands:[c 0,c 0] ~post pre dummy_loc in
    let graph = match choose pre with [g] -> g | _ -> assert_failure "missing endpoint graph" in
    let half x a = Eq (v x,Cst (a,2),dummy_loc) in
    List.iter (fun n -> ignore (satisfiable_exn (half i 1 :: half k n :: graph))) [-3;1];
    let extra = numeric_formula "min(k+1,1 + -k)<=0" in
    assert_equal [] (guarded_interval_call ~inputs ~key:k ~result:r ~bands:[c 10,c 10]
      ~post (pre @ extra) dummy_loc));
  "a component inside a forbidden band survives boundary pruning" >:: (fun () ->
    let key = VNam (Num_sort,"k") and result = VNam (Num_sort,"l") in
    let pre = numeric_formula "0<=k ∧ k<=11 ∧ min(k,10 + -k)<=0" in
    let post = numeric_formula "l=0 ∧ min(k + -l + -4,l+16 + -k)<=0" in
    let probes,defs = component_keys ~inputs:VarSet.empty ~key ~result ~post pre dummy_loc in
    assert_equal [] defs;
    assert_equal 2 (List.length probes);
    List.iter (fun p ->
        assert_equal (Cst (10,1),Cst (11,1)) (p.clip_lower,p.clip_upper)) probes);
  "symbolic interval keys attain the greatest and least admissible values" >:: (fun () ->
    let var s = VNam (Num_sort,s) in
    let i = var "i" and j = var "j" and k = var "k" and r = var "l" in
    let inputs = vars_of_list [i;j] in
    let package = k,r,numeric_formula "k+2<=l ∧ l<=k+4" in
    let pre = numeric_formula "i+(-20)<=k ∧ k<=i ∧ k<=j ∧ k<=n" in
    let bands = [8,9; 4,5; 17,17; 5,6] in
    let graphs = symbolic_interval_calls ~inputs ~key:k ~bands ~package pre dummy_loc in
    let high,low = match graphs with [hi;lo] -> hi,lo | _ -> assert_failure "both bounds yield graphs" in
    let at v x = Eq (Lin (1,1,v),Cst (x,1),dummy_loc) in
    let safe k = List.for_all (fun (a,b) -> k+4 < a || b < k+2) bands in
    let rec prev x = if safe x then x else prev (x-1) in
    let rec next x = if safe x then x else next (x+1) in
    List.iter (fun (x,y) -> List.iter (fun (graph,expected) ->
        assert_bool "private precondition variable is absent" (not (VarSet.mem (var "n") (fvs_formula graph)));
        let state = satisfiable_exn (at i x :: at j y :: graph) in
        assert_bool "graph forces the extremal safe key" (implies_cnj state [at k expected]))
      [high,prev (min x y); low,next (x-20)])
      [3,6; 21,17; 25,14; 33,7; -1,100; 100,-7]);
  "integer envelopes and interpolation obey every sampled interval" >:: (fun () ->
    let var s = VNam (Num_sort,s) in
    let key = var "k" and index = var "i" and result = var "j" in
    let package = key,result,numeric_formula "k<=j ∧ j<=k+20" in
    let pre = numeric_formula "k<=100 i+10 ∧ 100 i+10<=k+20" in
    let check offsets expect_extremum =
      let points = List.mapi (fun x d -> x, 100*x+d) offsets in
      let bands = concat_map (fun (_,k) -> [k-1,k-1; k+21,k+21]) points in
      let answers = fit_interval_calls ~index ~key ~samples:(List.map fst points) ~package ~bands pre dummy_loc in
      (* Five strictly concave or convex points need at least three lines.
         Their extrema have a fresh intermediate, as does the mixed case. *)
      let is_extremum phi = List.for_all (function Opti _ -> true | _ -> false) phi in
      let extremes = List.filter is_extremum answers in
      assert_equal (if expect_extremum then 1 else 0) (List.length extremes);
      assert_bool "interpolation supplied a graph" (List.exists (fun phi -> not (is_extremum phi)) answers);
      List.iter (fun graph ->
          assert_bool "the graph needs a local numeric intermediate"
            (not (VarSet.is_empty (VarSet.diff (fvs_formula graph) (vars_of_list [index; key]))));
          List.iter (fun (x,k) ->
              let at v n = Eq (Lin (1,1,v),Cst (n,1),dummy_loc) in
              let state = satisfiable_exn (at index x :: graph) in
              assert_bool "the graph forces the required key" (implies_cnj state [at key k])) points) answers in
    check [0;5;7;8;8] true;
    check [0;-5;-7;-8;-8] true;
    check [0;3;0;3;0] false);
  "a change of pivot preserves the other equations" >:: (fun () ->
    let input = numeric_formula "n1=n2+n3 ∧ n1=n4+n5 ∧ n2<=n5" in
    let all = fvs_formula input in
    List.iter (fun keep -> List.iter (fun apply ->
      let _, sb, residual = separate_subst q ~keep ~bvs:all ~apply input in
      let output = VarMap.fold (fun v t phi -> Eq (Lin (1,1,v), t, dummy_loc) :: phi)
          sb residual in
      assert_bool "retained equations and bindings imply the original constraints"
        (implies_cnj (satisfiable_exn output) input);
      assert_bool "the separated constraints accept every original solution"
        (implies_cnj (satisfiable_exn input) output)) [false; true])
      [VarSet.empty; fvs_formula (numeric_formula "n1=n3"); all]);
  "combine branch equations across two result indices" >:: (fun () ->
    let graph = numeric_formula "n2=n1+n3" in
    let targets = fvs_formula (numeric_formula "n1=n2") in
    let check branches expected =
      let branches = List.map (fun text -> [], numeric_formula text) branches in
      let preserve = fvs_formula graph in
      let _, _, result, _ = disjelim q ~target_vs:targets ~preserve
          ~bvs:VarSet.empty ~param_bvs:(VarSet.diff preserve targets)
          ~guess:false ~initstep:false branches in
      assert_bool "every branch establishes the inferred equations"
        (List.for_all (fun (_, br) -> implies_cnj (satisfiable_exn br) result) branches);
      assert_equal expected (implies_cnj (satisfiable_exn result) graph) in
    let base = "n1=n3 ∧ n2=2 n3" and step = "n1=n3+1 ∧ n2=2 n3+1" in
    check [base; step] true;
    check [step; base] true;
    check [base; step; "n1=n3+2 ∧ n2=2 n3+3"] false);

  "generalize two rational endpoints" >:: (fun () ->
    let bounds = numeric_formula "1/2<=n1 ∧ n1<=3/2" in
    let vs = fvs_formula bounds in
    let branches = List.map (fun s -> [], numeric_formula s) ["n1=1/2"; "n1=3/2"] in
    let _, _, result, _ = disjelim q ~target_vs:vs ~preserve:vs
        ~bvs:VarSet.empty ~param_bvs:VarSet.empty ~guess:false ~initstep:false branches in
    assert_bool "both endpoints fit the inferred interval"
      (List.for_all (fun (_, br) -> implies_cnj (satisfiable_exn br) result) branches);
    assert_bool "inferred interval fits the caller" (implies_cnj (satisfiable_exn result) bounds));

  "printed extrema preserve the coefficient of the isolated variable" >:: (fun () ->
    let check source =
      let input = numeric_formula source in
      let written = Format.asprintf "%a" NumDefs.pr_formula input in
      let parsed = numeric_formula written in
      assert_bool written (implies_cnj (satisfiable_exn input) parsed);
      assert_bool written (implies_cnj (satisfiable_exn parsed) input) in
    List.iter check ["3 n1<=max(n2,n3)"; "min(n2,n3)<=2 n1";
                     "(2/3) n1=min(n2,n3)"; "(-2/3) n1=max(n2,n3)"]);

  "extremum at a universal result index" >:: (fun () ->
    let q = {q with uni_v = (fun _ -> true)} in
    let goal = numeric_formula "n2<=max(n1+20,0)" in
    let vars = NumDefs.fvs_formula goal in
    let rejected =
      try ignore (holds q VarSet.empty empty_state goal); false
      with Terms.Contradiction _ -> true in
    assert_bool "the caller bound restricts an arbitrary result" rejected;
    let _, demand = abductive_holds q ~bvs:vars empty_state goal in
    assert_bool "Split receives the caller bound"
      (implies_cnj (satisfiable_exn demand) goal);
    ignore (holds q VarSet.empty empty_state
              (numeric_formula "n1<=max(2 n1,0)")));

  "pruning keeps bounds that fail on an equality face" >:: (fun () ->
    let check premise conclusion redundant =
      let guard = numeric_formula premise and goal = numeric_formula conclusion in
      let kept = prune_redundant q ~guard ~initstep:false goal in
      assert_equal ~msg:conclusion ~printer:string_of_bool redundant (kept = []);
      let entails = try implies_cnj (satisfiable_exn (guard @ kept)) goal
        with Terms.Contradiction _ -> true in
      assert_bool "the pruned formula still entails the goal under its guard" entails in
    check "n1=0" "min(1,2)<=n1" false;
    check "n1=0" "min(-1,2)<=n1" true;
    check "n1=max(n2,n3)" "n1+1<=max(n2,n3)" false;
    check "n1=max(n2,n3)" "n1+1<=max(n2,n3+1)" false;
    check "n1=max(n2,n3)" "n1<=max(n2+1,n3+1)" true;
    check "n1=min(n2,n3)" "min(n2,n3)<=n1+ -1" false);

  "initial generalization may forget an extremum that pruning must keep" >:: (fun () ->
    let f = numeric_formula
      "n2=min(n1,0) ∧ n2=max(0,n2) ∧ n2=max(0,n1) ∧ n2=min(n2,0) ∧ n2=max(n2,n1)" in
    let exact = prune_redundant q ~initstep:true f
    and general = prune_redundant q ~allow_weakening:true ~initstep:true f in
    assert_bool "exact simplification preserves both equalities"
      (implies_cnj (satisfiable_exn exact) (numeric_formula "n1=0 ∧ n2=0"));
    assert_bool "every supplier satisfies the proposed generalization"
      (implies_cnj (satisfiable_exn f) general);
    assert_bool "the early summary also admits positive equal arguments"
      (implies_cnj (satisfiable_exn (numeric_formula "n1=1 ∧ n2=1")) general));

  "widen against every supplier on the public interface" >:: (fun () ->
    let old = numeric_formula "n1<=n2 ∧ n2<=max(n1+20,0)" in
    let summary = numeric_formula "n1<=n2" in
    let public = NumDefs.fvs_formula old in
    let check interface branches expected =
      let result = converge q ~initstep:false
          ~suppliers:(interface, List.map numeric_formula branches) old summary in
      assert_equal ~printer:string_of_bool expected
        (implies_cnj (satisfiable_exn result) old) in
    let base = "n2=n1" and left = "n2<=n1+19" and right = "n2<=0" in
    check public [base; left; right] true;
    check public [base; left; "n2<=n1+21"] false;
    check public [base; "0<=n1"] false;
    check public [] false;
    check VarSet.empty [base; left; right] false);

  "a stalled jump narrows the cap on its existing interface" >:: (fun () ->
    let old = numeric_formula "n1<=max(n2+20,n3)"
    and tighter = numeric_formula "n1<=max(n3,n2+19)"
    and other = numeric_formula "n4<=max(n1,n3)" in
    let check recover_caps interface expected =
      let result = converge q ~recover_caps ~initstep:false
          ~suppliers:(interface, []) old (tighter @ other) in
      let state = satisfiable_exn result in
      assert_equal ~printer:string_of_bool expected (implies_cnj state tighter);
      assert_bool "an unrelated witness stays out" (not (implies_cnj state other)) in
    check false (fvs_formula old) false;
    check true (fvs_formula old) true;
    check true VarSet.empty false);

  "keep a supplier extremum only when every branch proves it" >:: (fun () ->
    let cap = numeric_formula "n1<=max(n2+19,0)" in
    let preserve = fvs_formula cap in
    let target_vs = fvs_formula (numeric_formula "n1=0")
    and param_bvs = fvs_formula (numeric_formula "n2=0") in
    let check extra expected =
      let branches = ["n1=0"; "0<=n1 ∧ n1<=max(n2+19,0)"] @ extra in
      let _, _, result, _ = disjelim q ~target_vs ~preserve ~param_bvs
          ~bvs:VarSet.empty ~guess:false ~initstep:false
          (List.map (fun s -> [], numeric_formula s) branches) in
      assert_equal ~printer:string_of_bool expected
        (implies_cnj (satisfiable_exn result) cap) in
    check [] true;
    check ["n1=1"] false);

  "instantiate caller thresholds on the supplier result" >:: (fun () ->
    let cap = numeric_formula "n1<=max(n2+19,0)" in
    let target_vs = fvs_formula (numeric_formula "n1=0")
    and param_bvs = fvs_formula (numeric_formula "n2=0") in
    let check extra expected =
      let branches = ["n1=0"; "0<=n1 ∧ n1<=n2+19"] @ extra in
      let _, _, result, _ = disjelim q ~target_vs ~preserve:(fvs_formula cap)
          ~previous:(numeric_formula "n8<=max(n9+20,0)") ~param_bvs
          ~bvs:VarSet.empty ~guess:false ~initstep:false
          (List.map (fun s -> [], numeric_formula s) branches) in
      assert_bool "no caller-local variable escapes"
        (VarSet.subset (fvs_formula result) (fvs_formula cap));
      assert_equal ~printer:string_of_bool expected
        (implies_cnj (satisfiable_exn result) cap) in
    check [] true;
    check ["n1=1"] false);

  "extrema on ground inputs" >:: (fun () ->
    let goals = List.map (fun (text, holds) -> text, numeric_formula text, holds)
        ["n1 = max(n2,n3)", (fun x y z -> x = max y z);
         "n1 = min(n2,n3)", (fun x y z -> x = min y z);
         "n1 <= max(n2,n3)", (fun x y z -> x <= max y z);
         "min(n2,n3) <= n1", (fun x y z -> min y z <= x)] in
    for x = -2 to 2 do
      for y = -2 to 2 do
        for z = -2 to 2 do
          let given = Printf.sprintf "n1=%d ∧ n2=%d ∧ n3=%d" x y z in
          let st = satisfiable_exn (numeric_formula given) in
          List.iter (fun (text, goal, holds) ->
            assert_equal ~msg:(given ^ " implies " ^ text) ~printer:string_of_bool
              (holds x y z) (implies_cnj st goal)) goals
        done
      done
    done);

  "extrema under substitutions" >:: (fun () ->
    let feasible batches =
      try
        ignore (List.fold_left (fun state batch ->
          satisfiable_exn ~state (numeric_formula batch)) empty_state batches);
        true
      with Terms.Contradiction _ -> false in
    let values = "n1=0 ∧ n2=2 ∧ n3=1" in
    List.iter (fun (atom, expected) ->
      List.iter (fun batches ->
        assert_equal ~msg:(String.concat " then " batches) ~printer:string_of_bool
          expected (feasible batches))
        [[values ^ " ∧ " ^ atom]; [values;atom]; [atom;values]])
      ["min(n1,n2)<=n3", true; "n3<=max(n1,n2)", true;
       "n1+1<=max(n1,n1)", false; "min(n2,n3)<=n1", false;
       "n1=min(n1,n2)", true; "n1=max(n1,n2)", false]);

  "joint feasibility of extremum alternatives" >:: (fun () ->
    let possible batches = List.fold_left (fun state batch ->
        match state with
        | Aux.Left _ -> state
        | Aux.Right state -> satisfiable ~state (numeric_formula batch))
        (Aux.Right empty_state) batches |> Aux.is_right in
    let corners = ["1<=max(n1,n2)"; "1<=max(-n1,n2)";
                   "1<=max(n1,-n2)"; "1<=max(-n1,-n2)"] in
    List.iter (fun atoms ->
        assert_bool "no common choice" (not (possible [String.concat " ∧ " atoms]));
        assert_bool "incremental, either order" (not (possible atoms || possible (List.rev atoms))))
      [corners; ["n3=max(n1,n2)"; "n1+1<=n3"; "n2+1<=n3"]];
    List.iter (fun missing -> assert_bool "any three corners have a witness"
        (possible (List.filter ((<>) missing) corners))) corners);
  "an early counterexample among many extrema" >:: (fun () ->
    let rec constraints n acc =
      if n = 0 then acc else
        let atom = Printf.sprintf "min(n%d,n%d)<=n%d" (3*n) (3*n+1) (3*n+2) in
        constraints (n-1) (atom :: acc) in
    let st = satisfiable_exn (numeric_formula (String.concat " ∧ " (constraints 30 []))) in
    assert_bool "the independent n1 is unrestricted"
      (not (implies_cnj st (numeric_formula "n1<=0"))));

  "extrema across alternatives" >:: (fun () ->
    List.iter (fun (given, goal, expected) ->
      let st = satisfiable_exn (numeric_formula given) in
      assert_equal ~msg:(given ^ " implies " ^ goal) ~printer:string_of_bool
        expected (implies_cnj st (numeric_formula goal)))
      ["min(n1,n2) <= n3 ∧ n3+1 <= n2", "n1 <= n3", true;
       "min(n1,n2) <= n3", "n1 <= n3", false;
       "n1+n2=0 ∧ n3=0", "min(n1,n2) <= n3", true;
       "n1+n2=0 ∧ n3=0", "n3 <= max(n1,n2)", true;
       "n1+n2=0 ∧ n3= -1", "min(n1,n2) <= n3", false;
       "n1<=n3 ∧ n2<=n3", "n3=max(n1,n2)", false;
       "n1=0 ∧ n1+n2<=2 n3 ∧ n2=max(n3,n1)", "n2=n1+n3", true;
       "n1<=n2 ∧ n2<=n3 ∧ n3<=n1 ∧ n4<=n1 ∧ n2<=n4", "n4=n3", true;
       "n1<=n2 ∧ n2<=n3 ∧ n1<=n3", "n1=n3", false]);

  "convex hull: basic cst" >::
    (fun () ->
      skip_if !debug "debug";
      Terms.reset_state ();
      Infer.reset_state ();
      (* try *)
      try
        Printexc.record_backtrace true;
        let brs = Parser.cn_branches Lexer.token
	  (Lexing.from_string " ⟹ n1 = n2 ∧ n3 <= n2 + 2
|  ⟹ n1 = n2 ∧ n3 <= n2
|  ⟹ n1 = n2 ∧ n3 <= n2 + 1") in
        let brs = List.map (fun (_, c) -> [], sort_formula c) brs in
        let preserve = List.fold_left
            (fun vs (_, br) -> VarSet.union vs (fvs_formula br))
            VarSet.empty brs in
        let bvs = VarSet.empty in
        let param_bvs = VarSet.empty in
        let vs, _, ans, _ = disjelim q ~target_vs:preserve
            ~guess:false ~initstep:false ~preserve ~param_bvs ~bvs brs in
        let ans = prune_redundant q ~initstep:true ans in
        ignore (Format.flush_str_formatter ());
        Format.fprintf Format.str_formatter "@[<2>∃%a.@ %a@]"
          (pr_sep_list "," pr_tyvar) vs pr_formula ans;
        assert_equal ~printer:(fun x -> x)
          "∃. n2 = n1 ∧ n3 ≤ n1 + 2"
          (Format.flush_str_formatter ())
      with (Report_toplevel _ | Terms.Contradiction _) as exn ->
        ignore (Format.flush_str_formatter ());
        Terms.pr_exception Format.str_formatter exn;
        assert_failure (Format.flush_str_formatter ())
      (* with exn ->
        Printexc.print_backtrace stdout;
        assert_failure (Printexc.to_string exn) *)
    );

  "convex hull: basic equations 1" >::
    (fun () ->
      skip_if !debug "debug";
      Terms.reset_state ();
      Infer.reset_state ();
      let old_max_subopti_postcond = !max_subopti_postcond in
      (* try *)
      try
        Printexc.record_backtrace true;
        let brs = Parser.cn_branches Lexer.token
	  (Lexing.from_string " ⟹ n1 = n3 ∧ n2 = n3
|  ⟹ n1 = n4 ∧ n2 = n4") in
        let brs = List.map (fun (_, c) -> [], sort_formula c) brs in
        let preserve = List.fold_left
            (fun vs (_, br) -> VarSet.union vs (fvs_formula br))
            VarSet.empty brs in
        let bvs = VarSet.empty in
        let param_bvs = VarSet.empty in
        max_subopti_postcond := 10;
        let vs, _, ans, _ = disjelim q ~target_vs:preserve
            ~guess:false ~initstep:false ~preserve ~bvs ~param_bvs brs in
        let ans = prune_redundant q ~initstep:false ans in
        max_subopti_postcond := old_max_subopti_postcond;
        ignore (Format.flush_str_formatter ());
        Format.fprintf Format.str_formatter "@[<2>∃%a.@ %a@]"
          (pr_sep_list "," pr_tyvar) vs pr_formula ans;
        assert_equal ~printer:(fun x -> x)
          "∃. n2 = n1 ∧ min (n3, n4)≤n2 ∧ n2≤max (n3, n4)"
          (Format.flush_str_formatter ())
      with (Report_toplevel _ | Terms.Contradiction _) as exn ->
        max_subopti_postcond := old_max_subopti_postcond;
        ignore (Format.flush_str_formatter ());
        Terms.pr_exception Format.str_formatter exn;
        assert_failure (Format.flush_str_formatter ())
      (* with exn ->
        Printexc.print_backtrace stdout;
        assert_failure (Printexc.to_string exn) *)
    );

  "convex hull: basic equations 2" >::
    (fun () ->
      skip_if !debug "debug";
      Terms.reset_state ();
      Infer.reset_state ();
      let old_max_subopti_postcond = !max_subopti_postcond in
      try
        Printexc.record_backtrace true;
        let brs = Parser.cn_branches Lexer.token
	  (Lexing.from_string " ⟹ n3 = n1 ∧ n4 = n1
|  ⟹ n3 = n2 ∧ n4 = n2") in
        let brs = List.map (fun (_, c) -> [], sort_formula c) brs in
        let preserve = List.fold_left
            (fun vs (_, br) -> VarSet.union vs (fvs_formula br))
            VarSet.empty brs in
        let bvs = VarSet.empty in
        let param_bvs = VarSet.empty in
        max_subopti_postcond := 10;
        let vs, _, ans, _ = disjelim q ~target_vs:preserve
            ~guess:false ~initstep:false ~preserve ~bvs ~param_bvs brs in
        let ans = prune_redundant q ~initstep:false ans in
        max_subopti_postcond := old_max_subopti_postcond;
        ignore (Format.flush_str_formatter ());
        Format.fprintf Format.str_formatter "@[<2>∃%a.@ %a@]"
          (pr_sep_list "," pr_tyvar) vs pr_formula ans;
        assert_equal ~printer:(fun x -> x)
          "∃. n4 = n3 ∧ n3≤max (n1, n2) ∧ min (n1, n2)≤n3"
          (Format.flush_str_formatter ())
      with (Report_toplevel _ | Terms.Contradiction _) as exn ->
        max_subopti_postcond := old_max_subopti_postcond;
        ignore (Format.flush_str_formatter ());
        Terms.pr_exception Format.str_formatter exn;
        assert_failure (Format.flush_str_formatter ())
      (* with exn ->
        Printexc.print_backtrace stdout;
        assert_failure (Printexc.to_string exn) *)
    );

  "convex hull: basic sides" >::
    (fun () ->
      skip_if !debug "debug";
      Terms.reset_state ();
      Infer.reset_state ();
      (* try *)
      try
        Printexc.record_backtrace true;
        let brs = Parser.cn_branches Lexer.token
	  (Lexing.from_string " ⟹ n1 <= n2 ∧ 0 <= n1 ∧ n2 <= 1
|  ⟹ n2 <= n1 + 2 ∧ 2 <= n2 ∧ n1 <= 1") in
        let brs = List.map (fun (_, c) -> [], sort_formula c) brs in
        let preserve = List.fold_left
            (fun vs (_, br) -> VarSet.union vs (fvs_formula br))
            VarSet.empty brs in
        let bvs = VarSet.empty in
        let param_bvs = VarSet.empty in
        let vs, _, ans, _ = disjelim q ~target_vs:preserve
            ~guess:false ~initstep:false ~preserve ~bvs ~param_bvs brs in
        ignore (Format.flush_str_formatter ());
        Format.fprintf Format.str_formatter "@[<2>∃%a.@ %a@]"
          (pr_sep_list "," pr_tyvar) vs pr_formula ans;
        assert_equal ~printer:(fun x -> x)
          "∃. 0 ≤ n1 ∧ n1 ≤ 1 ∧ n1 ≤ n2 ∧ n2 ≤ n1 + 2"
          (Format.flush_str_formatter ())
      with (Report_toplevel _ | Terms.Contradiction _) as exn ->
        ignore (Format.flush_str_formatter ());
        Terms.pr_exception Format.str_formatter exn;
        assert_failure (Format.flush_str_formatter ())
      (* with exn ->
        Printexc.print_backtrace stdout;
        assert_failure (Printexc.to_string exn) *)
    );

  "convex hull: basic angle" >::
    (fun () ->
      skip_if !debug "debug";
      Terms.reset_state ();
      Infer.reset_state ();
      let old_disjelim_rotations = !disjelim_rotations in
      (* try *)
      try
        Printexc.record_backtrace true;
        disjelim_rotations := 3;
        let brs = Parser.cn_branches Lexer.token
	  (Lexing.from_string " ⟹ n1 <= n2 ∧ 0 <= n1 ∧ n2 <= 1
|  ⟹ n2 <= n1 ∧ 2 <= n2 ∧ n1 <= 3") in
        let brs = List.map (fun (_, c) -> [], sort_formula c) brs in
        let preserve = List.fold_left
            (fun vs (_, br) -> VarSet.union vs (fvs_formula br))
            VarSet.empty brs in
        let bvs = VarSet.empty in
        let param_bvs = VarSet.empty in
        let vs, _, ans, _ = disjelim q ~target_vs:preserve
            ~guess:false ~initstep:false ~preserve ~bvs ~param_bvs brs in
        disjelim_rotations := old_disjelim_rotations;
        ignore (Format.flush_str_formatter ());
        Format.fprintf Format.str_formatter "@[<2>∃%a.@ %a@]"
          (pr_sep_list "," pr_tyvar) vs pr_formula ans;
        assert_equal ~printer:(fun x -> x)
          "∃. 0 ≤ n1 ∧ n1 ≤ 3 ∧ 2 n1 ≤ 3 n2 ∧ 3 n2 ≤ 2 n1 + 3"
          (Format.flush_str_formatter ())
      with (Report_toplevel _ | Terms.Contradiction _) as exn ->
        disjelim_rotations := old_disjelim_rotations;
        ignore (Format.flush_str_formatter ());
        Terms.pr_exception Format.str_formatter exn;
        assert_failure (Format.flush_str_formatter ())
      (* with exn ->
        Printexc.print_backtrace stdout;
        assert_failure (Printexc.to_string exn) *)
    );

]


let () =
  let executable = Filename.basename Sys.executable_name in
  let chop f =
    try Filename.chop_extension f with Invalid_argument _ -> f in
  let executable = chop (chop executable) in
  if executable = "NumSTest"
  then ignore (OUnit.run_test_tt ~verbose:true tests)
