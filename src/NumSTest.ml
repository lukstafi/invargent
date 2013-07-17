(** Numeric sort operations tests for InvarGenT.

    Released under the GNU General Public Licence (version 2 or
    higher), NO WARRANTY of correctness etc. (C) Lukasz Stafiniak 2013
    @author Lukasz Stafiniak lukstafi (AT) gmail.com
    @since Mar 2013
*)
open OUnit
open Terms
open NumS

let test1_brs = " ⟹ 
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

let test2_brs = " ⟹ 
|  ⟹ 
| 0 = n7 ⟹ n7 = n5 ∧ 0 = n10
| (n17 + 1) = n15 ⟹ n15 = n5
| (n17 + 1) = n15 ⟹ n15 = n5 ∧ (n25 + 1) = n23
| (n17 + 1) = n15 ⟹ n15 = n5"

let tests = "NumS" >::: [

  "satisfiable: binary plus" >::
    (fun () ->
      Terms.reset_state ();
      Infer.reset_state ();
      try
      try
        Printexc.record_backtrace true;
        let brs = Parser.cn_branches Lexer.token
	  (Lexing.from_string test1_brs) in
        List.iter
          (fun (prem,concl) ->
            let cnj = prem @ concl in
            assert_bool (pr_to_str pr_formula cnj)
              (satisfiable cnj))
          brs;
      with (Terms.Report_toplevel _ | Terms.Contradiction _) as exn ->
        ignore (Format.flush_str_formatter ());
        Terms.pr_exception Format.str_formatter exn;
        assert_failure (Format.flush_str_formatter ())
      with exn ->
        Printexc.print_backtrace stdout;
        assert_failure (Printexc.to_string exn)
    );

  "satisfiable: filter" >::
    (fun () ->
      Terms.reset_state ();
      Infer.reset_state ();
      try
      try
        Printexc.record_backtrace true;
        let brs = Parser.cn_branches Lexer.token
	  (Lexing.from_string test2_brs) in
        List.iter
          (fun (prem,concl) ->
            let cnj = prem @ concl in
            assert_bool (pr_to_str pr_formula cnj)
              (satisfiable cnj))
          brs;
      with (Terms.Report_toplevel _ | Terms.Contradiction _) as exn ->
        ignore (Format.flush_str_formatter ());
        Terms.pr_exception Format.str_formatter exn;
        assert_failure (Format.flush_str_formatter ())
      with exn ->
        Printexc.print_backtrace stdout;
        assert_failure (Printexc.to_string exn)
    );

  "convex hull: basic cst" >::
    (fun () ->
      Terms.reset_state ();
      Infer.reset_state ();
      (* try *)
      try
        Printexc.record_backtrace true;
        let cmp_v _ _ = Same_quant in
        let uni_v _ = false in
        let brs = Parser.cn_branches Lexer.token
	  (Lexing.from_string " ⟹ n1 = n2 ∧ n3 <= n2 + 2
|  ⟹ n1 = n2 ∧ n3 <= n2
|  ⟹ n1 = n2 ∧ n3 <= n2 + 1") in
        let brs = List.map snd brs in
        let vs, ans = disjelim cmp_v uni_v brs in
        ignore (Format.flush_str_formatter ());
        Format.fprintf Format.str_formatter "@[<2>∃%a.@ %a@]"
          (pr_sep_list "," pr_tyvar) vs pr_formula ans;
        assert_equal ~printer:(fun x -> x)
          "∃. n2 = n1 ∧ n3 ≤ (2 + n2)"
          (Format.flush_str_formatter ())
      with (Terms.Report_toplevel _ | Terms.Contradiction _) as exn ->
        ignore (Format.flush_str_formatter ());
        Terms.pr_exception Format.str_formatter exn;
        assert_failure (Format.flush_str_formatter ())
      (* with exn ->
        Printexc.print_backtrace stdout;
        assert_failure (Printexc.to_string exn) *)
    );

  "convex hull: basic equations" >::
    (fun () ->
      Terms.reset_state ();
      Infer.reset_state ();
      (* try *)
      try
        Printexc.record_backtrace true;
        let cmp_v _ _ = Same_quant in
        let uni_v _ = false in
        let brs = Parser.cn_branches Lexer.token
	  (Lexing.from_string " ⟹ n1 = n3 ∧ n2 = n3
|  ⟹ n1 = n4 ∧ n2 = n4") in
        let brs = List.map snd brs in
        let vs, ans = disjelim cmp_v uni_v brs in
        ignore (Format.flush_str_formatter ());
        Format.fprintf Format.str_formatter "@[<2>∃%a.@ %a@]"
          (pr_sep_list "," pr_tyvar) vs pr_formula ans;
        assert_equal ~printer:(fun x -> x)
          "∃. n2 = n1"
          (Format.flush_str_formatter ())
      with (Terms.Report_toplevel _ | Terms.Contradiction _) as exn ->
        ignore (Format.flush_str_formatter ());
        Terms.pr_exception Format.str_formatter exn;
        assert_failure (Format.flush_str_formatter ())
      (* with exn ->
        Printexc.print_backtrace stdout;
        assert_failure (Printexc.to_string exn) *)
    );

  "convex hull: basic sides" >::
    (fun () ->
      Terms.reset_state ();
      Infer.reset_state ();
      (* try *)
      try
        Printexc.record_backtrace true;
        let cmp_v _ _ = Same_quant in
        let uni_v _ = false in
        let brs = Parser.cn_branches Lexer.token
	  (Lexing.from_string " ⟹ n1 <= n2 ∧ 0 <= n1 ∧ n2 <= 1
|  ⟹ n2 <= n1 + 2 ∧ 2 <= n2 ∧ n1 <= 1") in
        let brs = List.map snd brs in
        let vs, ans = disjelim cmp_v uni_v brs in
        ignore (Format.flush_str_formatter ());
        Format.fprintf Format.str_formatter "@[<2>∃%a.@ %a@]"
          (pr_sep_list "," pr_tyvar) vs pr_formula ans;
        assert_equal ~printer:(fun x -> x)
          "∃. 0 ≤ n1 ∧ n2 ≤ (2 + n1) ∧ n1 ≤ 1 ∧ n1 ≤ n2"
          (Format.flush_str_formatter ())
      with (Terms.Report_toplevel _ | Terms.Contradiction _) as exn ->
        ignore (Format.flush_str_formatter ());
        Terms.pr_exception Format.str_formatter exn;
        assert_failure (Format.flush_str_formatter ())
      (* with exn ->
        Printexc.print_backtrace stdout;
        assert_failure (Printexc.to_string exn) *)
    );

  "convex hull: basic angle" >::
    (fun () ->
      Terms.reset_state ();
      Infer.reset_state ();
      (* try *)
      try
        Printexc.record_backtrace true;
        let cmp_v _ _ = Same_quant in
        let uni_v _ = false in
        let brs = Parser.cn_branches Lexer.token
	  (Lexing.from_string " ⟹ n1 <= n2 ∧ 0 <= n1 ∧ n2 <= 1
|  ⟹ n2 <= n1 ∧ 2 <= n2 ∧ n1 <= 3") in
        let brs = List.map snd brs in
        let vs, ans = disjelim cmp_v uni_v brs in
        ignore (Format.flush_str_formatter ());
        Format.fprintf Format.str_formatter "@[<2>∃%a.@ %a@]"
          (pr_sep_list "," pr_tyvar) vs pr_formula ans;
        assert_equal ~printer:(fun x -> x)
          "∃. (n2 + n2 + n2) ≤ (3 + n1 + n1) ∧ 0 ≤ n1 ∧ n1 ≤ 3 ∧
  (n1 + n1) ≤ (n2 + n2 + n2)"
          (Format.flush_str_formatter ())
      with (Terms.Report_toplevel _ | Terms.Contradiction _) as exn ->
        ignore (Format.flush_str_formatter ());
        Terms.pr_exception Format.str_formatter exn;
        assert_failure (Format.flush_str_formatter ())
      (* with exn ->
        Printexc.print_backtrace stdout;
        assert_failure (Printexc.to_string exn) *)
    );

]
