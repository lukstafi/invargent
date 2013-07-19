(** Numeric sort operations tests for InvarGenT.

    Released under the GNU General Public Licence (version 2 or
    higher), NO WARRANTY of correctness etc. (C) Lukasz Stafiniak 2013
    @author Lukasz Stafiniak lukstafi (AT) gmail.com
    @since Mar 2013
*)
open OUnit
open Terms
open NumS

(* 
   Binary addition legend:
   - t1: result
   - t3, n5: the carry bit and its value
   - n6: case when carry is 0
   - t7, n9, n13: the first number (A)
   - n10=0, t11, t12: case when A is 0
   - n15=2*n16: case when A ends with 0
   - t17, n19, n21: the second number (B)
   - t18, n25: the result (C)
   - n20=0: case when B is 0
   - n23=2*n24: case when B ends with 0
   - n25=2*n26: C ends with 0, recursive call A=n16, B=n24, C=n26
   - n30=0: recursive carry in above call
   - n32: B
   - n34=2*n35+1: case B ends with 1
   - n36=2*n37+1: C
   - recursive call carry=n41=0, A=n16, B=n35, C=n37
   - n43, n45=2*n46+1: case when A ends with 1
   - t47, n49, n51, n62: B
   - t48: C
   - n50=0: B is 0
   - n53=2*n54: B ends with 0
   - n55=2*n56: C ends with 0
   - recursive call carry=n60=0, A=n46, B=n54, C=n56
   - n64=2*n65+1: case B ends with 1
   - n66=2*n67: C ends with 0
   - recursive call carry=n71=1, A=n46, B=n65, C=n67
   - n73, n74=1: case carry is 1
   - t75, n77, n104, n136: A
   - n78=0: case A is 0
   - t79, n81, n92, n110, n114, n125, n142, n152, n163: B
   - n82=0: case B is 0
   - t80, n83=2*n84+1, n84=n85=0: C
   - n86=n88=2*n89: B ends with 0
   - n90=2*n91+1, n91=n89: C=B
   - n94=2*n95+1: B ends with 1
   - n96=2*n97: C ends with 0
   - recursive call carry=n102=1, A=n100=0, B=n95
   - n106=2*n107: case A ends with 0
   - n111=0: case B is 0
   - n112=2*n113+1, n113=n107: C ends with 1
   - n116=2*n117: case B ends with 0
   - n118=2*n119+1: C ends with 1
   - recursive call carry=n123=0, A=n107, B=n117, C=n119
   - n127=2*n128+1: case B ends with 1
   - n129=2*n130: C ends with 0
   - recursive call carry=n134=1, A=n107, B=n128, C=n130
   - n138=2*n139+1: case A ends with 1
   - n143=0: case B is 0
   - n144=2*n145: case C ends with 0
   - recursive call carry=n150=1, A=n139, B=n147=0, C=n145
   - n154=2*n155: case B ends with 0
   - n156=2*n157: C ends with 0
   - recursive call carry=n161=1, A=n139, B=n155, C=n157
   - n165=2*n166+1: case B ends with 1
   - n167=2*n168+1: C ends with 1
   - recursive call carry=n172=1, A=n139, B=n166, C=n168
   - alien subterm variables:
n266:=n172; n265:=n139; n264:=n166; n263:=n168; n262:=n161;
n261:=n139; n260:=n155; n259:=n157; n258:=n150; n257:=n139; n256:=n147;
n255:=n145; n254:=n19; n253:=n142; n252:=n134; n251:=n107; n250:=n128;
n249:=n130; n248:=n123; n247:=n107; n246:=n117; n245:=n119; n244:=n19;
n243:=n110; n242:=n102; n241:=n100; n240:=n95; n239:=n97; n238:=n19;
n237:=n81; n236:=n19; n235:=n19; n234:=n77; n233:=n71; n232:=n46; n231:=n65;
n230:=n67; n229:=n60; n228:=n46; n227:=n54; n226:=n56; n225:=n19; n224:=n49;
n223:=n41; n222:=n16; n221:=n35; n220:=n37; n219:=n30; n218:=n16; n217:=n24;
n216:=n26; n215:=n19; n214:=n19; n213:=n19; n212:=n19; n211:=n19; n210:=n9;
n209:=n9; n208:=n19; n207:=n19; n206:=n5; n205:=n5; n204:=n9; n203:=n19;
n202:=n19
 *)

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
