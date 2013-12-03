(** Main executable for InvarGenT.

    Released under the GNU General Public Licence (version 2 or
    higher), NO WARRANTY of correctness etc. (C) Lukasz Stafiniak 2013
    @author Lukasz Stafiniak lukstafi (AT) gmail.com
    @since Mar 2013
*)
open Terms
open Aux

let solver preserve cn =
  let q_ops, cn = Infer.prenexize cn in
  let exty_res_of_chi, brs = Infer.normalize q_ops cn in
  let brs = Infer.simplify preserve q_ops brs in
  let q_ops, res, sol =
    Invariants.solve q_ops exty_res_of_chi brs in

let process_file file =
  let prog = (Infer.normalize_program % Parser.program Lexer.token)
      (Lexing.from_channel file) in
  let env, struc = Infer.infer_prog solver prog in

    let test_sol (chi, result) =
      let vs, ans = nice_ans (List.assoc chi sol) in
      ignore (Format.flush_str_formatter ());
      Format.fprintf Format.str_formatter "@[<2>∃%a.@ %a@]"
        (pr_sep_list "," pr_tyvar) vs pr_formula ans;
      assert_equal ~printer:(fun x -> x)
        result
        (Format.flush_str_formatter ()) in
    List.iter test_sol answers


  Format.fprintf Format.std_formatter "%a@\n%!" pr_program prog


let () =
  if Array.length Sys.argv <= 1 then (
    print_string ("Usage: "^Sys.argv.(0)^" \"program source file\"\n");
    exit 0
  ) else
    let file_name = Sys.argv.(1) in
    try process_file (open_in file_name)
    with (Report_toplevel _ | Contradiction _) as exn ->
      pr_exception Format.std_formatter exn; exit 2
