(** Main executable for InvarGenT.

    Released under the GNU General Public Licence (version 2 or
    higher), NO WARRANTY of correctness etc. (C) Lukasz Stafiniak 2013
    @author Lukasz Stafiniak lukstafi (AT) gmail.com
    @since Mar 2013
*)
open Terms
open Aux

let solver ~preserve cn =
  let q_ops, cn = Infer.prenexize cn in
  let exty_res_of_chi, brs = Infer.normalize q_ops cn in
  let brs = Infer.simplify preserve q_ops brs in
  Invariants.solve q_ops exty_res_of_chi brs

let process_file ?(do_sig=false) ?(do_ml=false) ?(do_mli=false) fname =
  current_file_name := fname;
  let file = open_in fname in
  let prog = (Infer.normalize_program % Parser.program Lexer.token)
      (Lexing.from_channel file) in
  let env, annot = Infer.infer_prog solver prog in
  let base = Filename.chop_extension fname in
  if do_sig then (
    let output = Format.formatter_of_out_channel
        (open_out (base^".gadti")) in
    Format.fprintf output "%a@\n%!" pr_signature annot);
  if do_ml then (
    let output = Format.formatter_of_out_channel
        (open_out (base^".ml")) in
    Format.fprintf output "%a@\n%!" OCaml.pr_ml annot);
  if do_mli then (
    let output = Format.formatter_of_out_channel
        (open_out (base^".mli")) in
    Format.fprintf output "%a@\n%!" OCaml.pr_mli annot);
  ()


let () =
  if Filename.basename Sys.executable_name <> "Tests.native"
  then (
    if Array.length Sys.argv <= 1 then (
      print_string ("Usage: "^Sys.argv.(0)^" \"program source file\"\n");
      exit 0
    ) else
      let file_name = Sys.argv.(1) in
      try process_file file_name
      with (Report_toplevel _ | Contradiction _) as exn ->
        pr_exception Format.std_formatter exn; exit 2
  )
