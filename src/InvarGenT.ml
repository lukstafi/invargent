(** Main executable for InvarGenT.

    Released under the GNU General Public Licence (version 2 or
    higher), NO WARRANTY of correctness etc. (C) Lukasz Stafiniak 2013
    @author Lukasz Stafiniak lukstafi (AT) gmail.com
    @since Mar 2013
*)

(** Annotate [let-in] nodes in fallback mode of .ml generation. *)
let let_in_fallback = ref false

open Terms
open Aux

let solver ~new_ex_types ~preserve cn =
  let q_ops, cn = Infer.prenexize cn in
  let exty_res_of_chi, brs = Infer.normalize q_ops cn in
  let brs = Infer.simplify preserve q_ops brs in
  Invariants.solve q_ops new_ex_types exty_res_of_chi brs

let process_file ?(do_sig=false) ?(do_ml=false) ?(do_mli=false)
    ?(verif_ml=true) ?(full_annot=false) fname =
  current_file_name := fname;
  let infer_annot_fun = !Infer.annotating_fun in
  let infer_annot_letin = !Infer.annotating_letin in
  Infer.annotating_fun := infer_annot_fun || full_annot;
  Infer.annotating_letin := infer_annot_letin || full_annot;
  let file = open_in fname in
  let prog = (Infer.normalize_program % Parser.program Lexer.token)
      (Lexing.from_channel file) in
  let env, annot = Infer.infer_prog solver prog in
  Infer.annotating_fun := infer_annot_fun;
  Infer.annotating_letin := infer_annot_letin;
  let base = Filename.chop_extension fname in
  if do_sig then (
    let output = Format.formatter_of_out_channel
        (open_out (base^".gadti")) in
    Format.fprintf output "%a@\n%!" pr_signature annot;
    Format.printf "InvarGenT: Generated file %s@\n%!" (base^".gadti"));
  if do_ml then (
    let output = Format.formatter_of_out_channel
        (open_out (base^".ml")) in
    Format.fprintf output "%a@\n%!"
      (OCaml.pr_ml ~funtys:full_annot ~lettys:full_annot) annot;
    Format.printf "InvarGenT: Generated file %s@\n%!" (base^".ml"));
  if do_mli then (
    let output = Format.formatter_of_out_channel
        (open_out (base^".mli")) in
    Format.fprintf output "%a@\n%!" OCaml.pr_mli annot;
    Format.printf "InvarGenT: Generated file %s@\n%!" (base^".mli"));
  if do_ml && verif_ml then
    let cmd = "ocamlc -c "^base^".ml" in
    let res = Sys.command cmd in
    Format.printf "InvarGenT: Command \"%s\" exited with code %d@\n%!"
      cmd res;
    if res = 0 || full_annot || not infer_annot_fun then Some res
    else (
      let output = Format.formatter_of_out_channel
          (open_out (base^".ml")) in
      Format.fprintf output "%a@\n%!"
        (OCaml.pr_ml ~funtys:true ~lettys:!let_in_fallback) annot;
      Format.printf "InvarGenT: Regenerated file %s@\n%!" (base^".ml");
      let res = Sys.command cmd in
      Format.printf "InvarGenT: Command \"%s\" exited with code %d@\n%!"
        cmd res;
      Some res)
  else None


let () =
  let executable = Filename.basename Sys.executable_name in
  let chop f =
    try Filename.chop_extension f with Invalid_argument _ -> f in
  let executable = chop (chop executable) in
  if executable <> "Tests" && executable <> "InvarGenTTest"
  then (
    if Array.length Sys.argv <= 1 then (
      print_string ("Usage: "^Sys.argv.(0)^" \"program source file\"\n");
      exit 0
    ) else (
      let file_name = Sys.argv.(1) in
      try
        ignore
          (process_file file_name ~do_sig:true ~do_ml:true ~do_mli:true)
      with (Report_toplevel _ | Contradiction _) as exn ->
        pr_exception Format.std_formatter exn; exit 2)
  )
