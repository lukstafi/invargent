(** Main executable for InvarGenT.

    Released under the GNU General Public Licence (version 2 or
    higher), NO WARRANTY of correctness etc. (C) Lukasz Stafiniak 2013
    @author Lukasz Stafiniak lukstafi (AT) gmail.com
    @since Mar 2013
*)
open Terms
open Aux

let () =
  if Array.length Sys.argv <= 1 then (
    print_string ("Usage: "^Sys.argv.(0)^" \"program source file\"\n");
    exit 0
  ) else (
    current_file_name :=  Sys.argv.(1);
    (* *)
    try
      (* *)
      let prog = (Infer.normalize_program % Parser.program Lexer.token)
	(Lexing.from_channel (open_in !current_file_name)) in
      pr_program Format.std_formatter prog
    (* *)
    with (Report_toplevel _ | Contradiction _) as exn ->
      pr_exception Format.std_formatter exn; exit 2
  (* *)
  )
