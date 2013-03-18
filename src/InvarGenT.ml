(** Main executable for InvarGenT.

    Released under the GNU General Public Licence (version 2 or
    higher), NO WARRANTY of correctness etc. (C) Lukasz Stafiniak 2013
    @author Lukasz Stafiniak <lukstafi@gmail.com>
    @since Mar 2013
*)
open Terms

let () =
  if Array.length Sys.argv <= 1 then (
    print_string ("Usage: "^Sys.argv.(0)^" \"program source file\"\n");
    exit 0
  ) else (
    current_file_name :=  Sys.argv.(1);
    (* *)
    try
      (* *)
      let prog = Parser.program Lexer.token
	(Lexing.from_channel (open_in !current_file_name)) in
      pr_program Format.std_formatter prog
    (* *)
    with
    | Report_toplevel (what, None) ->
      Printf.printf "%!\n%s\n%!" what; exit (2)
    | Report_toplevel (what, Some where) ->
      pr_loc_long Format.std_formatter where;
      Printf.printf "%!\n%s\n%!" what;
      exit (2)
    | Infer.Contradiction (what, None, where) ->
      pr_loc_long Format.std_formatter where;
      Printf.printf "%!\n%s\n%!" what;
      exit (2)
    | Infer.Contradiction (what, Some (ty1, ty2), where) ->
      pr_loc_long Format.std_formatter where;
      Format.printf "%!\n%s\ntypes involved:\n%a\n%a\n%!"
        what (pr_ty false) ty1 (pr_ty false) ty2;
      exit (2)
  (* *)
  )
