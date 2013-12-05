(** Inferring and normalizing formulas tests for InvarGenT.

    Released under the GNU General Public Licence (version 2 or
    higher), NO WARRANTY of correctness etc. (C) Lukasz Stafiniak 2013
    @author Lukasz Stafiniak lukstafi (AT) gmail.com
    @since Mar 2013
*)
open OUnit
open Infer
open Aux

let tests = "Infer" >::: [

  (* FIXME: write some very simple test -- verifiable by reading. *)
(*
  "constraints: eval" >::
    (fun () ->
      Terms.reset_state ();
      Infer.reset_state ();
      let prog = (normalize_program % Parser.program Lexer.token)
	(Lexing.from_string
"") in
      try
        let preserve, cn = infer_prog_mockup prog in
        (*[* Format.printf "cn:@\n%a@\n" pr_cnstrnt cn; *)
        let cmp_v, uni_v, brs = normalize cn in
        let uni_v v =
          try Hashtbl.find uni_v v with Not_found -> false in
        let sbrs = simplify preserve cmp_v uni_v brs in
        ignore (Format.flush_str_formatter ());
        pr_brs Format.str_formatter sbrs;
        assert_equal ~printer:(fun x -> x)
""
          (Format.flush_str_formatter ());
      with (Terms.Report_toplevel _ | Terms.Contradiction _) as exn ->
        ignore (Format.flush_str_formatter ());
        Terms.pr_exception Format.str_formatter exn;
        assert_failure (Format.flush_str_formatter ())
    );
*)
]
