(** Main executable for InvarGenT.

    Released under the GNU General Public Licence (version 2 or
    higher), NO WARRANTY of correctness etc. (C) Lukasz Stafiniak 2013
    @author Lukasz Stafiniak lukstafi (AT) gmail.com
    @since Mar 2013
*)
let version = "1.2"

(** Annotate [let-in] nodes in fallback mode of .ml generation. *)
let let_in_fallback = ref false

open Defs
open Terms
open Aux

let solver ~new_ex_types ~preserve cn =
  let q_ops, cn = Infer.prenexize cn in
  let exty_res_of_chi, brs = Infer.normalize q_ops cn in
  let brs = Infer.simplify preserve q_ops brs in
  Invariants.solve q_ops new_ex_types exty_res_of_chi brs

let process_file ?(do_sig=false) ?(do_ml=false)
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
  if do_ml && verif_ml then
    let cmd = "ocamlc -w -25 -c "^base^".ml" in
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

let main () =
  let do_ml = ref true
  and do_sig = ref true
  and verif_ml = ref true
  and full_annot = ref false in
  let num_is_mod s =
    OCaml.num_is := s; OCaml.num_is_mod := true in
  let cli = [
    "-inform", Arg.Set Infer.inform_toplevel,
    "Print type schemes of toplevel definitions as they are inferred";
    "-no_sig", Arg.Clear do_sig,
    "Do not generate the `.gadti` file";
    "-no_ml", Arg.Clear do_ml,
    "Do not generate the `.ml` file";
    "-no_verif", Arg.Clear verif_ml,
    "Do not call `ocamlc -c` on the generated `.ml` file";
    "-num_is", Arg.Set_string OCaml.num_is,
    "The exported type for which `Num` is an alias (default `int`); apply `s_of_int` to numerals.";
    "-num_is_mod", Arg.String num_is_mod,
    "The exported type for which `Num` is an alias (default `int`); apply `S.of_int` to numerals.";
    "-full_annot", Arg.Set full_annot,
    "Annotate the `function` and `let..in` nodes in generated OCaml code";
    "-keep_assert_false", Arg.Clear OCaml.drop_assert_false,
    "Keep `assert false` clauses in exported code";
    "-term_abduction_timeout", Arg.Set_int Abduction.timeout_count,
    "Limit on term simple abduction steps (default 700)";
    "-term_abduction_fail", Arg.Set_int Abduction.fail_timeout_count,
    "Limit on backtracking steps in term joint abduction (default 4)";
    "-no_alien_prem", Arg.Set Abduction.no_alien_prem,
    "Do not include alien (e.g. numerical) premise info in term abduction";
    "-early_num_abduction", Arg.Set NumS.early_num_abduction,
    "Include recursive branches in numerical abduction from the start";
    "-early_postcond_abd", Arg.Set Invariants.early_postcond_abd,
    "Include postconditions from recursive calls in abduction from the start";
    "-num_abduction_rotations", Arg.Set_int NumS.abd_rotations,
    "Numerical abduction: coefficients from +/- 1/N to +/- N (default 3)";
    "-num_prune_at", Arg.Set_int NumS.abd_prune_at,
    "Keep less than N elements in abduction sums (default 6)";
    "-num_abduction_timeout", Arg.Set_int NumS.abd_timeout_count,
    "Limit on numerical simple abduction steps (default 1000)";
    "-num_abduction_fail", Arg.Set_int NumS.abd_fail_timeout_count,
    "Limit on backtracking steps in numerical joint abduction (default 10)";
    "-no_num_abduction", Arg.Set Abduction.no_num_abduction,
    "Turn off numerical abduction; will not ensure correctness.";
    "-disjelim_rotations", Arg.Set_int NumS.disjelim_rotations,
    "Disjunction elimination: check coefficients from 1/N (default 3)";
    "-iterations_timeout", Arg.Set_int Invariants.timeout_count,
    "Limit on main algorithm iterations (default 7)";
    "-weaker_pruning", Arg.Clear NumS.int_pruning,
    "Do not assume integers as the numerical domain when pruning \
     redundant atoms.";
    "-stronger_pruning", Arg.Set NumS.strong_int_pruning,
    "Prune atoms that force a numerical variable to a single value \
     under certain conditions; exclusive with -weaker_pruning.";
    "-richer_answers", Arg.Set Abduction.richer_answers,
    "Keep some equations in term abduction answers even if redundant.";
    "-more_existential", Arg.Set DisjElim.more_existential,
    "More general invariant at expense of more existential postcondition.";
    "-passing_ineq_trs", Arg.Set NumS.passing_ineq_trs,
    "Include inequalities in conclusion when solving numerical abduction";
    "-not_annotating_fun", Arg.Clear Infer.annotating_fun,
    "Do not keep information for annotating `function` nodes";
    "-annotating_letin", Arg.Set Infer.annotating_letin,
    "Keep information for annotating `let..in` nodes";
    "-let_in_fallback", Arg.Set let_in_fallback,
    "Annotate `let..in` nodes in fallback mode of .ml generation";
  ] in
  let fname = ref "" in
  let anon_fun f = fname := f in
  let msg = "InvarGenT version "^version^
              ". Usage: "^Sys.argv.(0)^"[OPTIONS] source.gadt" in
  Arg.parse (Arg.align cli) anon_fun msg;
  try
    ignore
      (process_file !fname ~do_sig:!do_sig ~do_ml:!do_ml
         ~verif_ml:!verif_ml ~full_annot:!full_annot)
  with (Report_toplevel _ | Contradiction _ | NoAnswer _) as exn ->
    Format.printf "%a@\n%!" pr_exception exn;
    if !Abduction.abd_timeout_flag then Format.printf
        "Perhaps increase the -term_abduction_timeout parameter.@\n%!";
    if !Abduction.abd_fail_flag then Format.printf
        "Perhaps increase the -term_abduction_fail parameter.@\n%!";
    if !NumS.abd_timeout_flag then Format.printf
        "Perhaps increase the -num_abduction_timeout parameter.@\n%!";
    if !NumS.abd_fail_flag then Format.printf
        "Perhaps increase the -num_abduction_fail parameter.@\n%!";
    if !Invariants.timeout_flag then Format.printf
        "Perhaps increase the -iterations_timeout parameter or try the \
         -more_existential option.@\n%!";
    if !Invariants.unfinished_postcond_flag then Format.printf
        "Perhaps some definition is used with requirements on@ its \
         inferred postcondition not warranted by the definition.@\n%!";
    exit 2
  

let () =
  let executable = Filename.basename Sys.executable_name in
  let chop f =
    try Filename.chop_extension f with Invalid_argument _ -> f in
  let executable = chop (chop executable) in
  if executable <> "Tests" && executable <> "InvarGenTTest"
  then main ()
