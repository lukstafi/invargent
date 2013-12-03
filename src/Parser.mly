/** YACC-type grammar for InvarGenT.

    Released under the GNU General Public Licence (version 2 or
    higher), NO WARRANTY of correctness etc. (C) Lukasz Stafiniak 2013
    @author Lukasz Stafiniak lukstafi (AT) gmail.com
    @since Mar 2013
*/

%{
open Terms
open Lexing

let get_loc () =
  try
    {beg_pos = symbol_start_pos (); end_pos = symbol_end_pos ()}
  with Invalid_argument _ -> dummy_loc

let rhs_loc i = {beg_pos = rhs_start_pos i; end_pos = rhs_end_pos i}

let unclosed opening_name opening_num closing_name closing_num =
  ignore (Format.flush_str_formatter ());
  Format.fprintf Format.str_formatter
    "@[<0>Syntax error:@ unclosed@ \"%s\"@ at@ %a:@ \"%s\" expected@ at@ %a@]"
    opening_name pr_loc (rhs_loc opening_num)
    closing_name pr_loc (rhs_loc closing_num);
  raise (Report_toplevel
	    (Format.flush_str_formatter (),
	    Some (rhs_loc closing_num)))

let syntax_error what where =
    raise (Report_toplevel ("Syntax error: "^what,
			   Some (rhs_loc where)))

let parse_error s =
  Format.printf
    "@[<2>%s@ %a@]@." s pr_loc (get_loc ())

let name_sort loc v =
  if List.mem v.[0]
      ['a';'b';'c';'r';'s';'t']
  then Type_sort
  else if List.mem v.[0]
      ['i';'j';'k';'l';'m';'n']
  then Num_sort
  else syntax_error
    ("type variable <"^v^"> starts with a letter reserved for a future sort")
    loc

let more_items = parser_more_items
let existential evs exphi ty loc =
  let allvs = VarSet.union (fvs_typ ty) (fvs_formula exphi) in
  let allvs = VarSet.diff allvs (vars_of_list [delta; delta']) in
  let pvs = VarSet.elements (VarSet.diff allvs (vars_of_list evs)) in
  let allvs = VarSet.elements allvs in
  let targs = List.map (fun v -> TVar v) pvs in
  let ety_id = incr extype_id; !extype_id in
  assert (not (List.mem_assoc ety_id !all_ex_types));
  let ety_cn = Extype ety_id in
  let ety = TCons (ety_cn, targs) in
  let extydec =
    TypConstr (ety_cn, List.map var_sort pvs, loc) in
  let extydef =
    ValConstr (ety_cn, allvs, exphi, [ty], ety_cn, pvs, loc) in
  more_items := extydef :: extydec :: !more_items;
  let ex_sch = allvs, exphi, [ty], ety_cn, pvs in
  all_ex_types := (ety_id, loc) :: !all_ex_types;
  Hashtbl.add sigma ety_cn ex_sch;
  (* Format.printf "Parser-existential-ex_types: id=%d@ phi=%a@ ty=%a@\n%!"
    ety_id pr_formula exphi (pr_ty false) ty;
  * *)
  (* Here in [ety] the variables are free, unlike the
     occurrences in [exphi]. *)
  ety

let unary_typs = parser_unary_typs
let unary_vals = parser_unary_vals
let last_typ = parser_last_typ
let last_num = parser_last_num

let extract_datatyp allvs loc = function
  | TCons (CNam m as n, args) ->
    let args = match args with
      | [TCons (CNam "Tuple", targs)] when not (Hashtbl.mem unary_typs m) ->
        targs
      | _ -> args in
    let (_, phi), args = Aux.fold_map
      (fun (used, phi) -> function
      | TVar v as t ->
        if not (VarSet.mem v used) then (VarSet.add v used, phi), v
        else
          let v' = next_var allvs (typ_sort t) in
          (VarSet.add v' used, Eqty (t, TVar v', loc)::phi), v'
      | t ->
        let v = next_var allvs (typ_sort t) in
        (VarSet.add v used, Eqty (t, TVar v, loc)::phi), v)
      (VarSet.empty, []) args in
    n, args, phi
  | _ -> raise (Report_toplevel ("Syntax error: expected datatype",
			         Some loc))

%}

      /* Ocamlyacc Declarations */
%token LPAREN RPAREN LBRACKET RBRACKET COMMA DOT COLON EQUAL SEMICOLON AND
%token UNDERSCORE EXCLAMATION LOGAND
%token LET REC IN ALL EX
%token <string> UIDENT
%token <string> LIDENT
%token <int> INT
%token PLUS MULTIPLY ARROW BAR AS
%token FUNCTION EFUNCTION FUN MATCH EMATCH WITH
%token NUM TYPE
%token LESSEQUAL
%token ASSERT FALSE TEST
%token NEWCONS NEWTYPE EXTERNAL LONGARROW DOUBLEARROW
%token EOF

%nonassoc IN
%nonassoc LET AND
%nonassoc below_WITH
%nonassoc FUNCTION EFUNCTION WITH
%right ARROW
%nonassoc AS
%nonassoc BAR
%left SEMICOLON
%right BARBAR
%nonassoc below_LOGAND
%nonassoc LOGAND
%nonassoc below_COMMA
%left COMMA
%nonassoc DOT
%left PLUS
%nonassoc MULTIPLY
%nonassoc prec_constr_appl              /* above AS BAR COLONCOLON COMMA */
%nonassoc LPAREN LBRACKET

%start program typ formula cn_branches
%type <Terms.struct_item list> program
%type <Terms.typ> simple_typ typ
%type <Terms.formula> formula
%type <(Terms.formula * Terms.formula) list> cn_branches

/* Grammar follows */
%%
expr:
  | LET REC LIDENT EQUAL expr IN expr
      { Letrec ((), $3, $5,
	       (* {beg_pos = rhs_start_pos 2; FIXME: body loc
		  end_pos = rhs_end_pos 5}, *) $7, get_loc ()) }
  | LET pattern EQUAL expr IN expr
      { Letin ($2, (* rhs_loc 3, *) $4, $6, get_loc ()) }
  | LET REC EQUAL expr IN expr
      { syntax_error "lacking let-rec-binding identifier" 3 }
  | LET EQUAL expr IN expr
      { syntax_error "lacking let-binding pattern" 2 }
  | LET REC LIDENT EQUAL expr error
      { unclosed "let" 1 "in" 6 }
  | LET pattern EQUAL expr error
      { unclosed "let" 1 "in" 5 }
  | FUNCTION opt_bar match_cases %prec below_WITH
      { Lam (List.rev $3, get_loc ()) }
  | EFUNCTION opt_bar match_cases %prec below_WITH
      { incr extype_id; ExLam (!extype_id, List.rev $3, get_loc ()) }
  | FUNCTION error
      { syntax_error "function case branches expected" 2 }
  | EFUNCTION error
      { syntax_error "existential function case branches expected" 2 }
  | FUN simple_pattern_list match_action
      { List.fold_right (fun p e -> Lam ([p, e], get_loc ()))
	  (List.rev $2) $3 }
  | MATCH expr WITH opt_bar match_cases %prec below_WITH
      { App (Lam (List.rev $5,
                  {beg_pos = rhs_start_pos 3; end_pos = rhs_end_pos 5}),
             $2, get_loc ()) }
  | EMATCH expr WITH opt_bar match_cases %prec below_WITH
      { incr extype_id;
        App (ExLam (!extype_id, List.rev $5,
                  {beg_pos = rhs_start_pos 3; end_pos = rhs_end_pos 5}),
             $2, get_loc ()) }
  | MATCH expr error
      { unclosed "match" 1 "with" 3 }
  | EMATCH expr error
      { unclosed "ematch" 1 "with" 3 }
  | ASSERT FALSE
      { AssertFalse (get_loc ()) }
  | ASSERT expr LESSEQUAL expr SEMICOLON expr
      { AssertLeq ($2, $4, $6, get_loc ()) }
  | ASSERT EQUAL TYPE expr expr SEMICOLON expr
      { AssertEqty ($4, $5, $7, get_loc ()) }
  | expr_comma_list %prec below_COMMA
      { Cons (tuple, (List.rev $1), get_loc ()) }
  | simple_expr
      { $1 }
  | simple_expr_list
      { let loc = get_loc () in
	match List.rev $1 with
	  | [] | [_] -> assert false
	  | [f; a] ->
	      (match f, a with
		| Cons (x, [], _), Cons (tuple, args, _)
		    (* syntax... *)
		    when not (Hashtbl.mem unary_vals x) ->
		    Cons (x, args, loc)
		| Cons (x, [], _), _ -> Cons (x, [ a ], loc)
		| _ -> App(f, a, loc))
	  | f::args -> List.fold_left (fun f a ->
	      App (f, a, {beg_pos = symbol_start_pos ();
			  end_pos = (expr_loc a).end_pos})) f args }
;     
simple_expr:
  | LIDENT
      { Var ($1, get_loc ()) }
  | UIDENT
      { Cons (CNam $1, [], get_loc ()) }
  | INT
      { Num ($1, get_loc ()) }
  | LPAREN expr RPAREN
      { $2 }
  | LPAREN expr error
      { unclosed "(" 1 ")" 3 }
;
simple_expr_list:
  | simple_expr simple_expr
      { [ $2 ; $1 ] }
  | simple_expr_list simple_expr
      { $2 :: $1 }
;
expr_comma_list:
  | expr_comma_list COMMA expr
      { $3 :: $1 }
  | expr COMMA expr
      { [ $3; $1 ] }
;
expr_semicolon_list:
  | expr_semicolon_list SEMICOLON expr
      { $3 :: $1 }
  | expr
      { [ $1 ] }
;

match_cases:
  |  pattern match_action
      { [$1, $2] }
  | match_cases BAR pattern match_action
      { ($3, $4) :: $1 }
;
match_action:
  | ARROW expr %prec below_WITH
      { $2 }
  | error
      { syntax_error "-> expected (function or match action)" 1 }
;

pattern:
  | simple_pattern
      { $1 }
  | UIDENT pattern %prec prec_constr_appl
      { match $2 with
	| PCons (CNam "Tuple", args, _)
	    (* syntax... *)
	    when not (Hashtbl.mem unary_vals (CNam $1)) ->
	    PCons (CNam $1, args, get_loc ())
	| _ -> PCons (CNam $1, [ $2 ], get_loc ()) }
  | pattern AS pattern
      { PAnd ($1, $3, get_loc ()) }
  | pattern_comma_list  %prec below_COMMA
      { PCons (CNam "Tuple", List.rev $1, get_loc ()) }
;
pattern_comma_list:
  | pattern COMMA pattern
      { [ $3 ; $1 ] }
  | pattern_comma_list COMMA pattern
      { $3 :: $1 }
;

simple_pattern:
  LIDENT                                    { PVar ($1, get_loc ()) }
  | UNDERSCORE                              { One (get_loc ())}
  | EXCLAMATION                             { Zero }
  | UIDENT
      { PCons (CNam $1, [], get_loc ()) }
  | LPAREN pattern RPAREN
      { $2 }
;
simple_pattern_list:
  | simple_pattern
      { [ $1 ] }
  | simple_pattern_list simple_pattern
      { $2 :: $1 }
;

typ:
  | EX lident_list DOT typ
      { existential $2 [] $4 (get_loc ()) }
  | EX lident_list LBRACKET formula RBRACKET DOT typ
      { existential $2 $4 $7 (get_loc ()) }
  | simple_typ
      { $1 }
  | typ ARROW typ
      { Fun ($1, $3) }
  | typ_comma_list %prec below_COMMA
      { TCons (tuple, List.rev $1) }
  | UIDENT simple_typ
      { match $2 with
	| TCons (CNam "Tuple", args)
	    (* syntax... *)
	    when not (Hashtbl.mem unary_typs $1) ->
	    TCons (CNam $1, args)
	| _ -> TCons (CNam $1, [ $2 ]) }
;

typ_comma_list:
  | typ COMMA typ
      { [ $3 ; $1 ] }
  | typ_comma_list COMMA typ
      { $3 :: $1 }
;

simple_typ:
  | simple_typ PLUS simple_typ
      { ty_add $1 $3 }
  | LIDENT   { TVar (VNam (name_sort 1 $1, $1)) }
  | UIDENT   { TCons (CNam $1, []) }
  | INT      { NCst $1 }
  | LPAREN typ RPAREN
      { $2 }
  | LPAREN typ error
      { unclosed "(" 1 ")" 3 }
;

sort:
  | NUM
      { Num_sort }
  | TYPE
      { Type_sort }
;

formula:
  | formula_logand_list %prec below_LOGAND
      { List.rev $1 }
  | typ LESSEQUAL typ
      { [Leq ($1, $3, get_loc ())] }
  | typ EQUAL typ
      { [Eqty ($1, $3, get_loc ())] }
  | FALSE    { [CFalse (get_loc ())] }
;

formula_logand_list:
  | formula LOGAND formula
      { $3 @ $1 }
  | formula_logand_list LOGAND formula
      { $3 @ $1 }
;

cn_branch:
  | DOUBLEARROW { [], [] }
  | DOUBLEARROW formula { [], $2 }
  | formula DOUBLEARROW { $1, [] }
  | formula DOUBLEARROW formula { $1, $3 }

cn_branches_list:
  | cn_branch { [$1] }
  | cn_branches_list BAR cn_branch { $3 :: $1 }

cn_branches:
  | cn_branches_list EOF { List.rev $1 }

opt_constr_intro:
  | ALL lident_list DOT
      { List.rev $2, [] }
  | ALL lident_list error
      { unclosed "all" 1 "." 3 }
  | ALL lident_list LBRACKET formula RBRACKET DOT
      { List.rev $2, $4 }
  | ALL lident_list LBRACKET formula RBRACKET error
      { unclosed "all" 1 "." 6 }
  | ALL lident_list LBRACKET formula error
      { unclosed "[" 3 "]" 5 }
  | ALL lident_list error
      { unclosed "all" 1 "." 3 }
  | ALL error
      { syntax_error "variables or [ expected" 2 }
  | /* empty */
      { [], [] }
;

lident_list:
  | LIDENT
      { [ VNam (name_sort 1 $1, $1) ] }
  | lident_list LIDENT
      { VNam (name_sort 2 $2, $2) :: $1 }
  | lident_list COMMA LIDENT
      { VNam (name_sort 3 $3, $3) :: $1 }
;

structure_item_raw:
  | NEWCONS UIDENT COLON opt_constr_intro typ_star_list LONGARROW typ
      { let n = CNam $2 in
        if List.length $5 = 1 then Hashtbl.add unary_vals n ();
        let vs, phi = $4 in
        let args = List.rev $5 in
        let res = $7 in
        let allvs = VarSet.union (vars_of_list vs)
          (VarSet.union (fvs_formula phi)
             (List.fold_left VarSet.union (fvs_typ res)
                (List.map fvs_typ args))) in
        let c_n, c_args, more_phi =
          extract_datatyp allvs (rhs_loc 7) res in
        let vs = Aux.unique_sorted (c_args @ vs) in
        let phi = more_phi @ phi in
        Hashtbl.add sigma n (vs, phi, args, c_n, c_args);
        ValConstr (n, vs, phi, args, c_n, c_args, get_loc ()) }
  | NEWCONS UIDENT COLON opt_constr_intro typ_star_list error
      { unclosed "newcons" 1 "-->" 6 }
  | NEWCONS UIDENT COLON opt_constr_intro LONGARROW
      { syntax_error
	  "do not use --> for constructors without arguments" 5 }
  | NEWCONS UIDENT COLON opt_constr_intro typ
      { let n = CNam $2 in
        let vs, phi = $4 in
        let res = $5 in
        let allvs = VarSet.union (vars_of_list vs)
          (VarSet.union (fvs_formula phi) (fvs_typ res)) in
        let c_n, c_args, more_phi =
          extract_datatyp allvs (rhs_loc 5) res in
        let vs = Aux.unique_sorted (c_args @ vs) in
        let phi = more_phi @ phi in
        Hashtbl.add sigma n (vs, phi, [], c_n, c_args);
        ValConstr (n, vs, phi, [], c_n, c_args, get_loc ()) }
  | NEWCONS UIDENT COLON opt_constr_intro typ_star_list LONGARROW error
      { syntax_error ("inside the constructor value type") 4 }
  | NEWCONS UIDENT COLON opt_constr_intro error
      { syntax_error ("inside the constructor type") 4 }
  | NEWCONS UIDENT COLON error
      { syntax_error ("<all>, <with>,"^
	  " a star-separated list of types, or a type expected") 4 }
  | NEWCONS COLON
      { syntax_error
	  "lacking constructor identifier" 2 }
  | NEWCONS UIDENT error
      { unclosed "newcons" 1 ":" 3 }
  | NEWTYPE UIDENT COLON sort_star_list
      {
        if List.length ($4) = 1 then Hashtbl.add unary_typs ($2) ();
        TypConstr (CNam ($2), List.rev ($4), get_loc ()) }
  | NEWTYPE COLON
      { syntax_error
	  "lacking type identifier" 2 }
  | NEWTYPE UIDENT
      { TypConstr (CNam $2, [], get_loc ()) }
  | EXTERNAL LIDENT COLON opt_constr_intro typ
      { PrimVal ($2, (fst $4, snd $4, $5), get_loc ()) }
  | EXTERNAL COLON
      { syntax_error
	  "lacking external binding identifier" 2 }
  | LET REC LIDENT opt_sig_typ_scheme EQUAL expr opt_tests
      { LetRecVal ($3, $6, $4, $7, get_loc ()) }
  | LET REC EQUAL
      { syntax_error
	  "lacking global let-rec-binding identifier" 3 }
  | LET pattern opt_sig_typ_scheme EQUAL expr opt_tests
      { LetVal ($2, $5, $3, $6, get_loc ()) }
  | LET EQUAL
      { syntax_error
	  "lacking global let-binding identifier" 3 }
;
opt_sig_typ_scheme:
  | /* empty */
      { None }
  | COLON opt_constr_intro typ
      { Some (fst $2, snd $2, $3) }
;
opt_tests:
  | /* empty */
      { [] }
  | TEST expr_semicolon_list
      { List.rev $2 }
;
structure_item:
  | structure_item_raw
      { let res = List.rev !more_items @ [ $1 ] in more_items := []; res }

typ_star_list:
  | typ
      { [ $1 ] }
  | typ_star_list MULTIPLY typ
      { $3 :: $1 }
;

sort_star_list:
  | sort           { [ $1 ] }
  | sort_star_list MULTIPLY sort
      { $3 :: $1 }
  | error
      { syntax_error "unrecognized sort" 1 }
;

opt_bar:
  | /* empty */      { () }
  | BAR              { () }
;

structure_item_list:
  | structure_item    { [ $1 ] }
  | structure_item_list structure_item { $2 :: $1 }
;

program:
  | EOF              { [] }
  | structure_item_list EOF { List.concat (List.rev $1) }
;

