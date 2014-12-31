/** YACC-type grammar for InvarGenT.

    Released under the GNU General Public Licence (version 2 or
    higher), NO WARRANTY of correctness etc. (C) Lukasz Stafiniak 2013
    @author Lukasz Stafiniak lukstafi (AT) gmail.com
    @since Mar 2013
*/

%{
open Defs
open Terms
open Lexing

let pr i s = Printf.printf "%d-%s;%!" i s

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

let name_sort loc v =
  if List.mem v.[0]
      ['a';'b';'c';'r';'s';'t']
  then Type_sort
  else if List.mem v.[0]
      ['i';'j';'k';'l';'m';'n']
  then Num_sort
  else if List.mem v.[0]
      ['o';'p';'q']
  then Order_sort
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
    TypConstr (None, ety_cn, List.map var_sort pvs, loc) in
  let extydef =
    ValConstr (None, ety_cn, allvs, exphi, [ty], ety_cn, pvs, loc) in
  more_items := extydef :: extydec :: !more_items;
  let ex_sch = allvs, exphi, [ty], ety_cn, pvs in
  all_ex_types := (ety_id, loc) :: !all_ex_types;
  Hashtbl.add sigma ety_cn ex_sch;
  (*[* Format.printf "Parser-existential-ex_types: id=%d@ phi=%a@ ty=%a@\n%!"
    ety_id pr_formula exphi pr_ty ty;
  *]*)
  (* Here in [ety] the variables are free, unlike the
     occurrences in [exphi]. *)
  ety

let unary_typs = parser_unary_typs
let unary_vals = parser_unary_vals
let last_typ = parser_last_typ
let last_num = parser_last_num

let extract_datatyp allvs loc = function
  | TCons (CNam m as n, args) (*[*as ty*]*) ->
    (*[*Format.printf "Parser-extract_datatyp: ty=%a@\n%!" pr_ty ty; *]*)
    let args = match args with
      | [TCons (CNam "Tuple", targs)] when not (Hashtbl.mem unary_typs m) ->
        targs
      | _ -> args in
    let (_, phi), args = Aux.fold_map
      (fun (used, phi) -> function
      | TVar v as t ->
        if not (VarSet.mem v used) then (VarSet.add v used, phi), v
        else
          let v' = next_var (VarSet.union used allvs) (typ_sort t) in
          (VarSet.add v' used, Eqty (t, TVar v', loc)::phi), v'
      | Alien (Num_term (NumDefs.Lin (1,1,v) as t)) ->
        if not (VarSet.mem v used) then (VarSet.add v used, phi), v
        else
          let v' = next_var (VarSet.union used allvs) Num_sort in
          (VarSet.add v' used,
           A (Num_atom NumDefs.(Eq (t, Lin (1,1,v'), loc)))::phi), v'
      | Alien (Order_term (OrderDefs.OVar v as t)) ->
        if not (VarSet.mem v used) then (VarSet.add v used, phi), v
        else
          let v' = next_var (VarSet.union used allvs) Order_sort in
          (VarSet.add v' used,
           A (Order_atom OrderDefs.(Eq (t, OVar v', loc)))::phi), v'
      | t ->
        let v = next_var (VarSet.union used allvs) (typ_sort t) in
        (VarSet.add v used, Eqty (t, TVar v, loc)::phi), v)
      (VarSet.empty, []) args in
    (*[*Format.printf
      "Parser-extract_datatyp: n=%s@ args=%s@ phi=%a@\n%!"
      (cns_str n) (String.concat "," (List.map var_str args))
      pr_formula phi; *]*)
    n, args, phi
  | _ -> raise (Report_toplevel ("Syntax error: expected datatype",
			         Some loc))

let expand_if_syntax_nums is_ex ineqs e1 e2 cond_lc case1_lc case2_lc lc =
  let cases =
    match ineqs with
    | [lhs, rhs] when !parse_if_as_integer ->
      [One case1_lc, ineqs, e1;
       One case2_lc, [NumAdd (rhs, Num (1, dummy_loc), case2_lc), lhs], e2]
    | _ -> [One case1_lc, ineqs, e1; One case2_lc, [], e2] in
  if is_ex
  then (incr extype_id;
        App (ExLam (!extype_id, cases, lc),
             Cons (tuple, [], cond_lc), lc))
  else App (Lam ((), cases, lc), Cons (tuple, [], cond_lc), lc)


let expand_if_syntax_bool is_ex cond e1 e2 case1_lc case2_lc lc =
  let cases =
    [PCons (CNam "True", [], case1_lc), [], e1;
     PCons (CNam "False", [], case2_lc), [], e2] in
  if is_ex
  then (incr extype_id;
        App (ExLam (!extype_id, cases, lc), cond, lc))
  else App (Lam ((), cases, lc), cond, lc)

%}

      /* Ocamlyacc Declarations */
%token LPAREN RPAREN LBRACKET RBRACKET COMMA DOT COLON EQUAL SEMICOLON AND
%token UNDERSCORE EXCLAMATION LOGAND
%token LET REC IN ALL EX
%token <string> UIDENT
%token <string> LIDENT_ABCRST LIDENT_IJKLMN LIDENT_DEFGH
  LIDENT_OPQ LIDENT_UVWXYZ
%token <int> INT
%token <string> STRING
%token <string> DOCUCOMMENT
%token STAR SLASH
%token MINUS
%token PLUS ARROW BAR AS
%token MIN MAX SUCC
%token ZERO TOP
%token FUNCTION EFUNCTION FUN MATCH EMATCH WITH WHEN IF EIF THEN ELSE
%token NUM TYPE ORDER
%token LESSEQUAL
%token ASSERT FALSE TEST
%token DATACONS DATATYPE EXTERNAL LONGARROW DOUBLEARROW
%token EOF

%nonassoc IN
%nonassoc LET AND
%nonassoc below_WITH
%nonassoc FUNCTION EFUNCTION WITH WHEN
%nonassoc THEN
%nonassoc ELSE
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
%left PLUS MINUS
%nonassoc STAR
%nonassoc prec_constr_appl              /* above AS BAR COLONCOLON COMMA */
%nonassoc LPAREN LBRACKET

%start program typ formula cn_branches
%type <Terms.struct_item list> program
%type <Terms.typ> simple_typ typ
%type <Terms.formula> formula
%type <(Terms.formula * Terms.formula) list> cn_branches

/* Grammar follows */
%%
/* Add new sort entries to these rules */
sort:
  | NUM
      { Num_sort }
  | TYPE
      { Type_sort }
  | ORDER
      { Order_sort }
;

alien_term:
  | num_term { Num_term $1 }
  | order_term { Order_term $1 }
;

alien_atom:
  | num_atom { Num_atom $1 }
  | order_atom { Order_atom $1 }
;

/* Add new sort syntax here (most recent domain first) */

/* Linear order sort with bottom and top elements: natural numbers
   with infinity, i.e. countable cardinal numbers. */

order_term:
  | ZERO
    { OrderDefs.Zero }
  | TOP
    { OrderDefs.Top }
  | LIDENT_OPQ
    { OrderDefs.OVar (VNam (Order_sort, $1)) }
  | SUCC order_term
    { OrderDefs.Succ $2 }
;

order_atom:
  | order_term LESSEQUAL order_term
    { OrderDefs.Leq ($1, $3, get_loc ()) }
  | order_term EQUAL MIN LPAREN order_term COMMA order_term RPAREN
    { OrderDefs.EqMin ($1, $5, $7, get_loc ()) }
  | order_term EQUAL MAX LPAREN order_term COMMA order_term RPAREN
    { OrderDefs.EqMax ($1, $5, $7, get_loc ()) }
  | order_term LESSEQUAL MAX LPAREN order_term COMMA order_term RPAREN
    { OrderDefs.LeqMax ($1, $5, $7, get_loc ()) }
  | MIN LPAREN order_term COMMA order_term RPAREN LESSEQUAL order_term
    { OrderDefs.MinLeq ($3, $5, $8, get_loc ()) }
  | order_term EQUAL order_term
    { OrderDefs.Eq ($1, $3, get_loc ()) }
;

/* Numerical sort */

num_term:
  | num_coef
    { let j,k = $1 in NumDefs.Cst (j,k) }
  | num_coef LIDENT_IJKLMN
    { let j,k = $1 in NumDefs.Lin (j,k,VNam (Num_sort, $2)) }
  | MINUS LIDENT_IJKLMN
    { NumDefs.Lin ((-1),1,VNam (Num_sort, $2)) }
  | LIDENT_IJKLMN
    { NumDefs.Lin (1,1,VNam (Num_sort, $1)) }
  | num_term PLUS num_term
    { NumDefs.add $1 $3 }
  | LPAREN num_term RPAREN
    { $2 }
;

num_atom:
  | num_term LESSEQUAL num_term
    { NumDefs.Leq ($1, $3, get_loc ()) }
  | MIN BAR MAX LPAREN num_term COMMA num_term RPAREN
    { NumDefs.Opti ($5, $7, get_loc ()) }
  | MIN BAR BAR MAX LPAREN num_term COMMA num_term RPAREN
    { NumDefs.Subopti ($6, $8, get_loc ()) }
  | num_term EQUAL MIN LPAREN num_term COMMA num_term RPAREN
    { NumDefs.Opti (NumDefs.diff $1 $5, NumDefs.diff $1 $7, get_loc ()) }
  | num_term EQUAL MAX LPAREN num_term COMMA num_term RPAREN
    { NumDefs.Opti (NumDefs.diff $5 $1, NumDefs.diff $7 $1, get_loc ()) }
  | num_term LESSEQUAL MAX LPAREN num_term COMMA num_term RPAREN
    { NumDefs.Subopti (NumDefs.diff $1 $5, NumDefs.diff $1 $7, get_loc ()) }
  | MIN LPAREN num_term COMMA num_term RPAREN LESSEQUAL num_term
    { NumDefs.Subopti (NumDefs.diff $3 $8, NumDefs.diff $5 $8, get_loc ()) }
  | num_term EQUAL num_term
    { NumDefs.Eq ($1, $3, get_loc ()) }

num_coef:
  | INT  { $1, 1 }
  | MINUS INT { ~- $2, 1 }
  | INT SLASH INT { $1, $3 }
  | MINUS INT SLASH INT { ~- $2, $4 }
  | LPAREN INT SLASH INT RPAREN { $2, $4 }
  | LPAREN MINUS INT SLASH INT RPAREN { ~- $3, $5 }


/* Remaining grammar */ 
expr:
  | opt_docucomment LET REC lident EQUAL expr IN expr
      { Letrec ($1, (), $4, $6, $8, get_loc ()) }
  | opt_docucomment LET REC lident simple_pattern_list EQUAL expr IN expr
      { Letrec ($1, (), $4,
                (List.fold_right (fun p e -> Lam ((), [p, [], e], get_loc ()))
	           (List.rev $5) $7),
                $9, get_loc ()) }
  | opt_docucomment LET pattern EQUAL expr IN expr
      { Letin ($1, $3, $5, $7, get_loc ()) }
  | opt_docucomment LET pattern simple_pattern_list EQUAL expr IN expr
      { Letin ($1, $3,
                (List.fold_right (fun p e -> Lam ((), [p, [], e], get_loc ()))
	           (List.rev $4) $6),
               $8, get_loc ()) }
  | opt_docucomment LET REC EQUAL expr IN expr
      { syntax_error "lacking let-rec-binding identifier" 4 }
  | opt_docucomment LET EQUAL expr IN expr
      { syntax_error "lacking let-binding pattern" 3 }
  | opt_docucomment LET REC lident EQUAL expr error
      { unclosed "let" 2 "in" 7 }
  | opt_docucomment LET pattern EQUAL expr error
      { unclosed "let" 2 "in" 6 }
  | FUNCTION opt_bar match_cases %prec below_WITH
      { Lam ((), List.rev $3, get_loc ()) }
  | EFUNCTION opt_bar match_cases %prec below_WITH
      { incr extype_id; ExLam (!extype_id, List.rev $3, get_loc ()) }
  | FUNCTION error
      { syntax_error "function case branches expected" 2 }
  | EFUNCTION error
      { syntax_error "existential function case branches expected" 2 }
  | FUN simple_pattern_list match_action
      { List.fold_right (fun p e -> Lam ((), [p, [], e], get_loc ()))
	  (List.rev $2) $3 }
  | MATCH expr WITH opt_bar match_cases %prec below_WITH
      { App (Lam ((), List.rev $5,
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
  | IF expr_leqs_list THEN expr ELSE expr
      { expand_if_syntax_nums false $2 $4 $6
            {beg_pos = rhs_start_pos 2; end_pos = rhs_end_pos 2}
            {beg_pos = rhs_start_pos 4; end_pos = rhs_end_pos 4}
            {beg_pos = rhs_start_pos 6; end_pos = rhs_end_pos 6}
            (get_loc ()) }
  | EIF expr_leqs_list THEN expr ELSE expr
      { expand_if_syntax_nums true $2 $4 $6
            {beg_pos = rhs_start_pos 2; end_pos = rhs_end_pos 2}
            {beg_pos = rhs_start_pos 4; end_pos = rhs_end_pos 4}
            {beg_pos = rhs_start_pos 6; end_pos = rhs_end_pos 6}
            (get_loc ()) }
  | IF expr THEN expr ELSE expr
      { expand_if_syntax_bool false $2 $4 $6
            {beg_pos = rhs_start_pos 4; end_pos = rhs_end_pos 4}
            {beg_pos = rhs_start_pos 6; end_pos = rhs_end_pos 6}
            (get_loc ()) }
  | EIF expr THEN expr ELSE expr
      { expand_if_syntax_bool true $2 $4 $6
            {beg_pos = rhs_start_pos 4; end_pos = rhs_end_pos 4}
            {beg_pos = rhs_start_pos 6; end_pos = rhs_end_pos 6}
            (get_loc ()) }
  | ASSERT FALSE
      { AssertFalse (get_loc ()) }
  | ASSERT NUM expr LESSEQUAL expr SEMICOLON expr
      { AssertLeq ($3, $5, $7, get_loc ()) }
  | ASSERT TYPE expr EQUAL expr SEMICOLON expr
      { AssertEqty ($3, $5, $7, get_loc ()) }
  | expr PLUS expr
      { NumAdd ($1, $3, get_loc ()) }
  | expr MINUS expr
      { NumAdd ($1,
                NumCoef (-1, $3, {beg_pos = rhs_start_pos 2;
                                  end_pos = rhs_end_pos 3}),
                get_loc ()) }
  | expr error
      { syntax_error "error after expression " 2 }
  | expr STAR expr
      { match $1 with
        | Num (i, _) -> NumCoef (i, $3, get_loc ())
        | _ ->
          raise (Report_toplevel ("Non-constant coefficient",
			          Some (get_loc ()))) }
  | expr SEMICOLON expr
      { App (App (Var (builtin_progseq, get_loc ()),
                  $1, get_loc ()), $3, get_loc ()) }
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
		| Cons (x, [], _), Cons (n, args, _)
		    (* syntax... *)
		    when n = tuple && not (Hashtbl.mem unary_vals x) ->
		    Cons (x, args, loc)
		| Cons (x, [], _), _ -> Cons (x, [ a ], loc)
		| _ -> App(f, a, loc))
	  | f::args -> List.fold_left (fun f a ->
	      App (f, a, {beg_pos = symbol_start_pos ();
			  end_pos = (expr_loc a).end_pos})) f args }
;     
simple_expr:
  | lident
      { Var ($1, get_loc ()) }
  | UIDENT
      { Cons (CNam $1, [], get_loc ()) }
  | INT
      { Num ($1, get_loc ()) }
  | STRING
      { String ($1, get_loc ()) }
  | LPAREN RPAREN
      { Cons (tuple, [], get_loc ()) }
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
      { [$1, [], $2] }
  | match_cases BAR pattern match_action
      { ($3, [], $4) :: $1 }
  |  pattern when_guards match_action
      { [$1, $2, $3] }
  | match_cases BAR pattern when_guards match_action
      { ($3, $4, $5) :: $1 }
;
when_guards:
  | WHEN expr_leqs_list { List.rev $2 }
;
expr_leqs_list:
  | expr LESSEQUAL expr
    { [$1, $3] }
  | expr_leqs_list LOGAND expr LESSEQUAL expr
    { ($3, $5) :: $1 } 
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
      { PCons (tuple, List.rev $1, get_loc ()) }
;
pattern_comma_list:
  | pattern COMMA pattern
      { [ $3 ; $1 ] }
  | pattern_comma_list COMMA pattern
      { $3 :: $1 }
;

simple_pattern:
  lident                                    { PVar ($1, get_loc ()) }
  | UNDERSCORE                              { One (get_loc ())}
  | EXCLAMATION                             { Zero }
  | UIDENT
      { PCons (CNam $1, [], get_loc ()) }
  | LPAREN RPAREN
      { PCons (tuple, [], get_loc ()) }
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
  | LIDENT_ABCRST   { TVar (VNam (Type_sort, $1)) }
  | UIDENT          { TCons (CNam $1, []) }
  | alien_term      { Alien $1 }
  | LPAREN RPAREN
      { TCons (tuple, []) }
  | LPAREN typ RPAREN
      { $2 }
  | LPAREN typ error
      { unclosed "(" 1 ")" 3 }
;

formula:
  | formula_logand_list %prec below_LOGAND
      { List.rev $1 }
  | typ EQUAL typ
      { [Eqty ($1, $3, get_loc ())] }
  | alien_atom
      { [A $1] }
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
  | lident
      { [ VNam (name_sort 1 $1, $1) ] }
  | lident_list lident
      { VNam (name_sort 2 $2, $2) :: $1 }
  | lident_list COMMA lident
      { VNam (name_sort 3 $3, $3) :: $1 }
;

structure_item_raw:
  | opt_docucomment
    DATACONS UIDENT COLON opt_constr_intro typ_star_list LONGARROW typ
      { let n = CNam $3 in
        if List.length $6 = 1 then Hashtbl.add unary_vals n ();
        let vs, phi = $5 in
        let args = List.rev $6 in
        let res = $8 in
        let allvs = VarSet.union (vars_of_list vs)
          (VarSet.union (fvs_formula phi)
             (List.fold_left VarSet.union (fvs_typ res)
                (List.map fvs_typ args))) in
        let c_n, c_args, more_phi =
          extract_datatyp allvs (rhs_loc 7) res in
        let vs = Aux.unique_sorted (c_args @ vs) in
        let phi = more_phi @ phi in
        Hashtbl.add sigma n (vs, phi, args, c_n, c_args);
        ValConstr ($1, n, vs, phi, args, c_n, c_args, get_loc ()) }
  | opt_docucomment
    DATACONS UIDENT COLON opt_constr_intro typ_star_list error
      { unclosed "datacons" 2 "-->" 7 }
  | opt_docucomment
    DATACONS UIDENT COLON opt_constr_intro LONGARROW
      { syntax_error
	  "do not use --> for constructors without arguments" 6 }
  | opt_docucomment DATACONS UIDENT COLON opt_constr_intro typ
      { let n = CNam $3 in
        let vs, phi = $5 in
        let res = $6 in
        let allvs = VarSet.union (vars_of_list vs)
          (VarSet.union (fvs_formula phi) (fvs_typ res)) in
        let c_n, c_args, more_phi =
          extract_datatyp allvs (rhs_loc 6) res in
        let vs = Aux.unique_sorted (c_args @ vs) in
        let phi = more_phi @ phi in
        Hashtbl.add sigma n (vs, phi, [], c_n, c_args);
        ValConstr ($1, n, vs, phi, [], c_n, c_args, get_loc ()) }
  | opt_docucomment
    DATACONS UIDENT COLON opt_constr_intro typ_star_list LONGARROW error
      { syntax_error ("inside the constructor value type") 5 }
  | opt_docucomment DATACONS UIDENT COLON opt_constr_intro error
      { syntax_error ("inside the constructor type") 5 }
  | opt_docucomment DATACONS UIDENT COLON error
      { syntax_error ("<all>, <with>,"^
	  " a star-separated list of types, or a type expected") 5 }
  | opt_docucomment DATACONS COLON
      { syntax_error
	  "lacking constructor identifier" 3 }
  | opt_docucomment DATACONS UIDENT error
      { unclosed "datacons" 2 ":" 4 }
  | opt_docucomment DATATYPE UIDENT COLON sort_star_list
      {
        if List.length ($5) = 1 then Hashtbl.add unary_typs ($3) ();
        TypConstr ($1, CNam ($3), List.rev ($5), get_loc ()) }
  | opt_docucomment EXTERNAL TYPE UIDENT COLON sort_star_list EQUAL STRING
      {
        if List.length ($6) = 1 then Hashtbl.add unary_typs ($4) ();
        PrimTyp ($1, CNam ($4), List.rev ($6), $8, get_loc ()) }
  | opt_docucomment DATATYPE COLON
      { syntax_error
	  "lacking type identifier" 3 }
  | opt_docucomment DATATYPE UIDENT
      { TypConstr ($1, CNam $3, [], get_loc ()) }
  | opt_docucomment EXTERNAL TYPE UIDENT EQUAL STRING
      { PrimTyp ($1, CNam $4, [], $6, get_loc ()) }
  | opt_docucomment
    EXTERNAL lident COLON opt_constr_intro typ EQUAL STRING
      { PrimVal ($1, $3, (fst $5, snd $5, $6), Aux.Left $8, get_loc ()) }
  | opt_docucomment
    EXTERNAL lident COLON opt_constr_intro typ
      { PrimVal ($1, $3, (fst $5, snd $5, $6), Aux.Left $3, get_loc ()) }
  | opt_docucomment
    EXTERNAL LET lident COLON opt_constr_intro typ EQUAL STRING
      { PrimVal ($1, $4, (fst $6, snd $6, $7), Aux.Right $9, get_loc ()) }
  | opt_docucomment EXTERNAL COLON
      { syntax_error
	  "lacking external binding identifier" 3 }
  | opt_docucomment LET REC lident opt_sig_typ_scheme EQUAL expr opt_tests
      { LetRecVal ($1, $4, $7, $5, $8, get_loc ()) }
  | opt_docucomment LET REC lident simple_pattern_list
    opt_sig_typ_scheme EQUAL expr opt_tests
      { LetRecVal ($1, $4,
                   (List.fold_right
                      (fun p e -> Lam ((), [p, [], e], get_loc ()))
	              (List.rev $5) $8),
                   $6, $9, get_loc ()) }
  | opt_docucomment LET REC EQUAL
      { syntax_error
	  "lacking global let-rec-binding identifier" 4 }
  | opt_docucomment LET pattern opt_sig_typ_scheme EQUAL expr
      { LetVal ($1, $3, $6, $4, get_loc ()) }
  | opt_docucomment LET pattern simple_pattern_list
    opt_sig_typ_scheme EQUAL expr
      { LetVal ($1, $3,
                   (List.fold_right
                      (fun p e -> Lam ((), [p, [], e], get_loc ()))
	              (List.rev $4) $7),
                $5, get_loc ()) }
  | opt_docucomment LET EQUAL
      { syntax_error
	  "lacking global let-binding identifier" 3 }
;
opt_docucomment:
  | /* empty */
      { None }
  | DOCUCOMMENT
      { Some $1 }
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
  | typ_star_list STAR typ
      { $3 :: $1 }
;

sort_star_list:
  | sort           { [ $1 ] }
  | sort_star_list STAR sort
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

lident:
  | LIDENT_ABCRST { $1 }
  | LIDENT_IJKLMN { $1 }
  | LIDENT_DEFGH  { $1 }
  | LIDENT_OPQ    { $1 }
  | LIDENT_UVWXYZ { $1 }
