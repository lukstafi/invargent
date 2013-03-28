{
  open Parser
  open Lexing
  let incr_lineno lexbuf =
    let pos = lexbuf.lex_curr_p in
    lexbuf.lex_curr_p <- { pos with
      pos_lnum = pos.pos_lnum + 1;
      pos_bol = pos.pos_cnum;
    }
}
let digit = ['0'-'9']
let lowercase = ['a'-'z']
let uppercase = ['A'-'Z']
let ident_body = lowercase | uppercase | digit | '_'
rule token = parse
  | [' ' '\t']	{ token lexbuf }
  | '\n'	{ incr_lineno lexbuf; token lexbuf }
  | digit+ as num
		{ INT (int_of_string num) }
  | '+'		{ PLUS }
  | '*'		{ MULTIPLY }
  | '('		{ LPAREN }
  | ')'		{ RPAREN }
  | '['		{ LBRACKET }
  | ']'		{ RBRACKET }
  | '='		{ EQUAL }
  | ','		{ COMMA }
  | '.'		{ DOT }
  | ':'		{ COLON }
  | "function"  { FUNCTION }
  | "fun"       { FUN }
  | "match"     { MATCH }
  | "ematch"    { EMATCH }
  | "with"      { WITH }
  | "num"       { NUM }
  | "type"      { TYPE }
  | "<="        { LESSEQUAL }
  | "≤"         { LESSEQUAL }
  | ';'         { SEMICOLON }
  | "assert"    { ASSERT }
  | "false"     { FALSE }
  | "test"      { TEST }
  | "and"       { AND }
  | "&&"        { LOGAND }
  | "∧"         { LOGAND }
  | "ex"        { EX }
  | "\\E"       { EX }
  | "exists"    { EX }
  | "∃"         { EX }
  | "all"       { ALL }
  | "\\A"       { ALL }
  | "∀"         { ALL }
  | "newcons"   { NEWCONS }
  | "newtype"   { NEWTYPE }
  | "external"  { EXTERNAL }
  | "-->"       { LONGARROW }
  | "⟶"        { LONGARROW }
  | '_'		{ UNDERSCORE }
  | '|'		{ BAR }
  | '!'		{ EXCLAMATION }
  | "let"       { LET }
  | "rec"       { REC }
  | "and"       { AND }
  | "in"        { IN }
  | "as"        { AS }
  | "->"        { ARROW }
  | "→"         { ARROW }
  | (lowercase ident_body*) as id
      { LIDENT id }
  | (uppercase ident_body*) as id
      { UIDENT id }
  | eof		{ EOF }
