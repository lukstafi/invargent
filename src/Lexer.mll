{
  open Parser
  open Defs
  open Terms
  open Lexing
  let incr_lineno lexbuf =
    let pos = lexbuf.lex_curr_p in
    lexbuf.lex_curr_p <- { pos with
      pos_lnum = pos.pos_lnum + 1;
      pos_bol = pos.pos_cnum;
    }
  let string_buff = Buffer.create 256
  let string_start_loc = ref dummy_loc
  let comment_start_loc = ref []
  let in_comment () = !comment_start_loc <> []
  let is_in_string = ref false
  let in_string () = !is_in_string

  let char_for_backslash = function
    | 'n' -> '\010'
    | 'r' -> '\013'
    | 'b' -> '\008'
    | 't' -> '\009'
    | c   -> c

  let curr_loc lexbuf =
    {beg_pos = lexbuf.lex_curr_p; end_pos = lexbuf.lex_curr_p}

  let char_for_decimal_code lexbuf i =
    let c = 100 * (Char.code(Lexing.lexeme_char lexbuf i) - 48) +
              10 * (Char.code(Lexing.lexeme_char lexbuf (i+1)) - 48) +
              (Char.code(Lexing.lexeme_char lexbuf (i+2)) - 48) in
    if (c < 0 || c > 255) then
      if in_comment ()
      then 'x'
      else raise (Report_toplevel
                    ("Lexer error: illegal escape sequence",
		     Some (curr_loc lexbuf)))
    else Char.chr c
        
  let char_for_hexadecimal_code lexbuf i =
    let d1 = Char.code (Lexing.lexeme_char lexbuf i) in
    let val1 = if d1 >= 97 then d1 - 87
      else if d1 >= 65 then d1 - 55
      else d1 - 48 in
    let d2 = Char.code (Lexing.lexeme_char lexbuf (i+1)) in
    let val2 = if d2 >= 97 then d2 - 87
      else if d2 >= 65 then d2 - 55
      else d2 - 48 in
    Char.chr (val1 * 16 + val2)

  let store_lexeme lexbuf =
    let s = Lexing.lexeme lexbuf in
    Buffer.add_string string_buff s
}
let digit = ['0'-'9']
let lowercase = ['a'-'z']
let uppercase = ['A'-'Z']
let ident_body = lowercase | uppercase | digit | '_' | '''
let newline = '\n' | "\r\n"
rule token = parse
  | [' ' '\t']	{ token lexbuf }
  | newline     { incr_lineno lexbuf; token lexbuf }
  | ('-' digit+) as num
		{ INT (int_of_string num) }
  | digit+ as num
		{ INT (int_of_string num) }
  | "+="	{ PLUSEQUAL }
  | '+'		{ PLUS }
  | '-'		{ MINUS }
  | '*'		{ STAR }
  | '/'		{ SLASH }
  | '('		{ LPAREN }
  | ')'		{ RPAREN }
  | '['		{ LBRACKET }
  | ']'		{ RBRACKET }
  | '='		{ EQUAL }
  | ','		{ COMMA }
  | ".."	{ DOTDOT }
  | '.'		{ DOT }
  | ':'		{ COLON }
  | "function"  { FUNCTION }
  | "efunction" { EFUNCTION }
  | "fun"       { FUN }
  | "match"     { MATCH }
  | "ematch"    { EMATCH }
  | "when"      { WHEN }
  | "with"      { WITH }
  | "if"        { IF }
  | "eif"       { EIF }
  | "then"      { THEN }
  | "else"      { ELSE }
  | "num"       { NUM }
  | "order"     { ORDER }
  | "type"      { TYPE }
  | "zero"      { ZERO }
  | "top"       { TOP }
  | "<="        { LESSEQUAL }
  | "≤"         { LESSEQUAL }
  | ';'         { SEMICOLON }
  | "assert"    { ASSERT }
  | "false"     { FALSE }
  | "runtime_failure" { RUNTIME_FAILURE }
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
  | "datacons"   { DATACONS }
  | "datatype"   { DATATYPE }
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
  | "min"       { MIN }
  | "max"       { MAX }
  | "succ"       { SUCC }
  | "==>"       { DOUBLEARROW }
  | "⟹"        { DOUBLEARROW }
  | "(**"
      { let start_loc = curr_loc lexbuf  in
        comment_start_loc := [start_loc];
        Buffer.reset string_buff;
        let (* end_loc *) _ = comment lexbuf in
        let s = Buffer.contents string_buff in
        Buffer.reset string_buff;
        DOCUCOMMENT s
      }
  | "(*"
      { let start_loc = curr_loc lexbuf  in
        comment_start_loc := [start_loc];
        Buffer.reset string_buff;
        let (* end_loc *) _ = comment lexbuf in
        Buffer.reset string_buff;
        token lexbuf
      }
  | "(*)"
      { let loc = curr_loc lexbuf  in
        raise (Report_toplevel ("Lexer error: ambiguous start of comment",
			        Some loc))
      }
  | "*)"
      { let loc = curr_loc lexbuf in
        raise (Report_toplevel ("Lexer error: unmatched end of comment",
			        Some loc))
      }
  | "\""
      { Buffer.reset string_buff;
        is_in_string := true;
        let string_start = lexbuf.lex_start_p in
        string_start_loc := curr_loc lexbuf;
        string lexbuf;
        is_in_string := false;
        lexbuf.lex_start_p <- string_start;
        STRING (Buffer.contents string_buff) }
  | (['a' 'b' 'c' 'r' 's' 't'] ident_body*) as id
      { LIDENT_ABCRST id }
  | (['i' 'j' 'k' 'l' 'm' 'n'] ident_body*) as id
      { LIDENT_IJKLMN id }
  | (['d' 'e' 'f' 'g' 'h'] ident_body*) as id
      { LIDENT_DEFGH id }
  | (['o' 'p' 'q'] ident_body*) as id
      { LIDENT_OPQ id }
  | (['u' 'v' 'w' 'x' 'y' 'z'] ident_body*) as id
      { LIDENT_UVWXYZ id }
  | (uppercase ident_body*) as id
      { UIDENT id }
  | eof		{ EOF }

and comment = parse
    "(*"
      { comment_start_loc := (curr_loc lexbuf) :: !comment_start_loc;
        store_lexeme lexbuf;
        comment lexbuf;
      }
  | "*)"
      { match !comment_start_loc with
        | [] -> assert false
        | [_] -> comment_start_loc := []; curr_loc lexbuf
        | _ :: l -> comment_start_loc := l;
                  store_lexeme lexbuf;
                  comment lexbuf
       }
  | "\""
      {
        string_start_loc := curr_loc lexbuf;
        Buffer.add_char string_buff '"';
        is_in_string := true;
        string lexbuf;
        is_in_string := false;
        Buffer.add_char string_buff '"';
        comment lexbuf }
  | "''"
      { store_lexeme lexbuf; comment lexbuf }
  | "'" newline "'"
      { incr_lineno lexbuf;
        store_lexeme lexbuf;
        comment lexbuf
      }
  | "'" [^ '\\' '\'' '\010' '\013' ] "'"
      { store_lexeme lexbuf; comment lexbuf }
  | "'\\" ['\\' '"' '\'' 'n' 't' 'b' 'r' ' '] "'"
      { store_lexeme lexbuf; comment lexbuf }
  | "'\\" ['0'-'9'] ['0'-'9'] ['0'-'9'] "'"
      { store_lexeme lexbuf; comment lexbuf }
  | "'\\" 'x' ['0'-'9' 'a'-'f' 'A'-'F'] ['0'-'9' 'a'-'f' 'A'-'F'] "'"
      { store_lexeme lexbuf; comment lexbuf }
  | eof
      { match !comment_start_loc with
        | [] -> assert false
        | loc :: _ ->
          comment_start_loc := [];
          raise (Report_toplevel
                   ("Lexer error: unterminated comment",
		    Some loc)) }
  | newline
      { incr_lineno lexbuf;
        store_lexeme lexbuf;
        comment lexbuf
      }
  | _
      { store_lexeme lexbuf; comment lexbuf }

and string = parse
    '"'
      { () }
  | '\\' newline ([' ' '\t'] * (* as space *))
      { incr_lineno lexbuf;
        string lexbuf
      }
  | '\\' ['\\' '\'' '"' 'n' 't' 'b' 'r' ' ']
      { Buffer.add_char string_buff(char_for_backslash(Lexing.lexeme_char lexbuf 1));
        string lexbuf }
  | '\\' ['0'-'9'] ['0'-'9'] ['0'-'9']
      { Buffer.add_char string_buff(char_for_decimal_code lexbuf 1);
         string lexbuf }
  | '\\' 'x' ['0'-'9' 'a'-'f' 'A'-'F'] ['0'-'9' 'a'-'f' 'A'-'F']
      { Buffer.add_char string_buff(char_for_hexadecimal_code lexbuf 2);
         string lexbuf }
  | '\\' _
      { if in_comment ()
        then string lexbuf
        else raise (Report_toplevel
                      ("Lexer error: illegal escape sequence",
		       Some (curr_loc lexbuf))) }
  | newline
      { incr_lineno lexbuf;
        store_lexeme lexbuf;
        string lexbuf
      }
  | eof
      { is_in_string := false;
        raise (Report_toplevel
                 ("Lexer error: unterminated string",
		  Some !string_start_loc)) }
  | _
      { Buffer.add_char string_buff (Lexing.lexeme_char lexbuf 0);
        string lexbuf }
