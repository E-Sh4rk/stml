{
  open Parser

  exception LexerError of string

  let enter_newline lexbuf =
    Lexing.new_line lexbuf;
    lexbuf

  let char_for_backslash = function
    | 'n' -> '\010'
    | 'r' -> '\013'
    | 'b' -> '\008'
    | 't' -> '\009'
    | c   -> c
}

let backslash_escapes = ['\\' '\'' '"' 'n' 't' 'b' 'r' ' ']

let newline = ('\010' | '\013' | "\013\010")

let blank   = [' ' '\009' '\012']

let id = ['a'-'z''_']['a'-'z''A'-'Z''0'-'9''_''\'']*
let constr_id = ['A'-'Z']['a'-'z''A'-'Z''0'-'9''_''\'']*
let param_constr_id = ['A'-'Z']['a'-'z''A'-'Z''0'-'9''_''\'']*'('

let decimal = ['0'-'9']+ ('_'+ ['0'-'9']+)*

let int = decimal

let float_e = decimal ['e' 'E'] (['-' '+']? decimal)?
let float_comma = decimal '.' decimal (['e' 'E'] ['-' '+']? decimal)?
let float = (float_e | float_comma)

let type_var = '\'' ['a'-'z''A'-'Z''0'-'9']['a'-'z''A'-'Z''0'-'9''_']*
let weak_type_var = '\'' '_' ['a'-'z''A'-'Z''0'-'9''_']*

let op_char =  '!' | '$' | '%' | '&' | '*' | '+' | '-' |
               '.' | '/' | ':' | ';' | '<' | '=' | '>' |
               '?' | '@' | '^' | '|' | '~'

let prefix_op = ('!' | '?') op_char*
let infix_op = ('=' | '<' | '>' | '@' | '^' | '|' | '&' |
                 '~' | '+' | '-' | '*' | '/' | '$' | '%') op_char*

rule token = parse
| newline { enter_newline lexbuf |> token }
| blank   { token lexbuf }
| "type"  { TYPE }
| "where" { WHERE }
| "and"   { TYPE_AND }
| "abstract"  { ABSTRACT }
| "(*"    { comment 0 lexbuf }
| "->"    { ARROW }
| "&"     { AND }
| "|"     { OR }
| "\\"    { DIFF }
| "~"     { NEG  }
| ":"     { COLON }
| ":?"    { COLON_OPT }
| "::"    { CONS }
| ":>"    { COERCE }
| ","     { COMMA }
| "."     { POINT }
| "="     { EQUAL }
| "?"     { INTERROGATION_MARK }
| "!"     { EXCLAMATION_MARK }
| "if"    { IF }
| "is"    { IS }
| "then"  { THEN }
| "else"  { ELSE }
| "match" { MATCH }
| "with"  { WITH }
| "end"   { END }
| "fun"   { FUN }
| "let"   { LET }
| "rec"   { REC }
| "gen"   { TOPLEVEL }
| "in"    { IN }
| "fst"   { FST }
| "snd"   { SND }
| "hd"    { HD }
| "tl"    { TL }
| "debug" { DEBUG }
| "("     { LPAREN }
| ")"     { RPAREN }
| "{"     { LBRACE }
| "}"     { RBRACE }
| "["     { LBRACKET }
| "]"     { RBRACKET }
| ";"     { SEMICOLON }
| "*"     { TIMES }
| ".."    { DOUBLEPOINT }
| "-"     { MINUS }
| "+"     { PLUS  }
| "/"     { DIV   }
| "magic" { MAGIC }
| "<"     { LT }
| ">"     { GT }
| int as i { LINT (Z.of_string i) }
| float as f { LFLOAT (float_of_string f) }
| "true"  { LBOOL true }
| "false" { LBOOL false }
| infix_op as s  { INFIX s }
| prefix_op as s { PREFIX s }
| '"' { read_string (Buffer.create 17) lexbuf }
| '\'' ([^ '\'' '\\' '\010' '\013'] as c) '\'' { LCHAR c }
| '\'' '\\' (backslash_escapes as c) '\'' { LCHAR (char_for_backslash c) }
| id as s { ID s }
| constr_id as s { CID s }
| param_constr_id as s { PCID (String.sub s 0 ((String.length s) - 1)) }
| type_var as s { TVAR s }
| weak_type_var as s { TVAR_WEAK s }
| eof     { EOF }
| _ { raise (LexerError ("Unexpected char: " ^ Lexing.lexeme lexbuf)) }

and comment depth = parse
| newline { enter_newline lexbuf |> comment depth }
| "*)" {
  if depth = 0 then token lexbuf else comment (depth - 1) lexbuf
}
| "(*" {
  comment (depth + 1) lexbuf
}
| eof { EOF }
| _ {
  comment depth lexbuf
}

and read_string buf = parse
| newline { enter_newline lexbuf |> read_string buf }
| '"' { LSTRING (Buffer.contents buf) }
| '\\' (backslash_escapes as c) { Buffer.add_char buf (char_for_backslash c); read_string buf lexbuf }
| [^ '"' '\\' '\010' '\013']+
  { Buffer.add_string buf (Lexing.lexeme lexbuf);
    read_string buf lexbuf
  }
| _ { raise (LexerError ("Illegal string character: " ^ Lexing.lexeme lexbuf)) }
| eof { raise (LexerError ("String is not terminated")) }
