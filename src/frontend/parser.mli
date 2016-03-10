exception Error

type token = 
  | TOK_int of (string)
  | TOK_id of (string)
  | TOK_WHILE
  | TOK_TRUE
  | TOK_STAR
  | TOK_SEMICOLON
  | TOK_RPAREN
  | TOK_RCURLY
  | TOK_RAND
  | TOK_PRINT
  | TOK_PLUS
  | TOK_PERCENT
  | TOK_NOT_EQUAL
  | TOK_MINUS
  | TOK_LPAREN
  | TOK_LESS_EQUAL
  | TOK_LESS
  | TOK_LCURLY
  | TOK_INT
  | TOK_IF
  | TOK_HALT
  | TOK_GREATER_EQUAL
  | TOK_GREATER
  | TOK_FALSE
  | TOK_EXCLAIM
  | TOK_EQUAL_EQUAL
  | TOK_EQUAL
  | TOK_EOF
  | TOK_ELSE
  | TOK_DIVIDE
  | TOK_COMMA
  | TOK_BAR_BAR
  | TOK_ASSERT
  | TOK_AND_AND


val file: (Lexing.lexbuf -> token) -> Lexing.lexbuf -> (Abstract_syntax_tree.prog)