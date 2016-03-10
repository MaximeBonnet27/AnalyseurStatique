exception Error

type token = 
  | TOK_int of (
# 56 "frontend/parser.mly"
       (string)
# 8 "frontend/parser.ml"
)
  | TOK_id of (
# 55 "frontend/parser.mly"
       (string)
# 13 "frontend/parser.ml"
)
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

and _menhir_env = {
  _menhir_lexer: Lexing.lexbuf -> token;
  _menhir_lexbuf: Lexing.lexbuf;
  mutable _menhir_token: token;
  mutable _menhir_startp: Lexing.position;
  mutable _menhir_endp: Lexing.position;
  mutable _menhir_shifted: int
}

and _menhir_state = 
  | MenhirState98
  | MenhirState94
  | MenhirState91
  | MenhirState86
  | MenhirState82
  | MenhirState80
  | MenhirState78
  | MenhirState73
  | MenhirState67
  | MenhirState65
  | MenhirState63
  | MenhirState60
  | MenhirState58
  | MenhirState52
  | MenhirState50
  | MenhirState48
  | MenhirState46
  | MenhirState44
  | MenhirState42
  | MenhirState40
  | MenhirState38
  | MenhirState36
  | MenhirState29
  | MenhirState27
  | MenhirState25
  | MenhirState23
  | MenhirState20
  | MenhirState18
  | MenhirState17
  | MenhirState16
  | MenhirState13
  | MenhirState6
  | MenhirState2
  | MenhirState0


# 15 "frontend/parser.mly"
  
open Abstract_syntax_tree

# 98 "frontend/parser.ml"
let _eRR =
  Error

let rec _menhir_run42 : _menhir_env -> 'ttv_tail * _menhir_state * 'tv_int_expr * Lexing.position * Lexing.position -> Lexing.position -> 'ttv_return =
  fun _menhir_env _menhir_stack _endpos ->
    let _menhir_stack = (_menhir_stack, _endpos) in
    let _tok = _menhir_discard _menhir_env in
    let (_menhir_env : _menhir_env) = _menhir_env in
    let (_menhir_stack : ('freshtv525 * _menhir_state * 'tv_int_expr * Lexing.position * Lexing.position) * Lexing.position) = _menhir_stack in
    let (_tok : token) = _tok in
    ((match _tok with
    | TOK_LPAREN ->
        _menhir_run18 _menhir_env (Obj.magic _menhir_stack) MenhirState42 _menhir_env._menhir_startp _menhir_env._menhir_endp
    | TOK_MINUS ->
        _menhir_run17 _menhir_env (Obj.magic _menhir_stack) MenhirState42 _menhir_env._menhir_startp _menhir_env._menhir_endp
    | TOK_PLUS ->
        _menhir_run16 _menhir_env (Obj.magic _menhir_stack) MenhirState42 _menhir_env._menhir_startp _menhir_env._menhir_endp
    | TOK_RAND ->
        _menhir_run5 _menhir_env (Obj.magic _menhir_stack) MenhirState42 _menhir_env._menhir_startp
    | TOK_id _v ->
        _menhir_run4 _menhir_env (Obj.magic _menhir_stack) MenhirState42 _v _menhir_env._menhir_startp _menhir_env._menhir_endp
    | TOK_int _v ->
        _menhir_run3 _menhir_env (Obj.magic _menhir_stack) MenhirState42 _v _menhir_env._menhir_startp _menhir_env._menhir_endp
    | _ ->
        assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
        _menhir_env._menhir_shifted <- (-1);
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState42) : 'freshtv526)

and _menhir_run44 : _menhir_env -> 'ttv_tail * _menhir_state * 'tv_int_expr * Lexing.position * Lexing.position -> Lexing.position -> 'ttv_return =
  fun _menhir_env _menhir_stack _endpos ->
    let _menhir_stack = (_menhir_stack, _endpos) in
    let _tok = _menhir_discard _menhir_env in
    let (_menhir_env : _menhir_env) = _menhir_env in
    let (_menhir_stack : ('freshtv523 * _menhir_state * 'tv_int_expr * Lexing.position * Lexing.position) * Lexing.position) = _menhir_stack in
    let (_tok : token) = _tok in
    ((match _tok with
    | TOK_LPAREN ->
        _menhir_run18 _menhir_env (Obj.magic _menhir_stack) MenhirState44 _menhir_env._menhir_startp _menhir_env._menhir_endp
    | TOK_MINUS ->
        _menhir_run17 _menhir_env (Obj.magic _menhir_stack) MenhirState44 _menhir_env._menhir_startp _menhir_env._menhir_endp
    | TOK_PLUS ->
        _menhir_run16 _menhir_env (Obj.magic _menhir_stack) MenhirState44 _menhir_env._menhir_startp _menhir_env._menhir_endp
    | TOK_RAND ->
        _menhir_run5 _menhir_env (Obj.magic _menhir_stack) MenhirState44 _menhir_env._menhir_startp
    | TOK_id _v ->
        _menhir_run4 _menhir_env (Obj.magic _menhir_stack) MenhirState44 _v _menhir_env._menhir_startp _menhir_env._menhir_endp
    | TOK_int _v ->
        _menhir_run3 _menhir_env (Obj.magic _menhir_stack) MenhirState44 _v _menhir_env._menhir_startp _menhir_env._menhir_endp
    | _ ->
        assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
        _menhir_env._menhir_shifted <- (-1);
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState44) : 'freshtv524)

and _menhir_run46 : _menhir_env -> 'ttv_tail * _menhir_state * 'tv_int_expr * Lexing.position * Lexing.position -> Lexing.position -> 'ttv_return =
  fun _menhir_env _menhir_stack _endpos ->
    let _menhir_stack = (_menhir_stack, _endpos) in
    let _tok = _menhir_discard _menhir_env in
    let (_menhir_env : _menhir_env) = _menhir_env in
    let (_menhir_stack : ('freshtv521 * _menhir_state * 'tv_int_expr * Lexing.position * Lexing.position) * Lexing.position) = _menhir_stack in
    let (_tok : token) = _tok in
    ((match _tok with
    | TOK_LPAREN ->
        _menhir_run18 _menhir_env (Obj.magic _menhir_stack) MenhirState46 _menhir_env._menhir_startp _menhir_env._menhir_endp
    | TOK_MINUS ->
        _menhir_run17 _menhir_env (Obj.magic _menhir_stack) MenhirState46 _menhir_env._menhir_startp _menhir_env._menhir_endp
    | TOK_PLUS ->
        _menhir_run16 _menhir_env (Obj.magic _menhir_stack) MenhirState46 _menhir_env._menhir_startp _menhir_env._menhir_endp
    | TOK_RAND ->
        _menhir_run5 _menhir_env (Obj.magic _menhir_stack) MenhirState46 _menhir_env._menhir_startp
    | TOK_id _v ->
        _menhir_run4 _menhir_env (Obj.magic _menhir_stack) MenhirState46 _v _menhir_env._menhir_startp _menhir_env._menhir_endp
    | TOK_int _v ->
        _menhir_run3 _menhir_env (Obj.magic _menhir_stack) MenhirState46 _v _menhir_env._menhir_startp _menhir_env._menhir_endp
    | _ ->
        assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
        _menhir_env._menhir_shifted <- (-1);
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState46) : 'freshtv522)

and _menhir_run48 : _menhir_env -> 'ttv_tail * _menhir_state * 'tv_int_expr * Lexing.position * Lexing.position -> Lexing.position -> 'ttv_return =
  fun _menhir_env _menhir_stack _endpos ->
    let _menhir_stack = (_menhir_stack, _endpos) in
    let _tok = _menhir_discard _menhir_env in
    let (_menhir_env : _menhir_env) = _menhir_env in
    let (_menhir_stack : ('freshtv519 * _menhir_state * 'tv_int_expr * Lexing.position * Lexing.position) * Lexing.position) = _menhir_stack in
    let (_tok : token) = _tok in
    ((match _tok with
    | TOK_LPAREN ->
        _menhir_run18 _menhir_env (Obj.magic _menhir_stack) MenhirState48 _menhir_env._menhir_startp _menhir_env._menhir_endp
    | TOK_MINUS ->
        _menhir_run17 _menhir_env (Obj.magic _menhir_stack) MenhirState48 _menhir_env._menhir_startp _menhir_env._menhir_endp
    | TOK_PLUS ->
        _menhir_run16 _menhir_env (Obj.magic _menhir_stack) MenhirState48 _menhir_env._menhir_startp _menhir_env._menhir_endp
    | TOK_RAND ->
        _menhir_run5 _menhir_env (Obj.magic _menhir_stack) MenhirState48 _menhir_env._menhir_startp
    | TOK_id _v ->
        _menhir_run4 _menhir_env (Obj.magic _menhir_stack) MenhirState48 _v _menhir_env._menhir_startp _menhir_env._menhir_endp
    | TOK_int _v ->
        _menhir_run3 _menhir_env (Obj.magic _menhir_stack) MenhirState48 _v _menhir_env._menhir_startp _menhir_env._menhir_endp
    | _ ->
        assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
        _menhir_env._menhir_shifted <- (-1);
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState48) : 'freshtv520)

and _menhir_run50 : _menhir_env -> 'ttv_tail * _menhir_state * 'tv_int_expr * Lexing.position * Lexing.position -> Lexing.position -> 'ttv_return =
  fun _menhir_env _menhir_stack _endpos ->
    let _menhir_stack = (_menhir_stack, _endpos) in
    let _tok = _menhir_discard _menhir_env in
    let (_menhir_env : _menhir_env) = _menhir_env in
    let (_menhir_stack : ('freshtv517 * _menhir_state * 'tv_int_expr * Lexing.position * Lexing.position) * Lexing.position) = _menhir_stack in
    let (_tok : token) = _tok in
    ((match _tok with
    | TOK_LPAREN ->
        _menhir_run18 _menhir_env (Obj.magic _menhir_stack) MenhirState50 _menhir_env._menhir_startp _menhir_env._menhir_endp
    | TOK_MINUS ->
        _menhir_run17 _menhir_env (Obj.magic _menhir_stack) MenhirState50 _menhir_env._menhir_startp _menhir_env._menhir_endp
    | TOK_PLUS ->
        _menhir_run16 _menhir_env (Obj.magic _menhir_stack) MenhirState50 _menhir_env._menhir_startp _menhir_env._menhir_endp
    | TOK_RAND ->
        _menhir_run5 _menhir_env (Obj.magic _menhir_stack) MenhirState50 _menhir_env._menhir_startp
    | TOK_id _v ->
        _menhir_run4 _menhir_env (Obj.magic _menhir_stack) MenhirState50 _v _menhir_env._menhir_startp _menhir_env._menhir_endp
    | TOK_int _v ->
        _menhir_run3 _menhir_env (Obj.magic _menhir_stack) MenhirState50 _v _menhir_env._menhir_startp _menhir_env._menhir_endp
    | _ ->
        assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
        _menhir_env._menhir_shifted <- (-1);
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState50) : 'freshtv518)

and _menhir_run52 : _menhir_env -> 'ttv_tail * _menhir_state * 'tv_int_expr * Lexing.position * Lexing.position -> Lexing.position -> 'ttv_return =
  fun _menhir_env _menhir_stack _endpos ->
    let _menhir_stack = (_menhir_stack, _endpos) in
    let _tok = _menhir_discard _menhir_env in
    let (_menhir_env : _menhir_env) = _menhir_env in
    let (_menhir_stack : ('freshtv515 * _menhir_state * 'tv_int_expr * Lexing.position * Lexing.position) * Lexing.position) = _menhir_stack in
    let (_tok : token) = _tok in
    ((match _tok with
    | TOK_LPAREN ->
        _menhir_run18 _menhir_env (Obj.magic _menhir_stack) MenhirState52 _menhir_env._menhir_startp _menhir_env._menhir_endp
    | TOK_MINUS ->
        _menhir_run17 _menhir_env (Obj.magic _menhir_stack) MenhirState52 _menhir_env._menhir_startp _menhir_env._menhir_endp
    | TOK_PLUS ->
        _menhir_run16 _menhir_env (Obj.magic _menhir_stack) MenhirState52 _menhir_env._menhir_startp _menhir_env._menhir_endp
    | TOK_RAND ->
        _menhir_run5 _menhir_env (Obj.magic _menhir_stack) MenhirState52 _menhir_env._menhir_startp
    | TOK_id _v ->
        _menhir_run4 _menhir_env (Obj.magic _menhir_stack) MenhirState52 _v _menhir_env._menhir_startp _menhir_env._menhir_endp
    | TOK_int _v ->
        _menhir_run3 _menhir_env (Obj.magic _menhir_stack) MenhirState52 _v _menhir_env._menhir_startp _menhir_env._menhir_endp
    | _ ->
        assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
        _menhir_env._menhir_shifted <- (-1);
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState52) : 'freshtv516)

and _menhir_run20 : _menhir_env -> 'ttv_tail * _menhir_state * 'tv_int_expr * Lexing.position * Lexing.position -> Lexing.position -> 'ttv_return =
  fun _menhir_env _menhir_stack _endpos ->
    let _menhir_stack = (_menhir_stack, _endpos) in
    let _tok = _menhir_discard _menhir_env in
    let (_menhir_env : _menhir_env) = _menhir_env in
    let (_menhir_stack : ('freshtv513 * _menhir_state * 'tv_int_expr * Lexing.position * Lexing.position) * Lexing.position) = _menhir_stack in
    let (_tok : token) = _tok in
    ((match _tok with
    | TOK_LPAREN ->
        _menhir_run18 _menhir_env (Obj.magic _menhir_stack) MenhirState20 _menhir_env._menhir_startp _menhir_env._menhir_endp
    | TOK_MINUS ->
        _menhir_run17 _menhir_env (Obj.magic _menhir_stack) MenhirState20 _menhir_env._menhir_startp _menhir_env._menhir_endp
    | TOK_PLUS ->
        _menhir_run16 _menhir_env (Obj.magic _menhir_stack) MenhirState20 _menhir_env._menhir_startp _menhir_env._menhir_endp
    | TOK_RAND ->
        _menhir_run5 _menhir_env (Obj.magic _menhir_stack) MenhirState20 _menhir_env._menhir_startp
    | TOK_id _v ->
        _menhir_run4 _menhir_env (Obj.magic _menhir_stack) MenhirState20 _v _menhir_env._menhir_startp _menhir_env._menhir_endp
    | TOK_int _v ->
        _menhir_run3 _menhir_env (Obj.magic _menhir_stack) MenhirState20 _v _menhir_env._menhir_startp _menhir_env._menhir_endp
    | _ ->
        assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
        _menhir_env._menhir_shifted <- (-1);
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState20) : 'freshtv514)

and _menhir_run22 : _menhir_env -> ('ttv_tail * _menhir_state * Lexing.position * Lexing.position) * _menhir_state * 'tv_int_expr * Lexing.position * Lexing.position -> Lexing.position -> Lexing.position -> 'ttv_return =
  fun _menhir_env _menhir_stack _startpos _endpos ->
    let _ = _menhir_discard _menhir_env in
    let (_menhir_env : _menhir_env) = _menhir_env in
    let (_menhir_stack : ('freshtv511 * _menhir_state * Lexing.position * Lexing.position) * _menhir_state * 'tv_int_expr * Lexing.position * Lexing.position) = Obj.magic _menhir_stack in
    let (_startpos__3_ : Lexing.position) = _startpos in
    let (_endpos__3_ : Lexing.position) = _endpos in
    ((let ((_menhir_stack, _menhir_s, _startpos__1_, _endpos__1_), _, e, _startpos_e_, _endpos_e_) = _menhir_stack in
    let _startpos = _startpos__1_ in
    let _endpos = _endpos__3_ in
    let _v : 'tv_int_expr = 
# 143 "frontend/parser.mly"
    ( e )
# 290 "frontend/parser.ml"
     in
    _menhir_goto_int_expr _menhir_env _menhir_stack _menhir_s _v _startpos _endpos) : 'freshtv512)

and _menhir_run23 : _menhir_env -> 'ttv_tail * _menhir_state * 'tv_int_expr * Lexing.position * Lexing.position -> Lexing.position -> Lexing.position -> 'ttv_return =
  fun _menhir_env _menhir_stack _startpos _endpos ->
    let _menhir_stack = (_menhir_stack, _startpos, _endpos) in
    let _tok = _menhir_discard _menhir_env in
    let (_menhir_env : _menhir_env) = _menhir_env in
    let (_menhir_stack : ('freshtv509 * _menhir_state * 'tv_int_expr * Lexing.position * Lexing.position) * Lexing.position * Lexing.position) = _menhir_stack in
    let (_tok : token) = _tok in
    ((match _tok with
    | TOK_LPAREN ->
        _menhir_run18 _menhir_env (Obj.magic _menhir_stack) MenhirState23 _menhir_env._menhir_startp _menhir_env._menhir_endp
    | TOK_MINUS ->
        _menhir_run17 _menhir_env (Obj.magic _menhir_stack) MenhirState23 _menhir_env._menhir_startp _menhir_env._menhir_endp
    | TOK_PLUS ->
        _menhir_run16 _menhir_env (Obj.magic _menhir_stack) MenhirState23 _menhir_env._menhir_startp _menhir_env._menhir_endp
    | TOK_RAND ->
        _menhir_run5 _menhir_env (Obj.magic _menhir_stack) MenhirState23 _menhir_env._menhir_startp
    | TOK_id _v ->
        _menhir_run4 _menhir_env (Obj.magic _menhir_stack) MenhirState23 _v _menhir_env._menhir_startp _menhir_env._menhir_endp
    | TOK_int _v ->
        _menhir_run3 _menhir_env (Obj.magic _menhir_stack) MenhirState23 _v _menhir_env._menhir_startp _menhir_env._menhir_endp
    | _ ->
        assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
        _menhir_env._menhir_shifted <- (-1);
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState23) : 'freshtv510)

and _menhir_run25 : _menhir_env -> 'ttv_tail * _menhir_state * 'tv_int_expr * Lexing.position * Lexing.position -> Lexing.position -> 'ttv_return =
  fun _menhir_env _menhir_stack _endpos ->
    let _menhir_stack = (_menhir_stack, _endpos) in
    let _tok = _menhir_discard _menhir_env in
    let (_menhir_env : _menhir_env) = _menhir_env in
    let (_menhir_stack : ('freshtv507 * _menhir_state * 'tv_int_expr * Lexing.position * Lexing.position) * Lexing.position) = _menhir_stack in
    let (_tok : token) = _tok in
    ((match _tok with
    | TOK_LPAREN ->
        _menhir_run18 _menhir_env (Obj.magic _menhir_stack) MenhirState25 _menhir_env._menhir_startp _menhir_env._menhir_endp
    | TOK_MINUS ->
        _menhir_run17 _menhir_env (Obj.magic _menhir_stack) MenhirState25 _menhir_env._menhir_startp _menhir_env._menhir_endp
    | TOK_PLUS ->
        _menhir_run16 _menhir_env (Obj.magic _menhir_stack) MenhirState25 _menhir_env._menhir_startp _menhir_env._menhir_endp
    | TOK_RAND ->
        _menhir_run5 _menhir_env (Obj.magic _menhir_stack) MenhirState25 _menhir_env._menhir_startp
    | TOK_id _v ->
        _menhir_run4 _menhir_env (Obj.magic _menhir_stack) MenhirState25 _v _menhir_env._menhir_startp _menhir_env._menhir_endp
    | TOK_int _v ->
        _menhir_run3 _menhir_env (Obj.magic _menhir_stack) MenhirState25 _v _menhir_env._menhir_startp _menhir_env._menhir_endp
    | _ ->
        assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
        _menhir_env._menhir_shifted <- (-1);
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState25) : 'freshtv508)

and _menhir_run29 : _menhir_env -> 'ttv_tail * _menhir_state * 'tv_int_expr * Lexing.position * Lexing.position -> Lexing.position -> Lexing.position -> 'ttv_return =
  fun _menhir_env _menhir_stack _startpos _endpos ->
    let _menhir_stack = (_menhir_stack, _startpos, _endpos) in
    let _tok = _menhir_discard _menhir_env in
    let (_menhir_env : _menhir_env) = _menhir_env in
    let (_menhir_stack : ('freshtv505 * _menhir_state * 'tv_int_expr * Lexing.position * Lexing.position) * Lexing.position * Lexing.position) = _menhir_stack in
    let (_tok : token) = _tok in
    ((match _tok with
    | TOK_LPAREN ->
        _menhir_run18 _menhir_env (Obj.magic _menhir_stack) MenhirState29 _menhir_env._menhir_startp _menhir_env._menhir_endp
    | TOK_MINUS ->
        _menhir_run17 _menhir_env (Obj.magic _menhir_stack) MenhirState29 _menhir_env._menhir_startp _menhir_env._menhir_endp
    | TOK_PLUS ->
        _menhir_run16 _menhir_env (Obj.magic _menhir_stack) MenhirState29 _menhir_env._menhir_startp _menhir_env._menhir_endp
    | TOK_RAND ->
        _menhir_run5 _menhir_env (Obj.magic _menhir_stack) MenhirState29 _menhir_env._menhir_startp
    | TOK_id _v ->
        _menhir_run4 _menhir_env (Obj.magic _menhir_stack) MenhirState29 _v _menhir_env._menhir_startp _menhir_env._menhir_endp
    | TOK_int _v ->
        _menhir_run3 _menhir_env (Obj.magic _menhir_stack) MenhirState29 _v _menhir_env._menhir_startp _menhir_env._menhir_endp
    | _ ->
        assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
        _menhir_env._menhir_shifted <- (-1);
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState29) : 'freshtv506)

and _menhir_run27 : _menhir_env -> 'ttv_tail * _menhir_state * 'tv_int_expr * Lexing.position * Lexing.position -> Lexing.position -> 'ttv_return =
  fun _menhir_env _menhir_stack _endpos ->
    let _menhir_stack = (_menhir_stack, _endpos) in
    let _tok = _menhir_discard _menhir_env in
    let (_menhir_env : _menhir_env) = _menhir_env in
    let (_menhir_stack : ('freshtv503 * _menhir_state * 'tv_int_expr * Lexing.position * Lexing.position) * Lexing.position) = _menhir_stack in
    let (_tok : token) = _tok in
    ((match _tok with
    | TOK_LPAREN ->
        _menhir_run18 _menhir_env (Obj.magic _menhir_stack) MenhirState27 _menhir_env._menhir_startp _menhir_env._menhir_endp
    | TOK_MINUS ->
        _menhir_run17 _menhir_env (Obj.magic _menhir_stack) MenhirState27 _menhir_env._menhir_startp _menhir_env._menhir_endp
    | TOK_PLUS ->
        _menhir_run16 _menhir_env (Obj.magic _menhir_stack) MenhirState27 _menhir_env._menhir_startp _menhir_env._menhir_endp
    | TOK_RAND ->
        _menhir_run5 _menhir_env (Obj.magic _menhir_stack) MenhirState27 _menhir_env._menhir_startp
    | TOK_id _v ->
        _menhir_run4 _menhir_env (Obj.magic _menhir_stack) MenhirState27 _v _menhir_env._menhir_startp _menhir_env._menhir_endp
    | TOK_int _v ->
        _menhir_run3 _menhir_env (Obj.magic _menhir_stack) MenhirState27 _v _menhir_env._menhir_startp _menhir_env._menhir_endp
    | _ ->
        assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
        _menhir_env._menhir_shifted <- (-1);
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState27) : 'freshtv504)

and _menhir_goto_sign_int_literal : _menhir_env -> 'ttv_tail -> _menhir_state -> 'tv_sign_int_literal -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v ->
    let _menhir_stack = (_menhir_stack, _menhir_s, _v) in
    match _menhir_s with
    | MenhirState6 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : (('freshtv491 * _menhir_state * Lexing.position) * Lexing.position * Lexing.position) * _menhir_state * 'tv_sign_int_literal) = Obj.magic _menhir_stack in
        ((assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
        let _tok = _menhir_env._menhir_token in
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : (('freshtv489 * _menhir_state * Lexing.position) * Lexing.position * Lexing.position) * _menhir_state * 'tv_sign_int_literal) = _menhir_stack in
        let (_tok : token) = _tok in
        ((match _tok with
        | TOK_COMMA ->
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : (('freshtv485 * _menhir_state * Lexing.position) * Lexing.position * Lexing.position) * _menhir_state * 'tv_sign_int_literal) = Obj.magic _menhir_stack in
            let (_startpos : Lexing.position) = _menhir_env._menhir_startp in
            let (_endpos : Lexing.position) = _menhir_env._menhir_endp in
            ((let _menhir_stack = (_menhir_stack, _startpos, _endpos) in
            let _tok = _menhir_discard _menhir_env in
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : ((('freshtv483 * _menhir_state * Lexing.position) * Lexing.position * Lexing.position) * _menhir_state * 'tv_sign_int_literal) * Lexing.position * Lexing.position) = _menhir_stack in
            let (_tok : token) = _tok in
            ((match _tok with
            | TOK_MINUS ->
                _menhir_run10 _menhir_env (Obj.magic _menhir_stack) MenhirState13 _menhir_env._menhir_startp _menhir_env._menhir_endp
            | TOK_PLUS ->
                _menhir_run8 _menhir_env (Obj.magic _menhir_stack) MenhirState13 _menhir_env._menhir_startp _menhir_env._menhir_endp
            | TOK_int _v ->
                _menhir_run7 _menhir_env (Obj.magic _menhir_stack) MenhirState13 _v _menhir_env._menhir_startp _menhir_env._menhir_endp
            | _ ->
                assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
                _menhir_env._menhir_shifted <- (-1);
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState13) : 'freshtv484)) : 'freshtv486)
        | _ ->
            assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
            _menhir_env._menhir_shifted <- (-1);
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : (('freshtv487 * _menhir_state * Lexing.position) * Lexing.position * Lexing.position) * _menhir_state * 'tv_sign_int_literal) = Obj.magic _menhir_stack in
            ((let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv488)) : 'freshtv490)) : 'freshtv492)
    | MenhirState13 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : (((('freshtv501 * _menhir_state * Lexing.position) * Lexing.position * Lexing.position) * _menhir_state * 'tv_sign_int_literal) * Lexing.position * Lexing.position) * _menhir_state * 'tv_sign_int_literal) = Obj.magic _menhir_stack in
        ((assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
        let _tok = _menhir_env._menhir_token in
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : (((('freshtv499 * _menhir_state * Lexing.position) * Lexing.position * Lexing.position) * _menhir_state * 'tv_sign_int_literal) * Lexing.position * Lexing.position) * _menhir_state * 'tv_sign_int_literal) = _menhir_stack in
        let (_tok : token) = _tok in
        ((match _tok with
        | TOK_RPAREN ->
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : (((('freshtv495 * _menhir_state * Lexing.position) * Lexing.position * Lexing.position) * _menhir_state * 'tv_sign_int_literal) * Lexing.position * Lexing.position) * _menhir_state * 'tv_sign_int_literal) = Obj.magic _menhir_stack in
            let (_startpos : Lexing.position) = _menhir_env._menhir_startp in
            let (_endpos : Lexing.position) = _menhir_env._menhir_endp in
            ((let _ = _menhir_discard _menhir_env in
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : (((('freshtv493 * _menhir_state * Lexing.position) * Lexing.position * Lexing.position) * _menhir_state * 'tv_sign_int_literal) * Lexing.position * Lexing.position) * _menhir_state * 'tv_sign_int_literal) = Obj.magic _menhir_stack in
            let (_startpos__menhir_p2_ : Lexing.position) = _startpos in
            let (_endpos__menhir_p2_ : Lexing.position) = _endpos in
            ((let (((((_menhir_stack, _menhir_s, _startpos__1_), _startpos__menhir_p0_, _endpos__menhir_p0_), _, x0), _startpos__menhir_p1_, _endpos__menhir_p1_), _, x1) = _menhir_stack in
            let _menhir_p2 = () in
            let _menhir_p1 = () in
            let _menhir_p0 = () in
            let _startpos = _startpos__1_ in
            let _endpos = _endpos__menhir_p2_ in
            let _v : 'tv_int_expr = let e2 =
              let _startpos = _endpos__menhir_p1_ in
              let _endpos = _startpos__menhir_p2_ in
              let x = x1 in
              
# 217 "frontend/parser.mly"
      ( x, (_startpos, _endpos) )
# 467 "frontend/parser.ml"
              
            in
            let e1 =
              let _startpos = _endpos__menhir_p0_ in
              let _endpos = _startpos__menhir_p1_ in
              let x = x0 in
              
# 217 "frontend/parser.mly"
      ( x, (_startpos, _endpos) )
# 477 "frontend/parser.ml"
              
            in
            
# 159 "frontend/parser.mly"
    ( AST_rand (e1, e2) )
# 483 "frontend/parser.ml"
             in
            _menhir_goto_int_expr _menhir_env _menhir_stack _menhir_s _v _startpos _endpos) : 'freshtv494)) : 'freshtv496)
        | _ ->
            assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
            _menhir_env._menhir_shifted <- (-1);
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : (((('freshtv497 * _menhir_state * Lexing.position) * Lexing.position * Lexing.position) * _menhir_state * 'tv_sign_int_literal) * Lexing.position * Lexing.position) * _menhir_state * 'tv_sign_int_literal) = Obj.magic _menhir_stack in
            ((let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv498)) : 'freshtv500)) : 'freshtv502)
    | _ ->
        _menhir_fail ()

and _menhir_run58 : _menhir_env -> 'ttv_tail * _menhir_state * 'tv_bool_expr * Lexing.position * Lexing.position -> Lexing.position -> 'ttv_return =
  fun _menhir_env _menhir_stack _endpos ->
    let _menhir_stack = (_menhir_stack, _endpos) in
    let _tok = _menhir_discard _menhir_env in
    let (_menhir_env : _menhir_env) = _menhir_env in
    let (_menhir_stack : ('freshtv481 * _menhir_state * 'tv_bool_expr * Lexing.position * Lexing.position) * Lexing.position) = _menhir_stack in
    let (_tok : token) = _tok in
    ((match _tok with
    | TOK_EXCLAIM ->
        _menhir_run40 _menhir_env (Obj.magic _menhir_stack) MenhirState58 _menhir_env._menhir_startp _menhir_env._menhir_endp
    | TOK_FALSE ->
        _menhir_run39 _menhir_env (Obj.magic _menhir_stack) MenhirState58 _menhir_env._menhir_startp _menhir_env._menhir_endp
    | TOK_LPAREN ->
        _menhir_run38 _menhir_env (Obj.magic _menhir_stack) MenhirState58 _menhir_env._menhir_startp _menhir_env._menhir_endp
    | TOK_MINUS ->
        _menhir_run17 _menhir_env (Obj.magic _menhir_stack) MenhirState58 _menhir_env._menhir_startp _menhir_env._menhir_endp
    | TOK_PLUS ->
        _menhir_run16 _menhir_env (Obj.magic _menhir_stack) MenhirState58 _menhir_env._menhir_startp _menhir_env._menhir_endp
    | TOK_RAND ->
        _menhir_run5 _menhir_env (Obj.magic _menhir_stack) MenhirState58 _menhir_env._menhir_startp
    | TOK_TRUE ->
        _menhir_run37 _menhir_env (Obj.magic _menhir_stack) MenhirState58 _menhir_env._menhir_startp _menhir_env._menhir_endp
    | TOK_id _v ->
        _menhir_run4 _menhir_env (Obj.magic _menhir_stack) MenhirState58 _v _menhir_env._menhir_startp _menhir_env._menhir_endp
    | TOK_int _v ->
        _menhir_run3 _menhir_env (Obj.magic _menhir_stack) MenhirState58 _v _menhir_env._menhir_startp _menhir_env._menhir_endp
    | _ ->
        assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
        _menhir_env._menhir_shifted <- (-1);
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState58) : 'freshtv482)

and _menhir_run60 : _menhir_env -> 'ttv_tail * _menhir_state * 'tv_bool_expr * Lexing.position * Lexing.position -> Lexing.position -> 'ttv_return =
  fun _menhir_env _menhir_stack _endpos ->
    let _menhir_stack = (_menhir_stack, _endpos) in
    let _tok = _menhir_discard _menhir_env in
    let (_menhir_env : _menhir_env) = _menhir_env in
    let (_menhir_stack : ('freshtv479 * _menhir_state * 'tv_bool_expr * Lexing.position * Lexing.position) * Lexing.position) = _menhir_stack in
    let (_tok : token) = _tok in
    ((match _tok with
    | TOK_EXCLAIM ->
        _menhir_run40 _menhir_env (Obj.magic _menhir_stack) MenhirState60 _menhir_env._menhir_startp _menhir_env._menhir_endp
    | TOK_FALSE ->
        _menhir_run39 _menhir_env (Obj.magic _menhir_stack) MenhirState60 _menhir_env._menhir_startp _menhir_env._menhir_endp
    | TOK_LPAREN ->
        _menhir_run38 _menhir_env (Obj.magic _menhir_stack) MenhirState60 _menhir_env._menhir_startp _menhir_env._menhir_endp
    | TOK_MINUS ->
        _menhir_run17 _menhir_env (Obj.magic _menhir_stack) MenhirState60 _menhir_env._menhir_startp _menhir_env._menhir_endp
    | TOK_PLUS ->
        _menhir_run16 _menhir_env (Obj.magic _menhir_stack) MenhirState60 _menhir_env._menhir_startp _menhir_env._menhir_endp
    | TOK_RAND ->
        _menhir_run5 _menhir_env (Obj.magic _menhir_stack) MenhirState60 _menhir_env._menhir_startp
    | TOK_TRUE ->
        _menhir_run37 _menhir_env (Obj.magic _menhir_stack) MenhirState60 _menhir_env._menhir_startp _menhir_env._menhir_endp
    | TOK_id _v ->
        _menhir_run4 _menhir_env (Obj.magic _menhir_stack) MenhirState60 _v _menhir_env._menhir_startp _menhir_env._menhir_endp
    | TOK_int _v ->
        _menhir_run3 _menhir_env (Obj.magic _menhir_stack) MenhirState60 _v _menhir_env._menhir_startp _menhir_env._menhir_endp
    | _ ->
        assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
        _menhir_env._menhir_shifted <- (-1);
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState60) : 'freshtv480)

and _menhir_goto_separated_nonempty_list_TOK_COMMA_ext_TOK_id__ : _menhir_env -> 'ttv_tail -> _menhir_state -> 'tv_separated_nonempty_list_TOK_COMMA_ext_TOK_id__ -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v ->
    match _menhir_s with
    | MenhirState67 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ('freshtv473 * _menhir_state * (
# 55 "frontend/parser.mly"
       (string)
# 566 "frontend/parser.ml"
        ) * Lexing.position * Lexing.position) * Lexing.position * Lexing.position) = Obj.magic _menhir_stack in
        let (_menhir_s : _menhir_state) = _menhir_s in
        let (_v : 'tv_separated_nonempty_list_TOK_COMMA_ext_TOK_id__) = _v in
        ((let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ('freshtv471 * _menhir_state * (
# 55 "frontend/parser.mly"
       (string)
# 574 "frontend/parser.ml"
        ) * Lexing.position * Lexing.position) * Lexing.position * Lexing.position) = Obj.magic _menhir_stack in
        let (_ : _menhir_state) = _menhir_s in
        let (xs : 'tv_separated_nonempty_list_TOK_COMMA_ext_TOK_id__) = _v in
        ((let ((_menhir_stack, _menhir_s, x0, _startpos_x0_, _endpos_x0_), _startpos__menhir_p0_, _endpos__menhir_p0_) = _menhir_stack in
        let _menhir_p0 = () in
        let _startpos = _startpos_x0_ in
        let _v : 'tv_separated_nonempty_list_TOK_COMMA_ext_TOK_id__ = let x =
          let _endpos = _startpos__menhir_p0_ in
          let x = x0 in
          
# 217 "frontend/parser.mly"
      ( x, (_startpos, _endpos) )
# 587 "frontend/parser.ml"
          
        in
        
# 146 "/home/maxime/.opam/system/lib/menhir/standard.mly"
    ( x :: xs )
# 593 "frontend/parser.ml"
         in
        _menhir_goto_separated_nonempty_list_TOK_COMMA_ext_TOK_id__ _menhir_env _menhir_stack _menhir_s _v) : 'freshtv472)) : 'freshtv474)
    | MenhirState65 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv477) = Obj.magic _menhir_stack in
        let (_menhir_s : _menhir_state) = _menhir_s in
        let (_v : 'tv_separated_nonempty_list_TOK_COMMA_ext_TOK_id__) = _v in
        ((let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv475) = Obj.magic _menhir_stack in
        let (_menhir_s : _menhir_state) = _menhir_s in
        let (x : 'tv_separated_nonempty_list_TOK_COMMA_ext_TOK_id__) = _v in
        ((let _v : 'tv_loption_separated_nonempty_list_TOK_COMMA_ext_TOK_id___ = 
# 59 "/home/maxime/.opam/system/lib/menhir/standard.mly"
    ( x )
# 608 "frontend/parser.ml"
         in
        _menhir_goto_loption_separated_nonempty_list_TOK_COMMA_ext_TOK_id___ _menhir_env _menhir_stack _menhir_s _v) : 'freshtv476)) : 'freshtv478)
    | _ ->
        _menhir_fail ()

and _menhir_goto_list_ext_decl__ : _menhir_env -> 'ttv_tail -> _menhir_state -> 'tv_list_ext_decl__ -> Lexing.position -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v _startpos ->
    let _menhir_stack = (_menhir_stack, _menhir_s, _v, _startpos) in
    match _menhir_s with
    | MenhirState73 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ('freshtv465 * _menhir_state * Lexing.position) * _menhir_state * 'tv_list_ext_decl__ * Lexing.position) = Obj.magic _menhir_stack in
        ((assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
        let _tok = _menhir_env._menhir_token in
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ('freshtv463 * _menhir_state * Lexing.position) * _menhir_state * 'tv_list_ext_decl__ * Lexing.position) = _menhir_stack in
        let (_tok : token) = _tok in
        ((match _tok with
        | TOK_ASSERT ->
            _menhir_run85 _menhir_env (Obj.magic _menhir_stack) MenhirState78 _menhir_env._menhir_startp
        | TOK_HALT ->
            _menhir_run83 _menhir_env (Obj.magic _menhir_stack) MenhirState78 _menhir_env._menhir_startp
        | TOK_IF ->
            _menhir_run79 _menhir_env (Obj.magic _menhir_stack) MenhirState78 _menhir_env._menhir_startp
        | TOK_LCURLY ->
            _menhir_run73 _menhir_env (Obj.magic _menhir_stack) MenhirState78 _menhir_env._menhir_startp
        | TOK_PRINT ->
            _menhir_run64 _menhir_env (Obj.magic _menhir_stack) MenhirState78 _menhir_env._menhir_startp
        | TOK_WHILE ->
            _menhir_run35 _menhir_env (Obj.magic _menhir_stack) MenhirState78 _menhir_env._menhir_startp
        | TOK_id _v ->
            _menhir_run1 _menhir_env (Obj.magic _menhir_stack) MenhirState78 _v _menhir_env._menhir_startp _menhir_env._menhir_endp
        | TOK_RCURLY ->
            _menhir_reduce29 _menhir_env (Obj.magic _menhir_stack) MenhirState78
        | _ ->
            assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
            _menhir_env._menhir_shifted <- (-1);
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState78) : 'freshtv464)) : 'freshtv466)
    | MenhirState98 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ('freshtv469 * _menhir_state * 'tv_decl * Lexing.position) * _menhir_state * 'tv_list_ext_decl__ * Lexing.position) = Obj.magic _menhir_stack in
        ((let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ('freshtv467 * _menhir_state * 'tv_decl * Lexing.position) * _menhir_state * 'tv_list_ext_decl__ * Lexing.position) = Obj.magic _menhir_stack in
        ((let ((_menhir_stack, _menhir_s, x0, _startpos_x0_), _, xs, _startpos_xs_) = _menhir_stack in
        let _startpos = _startpos_x0_ in
        let _v : 'tv_list_ext_decl__ = let x =
          let _endpos = _startpos_xs_ in
          let x = x0 in
          
# 217 "frontend/parser.mly"
      ( x, (_startpos, _endpos) )
# 660 "frontend/parser.ml"
          
        in
        
# 116 "/home/maxime/.opam/system/lib/menhir/standard.mly"
    ( x :: xs )
# 666 "frontend/parser.ml"
         in
        _menhir_goto_list_ext_decl__ _menhir_env _menhir_stack _menhir_s _v _startpos) : 'freshtv468)) : 'freshtv470)
    | _ ->
        _menhir_fail ()

and _menhir_fail : unit -> 'a =
  fun () ->
    Printf.fprintf Pervasives.stderr "Internal failure -- please contact the parser generator's developers.\n%!";
    assert false

and _menhir_goto_int_expr : _menhir_env -> 'ttv_tail -> _menhir_state -> 'tv_int_expr -> Lexing.position -> Lexing.position -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v _startpos _endpos ->
    let _menhir_stack = (_menhir_stack, _menhir_s, _v, _startpos, _endpos) in
    match _menhir_s with
    | MenhirState18 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ('freshtv347 * _menhir_state * Lexing.position * Lexing.position) * _menhir_state * 'tv_int_expr * Lexing.position * Lexing.position) = Obj.magic _menhir_stack in
        ((assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
        let _tok = _menhir_env._menhir_token in
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ('freshtv345 * _menhir_state * Lexing.position * Lexing.position) * _menhir_state * 'tv_int_expr * Lexing.position * Lexing.position) = _menhir_stack in
        let (_tok : token) = _tok in
        ((match _tok with
        | TOK_DIVIDE ->
            _menhir_run27 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_endp
        | TOK_MINUS ->
            _menhir_run29 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_startp _menhir_env._menhir_endp
        | TOK_PERCENT ->
            _menhir_run25 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_endp
        | TOK_PLUS ->
            _menhir_run23 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_startp _menhir_env._menhir_endp
        | TOK_RPAREN ->
            _menhir_run22 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_startp _menhir_env._menhir_endp
        | TOK_STAR ->
            _menhir_run20 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_endp
        | _ ->
            assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
            _menhir_env._menhir_shifted <- (-1);
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : ('freshtv343 * _menhir_state * Lexing.position * Lexing.position) * _menhir_state * 'tv_int_expr * Lexing.position * Lexing.position) = Obj.magic _menhir_stack in
            ((let (_menhir_stack, _menhir_s, _, _, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv344)) : 'freshtv346)) : 'freshtv348)
    | MenhirState20 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : (('freshtv351 * _menhir_state * 'tv_int_expr * Lexing.position * Lexing.position) * Lexing.position) * _menhir_state * 'tv_int_expr * Lexing.position * Lexing.position) = Obj.magic _menhir_stack in
        ((let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : (('freshtv349 * _menhir_state * 'tv_int_expr * Lexing.position * Lexing.position) * Lexing.position) * _menhir_state * 'tv_int_expr * Lexing.position * Lexing.position) = Obj.magic _menhir_stack in
        ((let (((_menhir_stack, _menhir_s, x0, _startpos_x0_, _endpos_x0_), _endpos__menhir_p0_), _, x1, _startpos_x1_, _endpos_x1_) = _menhir_stack in
        let _menhir_p0 = () in
        let _startpos = _startpos_x0_ in
        let _endpos = _endpos_x1_ in
        let _v : 'tv_int_expr = let e2 =
          let _startpos = _endpos__menhir_p0_ in
          let x = x1 in
          
# 217 "frontend/parser.mly"
      ( x, (_startpos, _endpos) )
# 724 "frontend/parser.ml"
          
        in
        let o =
          
# 98 "frontend/parser.mly"
                     ( AST_MULTIPLY )
# 731 "frontend/parser.ml"
          
        in
        let _startpos_o_ = _endpos_x0_ in
        let e1 =
          let _endpos = _startpos_o_ in
          let x = x0 in
          
# 217 "frontend/parser.mly"
      ( x, (_startpos, _endpos) )
# 741 "frontend/parser.ml"
          
        in
        
# 155 "frontend/parser.mly"
    ( AST_int_binary (o,e1,e2) )
# 747 "frontend/parser.ml"
         in
        _menhir_goto_int_expr _menhir_env _menhir_stack _menhir_s _v _startpos _endpos) : 'freshtv350)) : 'freshtv352)
    | MenhirState23 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : (('freshtv359 * _menhir_state * 'tv_int_expr * Lexing.position * Lexing.position) * Lexing.position * Lexing.position) * _menhir_state * 'tv_int_expr * Lexing.position * Lexing.position) = Obj.magic _menhir_stack in
        ((assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
        let _tok = _menhir_env._menhir_token in
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : (('freshtv357 * _menhir_state * 'tv_int_expr * Lexing.position * Lexing.position) * Lexing.position * Lexing.position) * _menhir_state * 'tv_int_expr * Lexing.position * Lexing.position) = _menhir_stack in
        let (_tok : token) = _tok in
        ((match _tok with
        | TOK_DIVIDE ->
            _menhir_run27 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_endp
        | TOK_PERCENT ->
            _menhir_run25 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_endp
        | TOK_STAR ->
            _menhir_run20 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_endp
        | TOK_AND_AND | TOK_BAR_BAR | TOK_EQUAL_EQUAL | TOK_GREATER | TOK_GREATER_EQUAL | TOK_LESS | TOK_LESS_EQUAL | TOK_MINUS | TOK_NOT_EQUAL | TOK_PLUS | TOK_RPAREN | TOK_SEMICOLON ->
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : (('freshtv353 * _menhir_state * 'tv_int_expr * Lexing.position * Lexing.position) * Lexing.position * Lexing.position) * _menhir_state * 'tv_int_expr * Lexing.position * Lexing.position) = Obj.magic _menhir_stack in
            ((let (((_menhir_stack, _menhir_s, x0, _startpos_x0_, _endpos_x0_), _startpos__menhir_p0_, _endpos__menhir_p0_), _, x1, _startpos_x1_, _endpos_x1_) = _menhir_stack in
            let _menhir_p0 = () in
            let _startpos = _startpos_x0_ in
            let _endpos = _endpos_x1_ in
            let _v : 'tv_int_expr = let e2 =
              let _startpos = _endpos__menhir_p0_ in
              let x = x1 in
              
# 217 "frontend/parser.mly"
      ( x, (_startpos, _endpos) )
# 778 "frontend/parser.ml"
              
            in
            let o =
              
# 100 "frontend/parser.mly"
                     ( AST_PLUS )
# 785 "frontend/parser.ml"
              
            in
            let _startpos_o_ = _endpos_x0_ in
            let e1 =
              let _endpos = _startpos_o_ in
              let x = x0 in
              
# 217 "frontend/parser.mly"
      ( x, (_startpos, _endpos) )
# 795 "frontend/parser.ml"
              
            in
            
# 155 "frontend/parser.mly"
    ( AST_int_binary (o,e1,e2) )
# 801 "frontend/parser.ml"
             in
            _menhir_goto_int_expr _menhir_env _menhir_stack _menhir_s _v _startpos _endpos) : 'freshtv354)
        | _ ->
            assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
            _menhir_env._menhir_shifted <- (-1);
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : (('freshtv355 * _menhir_state * 'tv_int_expr * Lexing.position * Lexing.position) * Lexing.position * Lexing.position) * _menhir_state * 'tv_int_expr * Lexing.position * Lexing.position) = Obj.magic _menhir_stack in
            ((let (_menhir_stack, _menhir_s, _, _, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv356)) : 'freshtv358)) : 'freshtv360)
    | MenhirState25 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : (('freshtv363 * _menhir_state * 'tv_int_expr * Lexing.position * Lexing.position) * Lexing.position) * _menhir_state * 'tv_int_expr * Lexing.position * Lexing.position) = Obj.magic _menhir_stack in
        ((let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : (('freshtv361 * _menhir_state * 'tv_int_expr * Lexing.position * Lexing.position) * Lexing.position) * _menhir_state * 'tv_int_expr * Lexing.position * Lexing.position) = Obj.magic _menhir_stack in
        ((let (((_menhir_stack, _menhir_s, x0, _startpos_x0_, _endpos_x0_), _endpos__menhir_p0_), _, x1, _startpos_x1_, _endpos_x1_) = _menhir_stack in
        let _menhir_p0 = () in
        let _startpos = _startpos_x0_ in
        let _endpos = _endpos_x1_ in
        let _v : 'tv_int_expr = let e2 =
          let _startpos = _endpos__menhir_p0_ in
          let x = x1 in
          
# 217 "frontend/parser.mly"
      ( x, (_startpos, _endpos) )
# 826 "frontend/parser.ml"
          
        in
        let o =
          
# 102 "frontend/parser.mly"
                      ( AST_MODULO )
# 833 "frontend/parser.ml"
          
        in
        let _startpos_o_ = _endpos_x0_ in
        let e1 =
          let _endpos = _startpos_o_ in
          let x = x0 in
          
# 217 "frontend/parser.mly"
      ( x, (_startpos, _endpos) )
# 843 "frontend/parser.ml"
          
        in
        
# 155 "frontend/parser.mly"
    ( AST_int_binary (o,e1,e2) )
# 849 "frontend/parser.ml"
         in
        _menhir_goto_int_expr _menhir_env _menhir_stack _menhir_s _v _startpos _endpos) : 'freshtv362)) : 'freshtv364)
    | MenhirState27 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : (('freshtv367 * _menhir_state * 'tv_int_expr * Lexing.position * Lexing.position) * Lexing.position) * _menhir_state * 'tv_int_expr * Lexing.position * Lexing.position) = Obj.magic _menhir_stack in
        ((let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : (('freshtv365 * _menhir_state * 'tv_int_expr * Lexing.position * Lexing.position) * Lexing.position) * _menhir_state * 'tv_int_expr * Lexing.position * Lexing.position) = Obj.magic _menhir_stack in
        ((let (((_menhir_stack, _menhir_s, x0, _startpos_x0_, _endpos_x0_), _endpos__menhir_p0_), _, x1, _startpos_x1_, _endpos_x1_) = _menhir_stack in
        let _menhir_p0 = () in
        let _startpos = _startpos_x0_ in
        let _endpos = _endpos_x1_ in
        let _v : 'tv_int_expr = let e2 =
          let _startpos = _endpos__menhir_p0_ in
          let x = x1 in
          
# 217 "frontend/parser.mly"
      ( x, (_startpos, _endpos) )
# 867 "frontend/parser.ml"
          
        in
        let o =
          
# 99 "frontend/parser.mly"
                     ( AST_DIVIDE )
# 874 "frontend/parser.ml"
          
        in
        let _startpos_o_ = _endpos_x0_ in
        let e1 =
          let _endpos = _startpos_o_ in
          let x = x0 in
          
# 217 "frontend/parser.mly"
      ( x, (_startpos, _endpos) )
# 884 "frontend/parser.ml"
          
        in
        
# 155 "frontend/parser.mly"
    ( AST_int_binary (o,e1,e2) )
# 890 "frontend/parser.ml"
         in
        _menhir_goto_int_expr _menhir_env _menhir_stack _menhir_s _v _startpos _endpos) : 'freshtv366)) : 'freshtv368)
    | MenhirState29 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : (('freshtv375 * _menhir_state * 'tv_int_expr * Lexing.position * Lexing.position) * Lexing.position * Lexing.position) * _menhir_state * 'tv_int_expr * Lexing.position * Lexing.position) = Obj.magic _menhir_stack in
        ((assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
        let _tok = _menhir_env._menhir_token in
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : (('freshtv373 * _menhir_state * 'tv_int_expr * Lexing.position * Lexing.position) * Lexing.position * Lexing.position) * _menhir_state * 'tv_int_expr * Lexing.position * Lexing.position) = _menhir_stack in
        let (_tok : token) = _tok in
        ((match _tok with
        | TOK_DIVIDE ->
            _menhir_run27 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_endp
        | TOK_PERCENT ->
            _menhir_run25 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_endp
        | TOK_STAR ->
            _menhir_run20 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_endp
        | TOK_AND_AND | TOK_BAR_BAR | TOK_EQUAL_EQUAL | TOK_GREATER | TOK_GREATER_EQUAL | TOK_LESS | TOK_LESS_EQUAL | TOK_MINUS | TOK_NOT_EQUAL | TOK_PLUS | TOK_RPAREN | TOK_SEMICOLON ->
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : (('freshtv369 * _menhir_state * 'tv_int_expr * Lexing.position * Lexing.position) * Lexing.position * Lexing.position) * _menhir_state * 'tv_int_expr * Lexing.position * Lexing.position) = Obj.magic _menhir_stack in
            ((let (((_menhir_stack, _menhir_s, x0, _startpos_x0_, _endpos_x0_), _startpos__menhir_p0_, _endpos__menhir_p0_), _, x1, _startpos_x1_, _endpos_x1_) = _menhir_stack in
            let _menhir_p0 = () in
            let _startpos = _startpos_x0_ in
            let _endpos = _endpos_x1_ in
            let _v : 'tv_int_expr = let e2 =
              let _startpos = _endpos__menhir_p0_ in
              let x = x1 in
              
# 217 "frontend/parser.mly"
      ( x, (_startpos, _endpos) )
# 921 "frontend/parser.ml"
              
            in
            let o =
              
# 101 "frontend/parser.mly"
                     ( AST_MINUS )
# 928 "frontend/parser.ml"
              
            in
            let _startpos_o_ = _endpos_x0_ in
            let e1 =
              let _endpos = _startpos_o_ in
              let x = x0 in
              
# 217 "frontend/parser.mly"
      ( x, (_startpos, _endpos) )
# 938 "frontend/parser.ml"
              
            in
            
# 155 "frontend/parser.mly"
    ( AST_int_binary (o,e1,e2) )
# 944 "frontend/parser.ml"
             in
            _menhir_goto_int_expr _menhir_env _menhir_stack _menhir_s _v _startpos _endpos) : 'freshtv370)
        | _ ->
            assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
            _menhir_env._menhir_shifted <- (-1);
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : (('freshtv371 * _menhir_state * 'tv_int_expr * Lexing.position * Lexing.position) * Lexing.position * Lexing.position) * _menhir_state * 'tv_int_expr * Lexing.position * Lexing.position) = Obj.magic _menhir_stack in
            ((let (_menhir_stack, _menhir_s, _, _, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv372)) : 'freshtv374)) : 'freshtv376)
    | MenhirState17 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ('freshtv383 * _menhir_state * Lexing.position * Lexing.position) * _menhir_state * 'tv_int_expr * Lexing.position * Lexing.position) = Obj.magic _menhir_stack in
        ((assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
        let _tok = _menhir_env._menhir_token in
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ('freshtv381 * _menhir_state * Lexing.position * Lexing.position) * _menhir_state * 'tv_int_expr * Lexing.position * Lexing.position) = _menhir_stack in
        let (_tok : token) = _tok in
        ((match _tok with
        | TOK_DIVIDE ->
            _menhir_run27 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_endp
        | TOK_PERCENT ->
            _menhir_run25 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_endp
        | TOK_STAR ->
            _menhir_run20 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_endp
        | TOK_AND_AND | TOK_BAR_BAR | TOK_EQUAL_EQUAL | TOK_GREATER | TOK_GREATER_EQUAL | TOK_LESS | TOK_LESS_EQUAL | TOK_MINUS | TOK_NOT_EQUAL | TOK_PLUS | TOK_RPAREN | TOK_SEMICOLON ->
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : ('freshtv377 * _menhir_state * Lexing.position * Lexing.position) * _menhir_state * 'tv_int_expr * Lexing.position * Lexing.position) = Obj.magic _menhir_stack in
            ((let ((_menhir_stack, _menhir_s, _startpos__menhir_p0_, _endpos__menhir_p0_), _, x0, _startpos_x0_, _endpos_x0_) = _menhir_stack in
            let _menhir_p0 = () in
            let _startpos = _startpos__menhir_p0_ in
            let _endpos = _endpos_x0_ in
            let _v : 'tv_int_expr = let e =
              let _startpos = _endpos__menhir_p0_ in
              let x = x0 in
              
# 217 "frontend/parser.mly"
      ( x, (_startpos, _endpos) )
# 982 "frontend/parser.ml"
              
            in
            let o =
              
# 90 "frontend/parser.mly"
                     ( AST_UNARY_MINUS )
# 989 "frontend/parser.ml"
              
            in
            
# 152 "frontend/parser.mly"
    ( AST_int_unary (o,e) )
# 995 "frontend/parser.ml"
             in
            _menhir_goto_int_expr _menhir_env _menhir_stack _menhir_s _v _startpos _endpos) : 'freshtv378)
        | _ ->
            assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
            _menhir_env._menhir_shifted <- (-1);
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : ('freshtv379 * _menhir_state * Lexing.position * Lexing.position) * _menhir_state * 'tv_int_expr * Lexing.position * Lexing.position) = Obj.magic _menhir_stack in
            ((let (_menhir_stack, _menhir_s, _, _, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv380)) : 'freshtv382)) : 'freshtv384)
    | MenhirState16 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ('freshtv391 * _menhir_state * Lexing.position * Lexing.position) * _menhir_state * 'tv_int_expr * Lexing.position * Lexing.position) = Obj.magic _menhir_stack in
        ((assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
        let _tok = _menhir_env._menhir_token in
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ('freshtv389 * _menhir_state * Lexing.position * Lexing.position) * _menhir_state * 'tv_int_expr * Lexing.position * Lexing.position) = _menhir_stack in
        let (_tok : token) = _tok in
        ((match _tok with
        | TOK_DIVIDE ->
            _menhir_run27 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_endp
        | TOK_PERCENT ->
            _menhir_run25 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_endp
        | TOK_STAR ->
            _menhir_run20 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_endp
        | TOK_AND_AND | TOK_BAR_BAR | TOK_EQUAL_EQUAL | TOK_GREATER | TOK_GREATER_EQUAL | TOK_LESS | TOK_LESS_EQUAL | TOK_MINUS | TOK_NOT_EQUAL | TOK_PLUS | TOK_RPAREN | TOK_SEMICOLON ->
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : ('freshtv385 * _menhir_state * Lexing.position * Lexing.position) * _menhir_state * 'tv_int_expr * Lexing.position * Lexing.position) = Obj.magic _menhir_stack in
            ((let ((_menhir_stack, _menhir_s, _startpos__menhir_p0_, _endpos__menhir_p0_), _, x0, _startpos_x0_, _endpos_x0_) = _menhir_stack in
            let _menhir_p0 = () in
            let _startpos = _startpos__menhir_p0_ in
            let _endpos = _endpos_x0_ in
            let _v : 'tv_int_expr = let e =
              let _startpos = _endpos__menhir_p0_ in
              let x = x0 in
              
# 217 "frontend/parser.mly"
      ( x, (_startpos, _endpos) )
# 1033 "frontend/parser.ml"
              
            in
            let o =
              
# 89 "frontend/parser.mly"
                     ( AST_UNARY_PLUS )
# 1040 "frontend/parser.ml"
              
            in
            
# 152 "frontend/parser.mly"
    ( AST_int_unary (o,e) )
# 1046 "frontend/parser.ml"
             in
            _menhir_goto_int_expr _menhir_env _menhir_stack _menhir_s _v _startpos _endpos) : 'freshtv386)
        | _ ->
            assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
            _menhir_env._menhir_shifted <- (-1);
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : ('freshtv387 * _menhir_state * Lexing.position * Lexing.position) * _menhir_state * 'tv_int_expr * Lexing.position * Lexing.position) = Obj.magic _menhir_stack in
            ((let (_menhir_stack, _menhir_s, _, _, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv388)) : 'freshtv390)) : 'freshtv392)
    | MenhirState2 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : (('freshtv401 * _menhir_state * (
# 55 "frontend/parser.mly"
       (string)
# 1061 "frontend/parser.ml"
        ) * Lexing.position * Lexing.position) * Lexing.position * Lexing.position) * _menhir_state * 'tv_int_expr * Lexing.position * Lexing.position) = Obj.magic _menhir_stack in
        ((assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
        let _tok = _menhir_env._menhir_token in
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : (('freshtv399 * _menhir_state * (
# 55 "frontend/parser.mly"
       (string)
# 1069 "frontend/parser.ml"
        ) * Lexing.position * Lexing.position) * Lexing.position * Lexing.position) * _menhir_state * 'tv_int_expr * Lexing.position * Lexing.position) = _menhir_stack in
        let (_tok : token) = _tok in
        ((match _tok with
        | TOK_DIVIDE ->
            _menhir_run27 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_endp
        | TOK_MINUS ->
            _menhir_run29 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_startp _menhir_env._menhir_endp
        | TOK_PERCENT ->
            _menhir_run25 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_endp
        | TOK_PLUS ->
            _menhir_run23 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_startp _menhir_env._menhir_endp
        | TOK_SEMICOLON ->
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : (('freshtv395 * _menhir_state * (
# 55 "frontend/parser.mly"
       (string)
# 1086 "frontend/parser.ml"
            ) * Lexing.position * Lexing.position) * Lexing.position * Lexing.position) * _menhir_state * 'tv_int_expr * Lexing.position * Lexing.position) = Obj.magic _menhir_stack in
            let (_startpos : Lexing.position) = _menhir_env._menhir_startp in
            let (_endpos : Lexing.position) = _menhir_env._menhir_endp in
            ((let _ = _menhir_discard _menhir_env in
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : (('freshtv393 * _menhir_state * (
# 55 "frontend/parser.mly"
       (string)
# 1095 "frontend/parser.ml"
            ) * Lexing.position * Lexing.position) * Lexing.position * Lexing.position) * _menhir_state * 'tv_int_expr * Lexing.position * Lexing.position) = Obj.magic _menhir_stack in
            let (_startpos__menhir_p1_ : Lexing.position) = _startpos in
            let (_endpos__menhir_p1_ : Lexing.position) = _endpos in
            ((let (((_menhir_stack, _menhir_s, x0, _startpos_x0_, _endpos_x0_), _startpos__menhir_p0_, _endpos__menhir_p0_), _, x1, _startpos_x1_, _endpos_x1_) = _menhir_stack in
            let _menhir_p1 = () in
            let _menhir_p0 = () in
            let _startpos = _startpos_x0_ in
            let _endpos = _endpos__menhir_p1_ in
            let _v : 'tv_stat = let f =
              let _startpos = _endpos__menhir_p0_ in
              let _endpos = _startpos__menhir_p1_ in
              let x = x1 in
              
# 217 "frontend/parser.mly"
      ( x, (_startpos, _endpos) )
# 1111 "frontend/parser.ml"
              
            in
            let e =
              let _endpos = _startpos__menhir_p0_ in
              let x = x0 in
              
# 217 "frontend/parser.mly"
      ( x, (_startpos, _endpos) )
# 1120 "frontend/parser.ml"
              
            in
            
# 191 "frontend/parser.mly"
  ( AST_assign (e, f) )
# 1126 "frontend/parser.ml"
             in
            _menhir_goto_stat _menhir_env _menhir_stack _menhir_s _v _startpos _endpos) : 'freshtv394)) : 'freshtv396)
        | TOK_STAR ->
            _menhir_run20 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_endp
        | _ ->
            assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
            _menhir_env._menhir_shifted <- (-1);
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : (('freshtv397 * _menhir_state * (
# 55 "frontend/parser.mly"
       (string)
# 1138 "frontend/parser.ml"
            ) * Lexing.position * Lexing.position) * Lexing.position * Lexing.position) * _menhir_state * 'tv_int_expr * Lexing.position * Lexing.position) = Obj.magic _menhir_stack in
            ((let (_menhir_stack, _menhir_s, _, _, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv398)) : 'freshtv400)) : 'freshtv402)
    | MenhirState86 | MenhirState80 | MenhirState36 | MenhirState60 | MenhirState58 | MenhirState40 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv407 * _menhir_state * 'tv_int_expr * Lexing.position * Lexing.position) = Obj.magic _menhir_stack in
        ((assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
        let _tok = _menhir_env._menhir_token in
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv405 * _menhir_state * 'tv_int_expr * Lexing.position * Lexing.position) = _menhir_stack in
        let (_tok : token) = _tok in
        ((match _tok with
        | TOK_DIVIDE ->
            _menhir_run27 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_endp
        | TOK_EQUAL_EQUAL ->
            _menhir_run52 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_endp
        | TOK_GREATER ->
            _menhir_run50 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_endp
        | TOK_GREATER_EQUAL ->
            _menhir_run48 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_endp
        | TOK_LESS ->
            _menhir_run46 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_endp
        | TOK_LESS_EQUAL ->
            _menhir_run44 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_endp
        | TOK_MINUS ->
            _menhir_run29 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_startp _menhir_env._menhir_endp
        | TOK_NOT_EQUAL ->
            _menhir_run42 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_endp
        | TOK_PERCENT ->
            _menhir_run25 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_endp
        | TOK_PLUS ->
            _menhir_run23 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_startp _menhir_env._menhir_endp
        | TOK_STAR ->
            _menhir_run20 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_endp
        | _ ->
            assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
            _menhir_env._menhir_shifted <- (-1);
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : 'freshtv403 * _menhir_state * 'tv_int_expr * Lexing.position * Lexing.position) = Obj.magic _menhir_stack in
            ((let (_menhir_stack, _menhir_s, _, _, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv404)) : 'freshtv406)) : 'freshtv408)
    | MenhirState42 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : (('freshtv415 * _menhir_state * 'tv_int_expr * Lexing.position * Lexing.position) * Lexing.position) * _menhir_state * 'tv_int_expr * Lexing.position * Lexing.position) = Obj.magic _menhir_stack in
        ((assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
        let _tok = _menhir_env._menhir_token in
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : (('freshtv413 * _menhir_state * 'tv_int_expr * Lexing.position * Lexing.position) * Lexing.position) * _menhir_state * 'tv_int_expr * Lexing.position * Lexing.position) = _menhir_stack in
        let (_tok : token) = _tok in
        ((match _tok with
        | TOK_DIVIDE ->
            _menhir_run27 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_endp
        | TOK_MINUS ->
            _menhir_run29 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_startp _menhir_env._menhir_endp
        | TOK_PERCENT ->
            _menhir_run25 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_endp
        | TOK_PLUS ->
            _menhir_run23 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_startp _menhir_env._menhir_endp
        | TOK_STAR ->
            _menhir_run20 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_endp
        | TOK_AND_AND | TOK_BAR_BAR | TOK_RPAREN ->
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : (('freshtv409 * _menhir_state * 'tv_int_expr * Lexing.position * Lexing.position) * Lexing.position) * _menhir_state * 'tv_int_expr * Lexing.position * Lexing.position) = Obj.magic _menhir_stack in
            ((let (((_menhir_stack, _menhir_s, x0, _startpos_x0_, _endpos_x0_), _endpos__menhir_p0_), _, x1, _startpos_x1_, _endpos_x1_) = _menhir_stack in
            let _menhir_p0 = () in
            let _startpos = _startpos_x0_ in
            let _endpos = _endpos_x1_ in
            let _v : 'tv_bool_expr = let e2 =
              let _startpos = _endpos__menhir_p0_ in
              let x = x1 in
              
# 217 "frontend/parser.mly"
      ( x, (_startpos, _endpos) )
# 1212 "frontend/parser.ml"
              
            in
            let o =
              
# 111 "frontend/parser.mly"
                     ( AST_NOT_EQUAL )
# 1219 "frontend/parser.ml"
              
            in
            let _startpos_o_ = _endpos_x0_ in
            let e1 =
              let _endpos = _startpos_o_ in
              let x = x0 in
              
# 217 "frontend/parser.mly"
      ( x, (_startpos, _endpos) )
# 1229 "frontend/parser.ml"
              
            in
            
# 137 "frontend/parser.mly"
    ( AST_compare (o,e1,e2) )
# 1235 "frontend/parser.ml"
             in
            _menhir_goto_bool_expr _menhir_env _menhir_stack _menhir_s _v _startpos _endpos) : 'freshtv410)
        | _ ->
            assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
            _menhir_env._menhir_shifted <- (-1);
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : (('freshtv411 * _menhir_state * 'tv_int_expr * Lexing.position * Lexing.position) * Lexing.position) * _menhir_state * 'tv_int_expr * Lexing.position * Lexing.position) = Obj.magic _menhir_stack in
            ((let (_menhir_stack, _menhir_s, _, _, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv412)) : 'freshtv414)) : 'freshtv416)
    | MenhirState44 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : (('freshtv423 * _menhir_state * 'tv_int_expr * Lexing.position * Lexing.position) * Lexing.position) * _menhir_state * 'tv_int_expr * Lexing.position * Lexing.position) = Obj.magic _menhir_stack in
        ((assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
        let _tok = _menhir_env._menhir_token in
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : (('freshtv421 * _menhir_state * 'tv_int_expr * Lexing.position * Lexing.position) * Lexing.position) * _menhir_state * 'tv_int_expr * Lexing.position * Lexing.position) = _menhir_stack in
        let (_tok : token) = _tok in
        ((match _tok with
        | TOK_DIVIDE ->
            _menhir_run27 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_endp
        | TOK_MINUS ->
            _menhir_run29 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_startp _menhir_env._menhir_endp
        | TOK_PERCENT ->
            _menhir_run25 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_endp
        | TOK_PLUS ->
            _menhir_run23 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_startp _menhir_env._menhir_endp
        | TOK_STAR ->
            _menhir_run20 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_endp
        | TOK_AND_AND | TOK_BAR_BAR | TOK_RPAREN ->
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : (('freshtv417 * _menhir_state * 'tv_int_expr * Lexing.position * Lexing.position) * Lexing.position) * _menhir_state * 'tv_int_expr * Lexing.position * Lexing.position) = Obj.magic _menhir_stack in
            ((let (((_menhir_stack, _menhir_s, x0, _startpos_x0_, _endpos_x0_), _endpos__menhir_p0_), _, x1, _startpos_x1_, _endpos_x1_) = _menhir_stack in
            let _menhir_p0 = () in
            let _startpos = _startpos_x0_ in
            let _endpos = _endpos_x1_ in
            let _v : 'tv_bool_expr = let e2 =
              let _startpos = _endpos__menhir_p0_ in
              let x = x1 in
              
# 217 "frontend/parser.mly"
      ( x, (_startpos, _endpos) )
# 1277 "frontend/parser.ml"
              
            in
            let o =
              
# 108 "frontend/parser.mly"
                     ( AST_LESS_EQUAL )
# 1284 "frontend/parser.ml"
              
            in
            let _startpos_o_ = _endpos_x0_ in
            let e1 =
              let _endpos = _startpos_o_ in
              let x = x0 in
              
# 217 "frontend/parser.mly"
      ( x, (_startpos, _endpos) )
# 1294 "frontend/parser.ml"
              
            in
            
# 137 "frontend/parser.mly"
    ( AST_compare (o,e1,e2) )
# 1300 "frontend/parser.ml"
             in
            _menhir_goto_bool_expr _menhir_env _menhir_stack _menhir_s _v _startpos _endpos) : 'freshtv418)
        | _ ->
            assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
            _menhir_env._menhir_shifted <- (-1);
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : (('freshtv419 * _menhir_state * 'tv_int_expr * Lexing.position * Lexing.position) * Lexing.position) * _menhir_state * 'tv_int_expr * Lexing.position * Lexing.position) = Obj.magic _menhir_stack in
            ((let (_menhir_stack, _menhir_s, _, _, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv420)) : 'freshtv422)) : 'freshtv424)
    | MenhirState46 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : (('freshtv431 * _menhir_state * 'tv_int_expr * Lexing.position * Lexing.position) * Lexing.position) * _menhir_state * 'tv_int_expr * Lexing.position * Lexing.position) = Obj.magic _menhir_stack in
        ((assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
        let _tok = _menhir_env._menhir_token in
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : (('freshtv429 * _menhir_state * 'tv_int_expr * Lexing.position * Lexing.position) * Lexing.position) * _menhir_state * 'tv_int_expr * Lexing.position * Lexing.position) = _menhir_stack in
        let (_tok : token) = _tok in
        ((match _tok with
        | TOK_DIVIDE ->
            _menhir_run27 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_endp
        | TOK_MINUS ->
            _menhir_run29 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_startp _menhir_env._menhir_endp
        | TOK_PERCENT ->
            _menhir_run25 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_endp
        | TOK_PLUS ->
            _menhir_run23 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_startp _menhir_env._menhir_endp
        | TOK_STAR ->
            _menhir_run20 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_endp
        | TOK_AND_AND | TOK_BAR_BAR | TOK_RPAREN ->
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : (('freshtv425 * _menhir_state * 'tv_int_expr * Lexing.position * Lexing.position) * Lexing.position) * _menhir_state * 'tv_int_expr * Lexing.position * Lexing.position) = Obj.magic _menhir_stack in
            ((let (((_menhir_stack, _menhir_s, x0, _startpos_x0_, _endpos_x0_), _endpos__menhir_p0_), _, x1, _startpos_x1_, _endpos_x1_) = _menhir_stack in
            let _menhir_p0 = () in
            let _startpos = _startpos_x0_ in
            let _endpos = _endpos_x1_ in
            let _v : 'tv_bool_expr = let e2 =
              let _startpos = _endpos__menhir_p0_ in
              let x = x1 in
              
# 217 "frontend/parser.mly"
      ( x, (_startpos, _endpos) )
# 1342 "frontend/parser.ml"
              
            in
            let o =
              
# 106 "frontend/parser.mly"
                     ( AST_LESS )
# 1349 "frontend/parser.ml"
              
            in
            let _startpos_o_ = _endpos_x0_ in
            let e1 =
              let _endpos = _startpos_o_ in
              let x = x0 in
              
# 217 "frontend/parser.mly"
      ( x, (_startpos, _endpos) )
# 1359 "frontend/parser.ml"
              
            in
            
# 137 "frontend/parser.mly"
    ( AST_compare (o,e1,e2) )
# 1365 "frontend/parser.ml"
             in
            _menhir_goto_bool_expr _menhir_env _menhir_stack _menhir_s _v _startpos _endpos) : 'freshtv426)
        | _ ->
            assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
            _menhir_env._menhir_shifted <- (-1);
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : (('freshtv427 * _menhir_state * 'tv_int_expr * Lexing.position * Lexing.position) * Lexing.position) * _menhir_state * 'tv_int_expr * Lexing.position * Lexing.position) = Obj.magic _menhir_stack in
            ((let (_menhir_stack, _menhir_s, _, _, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv428)) : 'freshtv430)) : 'freshtv432)
    | MenhirState48 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : (('freshtv439 * _menhir_state * 'tv_int_expr * Lexing.position * Lexing.position) * Lexing.position) * _menhir_state * 'tv_int_expr * Lexing.position * Lexing.position) = Obj.magic _menhir_stack in
        ((assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
        let _tok = _menhir_env._menhir_token in
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : (('freshtv437 * _menhir_state * 'tv_int_expr * Lexing.position * Lexing.position) * Lexing.position) * _menhir_state * 'tv_int_expr * Lexing.position * Lexing.position) = _menhir_stack in
        let (_tok : token) = _tok in
        ((match _tok with
        | TOK_DIVIDE ->
            _menhir_run27 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_endp
        | TOK_MINUS ->
            _menhir_run29 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_startp _menhir_env._menhir_endp
        | TOK_PERCENT ->
            _menhir_run25 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_endp
        | TOK_PLUS ->
            _menhir_run23 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_startp _menhir_env._menhir_endp
        | TOK_STAR ->
            _menhir_run20 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_endp
        | TOK_AND_AND | TOK_BAR_BAR | TOK_RPAREN ->
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : (('freshtv433 * _menhir_state * 'tv_int_expr * Lexing.position * Lexing.position) * Lexing.position) * _menhir_state * 'tv_int_expr * Lexing.position * Lexing.position) = Obj.magic _menhir_stack in
            ((let (((_menhir_stack, _menhir_s, x0, _startpos_x0_, _endpos_x0_), _endpos__menhir_p0_), _, x1, _startpos_x1_, _endpos_x1_) = _menhir_stack in
            let _menhir_p0 = () in
            let _startpos = _startpos_x0_ in
            let _endpos = _endpos_x1_ in
            let _v : 'tv_bool_expr = let e2 =
              let _startpos = _endpos__menhir_p0_ in
              let x = x1 in
              
# 217 "frontend/parser.mly"
      ( x, (_startpos, _endpos) )
# 1407 "frontend/parser.ml"
              
            in
            let o =
              
# 109 "frontend/parser.mly"
                     ( AST_GREATER_EQUAL )
# 1414 "frontend/parser.ml"
              
            in
            let _startpos_o_ = _endpos_x0_ in
            let e1 =
              let _endpos = _startpos_o_ in
              let x = x0 in
              
# 217 "frontend/parser.mly"
      ( x, (_startpos, _endpos) )
# 1424 "frontend/parser.ml"
              
            in
            
# 137 "frontend/parser.mly"
    ( AST_compare (o,e1,e2) )
# 1430 "frontend/parser.ml"
             in
            _menhir_goto_bool_expr _menhir_env _menhir_stack _menhir_s _v _startpos _endpos) : 'freshtv434)
        | _ ->
            assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
            _menhir_env._menhir_shifted <- (-1);
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : (('freshtv435 * _menhir_state * 'tv_int_expr * Lexing.position * Lexing.position) * Lexing.position) * _menhir_state * 'tv_int_expr * Lexing.position * Lexing.position) = Obj.magic _menhir_stack in
            ((let (_menhir_stack, _menhir_s, _, _, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv436)) : 'freshtv438)) : 'freshtv440)
    | MenhirState50 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : (('freshtv447 * _menhir_state * 'tv_int_expr * Lexing.position * Lexing.position) * Lexing.position) * _menhir_state * 'tv_int_expr * Lexing.position * Lexing.position) = Obj.magic _menhir_stack in
        ((assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
        let _tok = _menhir_env._menhir_token in
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : (('freshtv445 * _menhir_state * 'tv_int_expr * Lexing.position * Lexing.position) * Lexing.position) * _menhir_state * 'tv_int_expr * Lexing.position * Lexing.position) = _menhir_stack in
        let (_tok : token) = _tok in
        ((match _tok with
        | TOK_DIVIDE ->
            _menhir_run27 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_endp
        | TOK_MINUS ->
            _menhir_run29 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_startp _menhir_env._menhir_endp
        | TOK_PERCENT ->
            _menhir_run25 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_endp
        | TOK_PLUS ->
            _menhir_run23 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_startp _menhir_env._menhir_endp
        | TOK_STAR ->
            _menhir_run20 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_endp
        | TOK_AND_AND | TOK_BAR_BAR | TOK_RPAREN ->
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : (('freshtv441 * _menhir_state * 'tv_int_expr * Lexing.position * Lexing.position) * Lexing.position) * _menhir_state * 'tv_int_expr * Lexing.position * Lexing.position) = Obj.magic _menhir_stack in
            ((let (((_menhir_stack, _menhir_s, x0, _startpos_x0_, _endpos_x0_), _endpos__menhir_p0_), _, x1, _startpos_x1_, _endpos_x1_) = _menhir_stack in
            let _menhir_p0 = () in
            let _startpos = _startpos_x0_ in
            let _endpos = _endpos_x1_ in
            let _v : 'tv_bool_expr = let e2 =
              let _startpos = _endpos__menhir_p0_ in
              let x = x1 in
              
# 217 "frontend/parser.mly"
      ( x, (_startpos, _endpos) )
# 1472 "frontend/parser.ml"
              
            in
            let o =
              
# 107 "frontend/parser.mly"
                     ( AST_GREATER )
# 1479 "frontend/parser.ml"
              
            in
            let _startpos_o_ = _endpos_x0_ in
            let e1 =
              let _endpos = _startpos_o_ in
              let x = x0 in
              
# 217 "frontend/parser.mly"
      ( x, (_startpos, _endpos) )
# 1489 "frontend/parser.ml"
              
            in
            
# 137 "frontend/parser.mly"
    ( AST_compare (o,e1,e2) )
# 1495 "frontend/parser.ml"
             in
            _menhir_goto_bool_expr _menhir_env _menhir_stack _menhir_s _v _startpos _endpos) : 'freshtv442)
        | _ ->
            assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
            _menhir_env._menhir_shifted <- (-1);
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : (('freshtv443 * _menhir_state * 'tv_int_expr * Lexing.position * Lexing.position) * Lexing.position) * _menhir_state * 'tv_int_expr * Lexing.position * Lexing.position) = Obj.magic _menhir_stack in
            ((let (_menhir_stack, _menhir_s, _, _, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv444)) : 'freshtv446)) : 'freshtv448)
    | MenhirState52 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : (('freshtv455 * _menhir_state * 'tv_int_expr * Lexing.position * Lexing.position) * Lexing.position) * _menhir_state * 'tv_int_expr * Lexing.position * Lexing.position) = Obj.magic _menhir_stack in
        ((assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
        let _tok = _menhir_env._menhir_token in
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : (('freshtv453 * _menhir_state * 'tv_int_expr * Lexing.position * Lexing.position) * Lexing.position) * _menhir_state * 'tv_int_expr * Lexing.position * Lexing.position) = _menhir_stack in
        let (_tok : token) = _tok in
        ((match _tok with
        | TOK_DIVIDE ->
            _menhir_run27 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_endp
        | TOK_MINUS ->
            _menhir_run29 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_startp _menhir_env._menhir_endp
        | TOK_PERCENT ->
            _menhir_run25 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_endp
        | TOK_PLUS ->
            _menhir_run23 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_startp _menhir_env._menhir_endp
        | TOK_STAR ->
            _menhir_run20 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_endp
        | TOK_AND_AND | TOK_BAR_BAR | TOK_RPAREN ->
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : (('freshtv449 * _menhir_state * 'tv_int_expr * Lexing.position * Lexing.position) * Lexing.position) * _menhir_state * 'tv_int_expr * Lexing.position * Lexing.position) = Obj.magic _menhir_stack in
            ((let (((_menhir_stack, _menhir_s, x0, _startpos_x0_, _endpos_x0_), _endpos__menhir_p0_), _, x1, _startpos_x1_, _endpos_x1_) = _menhir_stack in
            let _menhir_p0 = () in
            let _startpos = _startpos_x0_ in
            let _endpos = _endpos_x1_ in
            let _v : 'tv_bool_expr = let e2 =
              let _startpos = _endpos__menhir_p0_ in
              let x = x1 in
              
# 217 "frontend/parser.mly"
      ( x, (_startpos, _endpos) )
# 1537 "frontend/parser.ml"
              
            in
            let o =
              
# 110 "frontend/parser.mly"
                     ( AST_EQUAL )
# 1544 "frontend/parser.ml"
              
            in
            let _startpos_o_ = _endpos_x0_ in
            let e1 =
              let _endpos = _startpos_o_ in
              let x = x0 in
              
# 217 "frontend/parser.mly"
      ( x, (_startpos, _endpos) )
# 1554 "frontend/parser.ml"
              
            in
            
# 137 "frontend/parser.mly"
    ( AST_compare (o,e1,e2) )
# 1560 "frontend/parser.ml"
             in
            _menhir_goto_bool_expr _menhir_env _menhir_stack _menhir_s _v _startpos _endpos) : 'freshtv450)
        | _ ->
            assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
            _menhir_env._menhir_shifted <- (-1);
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : (('freshtv451 * _menhir_state * 'tv_int_expr * Lexing.position * Lexing.position) * Lexing.position) * _menhir_state * 'tv_int_expr * Lexing.position * Lexing.position) = Obj.magic _menhir_stack in
            ((let (_menhir_stack, _menhir_s, _, _, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv452)) : 'freshtv454)) : 'freshtv456)
    | MenhirState38 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ('freshtv461 * _menhir_state * Lexing.position * Lexing.position) * _menhir_state * 'tv_int_expr * Lexing.position * Lexing.position) = Obj.magic _menhir_stack in
        ((assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
        let _tok = _menhir_env._menhir_token in
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ('freshtv459 * _menhir_state * Lexing.position * Lexing.position) * _menhir_state * 'tv_int_expr * Lexing.position * Lexing.position) = _menhir_stack in
        let (_tok : token) = _tok in
        ((match _tok with
        | TOK_DIVIDE ->
            _menhir_run27 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_endp
        | TOK_EQUAL_EQUAL ->
            _menhir_run52 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_endp
        | TOK_GREATER ->
            _menhir_run50 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_endp
        | TOK_GREATER_EQUAL ->
            _menhir_run48 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_endp
        | TOK_LESS ->
            _menhir_run46 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_endp
        | TOK_LESS_EQUAL ->
            _menhir_run44 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_endp
        | TOK_MINUS ->
            _menhir_run29 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_startp _menhir_env._menhir_endp
        | TOK_NOT_EQUAL ->
            _menhir_run42 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_endp
        | TOK_PERCENT ->
            _menhir_run25 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_endp
        | TOK_PLUS ->
            _menhir_run23 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_startp _menhir_env._menhir_endp
        | TOK_RPAREN ->
            _menhir_run22 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_startp _menhir_env._menhir_endp
        | TOK_STAR ->
            _menhir_run20 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_endp
        | _ ->
            assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
            _menhir_env._menhir_shifted <- (-1);
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : ('freshtv457 * _menhir_state * Lexing.position * Lexing.position) * _menhir_state * 'tv_int_expr * Lexing.position * Lexing.position) = Obj.magic _menhir_stack in
            ((let (_menhir_stack, _menhir_s, _, _, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv458)) : 'freshtv460)) : 'freshtv462)
    | _ ->
        _menhir_fail ()

and _menhir_run7 : _menhir_env -> 'ttv_tail -> _menhir_state -> (
# 56 "frontend/parser.mly"
       (string)
# 1616 "frontend/parser.ml"
) -> Lexing.position -> Lexing.position -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v _startpos _endpos ->
    let _ = _menhir_discard _menhir_env in
    let (_menhir_env : _menhir_env) = _menhir_env in
    let (_menhir_stack : 'freshtv341) = Obj.magic _menhir_stack in
    let (_menhir_s : _menhir_state) = _menhir_s in
    let (i : (
# 56 "frontend/parser.mly"
       (string)
# 1626 "frontend/parser.ml"
    )) = _v in
    let (_startpos_i_ : Lexing.position) = _startpos in
    let (_endpos_i_ : Lexing.position) = _endpos in
    ((let _v : 'tv_sign_int_literal = 
# 164 "frontend/parser.mly"
                       ( i )
# 1633 "frontend/parser.ml"
     in
    _menhir_goto_sign_int_literal _menhir_env _menhir_stack _menhir_s _v) : 'freshtv342)

and _menhir_run8 : _menhir_env -> 'ttv_tail -> _menhir_state -> Lexing.position -> Lexing.position -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _startpos _endpos ->
    let _menhir_stack = (_menhir_stack, _menhir_s, _startpos, _endpos) in
    let _tok = _menhir_discard _menhir_env in
    let (_menhir_env : _menhir_env) = _menhir_env in
    let (_menhir_stack : 'freshtv339 * _menhir_state * Lexing.position * Lexing.position) = _menhir_stack in
    let (_tok : token) = _tok in
    ((match _tok with
    | TOK_int _v ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv335 * _menhir_state * Lexing.position * Lexing.position) = Obj.magic _menhir_stack in
        let (_v : (
# 56 "frontend/parser.mly"
       (string)
# 1651 "frontend/parser.ml"
        )) = _v in
        let (_startpos : Lexing.position) = _menhir_env._menhir_startp in
        let (_endpos : Lexing.position) = _menhir_env._menhir_endp in
        ((let _ = _menhir_discard _menhir_env in
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv333 * _menhir_state * Lexing.position * Lexing.position) = Obj.magic _menhir_stack in
        let (i : (
# 56 "frontend/parser.mly"
       (string)
# 1661 "frontend/parser.ml"
        )) = _v in
        let (_startpos_i_ : Lexing.position) = _startpos in
        let (_endpos_i_ : Lexing.position) = _endpos in
        ((let (_menhir_stack, _menhir_s, _startpos__1_, _endpos__1_) = _menhir_stack in
        let _v : 'tv_sign_int_literal = 
# 165 "frontend/parser.mly"
                       ( i )
# 1669 "frontend/parser.ml"
         in
        _menhir_goto_sign_int_literal _menhir_env _menhir_stack _menhir_s _v) : 'freshtv334)) : 'freshtv336)
    | _ ->
        assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
        _menhir_env._menhir_shifted <- (-1);
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv337 * _menhir_state * Lexing.position * Lexing.position) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _menhir_s, _, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv338)) : 'freshtv340)

and _menhir_run10 : _menhir_env -> 'ttv_tail -> _menhir_state -> Lexing.position -> Lexing.position -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _startpos _endpos ->
    let _menhir_stack = (_menhir_stack, _menhir_s, _startpos, _endpos) in
    let _tok = _menhir_discard _menhir_env in
    let (_menhir_env : _menhir_env) = _menhir_env in
    let (_menhir_stack : 'freshtv331 * _menhir_state * Lexing.position * Lexing.position) = _menhir_stack in
    let (_tok : token) = _tok in
    ((match _tok with
    | TOK_int _v ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv327 * _menhir_state * Lexing.position * Lexing.position) = Obj.magic _menhir_stack in
        let (_v : (
# 56 "frontend/parser.mly"
       (string)
# 1694 "frontend/parser.ml"
        )) = _v in
        let (_startpos : Lexing.position) = _menhir_env._menhir_startp in
        let (_endpos : Lexing.position) = _menhir_env._menhir_endp in
        ((let _ = _menhir_discard _menhir_env in
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv325 * _menhir_state * Lexing.position * Lexing.position) = Obj.magic _menhir_stack in
        let (i : (
# 56 "frontend/parser.mly"
       (string)
# 1704 "frontend/parser.ml"
        )) = _v in
        let (_startpos_i_ : Lexing.position) = _startpos in
        let (_endpos_i_ : Lexing.position) = _endpos in
        ((let (_menhir_stack, _menhir_s, _startpos__1_, _endpos__1_) = _menhir_stack in
        let _v : 'tv_sign_int_literal = 
# 166 "frontend/parser.mly"
                       ( "-"^i )
# 1712 "frontend/parser.ml"
         in
        _menhir_goto_sign_int_literal _menhir_env _menhir_stack _menhir_s _v) : 'freshtv326)) : 'freshtv328)
    | _ ->
        assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
        _menhir_env._menhir_shifted <- (-1);
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv329 * _menhir_state * Lexing.position * Lexing.position) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _menhir_s, _, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv330)) : 'freshtv332)

and _menhir_goto_bool_expr : _menhir_env -> 'ttv_tail -> _menhir_state -> 'tv_bool_expr -> Lexing.position -> Lexing.position -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v _startpos _endpos ->
    let _menhir_stack = (_menhir_stack, _menhir_s, _v, _startpos, _endpos) in
    match _menhir_s with
    | MenhirState40 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ('freshtv265 * _menhir_state * Lexing.position * Lexing.position) * _menhir_state * 'tv_bool_expr * Lexing.position * Lexing.position) = Obj.magic _menhir_stack in
        ((let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ('freshtv263 * _menhir_state * Lexing.position * Lexing.position) * _menhir_state * 'tv_bool_expr * Lexing.position * Lexing.position) = Obj.magic _menhir_stack in
        ((let ((_menhir_stack, _menhir_s, _startpos__menhir_p0_, _endpos__menhir_p0_), _, x0, _startpos_x0_, _endpos_x0_) = _menhir_stack in
        let _menhir_p0 = () in
        let _startpos = _startpos__menhir_p0_ in
        let _endpos = _endpos_x0_ in
        let _v : 'tv_bool_expr = let e =
          let _startpos = _endpos__menhir_p0_ in
          let x = x0 in
          
# 217 "frontend/parser.mly"
      ( x, (_startpos, _endpos) )
# 1742 "frontend/parser.ml"
          
        in
        let o =
          
# 94 "frontend/parser.mly"
                     ( AST_NOT )
# 1749 "frontend/parser.ml"
          
        in
        
# 131 "frontend/parser.mly"
    ( AST_bool_unary (o,e) )
# 1755 "frontend/parser.ml"
         in
        _menhir_goto_bool_expr _menhir_env _menhir_stack _menhir_s _v _startpos _endpos) : 'freshtv264)) : 'freshtv266)
    | MenhirState38 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ('freshtv275 * _menhir_state * Lexing.position * Lexing.position) * _menhir_state * 'tv_bool_expr * Lexing.position * Lexing.position) = Obj.magic _menhir_stack in
        ((assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
        let _tok = _menhir_env._menhir_token in
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ('freshtv273 * _menhir_state * Lexing.position * Lexing.position) * _menhir_state * 'tv_bool_expr * Lexing.position * Lexing.position) = _menhir_stack in
        let (_tok : token) = _tok in
        ((match _tok with
        | TOK_AND_AND ->
            _menhir_run60 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_endp
        | TOK_BAR_BAR ->
            _menhir_run58 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_endp
        | TOK_RPAREN ->
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : ('freshtv269 * _menhir_state * Lexing.position * Lexing.position) * _menhir_state * 'tv_bool_expr * Lexing.position * Lexing.position) = Obj.magic _menhir_stack in
            let (_startpos : Lexing.position) = _menhir_env._menhir_startp in
            let (_endpos : Lexing.position) = _menhir_env._menhir_endp in
            ((let _ = _menhir_discard _menhir_env in
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : ('freshtv267 * _menhir_state * Lexing.position * Lexing.position) * _menhir_state * 'tv_bool_expr * Lexing.position * Lexing.position) = Obj.magic _menhir_stack in
            let (_startpos__3_ : Lexing.position) = _startpos in
            let (_endpos__3_ : Lexing.position) = _endpos in
            ((let ((_menhir_stack, _menhir_s, _startpos__1_, _endpos__1_), _, e, _startpos_e_, _endpos_e_) = _menhir_stack in
            let _startpos = _startpos__1_ in
            let _endpos = _endpos__3_ in
            let _v : 'tv_bool_expr = 
# 122 "frontend/parser.mly"
    ( e )
# 1787 "frontend/parser.ml"
             in
            _menhir_goto_bool_expr _menhir_env _menhir_stack _menhir_s _v _startpos _endpos) : 'freshtv268)) : 'freshtv270)
        | _ ->
            assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
            _menhir_env._menhir_shifted <- (-1);
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : ('freshtv271 * _menhir_state * Lexing.position * Lexing.position) * _menhir_state * 'tv_bool_expr * Lexing.position * Lexing.position) = Obj.magic _menhir_stack in
            ((let (_menhir_stack, _menhir_s, _, _, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv272)) : 'freshtv274)) : 'freshtv276)
    | MenhirState58 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : (('freshtv283 * _menhir_state * 'tv_bool_expr * Lexing.position * Lexing.position) * Lexing.position) * _menhir_state * 'tv_bool_expr * Lexing.position * Lexing.position) = Obj.magic _menhir_stack in
        ((assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
        let _tok = _menhir_env._menhir_token in
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : (('freshtv281 * _menhir_state * 'tv_bool_expr * Lexing.position * Lexing.position) * Lexing.position) * _menhir_state * 'tv_bool_expr * Lexing.position * Lexing.position) = _menhir_stack in
        let (_tok : token) = _tok in
        ((match _tok with
        | TOK_AND_AND ->
            _menhir_run60 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_endp
        | TOK_BAR_BAR | TOK_RPAREN ->
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : (('freshtv277 * _menhir_state * 'tv_bool_expr * Lexing.position * Lexing.position) * Lexing.position) * _menhir_state * 'tv_bool_expr * Lexing.position * Lexing.position) = Obj.magic _menhir_stack in
            ((let (((_menhir_stack, _menhir_s, x0, _startpos_x0_, _endpos_x0_), _endpos__menhir_p0_), _, x1, _startpos_x1_, _endpos_x1_) = _menhir_stack in
            let _menhir_p0 = () in
            let _startpos = _startpos_x0_ in
            let _endpos = _endpos_x1_ in
            let _v : 'tv_bool_expr = let e2 =
              let _startpos = _endpos__menhir_p0_ in
              let x = x1 in
              
# 217 "frontend/parser.mly"
      ( x, (_startpos, _endpos) )
# 1821 "frontend/parser.ml"
              
            in
            let o =
              
# 116 "frontend/parser.mly"
                     ( AST_OR )
# 1828 "frontend/parser.ml"
              
            in
            let _startpos_o_ = _endpos_x0_ in
            let e1 =
              let _endpos = _startpos_o_ in
              let x = x0 in
              
# 217 "frontend/parser.mly"
      ( x, (_startpos, _endpos) )
# 1838 "frontend/parser.ml"
              
            in
            
# 134 "frontend/parser.mly"
    ( AST_bool_binary (o,e1,e2) )
# 1844 "frontend/parser.ml"
             in
            _menhir_goto_bool_expr _menhir_env _menhir_stack _menhir_s _v _startpos _endpos) : 'freshtv278)
        | _ ->
            assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
            _menhir_env._menhir_shifted <- (-1);
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : (('freshtv279 * _menhir_state * 'tv_bool_expr * Lexing.position * Lexing.position) * Lexing.position) * _menhir_state * 'tv_bool_expr * Lexing.position * Lexing.position) = Obj.magic _menhir_stack in
            ((let (_menhir_stack, _menhir_s, _, _, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv280)) : 'freshtv282)) : 'freshtv284)
    | MenhirState60 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : (('freshtv287 * _menhir_state * 'tv_bool_expr * Lexing.position * Lexing.position) * Lexing.position) * _menhir_state * 'tv_bool_expr * Lexing.position * Lexing.position) = Obj.magic _menhir_stack in
        ((let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : (('freshtv285 * _menhir_state * 'tv_bool_expr * Lexing.position * Lexing.position) * Lexing.position) * _menhir_state * 'tv_bool_expr * Lexing.position * Lexing.position) = Obj.magic _menhir_stack in
        ((let (((_menhir_stack, _menhir_s, x0, _startpos_x0_, _endpos_x0_), _endpos__menhir_p0_), _, x1, _startpos_x1_, _endpos_x1_) = _menhir_stack in
        let _menhir_p0 = () in
        let _startpos = _startpos_x0_ in
        let _endpos = _endpos_x1_ in
        let _v : 'tv_bool_expr = let e2 =
          let _startpos = _endpos__menhir_p0_ in
          let x = x1 in
          
# 217 "frontend/parser.mly"
      ( x, (_startpos, _endpos) )
# 1869 "frontend/parser.ml"
          
        in
        let o =
          
# 115 "frontend/parser.mly"
                     ( AST_AND )
# 1876 "frontend/parser.ml"
          
        in
        let _startpos_o_ = _endpos_x0_ in
        let e1 =
          let _endpos = _startpos_o_ in
          let x = x0 in
          
# 217 "frontend/parser.mly"
      ( x, (_startpos, _endpos) )
# 1886 "frontend/parser.ml"
          
        in
        
# 134 "frontend/parser.mly"
    ( AST_bool_binary (o,e1,e2) )
# 1892 "frontend/parser.ml"
         in
        _menhir_goto_bool_expr _menhir_env _menhir_stack _menhir_s _v _startpos _endpos) : 'freshtv286)) : 'freshtv288)
    | MenhirState36 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : (('freshtv297 * _menhir_state * Lexing.position) * Lexing.position * Lexing.position) * _menhir_state * 'tv_bool_expr * Lexing.position * Lexing.position) = Obj.magic _menhir_stack in
        ((assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
        let _tok = _menhir_env._menhir_token in
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : (('freshtv295 * _menhir_state * Lexing.position) * Lexing.position * Lexing.position) * _menhir_state * 'tv_bool_expr * Lexing.position * Lexing.position) = _menhir_stack in
        let (_tok : token) = _tok in
        ((match _tok with
        | TOK_AND_AND ->
            _menhir_run60 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_endp
        | TOK_BAR_BAR ->
            _menhir_run58 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_endp
        | TOK_RPAREN ->
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : (('freshtv291 * _menhir_state * Lexing.position) * Lexing.position * Lexing.position) * _menhir_state * 'tv_bool_expr * Lexing.position * Lexing.position) = Obj.magic _menhir_stack in
            let (_startpos : Lexing.position) = _menhir_env._menhir_startp in
            let (_endpos : Lexing.position) = _menhir_env._menhir_endp in
            ((let _menhir_stack = (_menhir_stack, _startpos, _endpos) in
            let _tok = _menhir_discard _menhir_env in
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : ((('freshtv289 * _menhir_state * Lexing.position) * Lexing.position * Lexing.position) * _menhir_state * 'tv_bool_expr * Lexing.position * Lexing.position) * Lexing.position * Lexing.position) = _menhir_stack in
            let (_tok : token) = _tok in
            ((match _tok with
            | TOK_ASSERT ->
                _menhir_run85 _menhir_env (Obj.magic _menhir_stack) MenhirState63 _menhir_env._menhir_startp
            | TOK_HALT ->
                _menhir_run83 _menhir_env (Obj.magic _menhir_stack) MenhirState63 _menhir_env._menhir_startp
            | TOK_IF ->
                _menhir_run79 _menhir_env (Obj.magic _menhir_stack) MenhirState63 _menhir_env._menhir_startp
            | TOK_LCURLY ->
                _menhir_run73 _menhir_env (Obj.magic _menhir_stack) MenhirState63 _menhir_env._menhir_startp
            | TOK_PRINT ->
                _menhir_run64 _menhir_env (Obj.magic _menhir_stack) MenhirState63 _menhir_env._menhir_startp
            | TOK_WHILE ->
                _menhir_run35 _menhir_env (Obj.magic _menhir_stack) MenhirState63 _menhir_env._menhir_startp
            | TOK_id _v ->
                _menhir_run1 _menhir_env (Obj.magic _menhir_stack) MenhirState63 _v _menhir_env._menhir_startp _menhir_env._menhir_endp
            | _ ->
                assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
                _menhir_env._menhir_shifted <- (-1);
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState63) : 'freshtv290)) : 'freshtv292)
        | _ ->
            assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
            _menhir_env._menhir_shifted <- (-1);
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : (('freshtv293 * _menhir_state * Lexing.position) * Lexing.position * Lexing.position) * _menhir_state * 'tv_bool_expr * Lexing.position * Lexing.position) = Obj.magic _menhir_stack in
            ((let (_menhir_stack, _menhir_s, _, _, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv294)) : 'freshtv296)) : 'freshtv298)
    | MenhirState80 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : (('freshtv307 * _menhir_state * Lexing.position) * Lexing.position * Lexing.position) * _menhir_state * 'tv_bool_expr * Lexing.position * Lexing.position) = Obj.magic _menhir_stack in
        ((assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
        let _tok = _menhir_env._menhir_token in
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : (('freshtv305 * _menhir_state * Lexing.position) * Lexing.position * Lexing.position) * _menhir_state * 'tv_bool_expr * Lexing.position * Lexing.position) = _menhir_stack in
        let (_tok : token) = _tok in
        ((match _tok with
        | TOK_AND_AND ->
            _menhir_run60 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_endp
        | TOK_BAR_BAR ->
            _menhir_run58 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_endp
        | TOK_RPAREN ->
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : (('freshtv301 * _menhir_state * Lexing.position) * Lexing.position * Lexing.position) * _menhir_state * 'tv_bool_expr * Lexing.position * Lexing.position) = Obj.magic _menhir_stack in
            let (_startpos : Lexing.position) = _menhir_env._menhir_startp in
            let (_endpos : Lexing.position) = _menhir_env._menhir_endp in
            ((let _menhir_stack = (_menhir_stack, _startpos, _endpos) in
            let _tok = _menhir_discard _menhir_env in
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : ((('freshtv299 * _menhir_state * Lexing.position) * Lexing.position * Lexing.position) * _menhir_state * 'tv_bool_expr * Lexing.position * Lexing.position) * Lexing.position * Lexing.position) = _menhir_stack in
            let (_tok : token) = _tok in
            ((match _tok with
            | TOK_ASSERT ->
                _menhir_run85 _menhir_env (Obj.magic _menhir_stack) MenhirState82 _menhir_env._menhir_startp
            | TOK_HALT ->
                _menhir_run83 _menhir_env (Obj.magic _menhir_stack) MenhirState82 _menhir_env._menhir_startp
            | TOK_IF ->
                _menhir_run79 _menhir_env (Obj.magic _menhir_stack) MenhirState82 _menhir_env._menhir_startp
            | TOK_LCURLY ->
                _menhir_run73 _menhir_env (Obj.magic _menhir_stack) MenhirState82 _menhir_env._menhir_startp
            | TOK_PRINT ->
                _menhir_run64 _menhir_env (Obj.magic _menhir_stack) MenhirState82 _menhir_env._menhir_startp
            | TOK_WHILE ->
                _menhir_run35 _menhir_env (Obj.magic _menhir_stack) MenhirState82 _menhir_env._menhir_startp
            | TOK_id _v ->
                _menhir_run1 _menhir_env (Obj.magic _menhir_stack) MenhirState82 _v _menhir_env._menhir_startp _menhir_env._menhir_endp
            | _ ->
                assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
                _menhir_env._menhir_shifted <- (-1);
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState82) : 'freshtv300)) : 'freshtv302)
        | _ ->
            assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
            _menhir_env._menhir_shifted <- (-1);
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : (('freshtv303 * _menhir_state * Lexing.position) * Lexing.position * Lexing.position) * _menhir_state * 'tv_bool_expr * Lexing.position * Lexing.position) = Obj.magic _menhir_stack in
            ((let (_menhir_stack, _menhir_s, _, _, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv304)) : 'freshtv306)) : 'freshtv308)
    | MenhirState86 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : (('freshtv323 * _menhir_state * Lexing.position) * Lexing.position * Lexing.position) * _menhir_state * 'tv_bool_expr * Lexing.position * Lexing.position) = Obj.magic _menhir_stack in
        ((assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
        let _tok = _menhir_env._menhir_token in
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : (('freshtv321 * _menhir_state * Lexing.position) * Lexing.position * Lexing.position) * _menhir_state * 'tv_bool_expr * Lexing.position * Lexing.position) = _menhir_stack in
        let (_tok : token) = _tok in
        ((match _tok with
        | TOK_AND_AND ->
            _menhir_run60 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_endp
        | TOK_BAR_BAR ->
            _menhir_run58 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_endp
        | TOK_RPAREN ->
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : (('freshtv317 * _menhir_state * Lexing.position) * Lexing.position * Lexing.position) * _menhir_state * 'tv_bool_expr * Lexing.position * Lexing.position) = Obj.magic _menhir_stack in
            let (_startpos : Lexing.position) = _menhir_env._menhir_startp in
            let (_endpos : Lexing.position) = _menhir_env._menhir_endp in
            ((let _menhir_stack = (_menhir_stack, _startpos, _endpos) in
            let _tok = _menhir_discard _menhir_env in
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : ((('freshtv315 * _menhir_state * Lexing.position) * Lexing.position * Lexing.position) * _menhir_state * 'tv_bool_expr * Lexing.position * Lexing.position) * Lexing.position * Lexing.position) = _menhir_stack in
            let (_tok : token) = _tok in
            ((match _tok with
            | TOK_SEMICOLON ->
                let (_menhir_env : _menhir_env) = _menhir_env in
                let (_menhir_stack : ((('freshtv311 * _menhir_state * Lexing.position) * Lexing.position * Lexing.position) * _menhir_state * 'tv_bool_expr * Lexing.position * Lexing.position) * Lexing.position * Lexing.position) = Obj.magic _menhir_stack in
                let (_startpos : Lexing.position) = _menhir_env._menhir_startp in
                let (_endpos : Lexing.position) = _menhir_env._menhir_endp in
                ((let _ = _menhir_discard _menhir_env in
                let (_menhir_env : _menhir_env) = _menhir_env in
                let (_menhir_stack : ((('freshtv309 * _menhir_state * Lexing.position) * Lexing.position * Lexing.position) * _menhir_state * 'tv_bool_expr * Lexing.position * Lexing.position) * Lexing.position * Lexing.position) = Obj.magic _menhir_stack in
                let (_startpos__5_ : Lexing.position) = _startpos in
                let (_endpos__5_ : Lexing.position) = _endpos in
                ((let ((((_menhir_stack, _menhir_s, _startpos__1_), _startpos__menhir_p0_, _endpos__menhir_p0_), _, x0, _startpos_x0_, _endpos_x0_), _startpos__menhir_p1_, _endpos__menhir_p1_) = _menhir_stack in
                let _menhir_p1 = () in
                let _menhir_p0 = () in
                let _startpos = _startpos__1_ in
                let _endpos = _endpos__5_ in
                let _v : 'tv_stat = let e =
                  let _startpos = _endpos__menhir_p0_ in
                  let _endpos = _startpos__menhir_p1_ in
                  let x = x0 in
                  
# 217 "frontend/parser.mly"
      ( x, (_startpos, _endpos) )
# 2039 "frontend/parser.ml"
                  
                in
                
# 203 "frontend/parser.mly"
  ( AST_assert e )
# 2045 "frontend/parser.ml"
                 in
                _menhir_goto_stat _menhir_env _menhir_stack _menhir_s _v _startpos _endpos) : 'freshtv310)) : 'freshtv312)
            | _ ->
                assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
                _menhir_env._menhir_shifted <- (-1);
                let (_menhir_env : _menhir_env) = _menhir_env in
                let (_menhir_stack : ((('freshtv313 * _menhir_state * Lexing.position) * Lexing.position * Lexing.position) * _menhir_state * 'tv_bool_expr * Lexing.position * Lexing.position) * Lexing.position * Lexing.position) = Obj.magic _menhir_stack in
                ((let ((_menhir_stack, _menhir_s, _, _, _), _, _) = _menhir_stack in
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv314)) : 'freshtv316)) : 'freshtv318)
        | _ ->
            assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
            _menhir_env._menhir_shifted <- (-1);
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : (('freshtv319 * _menhir_state * Lexing.position) * Lexing.position * Lexing.position) * _menhir_state * 'tv_bool_expr * Lexing.position * Lexing.position) = Obj.magic _menhir_stack in
            ((let (_menhir_stack, _menhir_s, _, _, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv320)) : 'freshtv322)) : 'freshtv324)
    | _ ->
        _menhir_fail ()

and _menhir_goto_list_ext_stat__ : _menhir_env -> 'ttv_tail -> _menhir_state -> 'tv_list_ext_stat__ -> Lexing.position -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v _startpos ->
    let _menhir_stack = (_menhir_stack, _menhir_s, _v, _startpos) in
    match _menhir_s with
    | MenhirState94 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ('freshtv229 * _menhir_state * 'tv_stat * Lexing.position * Lexing.position) * _menhir_state * 'tv_list_ext_stat__ * Lexing.position) = Obj.magic _menhir_stack in
        ((let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ('freshtv227 * _menhir_state * 'tv_stat * Lexing.position * Lexing.position) * _menhir_state * 'tv_list_ext_stat__ * Lexing.position) = Obj.magic _menhir_stack in
        ((let ((_menhir_stack, _menhir_s, x0, _startpos_x0_, _endpos_x0_), _, xs, _startpos_xs_) = _menhir_stack in
        let _startpos = _startpos_x0_ in
        let _v : 'tv_list_ext_stat__ = let x =
          let _endpos = _startpos_xs_ in
          let x = x0 in
          
# 217 "frontend/parser.mly"
      ( x, (_startpos, _endpos) )
# 2082 "frontend/parser.ml"
          
        in
        
# 116 "/home/maxime/.opam/system/lib/menhir/standard.mly"
    ( x :: xs )
# 2088 "frontend/parser.ml"
         in
        _menhir_goto_list_ext_stat__ _menhir_env _menhir_stack _menhir_s _v _startpos) : 'freshtv228)) : 'freshtv230)
    | MenhirState78 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : (('freshtv245 * _menhir_state * Lexing.position) * _menhir_state * 'tv_list_ext_decl__ * Lexing.position) * _menhir_state * 'tv_list_ext_stat__ * Lexing.position) = Obj.magic _menhir_stack in
        ((assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
        let _tok = _menhir_env._menhir_token in
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : (('freshtv243 * _menhir_state * Lexing.position) * _menhir_state * 'tv_list_ext_decl__ * Lexing.position) * _menhir_state * 'tv_list_ext_stat__ * Lexing.position) = _menhir_stack in
        let (_tok : token) = _tok in
        ((match _tok with
        | TOK_RCURLY ->
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : (('freshtv239 * _menhir_state * Lexing.position) * _menhir_state * 'tv_list_ext_decl__ * Lexing.position) * _menhir_state * 'tv_list_ext_stat__ * Lexing.position) = Obj.magic _menhir_stack in
            let (_endpos : Lexing.position) = _menhir_env._menhir_endp in
            ((let _ = _menhir_discard _menhir_env in
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : (('freshtv237 * _menhir_state * Lexing.position) * _menhir_state * 'tv_list_ext_decl__ * Lexing.position) * _menhir_state * 'tv_list_ext_stat__ * Lexing.position) = Obj.magic _menhir_stack in
            let (_endpos__4_ : Lexing.position) = _endpos in
            ((let (((_menhir_stack, _menhir_s, _startpos__1_), _, d, _startpos_d_), _, l, _startpos_l_) = _menhir_stack in
            let _startpos = _startpos__1_ in
            let _endpos = _endpos__4_ in
            let _v : 'tv_block = 
# 175 "frontend/parser.mly"
                                                             ( d, l )
# 2114 "frontend/parser.ml"
             in
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : 'freshtv235) = _menhir_stack in
            let (_menhir_s : _menhir_state) = _menhir_s in
            let (_v : 'tv_block) = _v in
            let (_startpos : Lexing.position) = _startpos in
            let (_endpos : Lexing.position) = _endpos in
            ((let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : 'freshtv233) = Obj.magic _menhir_stack in
            let (_menhir_s : _menhir_state) = _menhir_s in
            let (_v : 'tv_block) = _v in
            let (_startpos : Lexing.position) = _startpos in
            let (_endpos : Lexing.position) = _endpos in
            ((let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : 'freshtv231) = Obj.magic _menhir_stack in
            let (_menhir_s : _menhir_state) = _menhir_s in
            let (l : 'tv_block) = _v in
            let (_startpos_l_ : Lexing.position) = _startpos in
            let (_endpos_l_ : Lexing.position) = _endpos in
            ((let _startpos = _startpos_l_ in
            let _endpos = _endpos_l_ in
            let _v : 'tv_stat = 
# 188 "frontend/parser.mly"
  ( AST_block (fst l, snd l) )
# 2139 "frontend/parser.ml"
             in
            _menhir_goto_stat _menhir_env _menhir_stack _menhir_s _v _startpos _endpos) : 'freshtv232)) : 'freshtv234)) : 'freshtv236)) : 'freshtv238)) : 'freshtv240)
        | _ ->
            assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
            _menhir_env._menhir_shifted <- (-1);
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : (('freshtv241 * _menhir_state * Lexing.position) * _menhir_state * 'tv_list_ext_decl__ * Lexing.position) * _menhir_state * 'tv_list_ext_stat__ * Lexing.position) = Obj.magic _menhir_stack in
            ((let (_menhir_stack, _menhir_s, _, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv242)) : 'freshtv244)) : 'freshtv246)
    | MenhirState0 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv261 * _menhir_state * 'tv_list_ext_stat__ * Lexing.position) = Obj.magic _menhir_stack in
        ((assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
        let _tok = _menhir_env._menhir_token in
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv259 * _menhir_state * 'tv_list_ext_stat__ * Lexing.position) = _menhir_stack in
        let (_tok : token) = _tok in
        ((match _tok with
        | TOK_EOF ->
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : 'freshtv255 * _menhir_state * 'tv_list_ext_stat__ * Lexing.position) = Obj.magic _menhir_stack in
            ((let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : 'freshtv253 * _menhir_state * 'tv_list_ext_stat__ * Lexing.position) = Obj.magic _menhir_stack in
            ((let (_menhir_stack, _menhir_s, t, _startpos_t_) = _menhir_stack in
            let _v : (
# 71 "frontend/parser.mly"
      (Abstract_syntax_tree.prog)
# 2167 "frontend/parser.ml"
            ) = 
# 80 "frontend/parser.mly"
                                ( t )
# 2171 "frontend/parser.ml"
             in
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : 'freshtv251) = _menhir_stack in
            let (_menhir_s : _menhir_state) = _menhir_s in
            let (_v : (
# 71 "frontend/parser.mly"
      (Abstract_syntax_tree.prog)
# 2179 "frontend/parser.ml"
            )) = _v in
            ((let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : 'freshtv249) = Obj.magic _menhir_stack in
            let (_menhir_s : _menhir_state) = _menhir_s in
            let (_v : (
# 71 "frontend/parser.mly"
      (Abstract_syntax_tree.prog)
# 2187 "frontend/parser.ml"
            )) = _v in
            ((let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : 'freshtv247) = Obj.magic _menhir_stack in
            let (_menhir_s : _menhir_state) = _menhir_s in
            let (_1 : (
# 71 "frontend/parser.mly"
      (Abstract_syntax_tree.prog)
# 2195 "frontend/parser.ml"
            )) = _v in
            (Obj.magic _1 : 'freshtv248)) : 'freshtv250)) : 'freshtv252)) : 'freshtv254)) : 'freshtv256)
        | _ ->
            assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
            _menhir_env._menhir_shifted <- (-1);
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : 'freshtv257 * _menhir_state * 'tv_list_ext_stat__ * Lexing.position) = Obj.magic _menhir_stack in
            ((let (_menhir_stack, _menhir_s, _, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv258)) : 'freshtv260)) : 'freshtv262)
    | _ ->
        _menhir_fail ()

and _menhir_run18 : _menhir_env -> 'ttv_tail -> _menhir_state -> Lexing.position -> Lexing.position -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _startpos _endpos ->
    let _menhir_stack = (_menhir_stack, _menhir_s, _startpos, _endpos) in
    let _tok = _menhir_discard _menhir_env in
    let (_menhir_env : _menhir_env) = _menhir_env in
    let (_menhir_stack : 'freshtv225 * _menhir_state * Lexing.position * Lexing.position) = _menhir_stack in
    let (_tok : token) = _tok in
    ((match _tok with
    | TOK_LPAREN ->
        _menhir_run18 _menhir_env (Obj.magic _menhir_stack) MenhirState18 _menhir_env._menhir_startp _menhir_env._menhir_endp
    | TOK_MINUS ->
        _menhir_run17 _menhir_env (Obj.magic _menhir_stack) MenhirState18 _menhir_env._menhir_startp _menhir_env._menhir_endp
    | TOK_PLUS ->
        _menhir_run16 _menhir_env (Obj.magic _menhir_stack) MenhirState18 _menhir_env._menhir_startp _menhir_env._menhir_endp
    | TOK_RAND ->
        _menhir_run5 _menhir_env (Obj.magic _menhir_stack) MenhirState18 _menhir_env._menhir_startp
    | TOK_id _v ->
        _menhir_run4 _menhir_env (Obj.magic _menhir_stack) MenhirState18 _v _menhir_env._menhir_startp _menhir_env._menhir_endp
    | TOK_int _v ->
        _menhir_run3 _menhir_env (Obj.magic _menhir_stack) MenhirState18 _v _menhir_env._menhir_startp _menhir_env._menhir_endp
    | _ ->
        assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
        _menhir_env._menhir_shifted <- (-1);
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState18) : 'freshtv226)

and _menhir_goto_loption_separated_nonempty_list_TOK_COMMA_ext_TOK_id___ : _menhir_env -> 'ttv_tail -> _menhir_state -> 'tv_loption_separated_nonempty_list_TOK_COMMA_ext_TOK_id___ -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v ->
    let _menhir_stack = (_menhir_stack, _menhir_s, _v) in
    let (_menhir_env : _menhir_env) = _menhir_env in
    let (_menhir_stack : (('freshtv223 * _menhir_state * Lexing.position) * Lexing.position * Lexing.position) * _menhir_state * 'tv_loption_separated_nonempty_list_TOK_COMMA_ext_TOK_id___) = Obj.magic _menhir_stack in
    ((assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
    let _tok = _menhir_env._menhir_token in
    let (_menhir_env : _menhir_env) = _menhir_env in
    let (_menhir_stack : (('freshtv221 * _menhir_state * Lexing.position) * Lexing.position * Lexing.position) * _menhir_state * 'tv_loption_separated_nonempty_list_TOK_COMMA_ext_TOK_id___) = _menhir_stack in
    let (_tok : token) = _tok in
    ((match _tok with
    | TOK_RPAREN ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : (('freshtv217 * _menhir_state * Lexing.position) * Lexing.position * Lexing.position) * _menhir_state * 'tv_loption_separated_nonempty_list_TOK_COMMA_ext_TOK_id___) = Obj.magic _menhir_stack in
        let (_startpos : Lexing.position) = _menhir_env._menhir_startp in
        let (_endpos : Lexing.position) = _menhir_env._menhir_endp in
        ((let _menhir_stack = (_menhir_stack, _startpos, _endpos) in
        let _tok = _menhir_discard _menhir_env in
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ((('freshtv215 * _menhir_state * Lexing.position) * Lexing.position * Lexing.position) * _menhir_state * 'tv_loption_separated_nonempty_list_TOK_COMMA_ext_TOK_id___) * Lexing.position * Lexing.position) = _menhir_stack in
        let (_tok : token) = _tok in
        ((match _tok with
        | TOK_SEMICOLON ->
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : ((('freshtv211 * _menhir_state * Lexing.position) * Lexing.position * Lexing.position) * _menhir_state * 'tv_loption_separated_nonempty_list_TOK_COMMA_ext_TOK_id___) * Lexing.position * Lexing.position) = Obj.magic _menhir_stack in
            let (_startpos : Lexing.position) = _menhir_env._menhir_startp in
            let (_endpos : Lexing.position) = _menhir_env._menhir_endp in
            ((let _ = _menhir_discard _menhir_env in
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : ((('freshtv209 * _menhir_state * Lexing.position) * Lexing.position * Lexing.position) * _menhir_state * 'tv_loption_separated_nonempty_list_TOK_COMMA_ext_TOK_id___) * Lexing.position * Lexing.position) = Obj.magic _menhir_stack in
            let (_startpos__5_ : Lexing.position) = _startpos in
            let (_endpos__5_ : Lexing.position) = _endpos in
            ((let ((((_menhir_stack, _menhir_s, _startpos__1_), _startpos__2_, _endpos__2_), _, xs0), _startpos__4_, _endpos__4_) = _menhir_stack in
            let _startpos = _startpos__1_ in
            let _endpos = _endpos__5_ in
            let _v : 'tv_stat = let l =
              let xs = xs0 in
              
# 135 "/home/maxime/.opam/system/lib/menhir/standard.mly"
    ( xs )
# 2273 "frontend/parser.ml"
              
            in
            
# 206 "frontend/parser.mly"
  ( AST_print l )
# 2279 "frontend/parser.ml"
             in
            _menhir_goto_stat _menhir_env _menhir_stack _menhir_s _v _startpos _endpos) : 'freshtv210)) : 'freshtv212)
        | _ ->
            assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
            _menhir_env._menhir_shifted <- (-1);
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : ((('freshtv213 * _menhir_state * Lexing.position) * Lexing.position * Lexing.position) * _menhir_state * 'tv_loption_separated_nonempty_list_TOK_COMMA_ext_TOK_id___) * Lexing.position * Lexing.position) = Obj.magic _menhir_stack in
            ((let ((_menhir_stack, _menhir_s, _), _, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv214)) : 'freshtv216)) : 'freshtv218)
    | _ ->
        assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
        _menhir_env._menhir_shifted <- (-1);
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : (('freshtv219 * _menhir_state * Lexing.position) * Lexing.position * Lexing.position) * _menhir_state * 'tv_loption_separated_nonempty_list_TOK_COMMA_ext_TOK_id___) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv220)) : 'freshtv222)) : 'freshtv224)

and _menhir_run66 : _menhir_env -> 'ttv_tail -> _menhir_state -> (
# 55 "frontend/parser.mly"
       (string)
# 2300 "frontend/parser.ml"
) -> Lexing.position -> Lexing.position -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v _startpos _endpos ->
    let _menhir_stack = (_menhir_stack, _menhir_s, _v, _startpos, _endpos) in
    let _tok = _menhir_discard _menhir_env in
    let (_menhir_env : _menhir_env) = _menhir_env in
    let (_menhir_stack : 'freshtv207 * _menhir_state * (
# 55 "frontend/parser.mly"
       (string)
# 2309 "frontend/parser.ml"
    ) * Lexing.position * Lexing.position) = _menhir_stack in
    let (_tok : token) = _tok in
    ((match _tok with
    | TOK_COMMA ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv201 * _menhir_state * (
# 55 "frontend/parser.mly"
       (string)
# 2318 "frontend/parser.ml"
        ) * Lexing.position * Lexing.position) = Obj.magic _menhir_stack in
        let (_startpos : Lexing.position) = _menhir_env._menhir_startp in
        let (_endpos : Lexing.position) = _menhir_env._menhir_endp in
        ((let _menhir_stack = (_menhir_stack, _startpos, _endpos) in
        let _tok = _menhir_discard _menhir_env in
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ('freshtv199 * _menhir_state * (
# 55 "frontend/parser.mly"
       (string)
# 2328 "frontend/parser.ml"
        ) * Lexing.position * Lexing.position) * Lexing.position * Lexing.position) = _menhir_stack in
        let (_tok : token) = _tok in
        ((match _tok with
        | TOK_id _v ->
            _menhir_run66 _menhir_env (Obj.magic _menhir_stack) MenhirState67 _v _menhir_env._menhir_startp _menhir_env._menhir_endp
        | _ ->
            assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
            _menhir_env._menhir_shifted <- (-1);
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState67) : 'freshtv200)) : 'freshtv202)
    | TOK_RPAREN ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv203 * _menhir_state * (
# 55 "frontend/parser.mly"
       (string)
# 2343 "frontend/parser.ml"
        ) * Lexing.position * Lexing.position) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _menhir_s, x0, _startpos_x0_, _endpos_x0_) = _menhir_stack in
        let _startpos = _startpos_x0_ in
        let _endpos = _endpos_x0_ in
        let _v : 'tv_separated_nonempty_list_TOK_COMMA_ext_TOK_id__ = let x =
          let x = x0 in
          
# 217 "frontend/parser.mly"
      ( x, (_startpos, _endpos) )
# 2353 "frontend/parser.ml"
          
        in
        
# 144 "/home/maxime/.opam/system/lib/menhir/standard.mly"
    ( [ x ] )
# 2359 "frontend/parser.ml"
         in
        _menhir_goto_separated_nonempty_list_TOK_COMMA_ext_TOK_id__ _menhir_env _menhir_stack _menhir_s _v) : 'freshtv204)
    | _ ->
        assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
        _menhir_env._menhir_shifted <- (-1);
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv205 * _menhir_state * (
# 55 "frontend/parser.mly"
       (string)
# 2369 "frontend/parser.ml"
        ) * Lexing.position * Lexing.position) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _menhir_s, _, _, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv206)) : 'freshtv208)

and _menhir_reduce27 : _menhir_env -> 'ttv_tail -> _menhir_state -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s ->
    let _startpos = _menhir_env._menhir_startp in
    let _v : 'tv_list_ext_decl__ = 
# 114 "/home/maxime/.opam/system/lib/menhir/standard.mly"
    ( [] )
# 2380 "frontend/parser.ml"
     in
    _menhir_goto_list_ext_decl__ _menhir_env _menhir_stack _menhir_s _v _startpos

and _menhir_run74 : _menhir_env -> 'ttv_tail -> _menhir_state -> Lexing.position -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _startpos ->
    let _ = _menhir_discard _menhir_env in
    let (_menhir_env : _menhir_env) = _menhir_env in
    let (_menhir_stack : 'freshtv197) = Obj.magic _menhir_stack in
    let (_menhir_s : _menhir_state) = _menhir_s in
    let (_startpos__1_ : Lexing.position) = _startpos in
    ((let _startpos = _startpos__1_ in
    let _v : 'tv_typ = 
# 183 "frontend/parser.mly"
          ( AST_INT )
# 2395 "frontend/parser.ml"
     in
    let (_menhir_env : _menhir_env) = _menhir_env in
    let (_menhir_stack : 'freshtv195) = _menhir_stack in
    let (_menhir_s : _menhir_state) = _menhir_s in
    let (_v : 'tv_typ) = _v in
    let (_startpos : Lexing.position) = _startpos in
    ((let _menhir_stack = (_menhir_stack, _menhir_s, _v, _startpos) in
    let (_menhir_env : _menhir_env) = _menhir_env in
    let (_menhir_stack : 'freshtv193 * _menhir_state * 'tv_typ * Lexing.position) = Obj.magic _menhir_stack in
    ((assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
    let _tok = _menhir_env._menhir_token in
    let (_menhir_env : _menhir_env) = _menhir_env in
    let (_menhir_stack : 'freshtv191 * _menhir_state * 'tv_typ * Lexing.position) = _menhir_stack in
    let (_tok : token) = _tok in
    ((match _tok with
    | TOK_id _v ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv187 * _menhir_state * 'tv_typ * Lexing.position) = Obj.magic _menhir_stack in
        let (_v : (
# 55 "frontend/parser.mly"
       (string)
# 2417 "frontend/parser.ml"
        )) = _v in
        let (_startpos : Lexing.position) = _menhir_env._menhir_startp in
        let (_endpos : Lexing.position) = _menhir_env._menhir_endp in
        ((let _menhir_stack = (_menhir_stack, _v, _startpos, _endpos) in
        let _tok = _menhir_discard _menhir_env in
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ('freshtv185 * _menhir_state * 'tv_typ * Lexing.position) * (
# 55 "frontend/parser.mly"
       (string)
# 2427 "frontend/parser.ml"
        ) * Lexing.position * Lexing.position) = _menhir_stack in
        let (_tok : token) = _tok in
        ((match _tok with
        | TOK_SEMICOLON ->
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : ('freshtv181 * _menhir_state * 'tv_typ * Lexing.position) * (
# 55 "frontend/parser.mly"
       (string)
# 2436 "frontend/parser.ml"
            ) * Lexing.position * Lexing.position) = Obj.magic _menhir_stack in
            let (_startpos : Lexing.position) = _menhir_env._menhir_startp in
            let (_endpos : Lexing.position) = _menhir_env._menhir_endp in
            ((let _ = _menhir_discard _menhir_env in
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : ('freshtv179 * _menhir_state * 'tv_typ * Lexing.position) * (
# 55 "frontend/parser.mly"
       (string)
# 2445 "frontend/parser.ml"
            ) * Lexing.position * Lexing.position) = Obj.magic _menhir_stack in
            let (_startpos__3_ : Lexing.position) = _startpos in
            let (_endpos__3_ : Lexing.position) = _endpos in
            ((let ((_menhir_stack, _menhir_s, t, _startpos_t_), v, _startpos_v_, _endpos_v_) = _menhir_stack in
            let _startpos = _startpos_t_ in
            let _v : 'tv_decl = 
# 179 "frontend/parser.mly"
                               ( t, v )
# 2454 "frontend/parser.ml"
             in
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : 'freshtv177) = _menhir_stack in
            let (_menhir_s : _menhir_state) = _menhir_s in
            let (_v : 'tv_decl) = _v in
            let (_startpos : Lexing.position) = _startpos in
            ((let _menhir_stack = (_menhir_stack, _menhir_s, _v, _startpos) in
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : 'freshtv175 * _menhir_state * 'tv_decl * Lexing.position) = Obj.magic _menhir_stack in
            ((assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
            let _tok = _menhir_env._menhir_token in
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : 'freshtv173 * _menhir_state * 'tv_decl * Lexing.position) = _menhir_stack in
            let (_tok : token) = _tok in
            ((match _tok with
            | TOK_INT ->
                _menhir_run74 _menhir_env (Obj.magic _menhir_stack) MenhirState98 _menhir_env._menhir_startp
            | TOK_ASSERT | TOK_HALT | TOK_IF | TOK_LCURLY | TOK_PRINT | TOK_RCURLY | TOK_WHILE | TOK_id _ ->
                _menhir_reduce27 _menhir_env (Obj.magic _menhir_stack) MenhirState98
            | _ ->
                assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
                _menhir_env._menhir_shifted <- (-1);
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState98) : 'freshtv174)) : 'freshtv176)) : 'freshtv178)) : 'freshtv180)) : 'freshtv182)
        | _ ->
            assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
            _menhir_env._menhir_shifted <- (-1);
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : ('freshtv183 * _menhir_state * 'tv_typ * Lexing.position) * (
# 55 "frontend/parser.mly"
       (string)
# 2485 "frontend/parser.ml"
            ) * Lexing.position * Lexing.position) = Obj.magic _menhir_stack in
            ((let ((_menhir_stack, _menhir_s, _, _), _, _, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv184)) : 'freshtv186)) : 'freshtv188)
    | _ ->
        assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
        _menhir_env._menhir_shifted <- (-1);
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv189 * _menhir_state * 'tv_typ * Lexing.position) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _menhir_s, _, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv190)) : 'freshtv192)) : 'freshtv194)) : 'freshtv196)) : 'freshtv198)

and _menhir_goto_stat : _menhir_env -> 'ttv_tail -> _menhir_state -> 'tv_stat -> Lexing.position -> Lexing.position -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v _startpos _endpos ->
    let _menhir_stack = (_menhir_stack, _menhir_s, _v, _startpos, _endpos) in
    match _menhir_s with
    | MenhirState82 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : (((('freshtv159 * _menhir_state * Lexing.position) * Lexing.position * Lexing.position) * _menhir_state * 'tv_bool_expr * Lexing.position * Lexing.position) * Lexing.position * Lexing.position) * _menhir_state * 'tv_stat * Lexing.position * Lexing.position) = Obj.magic _menhir_stack in
        ((assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
        let _tok = _menhir_env._menhir_token in
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : (((('freshtv157 * _menhir_state * Lexing.position) * Lexing.position * Lexing.position) * _menhir_state * 'tv_bool_expr * Lexing.position * Lexing.position) * Lexing.position * Lexing.position) * _menhir_state * 'tv_stat * Lexing.position * Lexing.position) = _menhir_stack in
        let (_tok : token) = _tok in
        ((match _tok with
        | TOK_ELSE ->
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : (((('freshtv151 * _menhir_state * Lexing.position) * Lexing.position * Lexing.position) * _menhir_state * 'tv_bool_expr * Lexing.position * Lexing.position) * Lexing.position * Lexing.position) * _menhir_state * 'tv_stat * Lexing.position * Lexing.position) = Obj.magic _menhir_stack in
            let (_startpos : Lexing.position) = _menhir_env._menhir_startp in
            let (_endpos : Lexing.position) = _menhir_env._menhir_endp in
            ((let _menhir_stack = (_menhir_stack, _startpos, _endpos) in
            let _tok = _menhir_discard _menhir_env in
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : ((((('freshtv149 * _menhir_state * Lexing.position) * Lexing.position * Lexing.position) * _menhir_state * 'tv_bool_expr * Lexing.position * Lexing.position) * Lexing.position * Lexing.position) * _menhir_state * 'tv_stat * Lexing.position * Lexing.position) * Lexing.position * Lexing.position) = _menhir_stack in
            let (_tok : token) = _tok in
            ((match _tok with
            | TOK_ASSERT ->
                _menhir_run85 _menhir_env (Obj.magic _menhir_stack) MenhirState91 _menhir_env._menhir_startp
            | TOK_HALT ->
                _menhir_run83 _menhir_env (Obj.magic _menhir_stack) MenhirState91 _menhir_env._menhir_startp
            | TOK_IF ->
                _menhir_run79 _menhir_env (Obj.magic _menhir_stack) MenhirState91 _menhir_env._menhir_startp
            | TOK_LCURLY ->
                _menhir_run73 _menhir_env (Obj.magic _menhir_stack) MenhirState91 _menhir_env._menhir_startp
            | TOK_PRINT ->
                _menhir_run64 _menhir_env (Obj.magic _menhir_stack) MenhirState91 _menhir_env._menhir_startp
            | TOK_WHILE ->
                _menhir_run35 _menhir_env (Obj.magic _menhir_stack) MenhirState91 _menhir_env._menhir_startp
            | TOK_id _v ->
                _menhir_run1 _menhir_env (Obj.magic _menhir_stack) MenhirState91 _v _menhir_env._menhir_startp _menhir_env._menhir_endp
            | _ ->
                assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
                _menhir_env._menhir_shifted <- (-1);
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState91) : 'freshtv150)) : 'freshtv152)
        | TOK_ASSERT | TOK_EOF | TOK_HALT | TOK_IF | TOK_LCURLY | TOK_PRINT | TOK_RCURLY | TOK_WHILE | TOK_id _ ->
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : (((('freshtv153 * _menhir_state * Lexing.position) * Lexing.position * Lexing.position) * _menhir_state * 'tv_bool_expr * Lexing.position * Lexing.position) * Lexing.position * Lexing.position) * _menhir_state * 'tv_stat * Lexing.position * Lexing.position) = Obj.magic _menhir_stack in
            ((let (((((_menhir_stack, _menhir_s, _startpos__1_), _startpos__menhir_p0_, _endpos__menhir_p0_), _, x0, _startpos_x0_, _endpos_x0_), _startpos__menhir_p1_, _endpos__menhir_p1_), _, x1, _startpos_x1_, _endpos_x1_) = _menhir_stack in
            let _menhir_p1 = () in
            let _menhir_p0 = () in
            let _startpos = _startpos__1_ in
            let _endpos = _endpos_x1_ in
            let _v : 'tv_stat = let s =
              let _startpos = _endpos__menhir_p1_ in
              let x = x1 in
              
# 217 "frontend/parser.mly"
      ( x, (_startpos, _endpos) )
# 2553 "frontend/parser.ml"
              
            in
            let e =
              let _startpos = _endpos__menhir_p0_ in
              let _endpos = _startpos__menhir_p1_ in
              let x = x0 in
              
# 217 "frontend/parser.mly"
      ( x, (_startpos, _endpos) )
# 2563 "frontend/parser.ml"
              
            in
            
# 194 "frontend/parser.mly"
  ( AST_if (e, s, None) )
# 2569 "frontend/parser.ml"
             in
            _menhir_goto_stat _menhir_env _menhir_stack _menhir_s _v _startpos _endpos) : 'freshtv154)
        | _ ->
            assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
            _menhir_env._menhir_shifted <- (-1);
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : (((('freshtv155 * _menhir_state * Lexing.position) * Lexing.position * Lexing.position) * _menhir_state * 'tv_bool_expr * Lexing.position * Lexing.position) * Lexing.position * Lexing.position) * _menhir_state * 'tv_stat * Lexing.position * Lexing.position) = Obj.magic _menhir_stack in
            ((let (_menhir_stack, _menhir_s, _, _, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv156)) : 'freshtv158)) : 'freshtv160)
    | MenhirState91 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : (((((('freshtv163 * _menhir_state * Lexing.position) * Lexing.position * Lexing.position) * _menhir_state * 'tv_bool_expr * Lexing.position * Lexing.position) * Lexing.position * Lexing.position) * _menhir_state * 'tv_stat * Lexing.position * Lexing.position) * Lexing.position * Lexing.position) * _menhir_state * 'tv_stat * Lexing.position * Lexing.position) = Obj.magic _menhir_stack in
        ((let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : (((((('freshtv161 * _menhir_state * Lexing.position) * Lexing.position * Lexing.position) * _menhir_state * 'tv_bool_expr * Lexing.position * Lexing.position) * Lexing.position * Lexing.position) * _menhir_state * 'tv_stat * Lexing.position * Lexing.position) * Lexing.position * Lexing.position) * _menhir_state * 'tv_stat * Lexing.position * Lexing.position) = Obj.magic _menhir_stack in
        ((let (((((((_menhir_stack, _menhir_s, _startpos__1_), _startpos__menhir_p0_, _endpos__menhir_p0_), _, x0, _startpos_x0_, _endpos_x0_), _startpos__menhir_p1_, _endpos__menhir_p1_), _, x1, _startpos_x1_, _endpos_x1_), _startpos__menhir_p2_, _endpos__menhir_p2_), _, x2, _startpos_x2_, _endpos_x2_) = _menhir_stack in
        let _menhir_p2 = () in
        let _menhir_p1 = () in
        let _menhir_p0 = () in
        let _startpos = _startpos__1_ in
        let _endpos = _endpos_x2_ in
        let _v : 'tv_stat = let t =
          let _startpos = _endpos__menhir_p2_ in
          let x = x2 in
          
# 217 "frontend/parser.mly"
      ( x, (_startpos, _endpos) )
# 2596 "frontend/parser.ml"
          
        in
        let s =
          let _startpos = _endpos__menhir_p1_ in
          let _endpos = _startpos__menhir_p2_ in
          let x = x1 in
          
# 217 "frontend/parser.mly"
      ( x, (_startpos, _endpos) )
# 2606 "frontend/parser.ml"
          
        in
        let e =
          let _startpos = _endpos__menhir_p0_ in
          let _endpos = _startpos__menhir_p1_ in
          let x = x0 in
          
# 217 "frontend/parser.mly"
      ( x, (_startpos, _endpos) )
# 2616 "frontend/parser.ml"
          
        in
        
# 197 "frontend/parser.mly"
  ( AST_if (e, s, Some t) )
# 2622 "frontend/parser.ml"
         in
        _menhir_goto_stat _menhir_env _menhir_stack _menhir_s _v _startpos _endpos) : 'freshtv162)) : 'freshtv164)
    | MenhirState0 | MenhirState94 | MenhirState78 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv167 * _menhir_state * 'tv_stat * Lexing.position * Lexing.position) = Obj.magic _menhir_stack in
        ((assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
        let _tok = _menhir_env._menhir_token in
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv165 * _menhir_state * 'tv_stat * Lexing.position * Lexing.position) = _menhir_stack in
        let (_tok : token) = _tok in
        ((match _tok with
        | TOK_ASSERT ->
            _menhir_run85 _menhir_env (Obj.magic _menhir_stack) MenhirState94 _menhir_env._menhir_startp
        | TOK_HALT ->
            _menhir_run83 _menhir_env (Obj.magic _menhir_stack) MenhirState94 _menhir_env._menhir_startp
        | TOK_IF ->
            _menhir_run79 _menhir_env (Obj.magic _menhir_stack) MenhirState94 _menhir_env._menhir_startp
        | TOK_LCURLY ->
            _menhir_run73 _menhir_env (Obj.magic _menhir_stack) MenhirState94 _menhir_env._menhir_startp
        | TOK_PRINT ->
            _menhir_run64 _menhir_env (Obj.magic _menhir_stack) MenhirState94 _menhir_env._menhir_startp
        | TOK_WHILE ->
            _menhir_run35 _menhir_env (Obj.magic _menhir_stack) MenhirState94 _menhir_env._menhir_startp
        | TOK_id _v ->
            _menhir_run1 _menhir_env (Obj.magic _menhir_stack) MenhirState94 _v _menhir_env._menhir_startp _menhir_env._menhir_endp
        | TOK_EOF | TOK_RCURLY ->
            _menhir_reduce29 _menhir_env (Obj.magic _menhir_stack) MenhirState94
        | _ ->
            assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
            _menhir_env._menhir_shifted <- (-1);
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState94) : 'freshtv166)) : 'freshtv168)
    | MenhirState63 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : (((('freshtv171 * _menhir_state * Lexing.position) * Lexing.position * Lexing.position) * _menhir_state * 'tv_bool_expr * Lexing.position * Lexing.position) * Lexing.position * Lexing.position) * _menhir_state * 'tv_stat * Lexing.position * Lexing.position) = Obj.magic _menhir_stack in
        ((let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : (((('freshtv169 * _menhir_state * Lexing.position) * Lexing.position * Lexing.position) * _menhir_state * 'tv_bool_expr * Lexing.position * Lexing.position) * Lexing.position * Lexing.position) * _menhir_state * 'tv_stat * Lexing.position * Lexing.position) = Obj.magic _menhir_stack in
        ((let (((((_menhir_stack, _menhir_s, _startpos__1_), _startpos__menhir_p0_, _endpos__menhir_p0_), _, x0, _startpos_x0_, _endpos_x0_), _startpos__menhir_p1_, _endpos__menhir_p1_), _, x1, _startpos_x1_, _endpos_x1_) = _menhir_stack in
        let _menhir_p1 = () in
        let _menhir_p0 = () in
        let _startpos = _startpos__1_ in
        let _endpos = _endpos_x1_ in
        let _v : 'tv_stat = let s =
          let _startpos = _endpos__menhir_p1_ in
          let x = x1 in
          
# 217 "frontend/parser.mly"
      ( x, (_startpos, _endpos) )
# 2670 "frontend/parser.ml"
          
        in
        let e =
          let _startpos = _endpos__menhir_p0_ in
          let _endpos = _startpos__menhir_p1_ in
          let x = x0 in
          
# 217 "frontend/parser.mly"
      ( x, (_startpos, _endpos) )
# 2680 "frontend/parser.ml"
          
        in
        
# 200 "frontend/parser.mly"
  ( AST_while (e, s) )
# 2686 "frontend/parser.ml"
         in
        _menhir_goto_stat _menhir_env _menhir_stack _menhir_s _v _startpos _endpos) : 'freshtv170)) : 'freshtv172)
    | _ ->
        _menhir_fail ()

and _menhir_run3 : _menhir_env -> 'ttv_tail -> _menhir_state -> (
# 56 "frontend/parser.mly"
       (string)
# 2695 "frontend/parser.ml"
) -> Lexing.position -> Lexing.position -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v _startpos _endpos ->
    let _ = _menhir_discard _menhir_env in
    let (_menhir_env : _menhir_env) = _menhir_env in
    let (_menhir_stack : 'freshtv147) = Obj.magic _menhir_stack in
    let (_menhir_s : _menhir_state) = _menhir_s in
    let (x0 : (
# 56 "frontend/parser.mly"
       (string)
# 2705 "frontend/parser.ml"
    )) = _v in
    let (_startpos_x0_ : Lexing.position) = _startpos in
    let (_endpos_x0_ : Lexing.position) = _endpos in
    ((let _startpos = _startpos_x0_ in
    let _endpos = _endpos_x0_ in
    let _v : 'tv_int_expr = let e =
      let x = x0 in
      
# 217 "frontend/parser.mly"
      ( x, (_startpos, _endpos) )
# 2716 "frontend/parser.ml"
      
    in
    
# 146 "frontend/parser.mly"
    ( AST_int_const e )
# 2722 "frontend/parser.ml"
     in
    _menhir_goto_int_expr _menhir_env _menhir_stack _menhir_s _v _startpos _endpos) : 'freshtv148)

and _menhir_run4 : _menhir_env -> 'ttv_tail -> _menhir_state -> (
# 55 "frontend/parser.mly"
       (string)
# 2729 "frontend/parser.ml"
) -> Lexing.position -> Lexing.position -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v _startpos _endpos ->
    let _ = _menhir_discard _menhir_env in
    let (_menhir_env : _menhir_env) = _menhir_env in
    let (_menhir_stack : 'freshtv145) = Obj.magic _menhir_stack in
    let (_menhir_s : _menhir_state) = _menhir_s in
    let (x0 : (
# 55 "frontend/parser.mly"
       (string)
# 2739 "frontend/parser.ml"
    )) = _v in
    let (_startpos_x0_ : Lexing.position) = _startpos in
    let (_endpos_x0_ : Lexing.position) = _endpos in
    ((let _startpos = _startpos_x0_ in
    let _endpos = _endpos_x0_ in
    let _v : 'tv_int_expr = let e =
      let x = x0 in
      
# 217 "frontend/parser.mly"
      ( x, (_startpos, _endpos) )
# 2750 "frontend/parser.ml"
      
    in
    
# 149 "frontend/parser.mly"
    ( AST_identifier e )
# 2756 "frontend/parser.ml"
     in
    _menhir_goto_int_expr _menhir_env _menhir_stack _menhir_s _v _startpos _endpos) : 'freshtv146)

and _menhir_run37 : _menhir_env -> 'ttv_tail -> _menhir_state -> Lexing.position -> Lexing.position -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _startpos _endpos ->
    let _ = _menhir_discard _menhir_env in
    let (_menhir_env : _menhir_env) = _menhir_env in
    let (_menhir_stack : 'freshtv143) = Obj.magic _menhir_stack in
    let (_menhir_s : _menhir_state) = _menhir_s in
    let (_startpos__1_ : Lexing.position) = _startpos in
    let (_endpos__1_ : Lexing.position) = _endpos in
    ((let _startpos = _startpos__1_ in
    let _endpos = _endpos__1_ in
    let _v : 'tv_bool_expr = 
# 125 "frontend/parser.mly"
    ( AST_bool_const true )
# 2773 "frontend/parser.ml"
     in
    _menhir_goto_bool_expr _menhir_env _menhir_stack _menhir_s _v _startpos _endpos) : 'freshtv144)

and _menhir_run5 : _menhir_env -> 'ttv_tail -> _menhir_state -> Lexing.position -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _startpos ->
    let _menhir_stack = (_menhir_stack, _menhir_s, _startpos) in
    let _tok = _menhir_discard _menhir_env in
    let (_menhir_env : _menhir_env) = _menhir_env in
    let (_menhir_stack : 'freshtv141 * _menhir_state * Lexing.position) = _menhir_stack in
    let (_tok : token) = _tok in
    ((match _tok with
    | TOK_LPAREN ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv137 * _menhir_state * Lexing.position) = Obj.magic _menhir_stack in
        let (_startpos : Lexing.position) = _menhir_env._menhir_startp in
        let (_endpos : Lexing.position) = _menhir_env._menhir_endp in
        ((let _menhir_stack = (_menhir_stack, _startpos, _endpos) in
        let _tok = _menhir_discard _menhir_env in
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ('freshtv135 * _menhir_state * Lexing.position) * Lexing.position * Lexing.position) = _menhir_stack in
        let (_tok : token) = _tok in
        ((match _tok with
        | TOK_MINUS ->
            _menhir_run10 _menhir_env (Obj.magic _menhir_stack) MenhirState6 _menhir_env._menhir_startp _menhir_env._menhir_endp
        | TOK_PLUS ->
            _menhir_run8 _menhir_env (Obj.magic _menhir_stack) MenhirState6 _menhir_env._menhir_startp _menhir_env._menhir_endp
        | TOK_int _v ->
            _menhir_run7 _menhir_env (Obj.magic _menhir_stack) MenhirState6 _v _menhir_env._menhir_startp _menhir_env._menhir_endp
        | _ ->
            assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
            _menhir_env._menhir_shifted <- (-1);
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState6) : 'freshtv136)) : 'freshtv138)
    | _ ->
        assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
        _menhir_env._menhir_shifted <- (-1);
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv139 * _menhir_state * Lexing.position) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv140)) : 'freshtv142)

and _menhir_run16 : _menhir_env -> 'ttv_tail -> _menhir_state -> Lexing.position -> Lexing.position -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _startpos _endpos ->
    let _menhir_stack = (_menhir_stack, _menhir_s, _startpos, _endpos) in
    let _tok = _menhir_discard _menhir_env in
    let (_menhir_env : _menhir_env) = _menhir_env in
    let (_menhir_stack : 'freshtv133 * _menhir_state * Lexing.position * Lexing.position) = _menhir_stack in
    let (_tok : token) = _tok in
    ((match _tok with
    | TOK_LPAREN ->
        _menhir_run18 _menhir_env (Obj.magic _menhir_stack) MenhirState16 _menhir_env._menhir_startp _menhir_env._menhir_endp
    | TOK_MINUS ->
        _menhir_run17 _menhir_env (Obj.magic _menhir_stack) MenhirState16 _menhir_env._menhir_startp _menhir_env._menhir_endp
    | TOK_PLUS ->
        _menhir_run16 _menhir_env (Obj.magic _menhir_stack) MenhirState16 _menhir_env._menhir_startp _menhir_env._menhir_endp
    | TOK_RAND ->
        _menhir_run5 _menhir_env (Obj.magic _menhir_stack) MenhirState16 _menhir_env._menhir_startp
    | TOK_id _v ->
        _menhir_run4 _menhir_env (Obj.magic _menhir_stack) MenhirState16 _v _menhir_env._menhir_startp _menhir_env._menhir_endp
    | TOK_int _v ->
        _menhir_run3 _menhir_env (Obj.magic _menhir_stack) MenhirState16 _v _menhir_env._menhir_startp _menhir_env._menhir_endp
    | _ ->
        assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
        _menhir_env._menhir_shifted <- (-1);
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState16) : 'freshtv134)

and _menhir_run17 : _menhir_env -> 'ttv_tail -> _menhir_state -> Lexing.position -> Lexing.position -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _startpos _endpos ->
    let _menhir_stack = (_menhir_stack, _menhir_s, _startpos, _endpos) in
    let _tok = _menhir_discard _menhir_env in
    let (_menhir_env : _menhir_env) = _menhir_env in
    let (_menhir_stack : 'freshtv131 * _menhir_state * Lexing.position * Lexing.position) = _menhir_stack in
    let (_tok : token) = _tok in
    ((match _tok with
    | TOK_LPAREN ->
        _menhir_run18 _menhir_env (Obj.magic _menhir_stack) MenhirState17 _menhir_env._menhir_startp _menhir_env._menhir_endp
    | TOK_MINUS ->
        _menhir_run17 _menhir_env (Obj.magic _menhir_stack) MenhirState17 _menhir_env._menhir_startp _menhir_env._menhir_endp
    | TOK_PLUS ->
        _menhir_run16 _menhir_env (Obj.magic _menhir_stack) MenhirState17 _menhir_env._menhir_startp _menhir_env._menhir_endp
    | TOK_RAND ->
        _menhir_run5 _menhir_env (Obj.magic _menhir_stack) MenhirState17 _menhir_env._menhir_startp
    | TOK_id _v ->
        _menhir_run4 _menhir_env (Obj.magic _menhir_stack) MenhirState17 _v _menhir_env._menhir_startp _menhir_env._menhir_endp
    | TOK_int _v ->
        _menhir_run3 _menhir_env (Obj.magic _menhir_stack) MenhirState17 _v _menhir_env._menhir_startp _menhir_env._menhir_endp
    | _ ->
        assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
        _menhir_env._menhir_shifted <- (-1);
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState17) : 'freshtv132)

and _menhir_run38 : _menhir_env -> 'ttv_tail -> _menhir_state -> Lexing.position -> Lexing.position -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _startpos _endpos ->
    let _menhir_stack = (_menhir_stack, _menhir_s, _startpos, _endpos) in
    let _tok = _menhir_discard _menhir_env in
    let (_menhir_env : _menhir_env) = _menhir_env in
    let (_menhir_stack : 'freshtv129 * _menhir_state * Lexing.position * Lexing.position) = _menhir_stack in
    let (_tok : token) = _tok in
    ((match _tok with
    | TOK_EXCLAIM ->
        _menhir_run40 _menhir_env (Obj.magic _menhir_stack) MenhirState38 _menhir_env._menhir_startp _menhir_env._menhir_endp
    | TOK_FALSE ->
        _menhir_run39 _menhir_env (Obj.magic _menhir_stack) MenhirState38 _menhir_env._menhir_startp _menhir_env._menhir_endp
    | TOK_LPAREN ->
        _menhir_run38 _menhir_env (Obj.magic _menhir_stack) MenhirState38 _menhir_env._menhir_startp _menhir_env._menhir_endp
    | TOK_MINUS ->
        _menhir_run17 _menhir_env (Obj.magic _menhir_stack) MenhirState38 _menhir_env._menhir_startp _menhir_env._menhir_endp
    | TOK_PLUS ->
        _menhir_run16 _menhir_env (Obj.magic _menhir_stack) MenhirState38 _menhir_env._menhir_startp _menhir_env._menhir_endp
    | TOK_RAND ->
        _menhir_run5 _menhir_env (Obj.magic _menhir_stack) MenhirState38 _menhir_env._menhir_startp
    | TOK_TRUE ->
        _menhir_run37 _menhir_env (Obj.magic _menhir_stack) MenhirState38 _menhir_env._menhir_startp _menhir_env._menhir_endp
    | TOK_id _v ->
        _menhir_run4 _menhir_env (Obj.magic _menhir_stack) MenhirState38 _v _menhir_env._menhir_startp _menhir_env._menhir_endp
    | TOK_int _v ->
        _menhir_run3 _menhir_env (Obj.magic _menhir_stack) MenhirState38 _v _menhir_env._menhir_startp _menhir_env._menhir_endp
    | _ ->
        assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
        _menhir_env._menhir_shifted <- (-1);
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState38) : 'freshtv130)

and _menhir_run39 : _menhir_env -> 'ttv_tail -> _menhir_state -> Lexing.position -> Lexing.position -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _startpos _endpos ->
    let _ = _menhir_discard _menhir_env in
    let (_menhir_env : _menhir_env) = _menhir_env in
    let (_menhir_stack : 'freshtv127) = Obj.magic _menhir_stack in
    let (_menhir_s : _menhir_state) = _menhir_s in
    let (_startpos__1_ : Lexing.position) = _startpos in
    let (_endpos__1_ : Lexing.position) = _endpos in
    ((let _startpos = _startpos__1_ in
    let _endpos = _endpos__1_ in
    let _v : 'tv_bool_expr = 
# 128 "frontend/parser.mly"
    ( AST_bool_const false )
# 2908 "frontend/parser.ml"
     in
    _menhir_goto_bool_expr _menhir_env _menhir_stack _menhir_s _v _startpos _endpos) : 'freshtv128)

and _menhir_run40 : _menhir_env -> 'ttv_tail -> _menhir_state -> Lexing.position -> Lexing.position -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _startpos _endpos ->
    let _menhir_stack = (_menhir_stack, _menhir_s, _startpos, _endpos) in
    let _tok = _menhir_discard _menhir_env in
    let (_menhir_env : _menhir_env) = _menhir_env in
    let (_menhir_stack : 'freshtv125 * _menhir_state * Lexing.position * Lexing.position) = _menhir_stack in
    let (_tok : token) = _tok in
    ((match _tok with
    | TOK_EXCLAIM ->
        _menhir_run40 _menhir_env (Obj.magic _menhir_stack) MenhirState40 _menhir_env._menhir_startp _menhir_env._menhir_endp
    | TOK_FALSE ->
        _menhir_run39 _menhir_env (Obj.magic _menhir_stack) MenhirState40 _menhir_env._menhir_startp _menhir_env._menhir_endp
    | TOK_LPAREN ->
        _menhir_run38 _menhir_env (Obj.magic _menhir_stack) MenhirState40 _menhir_env._menhir_startp _menhir_env._menhir_endp
    | TOK_MINUS ->
        _menhir_run17 _menhir_env (Obj.magic _menhir_stack) MenhirState40 _menhir_env._menhir_startp _menhir_env._menhir_endp
    | TOK_PLUS ->
        _menhir_run16 _menhir_env (Obj.magic _menhir_stack) MenhirState40 _menhir_env._menhir_startp _menhir_env._menhir_endp
    | TOK_RAND ->
        _menhir_run5 _menhir_env (Obj.magic _menhir_stack) MenhirState40 _menhir_env._menhir_startp
    | TOK_TRUE ->
        _menhir_run37 _menhir_env (Obj.magic _menhir_stack) MenhirState40 _menhir_env._menhir_startp _menhir_env._menhir_endp
    | TOK_id _v ->
        _menhir_run4 _menhir_env (Obj.magic _menhir_stack) MenhirState40 _v _menhir_env._menhir_startp _menhir_env._menhir_endp
    | TOK_int _v ->
        _menhir_run3 _menhir_env (Obj.magic _menhir_stack) MenhirState40 _v _menhir_env._menhir_startp _menhir_env._menhir_endp
    | _ ->
        assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
        _menhir_env._menhir_shifted <- (-1);
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState40) : 'freshtv126)

and _menhir_discard : _menhir_env -> token =
  fun _menhir_env ->
    let lexbuf = _menhir_env._menhir_lexbuf in
    let _tok = _menhir_env._menhir_lexer lexbuf in
    _menhir_env._menhir_token <- _tok;
    _menhir_env._menhir_startp <- lexbuf.Lexing.lex_start_p;
    _menhir_env._menhir_endp <- lexbuf.Lexing.lex_curr_p;
    let shifted = Pervasives.(+) _menhir_env._menhir_shifted 1 in
    if Pervasives.(>=) shifted 0 then
      _menhir_env._menhir_shifted <- shifted;
    _tok

and _menhir_errorcase : _menhir_env -> 'ttv_tail -> _menhir_state -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s ->
    match _menhir_s with
    | MenhirState98 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv57 * _menhir_state * 'tv_decl * Lexing.position) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _menhir_s, _, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv58)
    | MenhirState94 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv59 * _menhir_state * 'tv_stat * Lexing.position * Lexing.position) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _menhir_s, _, _, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv60)
    | MenhirState91 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ((((('freshtv61 * _menhir_state * Lexing.position) * Lexing.position * Lexing.position) * _menhir_state * 'tv_bool_expr * Lexing.position * Lexing.position) * Lexing.position * Lexing.position) * _menhir_state * 'tv_stat * Lexing.position * Lexing.position) * Lexing.position * Lexing.position) = Obj.magic _menhir_stack in
        ((let ((_menhir_stack, _menhir_s, _, _, _), _, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv62)
    | MenhirState86 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ('freshtv63 * _menhir_state * Lexing.position) * Lexing.position * Lexing.position) = Obj.magic _menhir_stack in
        ((let ((_menhir_stack, _menhir_s, _), _, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv64)
    | MenhirState82 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ((('freshtv65 * _menhir_state * Lexing.position) * Lexing.position * Lexing.position) * _menhir_state * 'tv_bool_expr * Lexing.position * Lexing.position) * Lexing.position * Lexing.position) = Obj.magic _menhir_stack in
        ((let ((_menhir_stack, _menhir_s, _, _, _), _, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv66)
    | MenhirState80 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ('freshtv67 * _menhir_state * Lexing.position) * Lexing.position * Lexing.position) = Obj.magic _menhir_stack in
        ((let ((_menhir_stack, _menhir_s, _), _, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv68)
    | MenhirState78 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ('freshtv69 * _menhir_state * Lexing.position) * _menhir_state * 'tv_list_ext_decl__ * Lexing.position) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _menhir_s, _, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv70)
    | MenhirState73 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv71 * _menhir_state * Lexing.position) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv72)
    | MenhirState67 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ('freshtv73 * _menhir_state * (
# 55 "frontend/parser.mly"
       (string)
# 3003 "frontend/parser.ml"
        ) * Lexing.position * Lexing.position) * Lexing.position * Lexing.position) = Obj.magic _menhir_stack in
        ((let ((_menhir_stack, _menhir_s, _, _, _), _, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv74)
    | MenhirState65 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ('freshtv75 * _menhir_state * Lexing.position) * Lexing.position * Lexing.position) = Obj.magic _menhir_stack in
        ((let ((_menhir_stack, _menhir_s, _), _, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv76)
    | MenhirState63 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ((('freshtv77 * _menhir_state * Lexing.position) * Lexing.position * Lexing.position) * _menhir_state * 'tv_bool_expr * Lexing.position * Lexing.position) * Lexing.position * Lexing.position) = Obj.magic _menhir_stack in
        ((let ((_menhir_stack, _menhir_s, _, _, _), _, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv78)
    | MenhirState60 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ('freshtv79 * _menhir_state * 'tv_bool_expr * Lexing.position * Lexing.position) * Lexing.position) = Obj.magic _menhir_stack in
        ((let ((_menhir_stack, _menhir_s, _, _, _), _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv80)
    | MenhirState58 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ('freshtv81 * _menhir_state * 'tv_bool_expr * Lexing.position * Lexing.position) * Lexing.position) = Obj.magic _menhir_stack in
        ((let ((_menhir_stack, _menhir_s, _, _, _), _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv82)
    | MenhirState52 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ('freshtv83 * _menhir_state * 'tv_int_expr * Lexing.position * Lexing.position) * Lexing.position) = Obj.magic _menhir_stack in
        ((let ((_menhir_stack, _menhir_s, _, _, _), _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv84)
    | MenhirState50 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ('freshtv85 * _menhir_state * 'tv_int_expr * Lexing.position * Lexing.position) * Lexing.position) = Obj.magic _menhir_stack in
        ((let ((_menhir_stack, _menhir_s, _, _, _), _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv86)
    | MenhirState48 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ('freshtv87 * _menhir_state * 'tv_int_expr * Lexing.position * Lexing.position) * Lexing.position) = Obj.magic _menhir_stack in
        ((let ((_menhir_stack, _menhir_s, _, _, _), _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv88)
    | MenhirState46 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ('freshtv89 * _menhir_state * 'tv_int_expr * Lexing.position * Lexing.position) * Lexing.position) = Obj.magic _menhir_stack in
        ((let ((_menhir_stack, _menhir_s, _, _, _), _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv90)
    | MenhirState44 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ('freshtv91 * _menhir_state * 'tv_int_expr * Lexing.position * Lexing.position) * Lexing.position) = Obj.magic _menhir_stack in
        ((let ((_menhir_stack, _menhir_s, _, _, _), _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv92)
    | MenhirState42 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ('freshtv93 * _menhir_state * 'tv_int_expr * Lexing.position * Lexing.position) * Lexing.position) = Obj.magic _menhir_stack in
        ((let ((_menhir_stack, _menhir_s, _, _, _), _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv94)
    | MenhirState40 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv95 * _menhir_state * Lexing.position * Lexing.position) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _menhir_s, _, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv96)
    | MenhirState38 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv97 * _menhir_state * Lexing.position * Lexing.position) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _menhir_s, _, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv98)
    | MenhirState36 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ('freshtv99 * _menhir_state * Lexing.position) * Lexing.position * Lexing.position) = Obj.magic _menhir_stack in
        ((let ((_menhir_stack, _menhir_s, _), _, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv100)
    | MenhirState29 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ('freshtv101 * _menhir_state * 'tv_int_expr * Lexing.position * Lexing.position) * Lexing.position * Lexing.position) = Obj.magic _menhir_stack in
        ((let ((_menhir_stack, _menhir_s, _, _, _), _, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv102)
    | MenhirState27 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ('freshtv103 * _menhir_state * 'tv_int_expr * Lexing.position * Lexing.position) * Lexing.position) = Obj.magic _menhir_stack in
        ((let ((_menhir_stack, _menhir_s, _, _, _), _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv104)
    | MenhirState25 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ('freshtv105 * _menhir_state * 'tv_int_expr * Lexing.position * Lexing.position) * Lexing.position) = Obj.magic _menhir_stack in
        ((let ((_menhir_stack, _menhir_s, _, _, _), _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv106)
    | MenhirState23 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ('freshtv107 * _menhir_state * 'tv_int_expr * Lexing.position * Lexing.position) * Lexing.position * Lexing.position) = Obj.magic _menhir_stack in
        ((let ((_menhir_stack, _menhir_s, _, _, _), _, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv108)
    | MenhirState20 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ('freshtv109 * _menhir_state * 'tv_int_expr * Lexing.position * Lexing.position) * Lexing.position) = Obj.magic _menhir_stack in
        ((let ((_menhir_stack, _menhir_s, _, _, _), _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv110)
    | MenhirState18 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv111 * _menhir_state * Lexing.position * Lexing.position) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _menhir_s, _, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv112)
    | MenhirState17 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv113 * _menhir_state * Lexing.position * Lexing.position) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _menhir_s, _, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv114)
    | MenhirState16 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv115 * _menhir_state * Lexing.position * Lexing.position) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _menhir_s, _, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv116)
    | MenhirState13 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ((('freshtv117 * _menhir_state * Lexing.position) * Lexing.position * Lexing.position) * _menhir_state * 'tv_sign_int_literal) * Lexing.position * Lexing.position) = Obj.magic _menhir_stack in
        ((let ((_menhir_stack, _menhir_s, _), _, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv118)
    | MenhirState6 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ('freshtv119 * _menhir_state * Lexing.position) * Lexing.position * Lexing.position) = Obj.magic _menhir_stack in
        ((let ((_menhir_stack, _menhir_s, _), _, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv120)
    | MenhirState2 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ('freshtv121 * _menhir_state * (
# 55 "frontend/parser.mly"
       (string)
# 3127 "frontend/parser.ml"
        ) * Lexing.position * Lexing.position) * Lexing.position * Lexing.position) = Obj.magic _menhir_stack in
        ((let ((_menhir_stack, _menhir_s, _, _, _), _, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv122)
    | MenhirState0 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv123) = Obj.magic _menhir_stack in
        (raise _eRR : 'freshtv124)

and _menhir_reduce29 : _menhir_env -> 'ttv_tail -> _menhir_state -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s ->
    let _startpos = _menhir_env._menhir_startp in
    let _v : 'tv_list_ext_stat__ = 
# 114 "/home/maxime/.opam/system/lib/menhir/standard.mly"
    ( [] )
# 3142 "frontend/parser.ml"
     in
    _menhir_goto_list_ext_stat__ _menhir_env _menhir_stack _menhir_s _v _startpos

and _menhir_run1 : _menhir_env -> 'ttv_tail -> _menhir_state -> (
# 55 "frontend/parser.mly"
       (string)
# 3149 "frontend/parser.ml"
) -> Lexing.position -> Lexing.position -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v _startpos _endpos ->
    let _menhir_stack = (_menhir_stack, _menhir_s, _v, _startpos, _endpos) in
    let _tok = _menhir_discard _menhir_env in
    let (_menhir_env : _menhir_env) = _menhir_env in
    let (_menhir_stack : 'freshtv55 * _menhir_state * (
# 55 "frontend/parser.mly"
       (string)
# 3158 "frontend/parser.ml"
    ) * Lexing.position * Lexing.position) = _menhir_stack in
    let (_tok : token) = _tok in
    ((match _tok with
    | TOK_EQUAL ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv51 * _menhir_state * (
# 55 "frontend/parser.mly"
       (string)
# 3167 "frontend/parser.ml"
        ) * Lexing.position * Lexing.position) = Obj.magic _menhir_stack in
        let (_startpos : Lexing.position) = _menhir_env._menhir_startp in
        let (_endpos : Lexing.position) = _menhir_env._menhir_endp in
        ((let _menhir_stack = (_menhir_stack, _startpos, _endpos) in
        let _tok = _menhir_discard _menhir_env in
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ('freshtv49 * _menhir_state * (
# 55 "frontend/parser.mly"
       (string)
# 3177 "frontend/parser.ml"
        ) * Lexing.position * Lexing.position) * Lexing.position * Lexing.position) = _menhir_stack in
        let (_tok : token) = _tok in
        ((match _tok with
        | TOK_LPAREN ->
            _menhir_run18 _menhir_env (Obj.magic _menhir_stack) MenhirState2 _menhir_env._menhir_startp _menhir_env._menhir_endp
        | TOK_MINUS ->
            _menhir_run17 _menhir_env (Obj.magic _menhir_stack) MenhirState2 _menhir_env._menhir_startp _menhir_env._menhir_endp
        | TOK_PLUS ->
            _menhir_run16 _menhir_env (Obj.magic _menhir_stack) MenhirState2 _menhir_env._menhir_startp _menhir_env._menhir_endp
        | TOK_RAND ->
            _menhir_run5 _menhir_env (Obj.magic _menhir_stack) MenhirState2 _menhir_env._menhir_startp
        | TOK_id _v ->
            _menhir_run4 _menhir_env (Obj.magic _menhir_stack) MenhirState2 _v _menhir_env._menhir_startp _menhir_env._menhir_endp
        | TOK_int _v ->
            _menhir_run3 _menhir_env (Obj.magic _menhir_stack) MenhirState2 _v _menhir_env._menhir_startp _menhir_env._menhir_endp
        | _ ->
            assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
            _menhir_env._menhir_shifted <- (-1);
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState2) : 'freshtv50)) : 'freshtv52)
    | _ ->
        assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
        _menhir_env._menhir_shifted <- (-1);
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv53 * _menhir_state * (
# 55 "frontend/parser.mly"
       (string)
# 3204 "frontend/parser.ml"
        ) * Lexing.position * Lexing.position) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _menhir_s, _, _, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv54)) : 'freshtv56)

and _menhir_run35 : _menhir_env -> 'ttv_tail -> _menhir_state -> Lexing.position -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _startpos ->
    let _menhir_stack = (_menhir_stack, _menhir_s, _startpos) in
    let _tok = _menhir_discard _menhir_env in
    let (_menhir_env : _menhir_env) = _menhir_env in
    let (_menhir_stack : 'freshtv47 * _menhir_state * Lexing.position) = _menhir_stack in
    let (_tok : token) = _tok in
    ((match _tok with
    | TOK_LPAREN ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv43 * _menhir_state * Lexing.position) = Obj.magic _menhir_stack in
        let (_startpos : Lexing.position) = _menhir_env._menhir_startp in
        let (_endpos : Lexing.position) = _menhir_env._menhir_endp in
        ((let _menhir_stack = (_menhir_stack, _startpos, _endpos) in
        let _tok = _menhir_discard _menhir_env in
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ('freshtv41 * _menhir_state * Lexing.position) * Lexing.position * Lexing.position) = _menhir_stack in
        let (_tok : token) = _tok in
        ((match _tok with
        | TOK_EXCLAIM ->
            _menhir_run40 _menhir_env (Obj.magic _menhir_stack) MenhirState36 _menhir_env._menhir_startp _menhir_env._menhir_endp
        | TOK_FALSE ->
            _menhir_run39 _menhir_env (Obj.magic _menhir_stack) MenhirState36 _menhir_env._menhir_startp _menhir_env._menhir_endp
        | TOK_LPAREN ->
            _menhir_run38 _menhir_env (Obj.magic _menhir_stack) MenhirState36 _menhir_env._menhir_startp _menhir_env._menhir_endp
        | TOK_MINUS ->
            _menhir_run17 _menhir_env (Obj.magic _menhir_stack) MenhirState36 _menhir_env._menhir_startp _menhir_env._menhir_endp
        | TOK_PLUS ->
            _menhir_run16 _menhir_env (Obj.magic _menhir_stack) MenhirState36 _menhir_env._menhir_startp _menhir_env._menhir_endp
        | TOK_RAND ->
            _menhir_run5 _menhir_env (Obj.magic _menhir_stack) MenhirState36 _menhir_env._menhir_startp
        | TOK_TRUE ->
            _menhir_run37 _menhir_env (Obj.magic _menhir_stack) MenhirState36 _menhir_env._menhir_startp _menhir_env._menhir_endp
        | TOK_id _v ->
            _menhir_run4 _menhir_env (Obj.magic _menhir_stack) MenhirState36 _v _menhir_env._menhir_startp _menhir_env._menhir_endp
        | TOK_int _v ->
            _menhir_run3 _menhir_env (Obj.magic _menhir_stack) MenhirState36 _v _menhir_env._menhir_startp _menhir_env._menhir_endp
        | _ ->
            assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
            _menhir_env._menhir_shifted <- (-1);
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState36) : 'freshtv42)) : 'freshtv44)
    | _ ->
        assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
        _menhir_env._menhir_shifted <- (-1);
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv45 * _menhir_state * Lexing.position) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv46)) : 'freshtv48)

and _menhir_run64 : _menhir_env -> 'ttv_tail -> _menhir_state -> Lexing.position -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _startpos ->
    let _menhir_stack = (_menhir_stack, _menhir_s, _startpos) in
    let _tok = _menhir_discard _menhir_env in
    let (_menhir_env : _menhir_env) = _menhir_env in
    let (_menhir_stack : 'freshtv39 * _menhir_state * Lexing.position) = _menhir_stack in
    let (_tok : token) = _tok in
    ((match _tok with
    | TOK_LPAREN ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv35 * _menhir_state * Lexing.position) = Obj.magic _menhir_stack in
        let (_startpos : Lexing.position) = _menhir_env._menhir_startp in
        let (_endpos : Lexing.position) = _menhir_env._menhir_endp in
        ((let _menhir_stack = (_menhir_stack, _startpos, _endpos) in
        let _tok = _menhir_discard _menhir_env in
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ('freshtv33 * _menhir_state * Lexing.position) * Lexing.position * Lexing.position) = _menhir_stack in
        let (_tok : token) = _tok in
        ((match _tok with
        | TOK_id _v ->
            _menhir_run66 _menhir_env (Obj.magic _menhir_stack) MenhirState65 _v _menhir_env._menhir_startp _menhir_env._menhir_endp
        | TOK_RPAREN ->
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : 'freshtv31) = Obj.magic _menhir_stack in
            let (_menhir_s : _menhir_state) = MenhirState65 in
            ((let _v : 'tv_loption_separated_nonempty_list_TOK_COMMA_ext_TOK_id___ = 
# 57 "/home/maxime/.opam/system/lib/menhir/standard.mly"
    ( [] )
# 3286 "frontend/parser.ml"
             in
            _menhir_goto_loption_separated_nonempty_list_TOK_COMMA_ext_TOK_id___ _menhir_env _menhir_stack _menhir_s _v) : 'freshtv32)
        | _ ->
            assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
            _menhir_env._menhir_shifted <- (-1);
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState65) : 'freshtv34)) : 'freshtv36)
    | _ ->
        assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
        _menhir_env._menhir_shifted <- (-1);
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv37 * _menhir_state * Lexing.position) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv38)) : 'freshtv40)

and _menhir_run73 : _menhir_env -> 'ttv_tail -> _menhir_state -> Lexing.position -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _startpos ->
    let _menhir_stack = (_menhir_stack, _menhir_s, _startpos) in
    let _tok = _menhir_discard _menhir_env in
    let (_menhir_env : _menhir_env) = _menhir_env in
    let (_menhir_stack : 'freshtv29 * _menhir_state * Lexing.position) = _menhir_stack in
    let (_tok : token) = _tok in
    ((match _tok with
    | TOK_INT ->
        _menhir_run74 _menhir_env (Obj.magic _menhir_stack) MenhirState73 _menhir_env._menhir_startp
    | TOK_ASSERT | TOK_HALT | TOK_IF | TOK_LCURLY | TOK_PRINT | TOK_RCURLY | TOK_WHILE | TOK_id _ ->
        _menhir_reduce27 _menhir_env (Obj.magic _menhir_stack) MenhirState73
    | _ ->
        assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
        _menhir_env._menhir_shifted <- (-1);
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState73) : 'freshtv30)

and _menhir_run79 : _menhir_env -> 'ttv_tail -> _menhir_state -> Lexing.position -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _startpos ->
    let _menhir_stack = (_menhir_stack, _menhir_s, _startpos) in
    let _tok = _menhir_discard _menhir_env in
    let (_menhir_env : _menhir_env) = _menhir_env in
    let (_menhir_stack : 'freshtv27 * _menhir_state * Lexing.position) = _menhir_stack in
    let (_tok : token) = _tok in
    ((match _tok with
    | TOK_LPAREN ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv23 * _menhir_state * Lexing.position) = Obj.magic _menhir_stack in
        let (_startpos : Lexing.position) = _menhir_env._menhir_startp in
        let (_endpos : Lexing.position) = _menhir_env._menhir_endp in
        ((let _menhir_stack = (_menhir_stack, _startpos, _endpos) in
        let _tok = _menhir_discard _menhir_env in
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ('freshtv21 * _menhir_state * Lexing.position) * Lexing.position * Lexing.position) = _menhir_stack in
        let (_tok : token) = _tok in
        ((match _tok with
        | TOK_EXCLAIM ->
            _menhir_run40 _menhir_env (Obj.magic _menhir_stack) MenhirState80 _menhir_env._menhir_startp _menhir_env._menhir_endp
        | TOK_FALSE ->
            _menhir_run39 _menhir_env (Obj.magic _menhir_stack) MenhirState80 _menhir_env._menhir_startp _menhir_env._menhir_endp
        | TOK_LPAREN ->
            _menhir_run38 _menhir_env (Obj.magic _menhir_stack) MenhirState80 _menhir_env._menhir_startp _menhir_env._menhir_endp
        | TOK_MINUS ->
            _menhir_run17 _menhir_env (Obj.magic _menhir_stack) MenhirState80 _menhir_env._menhir_startp _menhir_env._menhir_endp
        | TOK_PLUS ->
            _menhir_run16 _menhir_env (Obj.magic _menhir_stack) MenhirState80 _menhir_env._menhir_startp _menhir_env._menhir_endp
        | TOK_RAND ->
            _menhir_run5 _menhir_env (Obj.magic _menhir_stack) MenhirState80 _menhir_env._menhir_startp
        | TOK_TRUE ->
            _menhir_run37 _menhir_env (Obj.magic _menhir_stack) MenhirState80 _menhir_env._menhir_startp _menhir_env._menhir_endp
        | TOK_id _v ->
            _menhir_run4 _menhir_env (Obj.magic _menhir_stack) MenhirState80 _v _menhir_env._menhir_startp _menhir_env._menhir_endp
        | TOK_int _v ->
            _menhir_run3 _menhir_env (Obj.magic _menhir_stack) MenhirState80 _v _menhir_env._menhir_startp _menhir_env._menhir_endp
        | _ ->
            assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
            _menhir_env._menhir_shifted <- (-1);
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState80) : 'freshtv22)) : 'freshtv24)
    | _ ->
        assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
        _menhir_env._menhir_shifted <- (-1);
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv25 * _menhir_state * Lexing.position) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv26)) : 'freshtv28)

and _menhir_run83 : _menhir_env -> 'ttv_tail -> _menhir_state -> Lexing.position -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _startpos ->
    let _menhir_stack = (_menhir_stack, _menhir_s, _startpos) in
    let _tok = _menhir_discard _menhir_env in
    let (_menhir_env : _menhir_env) = _menhir_env in
    let (_menhir_stack : 'freshtv19 * _menhir_state * Lexing.position) = _menhir_stack in
    let (_tok : token) = _tok in
    ((match _tok with
    | TOK_SEMICOLON ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv15 * _menhir_state * Lexing.position) = Obj.magic _menhir_stack in
        let (_startpos : Lexing.position) = _menhir_env._menhir_startp in
        let (_endpos : Lexing.position) = _menhir_env._menhir_endp in
        ((let _ = _menhir_discard _menhir_env in
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv13 * _menhir_state * Lexing.position) = Obj.magic _menhir_stack in
        let (_startpos__2_ : Lexing.position) = _startpos in
        let (_endpos__2_ : Lexing.position) = _endpos in
        ((let (_menhir_stack, _menhir_s, _startpos__1_) = _menhir_stack in
        let _startpos = _startpos__1_ in
        let _endpos = _endpos__2_ in
        let _v : 'tv_stat = 
# 209 "frontend/parser.mly"
  ( AST_HALT )
# 3391 "frontend/parser.ml"
         in
        _menhir_goto_stat _menhir_env _menhir_stack _menhir_s _v _startpos _endpos) : 'freshtv14)) : 'freshtv16)
    | _ ->
        assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
        _menhir_env._menhir_shifted <- (-1);
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv17 * _menhir_state * Lexing.position) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv18)) : 'freshtv20)

and _menhir_run85 : _menhir_env -> 'ttv_tail -> _menhir_state -> Lexing.position -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _startpos ->
    let _menhir_stack = (_menhir_stack, _menhir_s, _startpos) in
    let _tok = _menhir_discard _menhir_env in
    let (_menhir_env : _menhir_env) = _menhir_env in
    let (_menhir_stack : 'freshtv11 * _menhir_state * Lexing.position) = _menhir_stack in
    let (_tok : token) = _tok in
    ((match _tok with
    | TOK_LPAREN ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv7 * _menhir_state * Lexing.position) = Obj.magic _menhir_stack in
        let (_startpos : Lexing.position) = _menhir_env._menhir_startp in
        let (_endpos : Lexing.position) = _menhir_env._menhir_endp in
        ((let _menhir_stack = (_menhir_stack, _startpos, _endpos) in
        let _tok = _menhir_discard _menhir_env in
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ('freshtv5 * _menhir_state * Lexing.position) * Lexing.position * Lexing.position) = _menhir_stack in
        let (_tok : token) = _tok in
        ((match _tok with
        | TOK_EXCLAIM ->
            _menhir_run40 _menhir_env (Obj.magic _menhir_stack) MenhirState86 _menhir_env._menhir_startp _menhir_env._menhir_endp
        | TOK_FALSE ->
            _menhir_run39 _menhir_env (Obj.magic _menhir_stack) MenhirState86 _menhir_env._menhir_startp _menhir_env._menhir_endp
        | TOK_LPAREN ->
            _menhir_run38 _menhir_env (Obj.magic _menhir_stack) MenhirState86 _menhir_env._menhir_startp _menhir_env._menhir_endp
        | TOK_MINUS ->
            _menhir_run17 _menhir_env (Obj.magic _menhir_stack) MenhirState86 _menhir_env._menhir_startp _menhir_env._menhir_endp
        | TOK_PLUS ->
            _menhir_run16 _menhir_env (Obj.magic _menhir_stack) MenhirState86 _menhir_env._menhir_startp _menhir_env._menhir_endp
        | TOK_RAND ->
            _menhir_run5 _menhir_env (Obj.magic _menhir_stack) MenhirState86 _menhir_env._menhir_startp
        | TOK_TRUE ->
            _menhir_run37 _menhir_env (Obj.magic _menhir_stack) MenhirState86 _menhir_env._menhir_startp _menhir_env._menhir_endp
        | TOK_id _v ->
            _menhir_run4 _menhir_env (Obj.magic _menhir_stack) MenhirState86 _v _menhir_env._menhir_startp _menhir_env._menhir_endp
        | TOK_int _v ->
            _menhir_run3 _menhir_env (Obj.magic _menhir_stack) MenhirState86 _v _menhir_env._menhir_startp _menhir_env._menhir_endp
        | _ ->
            assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
            _menhir_env._menhir_shifted <- (-1);
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState86) : 'freshtv6)) : 'freshtv8)
    | _ ->
        assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
        _menhir_env._menhir_shifted <- (-1);
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv9 * _menhir_state * Lexing.position) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv10)) : 'freshtv12)

and file : (Lexing.lexbuf -> token) -> Lexing.lexbuf -> (
# 71 "frontend/parser.mly"
      (Abstract_syntax_tree.prog)
# 3454 "frontend/parser.ml"
) =
  fun lexer lexbuf ->
    let _menhir_env =
      let (lexer : Lexing.lexbuf -> token) = lexer in
      let (lexbuf : Lexing.lexbuf) = lexbuf in
      ((let _tok = lexer lexbuf in
      {
        _menhir_lexer = lexer;
        _menhir_lexbuf = lexbuf;
        _menhir_token = _tok;
        _menhir_startp = lexbuf.Lexing.lex_start_p;
        _menhir_endp = lexbuf.Lexing.lex_curr_p;
        _menhir_shifted = max_int;
        }) : _menhir_env)
    in
    Obj.magic (let (_menhir_env : _menhir_env) = _menhir_env in
    let (_menhir_stack : 'freshtv3) = () in
    ((assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
    let _tok = _menhir_env._menhir_token in
    let (_menhir_env : _menhir_env) = _menhir_env in
    let (_menhir_stack : 'freshtv1) = _menhir_stack in
    let (_tok : token) = _tok in
    ((match _tok with
    | TOK_ASSERT ->
        _menhir_run85 _menhir_env (Obj.magic _menhir_stack) MenhirState0 _menhir_env._menhir_startp
    | TOK_HALT ->
        _menhir_run83 _menhir_env (Obj.magic _menhir_stack) MenhirState0 _menhir_env._menhir_startp
    | TOK_IF ->
        _menhir_run79 _menhir_env (Obj.magic _menhir_stack) MenhirState0 _menhir_env._menhir_startp
    | TOK_LCURLY ->
        _menhir_run73 _menhir_env (Obj.magic _menhir_stack) MenhirState0 _menhir_env._menhir_startp
    | TOK_PRINT ->
        _menhir_run64 _menhir_env (Obj.magic _menhir_stack) MenhirState0 _menhir_env._menhir_startp
    | TOK_WHILE ->
        _menhir_run35 _menhir_env (Obj.magic _menhir_stack) MenhirState0 _menhir_env._menhir_startp
    | TOK_id _v ->
        _menhir_run1 _menhir_env (Obj.magic _menhir_stack) MenhirState0 _v _menhir_env._menhir_startp _menhir_env._menhir_endp
    | TOK_EOF ->
        _menhir_reduce29 _menhir_env (Obj.magic _menhir_stack) MenhirState0
    | _ ->
        assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
        _menhir_env._menhir_shifted <- (-1);
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState0) : 'freshtv2)) : 'freshtv4))




