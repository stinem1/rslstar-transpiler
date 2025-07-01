module Syntax.Parse

open FSharp.Text.Lexing
open System.IO
open AST
open Error

let setInitialPos (lexbuf: LexBuffer<_>) filename =
    lexbuf.EndPos <-
        { pos_fname = filename
          pos_orig_lnum = 1
          pos_lnum = 1
          pos_bol = 1
          pos_cnum = 1 }

let tokenIdToString id =
    match id with
    | Parser.TOKEN_EOF -> "EOF"
    | Parser.TOKEN_IDENT -> "<identifier>"
    | Parser.TOKEN_PRIME_IDENT -> "<primed_identifier>"
    | Parser.TOKEN_INT -> "<int>"
    | Parser.TOKEN_BOOL -> "<bool>"
    | Parser.TOKEN_LEFT_CURLY_DOT -> "{."
    | Parser.TOKEN_RIGHT_CURLY_DOT -> ".}"
    | Parser.TOKEN_LEFT_DOUBLE_CURLY -> "{|"
    | Parser.TOKEN_RIGHT_DOUBLE_CURLY -> "|}"
    | Parser.TOKEN_LEFT_PAREN -> "("
    | Parser.TOKEN_RIGHT_PAREN -> ")"
    | Parser.TOKEN_LEFT_SQUARE_DOT -> "[."
    | Parser.TOKEN_RIGHT_SQUARE_DOT -> ".]"
    | Parser.TOKEN_LEFT_SQUARE -> "["
    | Parser.TOKEN_RIGHT_SQUARE -> "]"
    | Parser.TOKEN_COMMA -> ","
    | Parser.TOKEN_RIGHT_ARROW -> "->"
    | Parser.TOKEN_BAR -> "|"
    | Parser.TOKEN_COLON -> ":"
    | Parser.TOKEN_LONG_DOUBLE_RIGHT_ARROW -> "==>"
    | Parser.TOKEN_TIMES -> "><"
    | Parser.TOKEN_LAMBDA -> "-\\"
    | Parser.TOKEN_COLON_DASH -> ":-"
    | Parser.TOKEN_TURNSTILE -> "|-"
    | Parser.TOKEN_EQ_EQ -> "=="
    | Parser.TOKEN_PLUS -> "+"
    | Parser.TOKEN_MINUS -> "-"
    | Parser.TOKEN_BACK_SLASH -> "\\"
    | Parser.TOKEN_STAR -> "*"
    | Parser.TOKEN_FORWARD_SLASH -> "/"
    | Parser.TOKEN_EQ -> "="
    | Parser.TOKEN_NEQ -> "~="
    | Parser.TOKEN_GE -> ">"
    | Parser.TOKEN_LE -> "<"
    | Parser.TOKEN_GEQ -> ">="
    | Parser.TOKEN_LEQ -> "<="
    | Parser.TOKEN_UNTIL -> "U"
    | Parser.TOKEN_GLOBAL -> "G"
    | Parser.TOKEN_FINALLY -> "F"
    | Parser.TOKEN_NEXT -> "X"
    | Parser.TOKEN_NON_DET_CHOICE -> "[=]"
    | Parser.TOKEN_PRIORITY_CHOICE -> "[>]"
    | Parser.TOKEN_IMP -> "=>"
    | Parser.TOKEN_OR -> "\\/"
    | Parser.TOKEN_AND -> "/\\"
    | Parser.TOKEN_NOT -> "~"
    | Parser.TOKEN_TYPE -> "type"
    | Parser.TOKEN_VALUE -> "value"
    | Parser.TOKEN_VARIABLE -> "variable"
    | Parser.TOKEN_TRANSITION_RULES -> "transition_rules"
    | Parser.TOKEN_TRANSITION_SYSTEM -> "transition_system"
    | Parser.TOKEN_OF -> "of"
    | Parser.TOKEN_SCHEME -> "scheme"
    | Parser.TOKEN_THEN -> "then"
    | Parser.TOKEN_INIT_CONSTRAINT -> "init_constraint"
    | Parser.TOKEN_IS -> "is"
    | Parser.TOKEN_LET -> "let"
    | Parser.TOKEN_LTL_ASSERTION -> "ltl_assertion"
    | Parser.TOKEN_CLASS -> "class"
    | Parser.TOKEN_ELSE -> "else"
    | Parser.TOKEN_END -> "end"
    | Parser.TOKEN_EXISTS -> "exists"
    | Parser.TOKEN_IF -> "if"
    | Parser.TOKEN_IN -> "in"
    | Parser.TOKEN_TYPE_BOOL -> "Bool"
    | Parser.TOKEN_TYPE_INT -> "Int"
    | Parser.TOKEN_ALL -> "all"
    | Parser.TOKEN_ARRAY -> "array"
    | Parser.TOKEN_AXIOM -> "axiom"
    | Parser.TOKEN_end_of_input -> "End of Input"
    | Parser.TOKEN_error -> "Error"

let parseLexBuffer (lexbuf: LexBuffer<char>) (filename: string) : Result<string * Scheme, List<SyntaxError>> =
    setInitialPos lexbuf filename

    try
        Ok(filename, Parser.scheme Lexer.tokenize lexbuf)
    with
    | Util.InvalidToken(span, token) -> Error [ InvalidToken(span, token) ]

    | Util.InvalidSyntax(span, token, expectedTags) ->
        let expected = List.map (Parser.tokenTagToTokenId >> tokenIdToString) expectedTags
        Error [ InvalidSyntax(span, token, expected) ]

    | Util.ReservedKeyword(span, token) -> Error [ ReservedKeyword(span, token) ]

    | Util.InvalidInt(span, msg) -> Error [ InvalidInt(span, msg) ]

    | exn -> raise exn

let parseFile (path: string) : Result<string * Scheme, List<SyntaxError>> =
    try
        if Path.GetExtension path <> ".rsl" then
            Error [ InvalidExtension path ]
        else
            use sr = new StreamReader(path)
            let lexbuf = LexBuffer<char>.FromTextReader sr
            let filename = Path.GetFileNameWithoutExtension path
            parseLexBuffer lexbuf filename

    with
    | :? FileNotFoundException
    | :? DirectoryNotFoundException
    | :? IOException as exn -> Error [ ReadFile(path, exn.Message) ]

let parseString (input: string) (filename: string) : Result<string * Scheme, List<SyntaxError>> =
    let lexbuf = LexBuffer<char>.FromString input
    parseLexBuffer lexbuf filename
