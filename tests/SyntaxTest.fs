module Syntax.Test

open FSharp.Text.Lexing
open Helpers
open Syntax
open System.IO
open Syntax.Parse
open Syntax.Error
open Expecto
open Unparse

let lexBuffer (lexbuf: LexBuffer<char>) : List<Parser.token> =
    List.unfold
        (fun _ ->
            if lexbuf.IsPastEndOfStream then
                None
            else
                Some(Lexer.tokenize lexbuf, ()))
        ()

let lexFile (path: string) : Result<List<Parser.token>, List<SyntaxError>> =
    use sr = new StreamReader(path)
    let lexbuf = LexBuffer<char>.FromTextReader sr
    setInitialPos lexbuf (Path.GetFileNameWithoutExtension path)

    try
        Ok(lexBuffer lexbuf)
    with
    | Util.InvalidToken(span, token) -> Error [ (InvalidToken(span, token)) ]
    | Util.ReservedKeyword(span, token) -> Error [ (ReservedKeyword(span, token)) ]
    | Util.InvalidInt(span, msg) -> Error [ (InvalidInt(span, msg)) ]

let makeFailSyntaxTest f (relativePath: string) (expectedError: SyntaxError) (errorText: string) =
    let path = Path.Combine [| __SOURCE_DIRECTORY__; "Specs"; relativePath |]

    testCase relativePath (fun _ ->
        let check =
            match parseFile path with
            | Ok _ -> true
            | Error actualErrors ->
                if
                    List.exists
                        (fun actual ->
                            match actual, expectedError with
                            | InvalidToken(_, tok1), InvalidToken(_, tok2) -> tok1 = tok2
                            | InvalidSyntax(_, tok1, _), InvalidSyntax(_, tok2, _) -> tok1 = tok2
                            | ReservedKeyword(_, tok1), ReservedKeyword(_, tok2) -> tok1 = tok2
                            | InvalidInt _, InvalidInt _
                            | ReadFile _, ReadFile _
                            | WriteFile _, WriteFile _
                            | InvalidExtension _, InvalidExtension _ -> true
                            | _ -> false)
                        actualErrors
                then
                    true
                else
                    failtestf "Failed with errors: %A" actualErrors
        Expect.isTrue check errorText)

let lexerFailCases =
    [ "Overflow.rsl", InvalidInt((0u, 0u), "")
      "Reserved_abs.rsl", ReservedKeyword((0u, 0u), "abs")
      "Reserved_always.rsl", ReservedKeyword((0u, 0u), "always")
      "Reserved_any.rsl", ReservedKeyword((0u, 0u), "any")
      "Reserved_as.rsl", ReservedKeyword((0u, 0u), "as")
      "Reserved_card.rsl", ReservedKeyword((0u, 0u), "card")
      "Reserved_case.rsl", ReservedKeyword((0u, 0u), "case")
      "Reserved_channel.rsl", ReservedKeyword((0u, 0u), "channel")
      "Reserved_chaos.rsl", ReservedKeyword((0u, 0u), "chaos")
      "Reserved_Char.rsl", ReservedKeyword((0u, 0u), "Char")
      "Reserved_distinct.rsl", ReservedKeyword((0u, 0u), "distinct")
      "Reserved_do.rsl", ReservedKeyword((0u, 0u), "do")
      "Reserved_dom.rsl", ReservedKeyword((0u, 0u), "dom")
      "Reserved_elems.rsl", ReservedKeyword((0u, 0u), "elems")
      "Reserved_elsif.rsl", ReservedKeyword((0u, 0u), "elsif")
      "Reserved_extend.rsl", ReservedKeyword((0u, 0u), "extend")
      "Reserved_for.rsl", ReservedKeyword((0u, 0u), "for")
      "Reserved_hd.rsl", ReservedKeyword((0u, 0u), "hd")
      "Reserved_hide.rsl", ReservedKeyword((0u, 0u), "hide")
      "Reserved_inds.rsl", ReservedKeyword((0u, 0u), "inds")
      "Reserved_initialise.rsl", ReservedKeyword((0u, 0u), "initialise")
      "Reserved_int.rsl", ReservedKeyword((0u, 0u), "int")
      "Reserved_inter.rsl", ReservedKeyword((0u, 0u), "inter")
      "Reserved_isin.rsl", ReservedKeyword((0u, 0u), "isin")
      "Reserved_len.rsl", ReservedKeyword((0u, 0u), "len")
      "Reserved_local.rsl", ReservedKeyword((0u, 0u), "local")
      "Reserved_Nat.rsl", ReservedKeyword((0u, 0u), "Nat")
      "Reserved_object.rsl", ReservedKeyword((0u, 0u), "object")
      "Reserved_out.rsl", ReservedKeyword((0u, 0u), "out")
      "Reserved_post.rsl", ReservedKeyword((0u, 0u), "post")
      "Reserved_pre.rsl", ReservedKeyword((0u, 0u), "pre")
      "Reserved_read.rsl", ReservedKeyword((0u, 0u), "read")
      "Reserved_Real.rsl", ReservedKeyword((0u, 0u), "Real")
      "Reserved_rng.rsl", ReservedKeyword((0u, 0u), "rng")
      "Reserved_skip.rsl", ReservedKeyword((0u, 0u), "skip")
      "Reserved_stop.rsl", ReservedKeyword((0u, 0u), "stop")
      "Reserved_swap.rsl", ReservedKeyword((0u, 0u), "swap")
      "Reserved_test_case.rsl", ReservedKeyword((0u, 0u), "test_case")
      "Reserved_Text.rsl", ReservedKeyword((0u, 0u), "Text")
      "Reserved_tl.rsl", ReservedKeyword((0u, 0u), "tl")
      "Reserved_union.rsl", ReservedKeyword((0u, 0u), "union")
      "Reserved_Unit.rsl", ReservedKeyword((0u, 0u), "Unit")
      "Reserved_until.rsl", ReservedKeyword((0u, 0u), "until")
      "Reserved_use.rsl", ReservedKeyword((0u, 0u), "use")
      "Reserved_where.rsl", ReservedKeyword((0u, 0u), "where")
      "Reserved_while.rsl", ReservedKeyword((0u, 0u), "while")
      "Reserved_with.rsl", ReservedKeyword((0u, 0u), "with")
      "Reserved_write.rsl", ReservedKeyword((0u, 0u), "write")
      "Underscore_Id.rsl", InvalidToken((0u, 0u), "_") ]

let parserFailCases =
    [ "RSL.txt", InvalidExtension ""
      "EffectExpr_Value.rsl", InvalidSyntax((0u, 0u), Some "BOOL true", [])
      "EffectVar_Prime.rsl", InvalidSyntax((0u, 0u), Some "IDENT \"x\"", [])
      "Multi_Eq.rsl", InvalidSyntax((0u, 0u), Some "EQ", [])
      "Multi_Ge.rsl", InvalidSyntax((0u, 0u), Some "GE", [])
      "Multi_Geq.rsl", InvalidSyntax((0u, 0u), Some "GEQ", [])
      "Multi_Le.rsl", InvalidSyntax((0u, 0u), Some "LE", [])
      "Multi_Leq.rsl", InvalidSyntax((0u, 0u), Some "LEQ", [])
      "Multi_Neq.rsl", InvalidSyntax((0u, 0u), Some "NEQ", []) ]

let parseWriteParseEq (fullPath: string) =
    let relativePath =
        Path.GetRelativePath(Path.Combine(__SOURCE_DIRECTORY__, "Specs"), fullPath)

    testCase $"ParseWriteParse {relativePath}"
    <| fun _ ->
        match parseFile fullPath with
        | Error err -> failtestf "Initial parse failed: %A" err
        | Ok parsed ->
            let scheme = snd parsed
            let unparsed = unparseScheme scheme

            match parseString unparsed (Path.GetFileName fullPath) with
            | Error err -> failtestf "Second parse failed: %A" err
            | Ok reparsed -> Expect.equal (snd reparsed) scheme "Expected the second parse to be equal"

[<Tests>]
let tests =
    testSequenced
    <| testList
        "Syntax Tests"
        [ testList
              "Lexer"
              [ testList
                    "Pass"
                    (getFilesInTestDirs [| [| "Lexer"; "Pass" |] |]
                     |> List.map (fun file -> testCase file (fun _ -> Expect.isOk (lexFile file) "Lexing failed")))
                testList
                    "Fail"
                    (List.map
                        (fun (file, expected) ->
                            makeFailSyntaxTest lexFile $"Lexer/Fail/{file}" expected "Lexing should have failed")
                        lexerFailCases)

                ]

          testList
              "Parser"
              [ testList
                    "Pass"
                    (getFilesInTestDirs [| [| "All" |]; [| "Unparser" |]; [| "TypeCheck" |]; [| "Unfold" |] |]
                     |> List.map (fun file -> testCase file (fun _ -> Expect.isOk (parseFile file) "Parsing failed")))
                testList
                    "Fail"
                    (List.map
                        (fun (file, expected) ->
                            makeFailSyntaxTest lexFile $"Parser/{file}" expected "Parsing should have failed")
                        parserFailCases) ]

          testList
              "Unparser"
              [ testList
                    "Pass"
                    (getFilesInTestDirs [| [| "All" |]; [| "TypeCheck" |]; [| "Unfold" |] |]
                     |> List.map parseWriteParseEq) ]

          ]
