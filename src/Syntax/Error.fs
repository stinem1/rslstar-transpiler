module Syntax.Error

open AST

open Diagnostic

type SyntaxError =
    | InvalidToken of span: Span * token: string
    | InvalidSyntax of span: Span * token: string option * expectedTokens: string list
    | ReservedKeyword of span: Span * token: string
    | InvalidInt of span: Span * msg: string
    | ReadFile of path: string * msg: string
    | WriteFile of path: string * msg: string
    | InvalidExtension of filename: string

    interface IDiagnostic with

        member this.Name =
            match this with
            | InvalidToken _ -> "Invalid Token"
            | InvalidSyntax _ -> "Invalid Syntax"
            | ReservedKeyword _ -> "Reserved Keyword"
            | InvalidInt _ -> "Invalid Integer"
            | ReadFile(path, _) -> $"Reading file \"{path}\""
            | WriteFile(path, _) -> $"Writing to file \"{path}\""
            | InvalidExtension _ -> "Invalid Extension"

        member this.Label =
            match this with
            | InvalidToken(span, token) -> $"The token '{token}' is invalid.", Some span

            | InvalidSyntax(span, optToken, _) ->
                match optToken with
                | Some token -> $"The token '{token}' is unexpected in this context."
                | None -> "The expression ends too early. Are you missing a token?"
                , Some span

            | ReservedKeyword(span, token) -> $"The keyword '{token}' has been reserved for future use.", Some span

            | InvalidInt(span, msg) -> msg, Some span
            | WriteFile(_, msg) -> msg, None
            | ReadFile(_, msg) -> msg, None

            | InvalidExtension path ->
                $"'{path}' is not a valid RSL* source file name. It must have the '.rsl' extension.", None

        member this.Help =
            match this with
            | InvalidSyntax(_, _, expected) ->
                (List.map (sprintf "'%s'") >> String.concat ", ") expected
                |> sprintf "The expected tokens are: %s."
                |> Some
            | _ -> None
