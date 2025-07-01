module Syntax.Util

open AST

open FSharp.Text.Lexing

exception InvalidToken of span: Span * token: string

exception ReservedKeyword of span: Span * token: string

exception InvalidSyntax of span: Span * token: Option<string> * expectedTags: List<int>

exception InvalidInt of span: Span * msg: string

let inline mkSpan (startPos: Position, endPos: Position) =
    uint startPos.AbsoluteOffset, uint endPos.AbsoluteOffset
