module Unfold.Error

open Diagnostic
open AST
open Syntax.Unparse
open TypeCheck.Error

type UnfoldingError =
    | InvalidDefinition of kind: DefinitionKind * span: Span
    | DuplicateDefinition of id: Node<string> * kind: DefinitionKind * ty: Option<Node<ValueExpr>>
    | MissingDefinition of id: Node<string> * kind: Option<DefinitionKind>
    | RecursiveFunction of id: Node<string>
    | InvalidRangeType of ty: Node<TypeExpr>
    | EmptyGenericIndex of id: Node<string>
    | InvalidEvaluation of span: Span
    | UnsupportedExpr of kind: ExprKind * span: Span
    | UnsupportedDefinition of kind: DefinitionKind * span: Span
    | UndefinedDefinition of kind: InitDefinitionKind * id: seq<Node<string>>

    interface IDiagnostic with

        member this.Name =
            match this with
            | InvalidDefinition(kind, _) -> $"Invalid {kind.Format} Definition"
            | InvalidRangeType _ -> "Invalid Range Type"
            | EmptyGenericIndex _ -> "Empty Generic Index"
            | DuplicateDefinition(_, kind, _) -> $"Duplicate {kind.Format} Definition"
            | MissingDefinition(_, optKind) ->
                let kind =
                    match optKind with
                    | Some kind -> $"{kind.Format} "
                    | _ -> ""

                $"""Missing {kind}Definition"""
            | RecursiveFunction _ -> "Recursive Function"
            | InvalidEvaluation _ -> "Invalid Evaluation"
            | UnsupportedExpr(kind, _) -> $"Unsupported {kind.Format} Expr"
            | UnsupportedDefinition(kind, _) -> $"Unsupported {kind.Format} Definition"
            | UndefinedDefinition(kind, _) -> $"Undefined {kind.Format} Definition"

        member this.Label =
            match this with
            | InvalidDefinition(kind, span) -> $"The {kind.Format} definition cannot be unfolded.", Some span

            | InvalidRangeType ty -> $"The type {unparseTypeExpr ty.Value} cannot be unfolded.", Some ty.Span

            | EmptyGenericIndex id -> $"The generic index with label {id.Value} has an empty range", Some id.Span

            | DuplicateDefinition(id, kind, optVal) ->
                let optTyStr =
                    match optVal with
                    | Some ty -> $" with value {unparseValueExpr ty.Value}."
                    | None -> "."

                $"The {kind.Format} identifier {id.Value} is already assigned{optTyStr}", Some id.Span

            | MissingDefinition(id, optKind) ->
                let kind =
                    match optKind with
                    | Some kind -> $"{kind.Format} "
                    | _ -> ""

                $"The {kind}identifier {id.Value} has already been defined or is missing a definition.", Some id.Span

            | RecursiveFunction id -> $"The recursive function {id.Value} is unsupported", Some id.Span

            | InvalidEvaluation span -> $"The expression could not be evaluated.", Some span

            | UnsupportedExpr(kind, span) -> $"The {kind.Format} expression could not be unfolded.", Some span

            | UnsupportedDefinition(kind, span) -> $"The {kind.Format} definition is unsupported.", Some span

            | UndefinedDefinition(kind, ids) ->
                $"""The {kind.Format} definitions have not been defined: {concatNodeSeq ", " id ids}""",
                Some((Seq.head ids).Span)

        member this.Help =
            match this with
            | InvalidDefinition(TypeDef, _) -> Some "Only abbreviations and finite variant definitions are supported."
            | MissingDefinition _ -> Some "Definitions must occur before use when unfolding."
            | InvalidRangeType _ ->
                Some(
                    String.concat
                        "\n"
                        [ "Support is limited to: Bool, finite variants and subtypes that match one of the following forms:"
                          "    1. {| x: Int :- x >= v1 /\ x < v2 |} where v1 and v2 can be evaluated to an integer."
                          "    2. {| x: T :- x ~= y ||} where T is a finite variant and y one of its members." ]
                )

            | InvalidEvaluation _ ->
                Some "Support is limited to basic infix and prefix operations involving values and generic values."

            | UnsupportedDefinition _ ->
                Some(
                    String.concat
                        "\n"
                        [ "Support is limited to definitions of the following form:"
                          "    1. x = v"
                          "    2. x[.v_1, ..., v_n.] = v"
                          "    3. all x: T :- v where T is a valid range type and v is of form 1 or 2" ]
                )

            | UndefinedDefinition(kind, _) ->
                let place =
                    match kind with
                    | ValueDef -> "axioms"
                    | VariableDef -> "init_constraints"

                Some $"A {kind.Format} definition is missing for one of your {place}"

            | _ -> None

and InitDefinitionKind =
    | ValueDef
    | VariableDef

    member this.Format =
        match this with
        | ValueDef -> "value"
        | VariableDef -> "variable"

and ExprKind =
    | TypeExpr
    | ValueExpr
    | RuleExpr

    member this.Format =
        match this with
        | TypeExpr -> "type expr"
        | ValueExpr -> "value expr"
        | RuleExpr -> "rule expr"
