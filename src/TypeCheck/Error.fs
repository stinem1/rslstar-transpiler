module TypeCheck.Error

open FSharpPlus.Data
open Diagnostic
open AST
open Syntax.Unparse

type TypeCheckingError =
    | ModuleNameMismatch of id: Node<string> * filename: string
    | DuplicateDefinition of id: Node<string> * kind: DefinitionKind * ty: Option<Node<TypeExpr>>
    | DuplicateDeclaration of id: Node<string>
    | SignatureMismatch of signatureId: Node<string> * formalId: Node<string>
    | CircularTypeDefinition of id: Node<string>
    | UseOfCircularType of id: Node<string>
    | MissingDefinition of id: Node<string> * kind: DefinitionKind
    | MissingDeclaration of id: Node<string>
    | DuplicateName of name: Node<string> * kind: NameKind
    | UnexpectedType of expected: Node<TypeExpr> * found: Node<TypeExpr> * span: Span
    | UnexpectedIndexType of found: Node<TypeExpr>
    | UnexpectedInfixOp of op: Node<InfixOp>
    | UnexpectedPrefixOp of op: Node<PrefixOp>
    | GenericReference of id: Node<string>
    | MissingDisambiguation of span: Span
    | UnexpectedArgument of args: NonEmptyList<Node<TypeExpr>> * ty: Node<TypeExpr>
    | InCompatibleIfCases of caseThen: Node<TypeExpr> * caseElse: Node<TypeExpr>
    | InCompatibleTypes of ty1: Node<TypeExpr> * ty2: Node<TypeExpr>

    interface IDiagnostic with

        member this.Name =
            match this with
            | ModuleNameMismatch _ -> "Module Name Mismatch"
            | DuplicateDefinition(_, kind, _) -> $"Duplicate {kind.Format} Definition"
            | DuplicateDeclaration _ -> $"Duplicate transition system Declaration"
            | SignatureMismatch _ -> "Signature Mismatch"
            | CircularTypeDefinition _ -> "Circular Type Definition"
            | UseOfCircularType _ -> "Use of Circular Type Definition"
            | MissingDefinition(_, kind) -> $"Missing {kind.Format} Definition"
            | MissingDeclaration _ -> $"Missing transition system Declaration"
            | DuplicateName _ -> "Duplicate Name"
            | UnexpectedType _ -> "Unexpected Type"
            | UnexpectedIndexType _ -> "Unexpected Index Type"
            | UnexpectedInfixOp _ -> "Unexpected Infix Operator"
            | UnexpectedPrefixOp _ -> "Unexpected Prefix Operator"
            | GenericReference _ -> "Unexpected Generic Reference"
            | MissingDisambiguation _ -> "Missing Disambiguation"
            | UnexpectedArgument _ -> "Unexpected Argument"
            | InCompatibleIfCases _ -> "Incompatible If Cases"
            | InCompatibleTypes _ -> "Incompatible Types"

        member this.Label =
            match this with
            | ModuleNameMismatch(id, filename) ->
                $"The module name {id.Value} does not match filename {filename}.", Some id.Span

            | DuplicateDefinition(id, kind, optTy) ->
                let optTyStr =
                    match optTy with
                    | Some ty -> $" with type {unparseTypeExpr ty.Value}."
                    | None -> "."

                $"The {kind.Format} identifier {id.Value} is already defined{optTyStr}", Some id.Span

            | DuplicateDeclaration id -> $"The transition system identifier {id.Value} is already defined", Some id.Span

            | SignatureMismatch(signatureId, formalId) ->
                $"The formal function name {formalId.Value} does not match its signature {signatureId.Value}.",
                Some formalId.Span

            | CircularTypeDefinition id -> $"The definition of {id.Value} is circular.", Some id.Span

            | UseOfCircularType id -> $"The annotated type {id.Value} is circular.", Some id.Span

            | MissingDefinition(id, kind) -> $"The {kind.Format} identifier {id.Value} is undefined.", Some id.Span

            | MissingDeclaration id -> $"The transition system identifier {id.Value} is undefined.", Some id.Span

            | DuplicateName(name, kind) -> $"The {kind.Format} name {name.Value} is already in use.", Some name.Span

            | UnexpectedType(expected, found, span) ->
                $"""The expected type is {unparseTypeExpr expected.Value} but found type {unparseTypeExpr found.Value}.""",
                Some span

            | UnexpectedIndexType found ->
                $"""The expected index types are Bool, Int, Sort, Variant but found type {unparseTypeExpr found.Value}.""",
                Some found.Span

            | UnexpectedInfixOp op ->
                $"The infix operator '{unparseInfixOp op.Value}' may not appear in this context.", Some op.Span

            | UnexpectedPrefixOp op ->
                $"The prefix operator '{unparsePrefixOp op.Value}' may not appear in this context.", Some op.Span

            | GenericReference id ->
                $"The generic value/variable '{id.Value}' cannot be referenced on its own.", Some id.Span

            | MissingDisambiguation span -> $"This expression needs to be disambiguated.", Some span

            | UnexpectedArgument(args, ty) ->
                $"""The argument(s) {concatNodeSeq " and " unparseTypeExpr args} cannot be argument type for {unparseTypeExpr ty.Value}.""",
                Some(Node.CommonSpan args)

            | InCompatibleIfCases(caseThen, caseElse) ->
                $"The then type {unparseTypeExpr caseThen.Value} and else type {unparseTypeExpr caseElse.Value} are not compatible",
                Some caseThen.Span

            | InCompatibleTypes(ty1, ty2) ->
                $"the type {unparseTypeExpr ty1.Value} and type {unparseTypeExpr ty2.Value} are not compatible",
                Some(Node.CommonSpan(ty1, ty2))

        member this.Help =
            match this with
            | _ -> None

and DefinitionKind =
    | TypeDef
    | ValueDef
    | VariableDef
    | AxiomDef
    | LTLAssertionDef
    | InitConstraintDef
    | RuleDef

    member this.Format =
        match this with
        | TypeDef -> "type"
        | ValueDef -> "value"
        | VariableDef -> "variable"
        | AxiomDef -> "axiom"
        | LTLAssertionDef -> "ltl assertion"
        | InitConstraintDef -> "init constraint"
        | RuleDef -> "rule"

and NameKind =
    | Axiom
    | Rule
    | LTLAssertion

    member this.Format =
        match this with
        | Axiom -> "axiom"
        | Rule -> "rule"
        | LTLAssertion -> "ltl assertion"
