module Typecheck.Test

open FSharpPlus.Data
open TypeCheck.Error
open Helpers
open Expecto
open TypeCheck.Phase2
open System.IO
open AST

let getTypeErrorTag e =
    match e with
    | ModuleNameMismatch _ -> "ModuleNameMismatch"
    | DuplicateDefinition _ -> "DuplicateDefinition"
    | DuplicateDeclaration _ -> "DuplicateDeclaration"
    | SignatureMismatch _ -> "SignatureMismatch"
    | CircularTypeDefinition _ -> "CircularTypeDefinition"
    | UseOfCircularType _ -> "UseOfCircularType"
    | MissingDefinition _ -> "MissingDefinition"
    | MissingDeclaration _ -> "MissingDeclaration"
    | DuplicateName _ -> "DuplicateName"
    | UnexpectedType _ -> "UnexpectedType"
    | UnexpectedIndexType _ -> "UnexpectedIndexType"
    | UnexpectedInfixOp _ -> "UnexpectedInfixOp"
    | UnexpectedPrefixOp _ -> "UnexpectedPrefixOp"
    | GenericReference _ -> "GenericReference"
    | MissingDisambiguation _ -> "MissingDisambiguation"
    | UnexpectedArgument _ -> "UnexpectedArgument"
    | InCompatibleIfCases _ -> "InCompatibleIfCases"
    | InCompatibleTypes _ -> "InCompatibleTypes"

let makeFailTypeCheckTest (relativePath: string) (expectedErrors: List<TypeCheckingError>) (errorText: string) =
    let path = Path.Combine [| __SOURCE_DIRECTORY__; "Specs"; relativePath |]

    testCase relativePath (fun _ ->
        let check =
            typecheckCheck path (fun res ->
                match res with
                | Ok _ -> true
                | Error actualErrors ->
                    let actualTags = countByTag getTypeErrorTag (DList.toList actualErrors)

                    if
                        countByTag getTypeErrorTag expectedErrors
                        |> Map.forall (fun tag count -> Map.tryFind tag actualTags = Some count)
                    then
                        true
                    else
                        failtestf "Failed with errors: %A" actualErrors)

        Expect.isTrue check errorText)

let typeCheckFailCases =
    [ "Declarations/WrongName.rsl", [ ModuleNameMismatch(Node.New("", (0u, 0u)), "") ]
      "Declarations/DuplicateDeclaration.rsl", [ DuplicateDeclaration(Node.New("", (0u, 0u))) ]
      "Declarations/TypeCheck.rsl",
      [ ModuleNameMismatch(Node.New("", (0u, 0u)), "")
        UnexpectedArgument(NonEmptyList.singleton (Node.New(Bot, (0u, 0u))), Node.New(Bot, (0u, 0u)))
        DuplicateDefinition(Node.New("", (0u, 0u)), TypeDef, None)
        MissingDisambiguation((0u, 0u))
        InCompatibleTypes(Node.New(Bot, (0u, 0u)), Node.New(Bot, (0u, 0u)))
        InCompatibleIfCases(Node.New(Bot, (0u, 0u)), Node.New(Bot, (0u, 0u)))
        SignatureMismatch(Node.New("", (0u, 0u)), Node.New("", (0u, 0u)))
        DuplicateName(Node.New("", (0u, 0u)), Axiom)
        DuplicateDefinition(Node.New("", (0u, 0u)), ValueDef, None) ]
      "Declarations/1_TypeDef/Circular_Array_1.rsl", [ CircularTypeDefinition(Node.New("", (0u, 0u))) ]
      "Declarations/1_TypeDef/Circular_Array_2.rsl", [ CircularTypeDefinition(Node.New("", (0u, 0u))) ]
      "Declarations/1_TypeDef/Circular_Id.rsl", [ CircularTypeDefinition(Node.New("", (0u, 0u))) ]
      "Declarations/1_TypeDef/Circular_Subtype.rsl", [ CircularTypeDefinition(Node.New("", (0u, 0u))) ]
      "Declarations/1_TypeDef/DuplicateDefinition.rsl", [ DuplicateDefinition(Node.New("", (0u, 0u)), TypeDef, None) ]
      "Declarations/1_TypeDef/MissingDefinition.rsl", [ MissingDefinition(Node.New("", (0u, 0u)), TypeDef) ]
      "Declarations/2_ValueDef/Distinct_Args.rsl", [ DuplicateDefinition(Node.New("", (0u, 0u)), ValueDef, None) ]
      "Declarations/2_ValueDef/Distinct_Generic.rsl", [ DuplicateDefinition(Node.New("", (0u, 0u)), ValueDef, None) ]
      "Declarations/2_ValueDef/DuplicateDefinition.rsl", [ DuplicateDefinition(Node.New("", (0u, 0u)), ValueDef, None) ]
      "Declarations/2_ValueDef/MissingDefinition_Type.rsl", [ MissingDefinition(Node.New("", (0u, 0u)), TypeDef) ]
      "Declarations/2_ValueDef/Signature.rsl", [ SignatureMismatch(Node.New("", (0u, 0u)), Node.New("", (0u, 0u))) ]
      "Declarations/3_AxiomDef/DuplicateName.rsl", [ DuplicateName(Node.New("", (0u, 0u)), Axiom) ]
      "Declarations/3_AxiomDef/IsBool.rsl",
      [ UnexpectedType(Node.New(Bot, (0u, 0u)), Node.New(Bot, (0u, 0u)), (0u, 0u)) ]
      "Declarations/3_AxiomDef/TemporalInfixOp.rsl", [ UnexpectedInfixOp(Node.New(Until, (0u, 0u))) ]
      "Declarations/3_AxiomDef/TemporalPrefixOp_Finally.rsl", [ UnexpectedPrefixOp(Node.New(Finally, (0u, 0u))) ]
      "Declarations/3_AxiomDef/TemporalPrefixOp_Global.rsl", [ UnexpectedPrefixOp(Node.New(Global, (0u, 0u))) ]
      "Declarations/3_AxiomDef/TemporalPrefixOp_Next.rsl", [ UnexpectedPrefixOp(Node.New(Next, (0u, 0u))) ]
      "Declarations/4_VariableDef/Distinct_Generic.rsl",
      [ DuplicateDefinition(Node.New("", (0u, 0u)), VariableDef, None) ]
      "Declarations/4_VariableDef/DuplicateDefinition.rsl",
      [ DuplicateDefinition(Node.New("", (0u, 0u)), VariableDef, None) ]
      "Declarations/4_VariableDef/MissingDefinition_Type.rsl", [ MissingDefinition(Node.New("", (0u, 0u)), TypeDef) ]
      "Declarations/7_LTLAssertionDef/DuplicateName.rsl", [ DuplicateName(Node.New("", (0u, 0u)), LTLAssertion) ]
      "Declarations/7_LTLAssertionDef/MissingDeclaration.rsl", [ MissingDeclaration(Node.New("", (0u, 0u))) ]
      "Expressions/1_TypeExpr/ArrayArrayIndex.rsl", [ UnexpectedIndexType(Node.New(Bot, (0u, 0u))) ]
      "Expressions/1_TypeExpr/Distinct_Variant.rsl", [ DuplicateDefinition(Node.New("", (0u, 0u)), TypeDef, None) ]
      "Expressions/1_TypeExpr/GenericArrayIndex.rsl", [ UnexpectedIndexType(Node.New(Bot, (0u, 0u))) ]
      "Expressions/1_TypeExpr/UseOfCircularType.rsl", [ UseOfCircularType(Node.New("", (0u, 0u))) ]
      "Expressions/2_ValueExpr/GenericReference.rsl", [ GenericReference(Node.New("", (0u, 0u))) ]
      "Expressions/2_ValueExpr/InCompatibleIf.rsl",
      [ InCompatibleIfCases(Node.New(Bot, (0u, 0u)), Node.New(Bot, (0u, 0u))) ]
      "Expressions/2_ValueExpr/InCompatibleTypesArray.rsl",
      [ InCompatibleTypes(Node.New(Bot, (0u, 0u)), Node.New(Bot, (0u, 0u))) ]
      "Expressions/2_ValueExpr/Lambda_Distinct.rsl", [ DuplicateDefinition(Node.New("", (0u, 0u)), ValueDef, None) ]
      "Expressions/2_ValueExpr/MissingDefinition.rsl", [ MissingDefinition(Node.New("", (0u, 0u)), ValueDef) ]
      "Expressions/2_ValueExpr/MissingDisambiguation_2.rsl", [ MissingDisambiguation((0u, 0u)) ]
      "Expressions/2_ValueExpr/MissingDisambiguation.rsl", [ MissingDisambiguation((0u, 0u)) ]
      "Expressions/2_ValueExpr/Quantifier_Distinct.rsl", [ DuplicateDefinition(Node.New("", (0u, 0u)), ValueDef, None) ]
      "Expressions/2_ValueExpr/TemporalInfixOp.rsl", [ UnexpectedInfixOp(Node.New(Until, (0u, 0u))) ]
      "Expressions/2_ValueExpr/TemporalPrefixOp_Finally.rsl", [ UnexpectedPrefixOp(Node.New(Finally, (0u, 0u))) ]
      "Expressions/2_ValueExpr/TemporalPrefixOp_Global.rsl", [ UnexpectedPrefixOp(Node.New(Global, (0u, 0u))) ]
      "Expressions/2_ValueExpr/TemporalPrefixOp_Next.rsl", [ UnexpectedPrefixOp(Node.New(Next, (0u, 0u))) ]
      "Expressions/2_ValueExpr/UnexpectedArgumentArray.rsl",
      [ UnexpectedArgument(NonEmptyList.singleton (Node.New(Bot, (0u, 0u))), Node.New(Bot, (0u, 0u))) ]
      "Expressions/2_ValueExpr/UnexpectedArgumentFunction.rsl",
      [ UnexpectedArgument(NonEmptyList.singleton (Node.New(Bot, (0u, 0u))), Node.New(Bot, (0u, 0u))) ]
      "Expressions/2_ValueExpr/UnexpectedArgumentGeneric.rsl",
      [ UnexpectedArgument(NonEmptyList.singleton (Node.New(Bot, (0u, 0u))), Node.New(Bot, (0u, 0u))) ]
      "Expressions/2_ValueExpr/UnexpectedArrayIndex.rsl",
      [ UnexpectedType(Node.New(Bot, (0u, 0u)), Node.New(Bot, (0u, 0u)), (0u, 0u)) ]
      "Expressions/3_RuleExpr/DuplicateName.rsl", [ DuplicateName(Node.New("", (0u, 0u)), Rule) ]
      "Expressions/3_RuleExpr/IsBool.rsl",
      [ UnexpectedType(Node.New(Bot, (0u, 0u)), Node.New(Bot, (0u, 0u)), (0u, 0u)) ]
      "Expressions/3_RuleExpr/TemporalInfixOp.rsl", [ UnexpectedInfixOp(Node.New(Until, (0u, 0u))) ]
      "Expressions/3_RuleExpr/TemporalPrefixOp_Finally.rsl", [ UnexpectedPrefixOp(Node.New(Finally, (0u, 0u))) ]
      "Expressions/3_RuleExpr/TemporalPrefixOp_Global.rsl", [ UnexpectedPrefixOp(Node.New(Global, (0u, 0u))) ]
      "Expressions/3_RuleExpr/TemporalPrefixOp_Next.rsl", [ UnexpectedPrefixOp(Node.New(Next, (0u, 0u))) ] ]

[<Tests>]
let tests =
    testSequenced
    <| testList
        "TypeChecker Tests"
        [ testList
              "Pass"
              (getFilesInTestDirs [| [| "All" |]; [| "Unparser" |]; [| "Unfold" |] |]
               |> List.map (fun file ->
                   testCase file (fun _ -> typecheckCheck file (fun res -> Expect.isOk res "Type Check failed"))))

          testList
              "Pass (Unfold)"
              (getFilesInTestDirs [| [| "All" |]; [| "Unparser" |] |]
               |> List.map (fun file ->
                   testCase file (fun _ ->
                       unfoldCheck file (fun res ->
                           match res with
                           | Ok spec ->
                               Expect.isOk
                                   (typecheck (Path.GetFileNameWithoutExtension file, spec.Scheme))
                                   "Type Check of unfold failed"
                           | Error errs -> failtestf "Unfolding failed with errors: %A" errs))))


          testList
              "Fail"
              (List.map
                  (fun (file, expected) ->
                      makeFailTypeCheckTest $"TypeCheck/{file}" expected "Type Checking should have failed")
                  typeCheckFailCases) ]
