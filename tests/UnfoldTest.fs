module Unfold.Test

open FSharpPlus.Data
open TypeCheck.Error
open Unfold.Error
open Helpers
open Expecto
open System.IO
open AST

let getUnfoldErrorTag e =
    match e with
    | InvalidDefinition _ -> "InvalidDefinition"
    | DuplicateDefinition _ -> "DuplicateDefinition"
    | MissingDefinition _ -> "MissingDefinition"
    | RecursiveFunction _ -> "RecursiveFunction"
    | InvalidRangeType _ -> "InvalidRangeType"
    | EmptyGenericIndex _ -> "EmptyGenericIndex"
    | InvalidEvaluation _ -> "InvalidEvaluation"
    | UnsupportedExpr _ -> "UnsupportedExpr"
    | UnsupportedDefinition _ -> "UnsupportedDefinition"
    | UndefinedDefinition _ -> "UndefinedDefinition"

let makeFailUnfoldTest (relativePath: string) (expectedErrors: List<UnfoldingError>) (errorText: string) =
    let path = Path.Combine [| __SOURCE_DIRECTORY__; "Specs"; relativePath |]

    testCase relativePath (fun _ ->
        let check =
            unfoldCheck path (fun res ->
                match res with
                | Ok _ -> true
                | Error actualErrors ->
                    let actualTags = countByTag getUnfoldErrorTag (DList.toList actualErrors)

                    if
                        countByTag getUnfoldErrorTag expectedErrors
                        |> Map.forall (fun tag count -> Map.tryFind tag actualTags = Some count)
                    then
                        true
                    else
                        failtestf "Failed with errors: %A" actualErrors)

        Expect.isTrue check errorText)

let unfoldFailCases = [
    "Declarations/1_TypeDef/Sort.rsl", [ InvalidDefinition(TypeDef, (0u,0u)) ]
    "Declarations/2_ValueDef/Single_Typing.rsl", [ MissingDefinition(Node.New("", (0u, 0u)), Some DefinitionKind.ValueDef) ]
    "Declarations/3_AxiomDef/Axiom.rsl", [ UnsupportedDefinition(AxiomDef, (0u,0u)) ]
    "Declarations/3_AxiomDef/Multi.rsl", [ UnsupportedDefinition(AxiomDef, (0u,0u)); UnsupportedDefinition(AxiomDef, (0u,0u)) ]
    "Declarations/3_AxiomDef/Named_Axiom.rsl", [ UnsupportedDefinition(AxiomDef, (0u,0u)) ]

    "Declarations/3_AxiomDef/Single.rsl", [ UnsupportedDefinition(AxiomDef, (0u,0u)); UnsupportedDefinition(AxiomDef, (0u,0u)) ]
    "Declarations/3_AxiomDef/Dup_Ax.rsl", [ DuplicateDefinition(Node.New("", (0u, 0u)), AxiomDef, None) ]
    "Declarations/4_VariableDef/Single_Typing.rsl", [ MissingDefinition(Node.New("", (0u, 0u)), Some DefinitionKind.VariableDef) ]
    "Declarations/5_InitConstraintDef/False.rsl", [ UnsupportedDefinition(InitConstraintDef, (0u,0u)) ]
    "Declarations/5_InitConstraintDef/Multi.rsl", [ UnsupportedDefinition(InitConstraintDef, (0u,0u)); UnsupportedDefinition(InitConstraintDef, (0u,0u)) ]
    "Declarations/5_InitConstraintDef/Single.rsl", [ UnsupportedDefinition(InitConstraintDef, (0u,0u)); UnsupportedDefinition(InitConstraintDef, (0u,0u)) ]
    "Declarations/5_InitConstraintDef/True.rsl", [ UnsupportedDefinition(InitConstraintDef, (0u,0u)) ]
    "Declarations/5_InitConstraintDef/Dup_Init.rsl", [ DuplicateDefinition(Node.New("", (0u, 0u)), InitConstraintDef, None) ]
    "Expressions/1_TypeExpr/InvalidRange.rsl", [ InvalidRangeType(Node.New(Bot, (0u, 0u))) ]
    "Expressions/2_ValueExpr/All.rsl", [ InvalidRangeType(Node.New(Bot, (0u, 0u))) ]
    "Expressions/2_ValueExpr/Exists.rsl", [ InvalidRangeType(Node.New(Bot, (0u, 0u))) ]
    "Expressions/2_ValueExpr/Lambda_Eq.rsl", [ UnsupportedExpr(ValueExpr, (0u,0u)); UnsupportedExpr(ValueExpr, (0u,0u)) ]
    "Expressions/2_ValueExpr/Rec_Func.rsl", [ RecursiveFunction(Node.New("", (0u,0u))); RecursiveFunction(Node.New("", (0u,0u))) ]
    "Expressions/2_ValueExpr/EmptyGeneric.rsl", [ EmptyGenericIndex(Node.New("", (0u, 0u))) ]
    "Expressions/3_RuleExpr/Priority.rsl", [ UnsupportedExpr(RuleExpr, (0u, 0u)) ]
    "Expressions/3_RuleExpr/InvalidEvaluation.rsl", [ InvalidEvaluation((0u, 0u)) ]
]

[<Tests>]
let tests =
    testSequenced
    <| testList
        "Unfolding Tests"
        [ testList
              "Pass"
              (getFilesInTestDirs [| [| "All" |]; [| "Unparser" |] |]
               |> List.map (fun file ->
                   testCase file (fun _ -> unfoldCheck file (fun res -> Expect.isOk res "Unfolding failed"))))


          testList
              "Fail"
              (List.map
                  (fun (file, expected) -> makeFailUnfoldTest $"Unfold/{file}" expected "Unfolding should have failed")
                  unfoldFailCases) ]
