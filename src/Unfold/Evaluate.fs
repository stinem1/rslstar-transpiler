module Unfold.Evaluate

open System
open FSharpPlus.Data
open Helpers
open AST
open Syntax.Unparse
open ASTUtil
open Error

type EvaluatedValue =
    | BoolVal of bool
    | IntVal of int
    | VariantVal of string

    member this.TypeName =
        match this with
        | BoolVal _ -> "Bool"
        | IntVal _ -> "Int"
        | VariantVal _ -> "Variant"

    member this.Format =
        match this with
        | BoolVal b -> toLower (string b)
        | IntVal i -> string i
        | VariantVal id -> id

let private getArithOp =
    function
    | Add -> Some (+)
    | Sub -> Some (-)
    | Mod -> Some (%)
    | Mul -> Some (*)
    | Div -> Some (/)
    | _ -> None

let private getOrderOp =
    function
    | Eq -> Some (=)
    | Neq -> Some (<>)
    | Ge -> Some (>)
    | Le -> Some (<)
    | Geq -> Some (>=)
    | Leq -> Some (<=)
    | _ -> None

let private getLogicOp =
    function
    | Imp -> Some(fun b1 b2 -> not b1 || b2)
    | Or -> Some (||)
    | And -> Some (&&)
    | Eq -> Some (=)
    | Neq -> Some (<>)
    | _ -> None

let isVariantType env (ty: Node<TypeExpr>) =
    match ty.Value with
    | TVariant _ -> true
    | TId t ->
        match Map.find t env.Ty with
        | Some { Value = TVariant _ } -> true
        | _ -> false
    | _ -> false

let isFalse ev =
    match ev with
    | Success(BoolVal false) -> true
    | _ -> false

let rec evaluate (env: Env) (v: Node<ValueExpr>) : MergeResult<EvaluatedValue, UnfoldingError> =
    match v.Value with
    | Bool b -> Success(BoolVal b.Value)
    | Int i -> Success(IntVal i.Value)
    | Id id ->
        match Map.tryFind id env.Val with
        | Some ty ->
            if isVariantType env ty then
                Success(VariantVal id.Value)
            else
                match Map.tryFind id env.Mem with
                | Some v -> evaluate env v
                | None -> Failure(DList.singleton (InvalidEvaluation v.Span))

        | None -> Failure(DList.singleton (InvalidEvaluation v.Span))

    | Disambiguation(value, _) -> evaluate env value

    | GenericApp(id, indices) ->
        generateGenericId env (id, indices)
        |> Validation.bind (fun newId -> evaluate env (Node.NewBasicNode v.Span Id newId))

    | Infix({ Value = And }, _, _) ->
        let results = collectInfixExpr And List.empty v |> List.map (evaluate env)

        if List.exists isFalse results then
            Success(BoolVal false)
        else
            List.traverse id results |> Validation.map (fun _ -> BoolVal true)

    | Infix(op, lhs, rhs) ->
        (evaluate env lhs, evaluate env rhs)
        ||> Validation.bind2 (fun lhs rhs ->
            match lhs, rhs with
            | BoolVal b1, BoolVal b2 ->
                match getLogicOp op.Value with
                | Some op -> Success(BoolVal(op b1 b2))
                | _ -> Failure(DList.singleton (InvalidEvaluation v.Span))

            | IntVal i1, IntVal i2 ->
                match getArithOp op.Value with
                | Some op -> Success(IntVal(op i1 i2))
                | None ->
                    match getOrderOp op.Value with
                    | Some op -> Success(BoolVal(op i1 i2))
                    | None -> Failure(DList.singleton (InvalidEvaluation v.Span))

            | _ -> Failure(DList.singleton (InvalidEvaluation v.Span)))

    | Prefix(op, expr) ->
        evaluate env expr
        |> Validation.bind (fun expr ->
            match expr with
            | BoolVal b ->
                match op.Value with
                | Not -> Success(BoolVal(not b))
                | _ -> Failure(DList.singleton (InvalidEvaluation v.Span))

            | IntVal i ->
                let optOp =
                    match op.Value with
                    | Pos -> Some (~+)
                    | Neg -> Some (~+)
                    | _ -> None

                match optOp with
                | Some op -> Success(IntVal(op i))
                | None -> Failure(DList.singleton (InvalidEvaluation v.Span))

            | _ -> Failure(DList.singleton (InvalidEvaluation v.Span)))

    | _ -> Failure(DList.singleton (InvalidEvaluation v.Span))

and collectInfixExpr op acc (v: Node<ValueExpr>) : List<Node<ValueExpr>> =
    match v.Value with
    | Infix({ Value = op' }, lhs, rhs) when op' = op -> collectInfixExpr op (collectInfixExpr op acc lhs) rhs
    | _ -> v :: acc

and generateGenericId env (id: Node<string>, indices) : MergeResult<string, UnfoldingError> =
    NonEmptyList.fold
        (fun acc index ->
            evaluate env index
            |> Validation.map2 (fun acc v -> String.Concat(acc, "_", v.Format)) acc)
        (Success(Node.GetValue(normalizeId id)))
        indices
    |> Validation.map (fun newId -> if id.Value.EndsWith ''' then $"{newId}'" else newId)
