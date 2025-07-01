module Unfold.Phase2

open FSharpPlus
open FSharpPlus.Data
open Helpers
open AST
open ASTUtil
open TypeCheck.Error
open Evaluate
open Error
open Phase1

let tryConsumeAssignment kind mem id =
    match Map.tryFind id mem with
    | Some v -> Success(v, Map.remove id mem)
    | None -> Failure(DList.singleton (MissingDefinition(id, Some kind)))

let unfoldTypeDefs env (td: Node<TypeDef>) : MergeResult<Node<TypeDef>, UnfoldingError> =
    match td.Value with
    | Variant _ -> Success td
    | Abbreviation(id, _) ->
        unfoldTypeExpr env (Option.get (Map.find id env.Ty))
        |> Validation.map (fun ty -> Node.Replace(Abbreviation(id, ty), td))
    | _ -> Failure(DList.singleton (InvalidDefinition(TypeDef, td.Span)))

let rec unfoldValueDef env (vald: Node<ValueDef>) (valds, mem) =
    match vald.Value with
    | ValueDef.Single(typing, _) ->
        let id, ty = typing.Value

        (unfoldTypeExpr env ty, tryConsumeAssignment DefinitionKind.ValueDef mem id)
        ||> Validation.map2 (fun ty (v, mem) ->
            let typing = Node.Replace((id, ty), typing)
            Node.Replace(ValueDef.Single(typing, Some v), vald) :: valds, mem)

    | ValueDef.Generic(id, typings, ty) ->
        generateGenericIds env id.Value typings
        // If any of the typings ranges are empty, invalid or cannot be evaluated no values are added.
        |> Validation.bind (fun idsRes ->
            NonEmptyList.foldBack
                (fun newId ->
                    let typing = Node.New((Node.New(newId, vald.Span), ty), vald.Span)

                    PartialResult.appValidation (
                        unfoldValueDef env (Node.Replace(ValueDef.Single(typing, None), vald))
                    ))
                idsRes
                (PersistResult.New(valds, mem))
            |> PartialResult.toValidation)

    | _ -> failwith $"BUG: Failed to remove function definition {vald.Value}"

let rec unfoldVariableDef env (vard: Node<VariableDef>) (vards, mem) =
    match vard.Value with
    | Single typing ->
        let id, ty = typing.Value

        (unfoldTypeExpr env ty, tryConsumeAssignment DefinitionKind.VariableDef mem id)
        ||> Validation.map2 (fun ty (_, mem) ->
            let typing = Node.Replace((id, ty), typing)
            Node.Replace(Single typing, vard) :: vards, mem)

    | VariableDef.Generic(id, typings, ty) ->
        generateGenericIds env id.Value typings
        // If any of the typings ranges are empty, invalid or cannot be evaluated no values are added.
        |> Validation.bind (
            NonEmptyList.fold
                (fun res newId ->
                    let typing = Node.New((Node.New(newId, vard.Span), ty), vard.Span)

                    PartialResult.appValidation (unfoldVariableDef env (Node.Replace(Single typing, vard))) res)

                (PersistResult.New(vards, mem))
            >> PartialResult.toValidation
        )

let rec unfoldRuleExpr (env: Env) (r: Node<RuleExpr>) : MergeResult<Option<Node<RuleExpr>>, UnfoldingError> =
    match r.Value with
    | GuardedCommand(id, guard, effects) ->
        unfoldValueExpr env guard
        |> Validation.bind (fun guard ->
            match evaluate env guard with
            | Success(BoolVal false) -> Success None
            | _ ->
                NonEmptyList.traverse (unfoldValueExpr env) effects
                |> Validation.map (fun effects -> Some(Node.Replace(GuardedCommand(id, guard, effects), r))))

    | QuantifiedRule(typings, rule) ->
        let choiceOp = Node.New(NonDeterministic, r.Span)

        replaceInQuantifiedExpr substRuleExpr' env [] typings rule
        |> Validation.bind (List.traverse (fst >> unfoldRuleExpr env))
        |> Validation.map (fun rs ->
            match rs with
            | [] -> None
            | r :: rs ->
                List.fold
                    (Option.appOption (fun acc r -> Node.New(Choice(choiceOp, acc, r), Node.CommonSpan(acc, r))))
                    r
                    rs)

    | Choice(op, lhs, rhs) ->
        match op.Value with
        | NonDeterministic ->
            (unfoldRuleExpr env lhs, unfoldRuleExpr env rhs)
            ||> Validation.map2 (Option.appOption (fun lhs rhs -> Node.Replace(Choice(op, lhs, rhs), r)))

        | Priority -> Failure(DList.singleton (UnsupportedExpr(RuleExpr, op.Span)))

let mkTsEnv id env tsEnvs =
    let tsEnv = Map.find id tsEnvs

    let valEnv =
        Map.fold (fun (valEnv: Typings) k _ -> valEnv.Remove k) env.Val tsEnv.Var

    { env with Val = valEnv; Var = tsEnv.Var; Mem = Map.union tsEnv.Mem env.Mem }

let unfoldTSDec env tsEnvs (tsd: TransitionSystemDec) : MergeResult<TransitionSystemDec, UnfoldingError> =
    let env' = mkTsEnv tsd.Id env tsEnvs

    let tsMem = Map.fold (fun (mem: Definitions) k _ -> mem.Remove k) env'.Mem env'.Val

    let vards =
        PersistResult.New(List.empty, tsMem)
        |> List.fold (fun acc vard -> PartialResult.appValidation (unfoldVariableDef env' vard) acc)
           /> tsd.VariableDefs
        |> PartialResult.toValidation
        |> Validation.bind (fun (vards, mem) ->
            if Map.isEmpty mem then
                Success vards
            else
                Failure(DList.singleton (UndefinedDefinition(VariableDef, Map.keys mem))))

    let icds =
        List.foldBack
            (fun v acc ->
                match v.Value with
                | Id id ->
                    let value = Map.find id tsMem
                    let span = Node.CommonSpan(id, value)

                    Node.New(Infix(Node.New(Eq, span), Node.New(Id id, id.Span), value), span)
                    :: acc
                | _ -> failwith $"BUG: {v} did not leave id as init constraint")
            tsd.InitConstraintDefs
            List.empty

    (vards,
     List.traverse (unfoldRuleExpr env') tsd.TransitionRuleDefs
     |> Validation.map (List.choose id))
    ||> Validation.map2 (fun vards tsr ->
        { tsd with VariableDefs = List.rev vards; InitConstraintDefs = icds; TransitionRuleDefs = tsr })

let unfoldLTLAssertionDef env tsEnvs (ad: Node<LTLAssertionDef>) =
    mkTsEnv ad.Value.TransitionSystem env tsEnvs
    |> unfoldValueExpr /> ad.Value.Assertion
    |> Validation.map (fun assertion -> Node.Replace({ ad.Value with Assertion = assertion }, ad))

let unfoldScheme (spec: Spec) : MergeResult<Spec, UnfoldingError> =

    let valdMem =
        Map.fold
            (fun (mem: Definitions) k (v: Node<ValueExpr>) ->
                match v.Value with
                | Lambda _ -> mem.Remove k
                | _ -> mem)
            spec.Env.Mem
            spec.Env.Mem


    let valds =
        PersistResult.New(List.empty, valdMem)
        |> List.fold (fun acc vald -> PartialResult.appValidation (unfoldValueDef spec.Env vald) acc)
           /> spec.Scheme.ValueDefs
        |> PartialResult.toValidation
        |> Validation.bind (fun (valds, mem) ->
            if Map.isEmpty mem then
                Success valds
            else
                Failure(DList.singleton (UndefinedDefinition(ValueDef, Map.keys mem))))

    (List.traverse (unfoldTypeDefs spec.Env) spec.Scheme.TypeDefs,
     valds,
     List.traverse (unfoldTSDec spec.Env spec.TsEnvs) spec.Scheme.TransitionSystemDecs,
     List.traverse (unfoldLTLAssertionDef spec.Env spec.TsEnvs) spec.Scheme.LTLAssertionDefs)
    |> uncurryN (
        Validation.map4 (fun tds valds tsds ads ->
            { spec with
                Scheme =
                    { spec.Scheme with
                        TypeDefs = tds
                        ValueDefs = valds
                        TransitionSystemDecs = tsds
                        LTLAssertionDefs = ads } })
    )

let unfold (spec: Spec) : Result<Spec, DList<UnfoldingError>> =
    let specRes = collectDefinitions spec

    PartialResult.toValidation specRes *> unfoldScheme specRes.Value
    |> Validation.toResult
