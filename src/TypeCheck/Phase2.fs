module TypeCheck.Phase2

open FSharpPlus
open FSharpPlus.Data

open Error
open Phase1
open Helpers
open AST
open ASTUtil

let validMaximalIndex (ty: Node<TypeExpr>) =
    match ty.Value with
    | Bot
    | TBool
    | TInt
    | TSort _
    | TVariant _ -> Success ty

    | _ -> Failure(DList.singleton (UnexpectedIndexType ty))

let addTypings kind env typings =
    NonEmptyList.fold
        (fun acc (typing: Node<Typing>) ->
            let ids, ty = typing.Value

            PartialResult.map
                (NonEmptyList.fold (fun (vals: Typings, vars: Typings) id -> vals.Add(id, ty), vars.Remove id)
                 /> ids)
                acc
            <<* checkPairwiseDistinct kind ids)
        (PersistResult.New((env.Val, env.Var)))
        typings
    |> PartialResult.map (fun (valEnv, varEnv) -> { env with Val = valEnv; Var = varEnv })

let rec lub (ty1: Node<TypeExpr>, ty2: Node<TypeExpr>) =
    match ty1.Value, ty2.Value with
    | v1, v2 when v1 = v2 -> Some ty1
    | _, Bot -> Some ty1
    | Bot, _ -> Some ty2

    | Array(index1, value1), Array(index2, value2) ->
        Option.bind
            (fun index ->
                Option.bind (fun value -> Some(Node.Replace(Array(index, value), ty1))) (lub (value1, value2)))
            (lub (index1, index2))

    | Function(args1, ret1), Function(args2, ret2) when args1.Length = args2.Length ->
        Option.bind
            (fun args -> Option.bind (fun ret -> Some(Node.Replace(Function(args, ret), ty1))) (lub (ret1, ret2)))
            (NonEmptyList.traverse lub (NonEmptyList.zip args1 args2))

    | Generic(indices1, value1), Generic(indices2, value2) when indices1.Length = indices2.Length ->
        Option.bind
            (fun indices ->
                Option.bind (fun value -> Some(Node.Replace(Generic(indices, value), ty1))) (lub (value1, value2)))
            (NonEmptyList.traverse lub (NonEmptyList.zip indices1 indices2))

    | _ -> None

let rec lubMany span tys =
    match tys with
    | [] -> Success(Node.New(Bot, span))
    | [ ty ] -> Success ty
    | ty :: tys ->
        List.fold
            (fun acc ty ->
                Validation.bind
                    (fun accTy ->
                        match lub (accTy, ty) with
                        | Some ty -> Success ty
                        | None -> Failure(DList.singleton (InCompatibleTypes(accTy, ty))))
                    acc)
            (Success ty)
            tys

let rec containsBot (ty: Node<TypeExpr>) =
    match ty.Value with
    | TBool
    | TInt
    | TId _
    | TSort _
    | TVariant _ -> false

    | Bot -> true

    | Array(index, value) -> containsBot index || containsBot value
    | Function(indices, value)
    | Generic(indices, value) -> NonEmptyList.exists containsBot indices || containsBot value
    | Subtype(typing, _) -> containsBot (snd typing.Value)

let rec synthesizeExpr
    allowTemporalOps
    defKind
    env
    (expr: Node<ValueExpr>)
    : MergeResult<Node<TypeExpr>, TypeCheckingError> =
    let synthesize = synthesizeExpr allowTemporalOps defKind
    let check = checkExpr allowTemporalOps defKind

    match expr.Value with
    | Bool _ -> Success(Node.New(TBool, expr.Span))
    | Int _ -> Success(Node.New(TInt, expr.Span))
    | Id id ->
        lookupMaximalType env defKind id
        |> Validation.bind (fun (ty: Node<TypeExpr>) ->
            match ty.Value with
            | Generic _ -> Failure(DList.singleton (GenericReference id))
            | _ -> Success ty)

    | Disambiguation(value, ty) ->
        validType env defKind ty
        *> Validation.bind (check env value) (maximal env defKind ty)

    | EnumeratedArray content ->
        List.traverse (synthesize env) content
        |> Validation.bind (fun contentTys ->
            lubMany expr.Span contentTys
            |> Validation.bind (fun ty -> Success(Node.New(Array(Node.New(Bot, expr.Span), ty), expr.Span))))

    | FunctionApp(value, args) ->
        synthesize env value
        |> Validation.bind (fun (ty: Node<TypeExpr>) ->
            match ty.Value with
            | Function(argsTy, retTy) when argsTy.Length = args.Length ->
                NonEmptyList.traverse (uncurry (check env)) (NonEmptyList.zip args argsTy)
                *> Success retTy
            | _ ->
                NonEmptyList.traverse (synthesize env) args
                |> Validation.bind (fun argsTy -> Failure(DList.singleton (UnexpectedArgument(argsTy, ty)))))

    | ArrayApp(value, indices) ->
        synthesize env value
        |> Validation.bind (fun ty ->
            NonEmptyList.fold
                (fun acc index ->
                    PartialResult.appValidation
                        (fun accTy ->
                            match accTy.Value with
                            | Array(expectedIndexTy, valueTy) ->
                                (synthesize env index
                                 |> Validation.bind (fun indexTy ->
                                     validMaximalIndex indexTy
                                     *> match lub (indexTy, expectedIndexTy) with
                                        | Some _ -> Success expectedIndexTy
                                        | None ->
                                            Failure(
                                                DList.singleton (
                                                    UnexpectedType(expectedIndexTy, indexTy, index.Span)
                                                )
                                            )))
                                *> Success valueTy
                            | _ ->
                                NonEmptyList.traverse (synthesize env) indices
                                |> Validation.bind (fun indicesTy ->
                                    Failure(DList.singleton (UnexpectedArgument(indicesTy, ty)))))
                        acc)
                (PersistResult.New ty)
                indices
            |> PartialResult.toValidation)

    | GenericApp(id, indices) ->
        lookupMaximalType env defKind id
        |> Validation.bind (fun (ty: Node<TypeExpr>) ->
            match ty.Value with
            | Generic(indicesTy, valueTy) when indicesTy.Length = indices.Length ->
                NonEmptyList.traverse (uncurry (check env)) (NonEmptyList.zip indices indicesTy)
                *> Success valueTy
            | _ ->
                NonEmptyList.traverse (synthesize env) indices
                |> Validation.bind (fun indicesTy -> Failure(DList.singleton (UnexpectedArgument(indicesTy, ty)))))

    | Lambda(typings, body) ->
        let envRes = addTypings defKind env typings

        PartialResult.toValidation envRes *> synthesize envRes.Value body
        |> Validation.bind (fun bodyTy ->
            toSingleTypings typings
            |> NonEmptyList.traverse (fun typing -> maximal env defKind (snd typing.Value))
            |> Validation.map (fun argTys -> Node.New(Function(argTys, bodyTy), expr.Span)))

    | Quantified(q, typings, restriction) ->
        let envRes = addTypings defKind env typings

        PartialResult.toValidation envRes
        *> check envRes.Value restriction (Node.New(TBool, q.Span))

    | Infix(op, lhs, rhs) ->
        let inputTy, outputTy, isTemporal =
            match op.Value with
            | (Add | Sub | Mod | Mul | Div) -> TInt, TInt, false
            | (Eq | Neq) -> Bot, TBool, false
            | (Ge | Le | Geq | Leq) -> TInt, TBool, false
            | (Imp | Or | And) -> TBool, TBool, false
            | Until -> TBool, TBool, true

        match inputTy with
        | Bot -> synthesize env lhs |> Validation.bind (check env rhs)
        | _ ->
            let inputTyNode = Node.New(inputTy, op.Span)
            check env lhs inputTyNode *> check env rhs inputTyNode

        *> Success(Node.New(outputTy, op.Span))

        <* if isTemporal && not allowTemporalOps then
               Failure(DList.singleton (UnexpectedInfixOp op))
           else
               Success()

    | Prefix(op, expr) ->
        let ty, isTemporal =
            match op.Value with
            | (Pos | Neg) -> TInt, false
            | Not -> TBool, false
            | (Global | Finally | Next) -> TBool, true

        check env expr (Node.New(ty, op.Span))
        <* if isTemporal && not allowTemporalOps then
               Failure(DList.singleton (UnexpectedPrefixOp op))
           else
               Success()

    | Let(id, init, body) ->
        synthesize env init
        |> Validation.bind (fun (ty: Node<TypeExpr>) ->
            let env' =
                { env with Val = env.Val.Add(id, Node.New(ty.Value, id.Span)); Var = env.Var.Remove id }

            if containsBot ty then
                Failure(DList.singleton (MissingDisambiguation init.Span))
            else
                synthesize env' body)

    | If(cond, ifTrue, ifFalse) ->
        check env cond (Node.New(TBool, cond.Span))
        *> ((synthesize env ifTrue, synthesize env ifFalse)
            ||> Validation.bind2 (fun ifTrueTy ifFalseTy ->
                match lub (ifTrueTy, ifFalseTy) with
                | Some ty -> Success ty
                | None -> Failure(DList.singleton (InCompatibleIfCases(ifTrueTy, ifFalseTy)))))

and checkExpr allowTemporalOps defKind env (expr: Node<ValueExpr>) expectedTy =
    synthesizeExpr allowTemporalOps defKind env expr
    |> Validation.bind (fun ty ->
        match lub (ty, expectedTy) with
        | Some _ -> Success expectedTy
        | None -> Failure(DList.singleton (UnexpectedType(expectedTy, ty, expr.Span))))

and maximal env defKind (ty: Node<TypeExpr>) : MergeResult<Node<TypeExpr>, TypeCheckingError> =
    match ty.Value with
    | TBool
    | TInt
    | TSort _
    | TVariant _ -> Success ty

    | TId t ->
        match Map.tryFind t env.Ty with
        | Some(Some ty) -> maximal env defKind ty
        | Some None -> Failure(DList.singleton (UseOfCircularType t))
        | None -> Failure(DList.singleton (MissingDefinition(t, TypeDef)))

    | Function(args, ret) ->
        (NonEmptyList.traverse (maximal env defKind) args, maximal env defKind ret)
        ||> Validation.map2 (fun args ret -> Node.Replace(Function(args, ret), ty))

    | Array(index, value) ->
        (maximal env defKind index, maximal env defKind value)
        ||> Validation.map2 (fun index value -> Node.Replace(Array(index, value), ty))

    | Generic(indices, value) ->
        (NonEmptyList.traverse (maximal env defKind) indices, maximal env defKind value)
        ||> Validation.map2 (fun indices value -> Node.Replace(Generic(indices, value), ty))

    | Subtype(typing, _) -> maximal env defKind (snd typing.Value)

    | _ -> failwith "BUG: The bottom type has no maximal type"

and lookupMaximalType env defKind id : MergeResult<Node<TypeExpr>, TypeCheckingError> =
    match Map.tryFind id env.Val with
    | Some ty -> maximal env defKind (Node.New(ty.Value, id.Span))
    | None ->
        match Map.tryFind (normalizeId id) env.Var with
        | Some ty -> maximal env defKind (Node.New(ty.Value, id.Span))
        | None -> Failure(DList.singleton (MissingDefinition(id, defKind)))

and validType env defKind (ty: Node<TypeExpr>) : MergeResult<unit, TypeCheckingError> =
    match ty.Value with
    | Bot
    | TBool
    | TInt
    | TSort _
    | TVariant _ -> Success()

    | TId t ->
        match Map.tryFind t env.Ty with
        | Some(Some _) -> Success()
        | Some None -> Failure(DList.singleton (UseOfCircularType t))
        | None -> Failure(DList.singleton (MissingDefinition(t, TypeDef)))

    | Function(args, ret) -> NonEmptyList.traverse (validType env defKind) args *> validType env defKind ret

    | Array(index, value) ->
        validType env defKind index
        *> Validation.bind validMaximalIndex (maximal env defKind index)
        *> validType env defKind value

    | Generic(indices, value) ->
        //FIXME: the typechecker reports an obscure error
        // related to FSharpPlus if x is substituted by its value
        let x = NonEmptyList.traverse (validType env defKind) indices

        x
        *> NonEmptyList.traverse (fun idx -> Validation.bind validMaximalIndex (maximal env defKind idx)) indices
        *> validType env defKind value

    | Subtype(typing, restriction) ->
        validType env defKind (snd typing.Value)
        |> Validation.bind (fun _ ->
            let id, ty = typing.Value

            let env = { env with Val = Map.add id ty env.Val; Var = Map.empty }

            checkExpr false defKind env restriction (Node.New(TBool, restriction.Span))
            *> Success())

let checkValueDef env (vald: Node<ValueDef>) : MergeResult<unit, TypeCheckingError> =
    match vald.Value with
    | ValueDef.Single(typing, init) ->
        validType env ValueDef (snd typing.Value)
        |> Validation.bind (fun _ ->
            maximal env ValueDef (snd typing.Value)
            |> Validation.bind (fun ty ->
                match init with
                | Some v -> checkExpr false ValueDef { env with Var = Map.empty } v ty *> Success()
                | None -> Success()))

    | ValueDef.Function(_, ty, _, args, body) ->
        let argTys, retTy = ty.Value

        let valEnv' =
            NonEmptyList.fold (fun (valEnv: Typings) entry -> valEnv.Add entry) env.Val (NonEmptyList.zip args argTys)

        let typeExpr = Node.New(Function ty.Value, ty.Span)

        validType env ValueDef typeExpr
        |> Validation.bind (fun _ ->
            maximal env ValueDef retTy
            |> Validation.bind (fun retTy ->
                checkExpr false ValueDef { env with Val = valEnv' } body retTy *> Success()))

    | ValueDef.Generic(_, typings, ty) ->
        let typeExpr =
            Node.New(Generic(NonEmptyList.map (Node.GetValue >> snd) typings, ty), vald.Span)

        validType env ValueDef typeExpr

let checkVariableDef env (vard: Node<VariableDef>) : MergeResult<unit, TypeCheckingError> =
    match vard.Value with
    | Single typing ->
        validType env VariableDef (snd typing.Value)
        |> Validation.bind (fun _ -> maximal env VariableDef (snd typing.Value) *> Success())

    | VariableDef.Generic(id, typings, ty) ->
        let typeExpr =
            Node.New(Generic(NonEmptyList.map (Node.GetValue >> snd) typings, ty), vard.Span)

        validType env VariableDef typeExpr

let checkId nameKind id idsRes =
    match id with
    | Some id ->
        PartialResult.appResult
            (fun ids ->
                if Set.contains id ids then
                    Error(DList.singleton (DuplicateName(id, nameKind)))
                else
                    Ok(Set.add id ids))
            idsRes
    | None -> idsRes

let checkAxiomDef env idsRes (axd: Node<AxiomDef>) : PersistResult<Set<Node<string>>, TypeCheckingError> =
    checkId Axiom axd.Value.Name idsRes
    <<* checkExpr false AxiomDef env axd.Value.Axiom (Node.New(TBool, axd.Value.Axiom.Span))

let mkTsEnv id env tsEnvs =
    match Map.tryFind id tsEnvs with
    | Some tsEnv ->
        let valEnv =
            Map.fold (fun (valEnv: Typings) k _ -> valEnv.Remove k) env.Val tsEnv.Var

        PersistResult.New { env with Val = valEnv; Var = tsEnv.Var }
    | None -> { Value = env; Errors = DList.singleton (MissingDeclaration id) }

let checkLTLAssertionDef env tsEnvs idsRes (ad: Node<LTLAssertionDef>) =
    let envRes = mkTsEnv ad.Value.TransitionSystem env tsEnvs

    checkId LTLAssertion (Some ad.Value.Name) idsRes
    <<* envRes
    <<* checkExpr true LTLAssertionDef envRes.Value ad.Value.Assertion (Node.New(TBool, ad.Value.Assertion.Span))

let rec checkRuleExpr (env: Env) idsRes (r: Node<RuleExpr>) : PersistResult<Set<Node<string>>, TypeCheckingError> =
    match r.Value with
    | GuardedCommand(id, guard, effects) ->
        checkId Rule id idsRes
        <<* checkExpr false RuleDef env guard (Node.New(TBool, guard.Span))
        <<* NonEmptyList.traverse
                (fun effect -> checkExpr false RuleDef env effect (Node.New(TBool, effect.Span)))
                effects

    | QuantifiedRule(typings, rule) ->
        PartialResult.apply (fun env -> checkRuleExpr env idsRes rule) (addTypings RuleDef env typings)

    | Choice(_, lhs, rhs) ->
        let idsRes' = checkRuleExpr env idsRes lhs
        checkRuleExpr env idsRes' rhs

let checkTsDef env tsEnvs (tsd: TransitionSystemDec) : MergeResult<unit, TypeCheckingError> =
    let envRes = mkTsEnv tsd.Id env tsEnvs

    PartialResult.toValidation envRes
    *> List.traverse (checkVariableDef envRes.Value) tsd.VariableDefs
    *> List.traverse
        (fun v -> checkExpr false InitConstraintDef envRes.Value v (Node.New(TBool, v.Span)))
        tsd.InitConstraintDefs
    *> PartialResult.toValidation (
        List.fold (checkRuleExpr envRes.Value) (PersistResult.New Set.empty) tsd.TransitionRuleDefs
    )
    *> Success()

let checkDecs (spec: Spec) : MergeResult<unit, TypeCheckingError> =
    Seq.traverse (fun ty -> validType spec.Env TypeDef ty) (Map.values spec.Env.Ty |> Seq.choose id)
    *> List.traverse (checkValueDef spec.Env) spec.Scheme.ValueDefs
    *> PartialResult.toValidation (
        List.fold (checkAxiomDef spec.Env) (PersistResult.New Set.empty) spec.Scheme.AxiomDefs
    )
    *> List.traverse (checkTsDef spec.Env spec.TsEnvs) spec.Scheme.TransitionSystemDecs
    *> PartialResult.toValidation (
        List.fold (checkLTLAssertionDef spec.Env spec.TsEnvs) (PersistResult.New Set.empty) spec.Scheme.LTLAssertionDefs
    )
    *> Success()

let typecheck (filename: string, scheme: Scheme) : Result<Spec, DList<TypeCheckingError>> =
    let specRes = collectDefs scheme

    checkFilename filename scheme *> PartialResult.toValidation specRes
    <* checkDecs specRes.Value
    |> Validation.toResult
