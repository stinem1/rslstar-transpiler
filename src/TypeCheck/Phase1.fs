module TypeCheck.Phase1

open FSharpPlus
open FSharpPlus.Data
open Helpers
open AST
open Error
open Syntax.Unparse

let checkPairwiseDistinct kind (xs: NonEmptyList<Node<string>>) =
    match NonEmptyList.length xs with
    | l when l > 1 ->
        NonEmptyList.pairwise xs
        |> NonEmptyList.fold
            (fun acc (x, y) ->
                if x = y then
                    match acc with
                    | Ok() -> Error(DList.singleton (DuplicateDefinition(x, kind, None)))
                    | Error es -> Error(DList.add (DuplicateDefinition(x, kind, None)) es)
                else
                    acc)
            (Ok())
    | _ -> Ok()

let tryAddDefinition kind (k, v) m =
    match Map.tryFind k m with
    | Some v' -> Error(DList.singleton (DuplicateDefinition(k, kind, Some v')))
    | None -> Ok(Map.add k v m)

let tryAddType entry (env, initialTypes) =
    Result.map (tuple2 env) (tryAddDefinition TypeDef entry initialTypes)

let tryAddVal entry env =
    Result.map (fun typings -> { env with Val = typings }) (tryAddDefinition ValueDef entry env.Val)

let addTypeDef envRes (def: Node<TypeDef>) =
    match def.Value with
    | Sort id -> PartialResult.appResult (tryAddType (id, Node.New(TSort id, def.Span))) envRes

    | Variant(id, cases) ->
        PartialResult.appResult (tryAddType (id, Node.New(TVariant(id, cases), def.Span))) envRes
        |> NonEmptyList.fold (fun res case ->
            PartialResult.appResult
                (fun (env, initialTypes) ->
                    tryAddVal (case, Node.New(TId id, def.Span)) env
                    |> Result.map (fun env -> env, initialTypes))
                res)
           /> cases

    | Abbreviation(id, ty) -> PartialResult.appResult (tryAddType (id, ty)) envRes

let addValueDef env (def: Node<ValueDef>) : PersistResult<Env, TypeCheckingError> =
    match def.Value with
    | ValueDef.Single(typing, _) -> PartialResult.appResult (tryAddVal typing.Value) env

    | ValueDef.Function(signatureId, ty, formalId, args, _) ->

        PartialResult.appResult (tryAddVal (signatureId, Node.New(Function ty.Value, ty.Span))) env
        <<* checkPairwiseDistinct ValueDef args
        <<* if signatureId.Value <> formalId.Value then
                Error(DList.singleton (SignatureMismatch(signatureId, formalId)))
            else
                Ok()

    | ValueDef.Generic(id, typings, ty) ->
        let ty' =
            Node.New(Generic(NonEmptyList.map (Node.GetValue >> snd) typings, ty), def.Span)

        PartialResult.appResult (tryAddVal (id, ty')) env
        <<* checkPairwiseDistinct ValueDef (NonEmptyList.cons id (NonEmptyList.map (Node.GetValue >> fst) typings))

let addVariableDef (varEnv: PersistResult<Typings, TypeCheckingError>) (def: Node<VariableDef>) =
    match def.Value with
    | Single typing -> PartialResult.appResult (tryAddDefinition VariableDef typing.Value) varEnv

    | VariableDef.Generic(id, typings, ty) ->
        let ty' =
            Node.New(Generic(NonEmptyList.map (Node.GetValue >> snd) typings, ty), def.Span)

        PartialResult.appResult (tryAddDefinition VariableDef (id, ty')) varEnv
        <<* checkPairwiseDistinct VariableDef (NonEmptyList.cons id (NonEmptyList.map (Node.GetValue >> fst) typings))

let rec checkTypeDefs
    initialTypes
    (ancestors: string Set)
    (ty: Node<TypeExpr>)
    (typesRes: PersistResult<Types, TypeCheckingError>)
    =
    match ty.Value with
    | TBool
    | TInt
    | TSort _
    | TVariant _ -> typesRes, Some ty

    | TId t ->
        let typesRes, optExpr =
            match Map.tryFind t typesRes.Value with
            | Some expr -> typesRes, expr
            | None ->
                match Map.tryFind t initialTypes with
                | Some expr ->
                    if Set.contains t.Value ancestors then
                        PersistResult.AddErrors (DList.singleton (CircularTypeDefinition t)) typesRes, None
                    else
                        checkTypeDefs initialTypes (Set.add t.Value ancestors) expr typesRes
                | None -> PersistResult.AddErrors (DList.singleton (MissingDefinition(t, TypeDef))) typesRes, None

        PartialResult.map (fun (types: Types) -> types.Add(t, optExpr)) typesRes,
        Option.map
            (fun (expr: Node<TypeExpr>) ->
                match expr.Value with
                | TSort _
                | TVariant _
                | Subtype _ -> ty
                | _ -> expr)
            optExpr

    | Array(index, value) ->
        let typesRes, index = checkTypeDefs initialTypes ancestors index typesRes
        let typesRes, value = checkTypeDefs initialTypes ancestors value typesRes
        typesRes, Option.map2 (fun index value -> Node.Replace(Array(index, value), ty)) index value

    | Subtype(typing, restriction) ->
        let id, expr = typing.Value
        let typesRes, expr = checkTypeDefs initialTypes ancestors expr typesRes
        typesRes, Option.map (fun expr -> Node.Replace(Subtype(Node.Replace((id, expr), typing), restriction), ty)) expr

    | _ -> failwith $"BUG: {unparseTypeExpr ty.Value} a Bottom, Generic and Function type cannot be abbreviated"

let checkTypes (env, initialTypes) =
    Seq.fold
        (fun typesRes (t: Node<string>) ->
            checkTypeDefs initialTypes Set.empty { Value = TId t; Span = t.Span } typesRes
            |> fst)
        (PersistResult.New Map.empty)
        initialTypes.Keys
    |> PartialResult.map (fun types -> { env with Ty = types })

let collectTsDefs (ts: TransitionSystemDec) tsEnvs =
    PersistResult.New Map.empty
    <<* (if Map.containsKey ts.Id tsEnvs then
             Error(DList.singleton (DuplicateDeclaration ts.Id))
         else
             Ok())
    |> List.fold addVariableDef /> ts.VariableDefs
    |> PartialResult.map (fun typings -> tsEnvs.Add(ts.Id, { Var = typings; Mem = Map.empty }))

let collectDefs (scheme: Scheme) : PersistResult<Spec, TypeCheckingError> =
    let env =
        PersistResult.New(
            { Ty = Map.empty
              Val = Map.empty
              Var = Map.empty
              Mem = Map.empty },
            Map.empty
        )
        |> List.fold addTypeDef /> scheme.TypeDefs
        |> PartialResult.apply checkTypes
        |> List.fold addValueDef /> scheme.ValueDefs

    let tsEnvs =
        PersistResult.New Map.empty
        |> List.fold (fun tsEnvRes ts -> PartialResult.apply (collectTsDefs ts) tsEnvRes)
           /> scheme.TransitionSystemDecs

    PartialResult.map2 (fun env tsEnvs -> { Env = env; TsEnvs = tsEnvs; Scheme = scheme }) env tsEnvs

let checkFilename filename (scheme: Scheme) : MergeResult<unit, TypeCheckingError> =
    if filename <> scheme.Id.Value then
        Failure(DList.singleton (ModuleNameMismatch(scheme.Id, filename)))
    else
        Success()
