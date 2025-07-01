module Unfold.Phase1

open System
open FSharpPlus
open FSharpPlus.Data
open Helpers
open AST
open ASTUtil
open Syntax.Unparse
open TypeCheck.Error
open Error
open Evaluate

type TypeRange =
    | BoolRange of NonEmptyList<bool>
    | IntRange of NonEmptyList<int>
    | VariantRange of NonEmptyList<string>
    | Empty

let rec getRange env (ty: Node<TypeExpr>) : MergeResult<TypeRange, UnfoldingError> =
    match ty.Value with
    | TId t -> getRange env (Option.get (Map.find t env.Ty))

    | TBool ->
        Success(
            BoolRange(
                nelist {
                    true
                    false
                }
            )
        )

    | TVariant(_, cases) -> NonEmptyList.map Node.GetValue cases |> VariantRange |> Success

    | Subtype(typing, restriction) ->
        match restriction.Value, typing.Value with
        | _, (id, { Value = TId t }) ->
            let typing = Node.Replace((id, Option.get (Map.find t env.Ty)), typing)
            getRange env (Node.Replace(Subtype(typing, restriction), ty))

        | Infix({ Value = Neq }, { Value = Id x }, { Value = Id y }), (id, { Value = TVariant(_, cases) }) ->
            if x = id && NonEmptyList.contains y cases then
                let ids = NonEmptyList.filter ((<>) y) cases |> NonEmptyList.map Node.GetValue

                Success(VariantRange ids)
            else
                Failure(DList.singleton (InvalidRangeType ty))

        | Infix({ Value = And },
                { Value = Infix({ Value = Geq }, { Value = Id x1 }, v1) },
                { Value = Infix({ Value = Le }, { Value = Id x2 }, v2) }),

          (id, { Value = TInt }) ->

            if x1 = x2 && x1 = id then
                (evaluate env v1, evaluate env v2)
                ||> Validation.map2 (fun v1 v2 ->
                    match v1, v2 with
                    | IntVal i1, IntVal i2 ->
                        if i2 - 1 > i1 then
                            IntRange(NonEmptyList.range i1 (i2 - 1))
                        else
                            Empty

                    | _ ->
                        failwith
                            $"BUG: {unparseInfixOp Geq} is applied to {v1.TypeName} 
                                    and {unparseInfixOp Le} is applied to {v2.TypeName}")
            else
                Failure(DList.singleton (InvalidRangeType ty))

        | _ -> Failure(DList.singleton (InvalidRangeType ty))

    | _ -> Failure(DList.singleton (InvalidRangeType ty))

let generateGenericIds env (baseId: string) typings : MergeResult<NonEmptyList<string>, UnfoldingError> =

    let addToIds rng ids =
        ids
        >>= fun id -> NonEmptyList.map (fun i -> String.Concat(id, "_", string i)) rng

    NonEmptyList.traverse
        (fun (typing: Node<SingleTyping>) ->
            let id, ty = typing.Value
            Validation.map (tuple2 id) (getRange env ty))
        typings
    |> Validation.bind (
        NonEmptyList.fold
            (fun idsRes (id, rngTy) ->
                Validation.bind
                    (fun ids ->
                        match rngTy with
                        | BoolRange rng -> Success(addToIds rng ids)
                        | IntRange rng -> Success(addToIds rng ids)
                        | VariantRange rng -> Success(addToIds rng ids)
                        | Empty -> Failure(DList.singleton (EmptyGenericIndex id)))
                    idsRes)
            (Success(NonEmptyList.singleton baseId))
    )

let substQuantified (subst': bool -> Node<string> * Node<ValueExpr> -> 'a -> 'a) (expr, typingsOpt) v' =
    match typingsOpt with
    | Some typings ->
        match typings with
        | { Head = { Node.Value = { Head = id; Tail = [] }, _ }; Tail = [] } -> subst' false (id, v') expr, None

        | { Head = { Node.Value = { Head = id; Tail = [] }, _ }; Tail = _ } ->
            substBindings subst' (id, v') expr (NonEmptyList.tail typings) |> mapItem2 Some

        | { Head = typing; Tail = rs } ->
            let ids, ty = typing.Value

            let typings =
                { Head = Node.Replace((NonEmptyList.tail ids, ty), typing); Tail = rs }

            substBindings subst' (ids.Head, v') expr typings |> mapItem2 Some
    | None -> failwith $"BUG: This expression {expr} tried to perform more substitutions than indicated by typings"

let inline substRange (subst: bool -> Node<string> * Node<ValueExpr> -> 'a -> 'a) kind id rng acc =
    acc
    >>= fun (v, typings) ->
        NonEmptyList.map (fun rv -> substQuantified subst (v, typings) (Node.NewBasicNode id.Span kind rv)) rng
        |> NonEmptyList.toList
    |> List.distinct

let replaceInQuantifiedExpr
    (subst: bool -> Node<string> * Node<ValueExpr> -> 'a -> 'a)
    env
    (vacuous: List<'a * Option<NonEmptyList<Node<Typing>>>>)
    typings
    (expr: 'a)
    : MergeResult<List<'a * Option<NonEmptyList<Node<Typing>>>>, UnfoldingError> =

    NonEmptyList.traverse
        (fun { Node.Value = id, ty } -> Validation.map (tuple2 id) (getRange env ty))
        (toSingleTypings typings)
    |> Validation.map (
        NonEmptyList.fold
            (fun rs (id: Node<string>, rngTy) ->
                match rngTy with
                | BoolRange rng -> substRange subst Bool id rng rs
                | IntRange rng -> substRange subst Int id rng rs
                | VariantRange rng -> substRange subst Id id rng rs
                | Empty -> vacuous)
            [ (expr, Some typings) ]
    )

let rec unfoldValueExpr (env: Env) (v: Node<ValueExpr>) : MergeResult<Node<ValueExpr>, UnfoldingError> =
    match v.Value with
    | Bool _
    | Int _
    | Id _ -> Success v

    | Disambiguation(value, ty) ->
        (unfoldValueExpr env value, unfoldTypeExpr env ty)
        ||> Validation.map2 (fun value ty -> Node.Replace(Disambiguation(value, ty), v))

    | EnumeratedArray content ->
        List.traverse (unfoldValueExpr env) content
        |> Validation.map (fun content -> Node.Replace(EnumeratedArray content, v))

    | FunctionApp(value, args) ->
        match value.Value with
        | Id id ->
            match Map.tryFind id env.Mem with
            | Some value -> unfoldValueExpr env (Node.Replace(FunctionApp(value, args), v))
            | None -> Failure(DList.singleton (RecursiveFunction id))

        | Lambda(typings, body) ->
            NonEmptyList.fold (substQuantified substValueExpr') (body, Some typings) args
            |> fst
            |> unfoldValueExpr env

        | _ -> Failure(DList.singleton (UnsupportedExpr(ValueExpr, v.Span)))

    | ArrayApp(value, indices) ->
        (unfoldValueExpr env value, NonEmptyList.traverse (unfoldValueExpr env) indices)
        ||> Validation.map2 (fun value indices -> Node.Replace(ArrayApp(value, indices), v))

    | GenericApp(id, indices) ->
        generateGenericId env (id, indices)
        |> Validation.map (fun newId -> Node.NewBasicNode v.Span Id newId)

    | Lambda _ -> Failure(DList.singleton (UnsupportedExpr(ValueExpr, v.Span)))

    | Quantified(q, typings, restriction) ->
        let connective =
            match q.Value with
            | All -> Node.New(And, q.Span)
            | Exists -> Node.New(Or, q.Span)

        // If a range is empty the expression is vacuously true/false
        // otherwise we generate a conjunction/disjunction from substituting v with
        // the product of the given ranges
        let vacuous =
            (match q.Value with
             | All -> true
             | Exists -> false)
            |> Node.NewBasicNode (Node.CommonSpan typings) Bool

        replaceInQuantifiedExpr substValueExpr' env [ (vacuous, None) ] typings restriction
        |> Validation.bind (NonEmptyList.ofList >> NonEmptyList.traverse (fst >> unfoldValueExpr env))
        |> Validation.map (fun { Head = v; Tail = vs } ->
            List.fold (fun acc v -> Node.New(Infix(connective, acc, v), Node.CommonSpan(acc, v))) v vs)

    | Infix(op, lhs, rhs) ->
        (unfoldValueExpr env lhs, unfoldValueExpr env rhs)
        ||> Validation.map2 (fun lhs rhs -> Node.Replace(Infix(op, lhs, rhs), v))

    | Prefix(op, expr) ->
        unfoldValueExpr env expr
        |> Validation.map (fun expr -> Node.Replace(Prefix(op, expr), v))

    | Let(id, init, body) ->
        unfoldValueExpr env init
        |> Validation.bind (fun init -> unfoldValueExpr env (substValueExpr (id, init) body))

    | If(cond, ifTrue, ifFalse) ->
        (unfoldValueExpr env cond, unfoldValueExpr env ifTrue, unfoldValueExpr env ifFalse)
        |||> Validation.map3 (fun cond ifTrue ifFalse -> Node.Replace(If(cond, ifTrue, ifFalse), v))

and unfoldTypeExpr (env: Env) (ty: Node<TypeExpr>) =
    match ty.Value with
    | Bot
    | TBool
    | TInt
    | TSort _
    | TVariant _ -> Success ty

    | TId t ->
        let abbrevTy = Option.get (Map.find t env.Ty)

        match abbrevTy.Value with
        | TSort _
        | TVariant _
        | Subtype _ -> Success ty
        | _ -> unfoldTypeExpr env abbrevTy

    | Function(args, ret) ->
        (NonEmptyList.traverse (unfoldTypeExpr env) args, unfoldTypeExpr env ret)
        ||> Validation.map2 (fun args ret -> Node.Replace(Function(args, ret), ty))

    | Array(index, value) ->
        (unfoldTypeExpr env index, unfoldTypeExpr env value)
        ||> Validation.map2 (fun index value -> Node.Replace(Array(index, value), ty))

    | Generic(indices, value) ->
        (NonEmptyList.traverse (unfoldTypeExpr env) indices, unfoldTypeExpr env value)
        ||> Validation.map2 (fun indices value -> Node.Replace(Generic(indices, value), ty))

    | Subtype(typing, restriction) ->
        let id, baseTy = typing.Value

        (unfoldTypeExpr env baseTy, unfoldValueExpr env restriction)
        ||> Validation.map2 (fun baseTy restriction ->
            let typing = Node.Replace((id, baseTy), typing)
            Node.Replace(Subtype(typing, restriction), ty))

let tryAddAssignmentOrder kind (k, v) (env: Env, ids) =
    (match Map.tryFind k env.Mem with
     | Some v' -> Failure(DList.singleton (DuplicateDefinition(k, kind, Some v')))
     | None -> Success(Map.add k v env.Mem))
    |> Validation.map (fun mem -> { env with Mem = mem }, Node.New(Id k, k.Span) :: ids)

let rec collectAssignments kind (env: Env, ids) (v: Node<ValueExpr>) =
    match v.Value with
    | Infix({ Value = Eq }, ident, value) ->
        match ident.Value with
        | Id id ->
            unfoldValueExpr env value
            |> Validation.bind (fun value -> tryAddAssignmentOrder kind (id, value) (env, ids))

        | GenericApp(id, indices) ->
            (generateGenericId env (id, indices), unfoldValueExpr env value)
            ||> Validation.bind2 (fun newId value ->
                tryAddAssignmentOrder kind (Node.New(newId, ident.Span), value) (env, ids))

        | _ -> Failure(DList.singleton (UnsupportedDefinition(kind, v.Span)))

    | Quantified({ Value = All }, typings, restriction) ->
        replaceInQuantifiedExpr substValueExpr' env [] typings restriction
        |> Validation.bind (List.traverse (fst >> unfoldValueExpr env))
        |> Validation.bind (fun rs ->
            match rs with
            | [] -> Success(env, ids)
            | _ -> List.fold (fun acc r -> Validation.bind (collectAssignments kind /> r) acc) (Success(env, ids)) rs)

    | _ -> Failure(DList.singleton (UnsupportedDefinition(kind, v.Span)))

let collectValueDef (vald: Node<ValueDef>) (valds, env) : MergeResult<List<Node<ValueDef>> * Env, UnfoldingError> =
    match vald.Value with
    | ValueDef.Single(typing, init) ->
        let id, _ = typing.Value

        match init with
        | Some value ->
            match value.Value with
            | Lambda(typings, body) ->
                unfoldValueExpr env body
                |> Validation.map (fun body ->
                    valds, { env with Mem = Map.add id (Node.Replace(Lambda(typings, body), value)) env.Mem })
            | _ ->
                unfoldValueExpr env value
                |> Validation.map (fun value ->
                    Node.Replace(ValueDef.Single(typing, None), vald) :: valds,
                    { env with Mem = Map.add id value env.Mem })

        | None -> Success(vald :: valds, env)

    | ValueDef.Function(signatureId, ty, _, args, body) ->
        let argsTy, _ = ty.Value

        let typings =
            NonEmptyList.map2
                (fun (arg: Node<string>) ty -> Node.New((NonEmptyList.singleton arg, ty), arg.Span))
                args
                argsTy

        unfoldValueExpr env body
        |> Validation.map (fun body ->
            valds, { env with Mem = Map.add signatureId (Node.New(Lambda(typings, body), vald.Span)) env.Mem })

    | ValueDef.Generic(id, typings, ty) ->
        generateGenericIds env id.Value typings
        |> Validation.bind (fun ids ->
            let valEnv =
                NonEmptyList.fold (fun (valEnv: Typings) id -> Map.add (Node.New(id, vald.Span)) ty valEnv) env.Val ids

            Success(vald :: valds, { env with Val = valEnv }))

let collectVariableDef (vard: Node<VariableDef>) (env, ics) : MergeResult<Env * List<Node<ValueExpr>>, UnfoldingError> =
    match vard.Value with
    | Single _ -> Success(env, ics)
    | VariableDef.Generic(id, typings, ty) ->
        generateGenericIds env id.Value typings
        |> Validation.bind (fun ids ->
            let env =
                NonEmptyList.fold
                    (fun env id ->
                        let id = Node.New(id, vard.Span)

                        { env with
                            Val = Map.remove id env.Val
                            Var = Map.add id ty env.Var
                            Mem = Map.remove id env.Mem })
                    env
                    ids

            Success(env, ics))

let collectTsDefs env (acc, tsEnvs) (ts: TransitionSystemDec) =
    let tsEnv = Map.find ts.Id tsEnvs

    let valEnv, valMem =
        Map.fold
            (fun (valEnv: Typings, valMem: Definitions) k _ -> valEnv.Remove k, valMem.Remove k)
            (env.Val, env.Mem)
            tsEnv.Var

    let env' = { env with Val = valEnv; Var = tsEnv.Var; Mem = valMem }

    PersistResult.New(env', List.empty)
    |> List.fold (fun acc vard -> PartialResult.appValidation (collectVariableDef vard) acc)
       /> ts.VariableDefs
    |> List.fold (fun envRes (ic: Node<ValueExpr>) ->
        PartialResult.appValidation (fun (env, ids) -> collectAssignments InitConstraintDef (env, ids) ic) envRes)
       /> ts.InitConstraintDefs
    |> PartialResult.map (fun (env', ids) ->
        let memEnv =
            Map.fold (fun (memEnv: Definitions) k _ -> memEnv.Remove k) env'.Mem env'.Val

        { ts with InitConstraintDefs = List.rev ids } :: acc,
        Map.change ts.Id (Option.map (fun tsEnv -> { tsEnv with TsEnv.Var = env'.Var; TsEnv.Mem = memEnv })) tsEnvs)

let collectDefinitions (spec: Spec) : PersistResult<Spec, UnfoldingError> =
    let envRes =
        PersistResult.New(List.empty, spec.Env)
        |> List.fold (fun acc vald -> PartialResult.appValidation (collectValueDef vald) acc)
           /> spec.Scheme.ValueDefs
        |> List.fold (fun acc (axd: Node<AxiomDef>) ->
            PartialResult.appValidation
                (fun (valds, env) ->
                    collectAssignments AxiomDef (env, []) axd.Value.Axiom
                    |> Validation.map (fst >> tuple2 valds))
                acc)
           /> spec.Scheme.AxiomDefs

    let tsEnvsRes =
        PersistResult.New(List.empty, spec.TsEnvs)
        |> List.fold (fun tsEnvRes ts ->
            PartialResult.apply (fun (acc, tsEnv) -> collectTsDefs (snd envRes.Value) (acc, tsEnv) ts) tsEnvRes)
           /> spec.Scheme.TransitionSystemDecs

    PartialResult.map2
        (fun (valds, env) (tsds, tsEnvs) ->
            { spec with
                Env = env
                TsEnvs = tsEnvs
                Scheme =
                    { spec.Scheme with
                        ValueDefs = valds
                        AxiomDefs = List.empty
                        TransitionSystemDecs = List.rev tsds } })
        envRes
        tsEnvsRes
