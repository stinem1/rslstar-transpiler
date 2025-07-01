module ASTUtil

open FSharpPlus
open FSharpPlus.Data
open AST
open Syntax.Unparse
open System.Collections.Generic

let normalizeId (id: Node<string>) =
    if id.Value.EndsWith ''' then
        Node.Replace(id.Value.Substring(0, id.Value.Length - 1), id)
    else
        id

let toSingleTypings (typings: NonEmptyList<Node<Typing>>) =
    typings
    >>= fun typing ->
        let ids, ty = typing.Value

        NonEmptyList.zip ids (NonEmptyList.replicate (NonEmptyList.length ids) ty)
        |> NonEmptyList.map (fun single -> Node.New(single, typing.Span))

let mutable globalIds = HashSet<string>()

let freshId =
    let mutable n = 0u

    fun (id: string) ->
        if globalIds.Add id then
            id
        else
            let freshId = $"@{id}{n}"
            n <- n + 1u
            globalIds.Add freshId |> ignore
            freshId
let rec freeIds (v: Node<ValueExpr>) =
    match v.Value with
    | Bool _
    | Int _ -> Set.empty
    | Id x -> Set.singleton x

    | Disambiguation(value, _) -> freeIds value
    | EnumeratedArray content -> freeIdsSeq content
    | GenericApp(id, values) -> Set.add id (freeIdsSeq values)
    | FunctionApp(value, args)
    | ArrayApp(value, args) -> Set.union (freeIds value) (freeIdsSeq args)
    | Lambda(typings, expr)
    | Quantified(_, typings, expr) ->
        let ids = Set.ofSeq (typings >>= (Node.GetValue >> fst))
        Set.difference (freeIds expr) ids
    | Infix(_, lhs, rhs) -> Set.union (freeIds lhs) (freeIds rhs)
    | Prefix(_, expr) -> freeIds expr
    | Let(id, init, body) -> Set.union (freeIds init) (Set.remove id (freeIds body))
    | If(cond, ifTrue, ifFalse) -> Set.union (Set.union (freeIds cond) (freeIds ifTrue)) (freeIds ifFalse)

and freeIdsSeq (vs: seq<Node<ValueExpr>>) =
    Seq.fold (fun acc v -> Set.union acc (freeIds v)) Set.empty vs

let substTyping (x: Node<string>, y: Node<string>) typings =
    NonEmptyList.map
        (fun (typing: Node<Typing>) ->
            let ids, ty = typing.Value
            let ids = NonEmptyList.map (fun id -> if id = x then y else id) ids
            Node.Replace((ids, ty), typing))
        typings

let substBindings (subst: bool -> Node<string> * Node<ValueExpr> -> 'a -> 'a) (x, v') (expr: 'a) typings =

    let ids = Set.ofSeq (typings >>= (Node.GetValue >> fst))

    if Set.contains x ids then
        expr, typings
    else
        let clashingIds = Set.intersect (freeIds v') ids

        Set.fold
            (fun (expr, typings) (id: Node<string>) ->
                let freshId = Node.New(freshId id.Value, id.Span)
                let freshValue = Node.New(Id freshId, id.Span)

                subst true (id, freshValue) expr, substTyping (id, freshId) typings)
            (expr, typings)
            clashingIds
        |> mapItem1 (subst false (x, v'))

let rec substValueExpr' isFresh (x, v') (v: Node<ValueExpr>) =
    match v.Value with
    | Id id when id = x -> v'
    | Bool _
    | Int _
    | Id _ -> v

    | Disambiguation(value, ty) ->
        let value = substValueExpr' isFresh (x, v') value
        Node.Replace(Disambiguation(value, ty), v)

    | EnumeratedArray content ->
        let content = List.map (substValueExpr' isFresh (x, v')) content
        Node.Replace(EnumeratedArray content, v)

    | FunctionApp(value, args) ->
        let value = substValueExpr' isFresh (x, v') value
        let args = NonEmptyList.map (substValueExpr' isFresh (x, v')) args
        Node.Replace(FunctionApp(value, args), v)

    | ArrayApp(value, indices) ->
        let value = substValueExpr' isFresh (x, v') value
        let indices = NonEmptyList.map (substValueExpr' isFresh (x, v')) indices
        Node.Replace(ArrayApp(value, indices), v)

    | GenericApp(id, indices) ->
        let idNode = substValueExpr' isFresh (x, v') (Node.New(Id id, id.Span))

        let id =
            match idNode.Value with
            | Id id -> id
            | _ ->
                failwith
                    $"BUG: Expected an id when substituting '{id.Value}'
                    with '{unparseValueExpr v'.Value}'.
                    The typechecker should ensure generic identifiers are only shadowed."

        let indices = NonEmptyList.map (substValueExpr' isFresh (x, v')) indices
        Node.Replace(GenericApp(id, indices), v)

    | Lambda(typings, body) ->
        let body, typings = substBindings substValueExpr' (x, v') body typings
        Node.Replace(Lambda(typings, body), v)

    | Quantified(q, typings, restriction) ->
        let restriction, typings = substBindings substValueExpr' (x, v') restriction typings
        Node.Replace(Quantified(q, typings, restriction), v)

    | Infix(op, lhs, rhs) ->
        let lhs = substValueExpr' isFresh (x, v') lhs
        let rhs = substValueExpr' isFresh (x, v') rhs
        Node.Replace(Infix(op, lhs, rhs), v)

    | Prefix(op, expr) ->
        let expr = substValueExpr' isFresh (x, v') expr
        Node.Replace(Prefix(op, expr), v)

    | Let(id, init, body) when id = x ->
        let init = substValueExpr' isFresh (x, v') init
        Node.Replace(Let(id, init, body), v)

    | Let(id, init, body) ->
        let init = substValueExpr' isFresh (x, v') init
        let body = substValueExpr' isFresh (x, v') body
        Node.Replace(Let(id, init, body), v)

    | If(cond, ifTrue, ifFalse) ->
        let cond = substValueExpr' isFresh (x, v') cond
        let ifTrue = substValueExpr' isFresh (x, v') ifTrue
        let ifFalse = substValueExpr' isFresh (x, v') ifFalse
        Node.Replace(If(cond, ifTrue, ifFalse), v)

let inline substValueExpr (x, v') (v: Node<ValueExpr>) = substValueExpr' false (x, v') v

let rec substRuleExpr' isFresh (x, v': Node<ValueExpr>) (r: Node<RuleExpr>) =
    match r.Value with
    | GuardedCommand(optId, guard, effects) ->
        // Currently it does not consider if the identifier is unused
        // which could make the expression distinct and yield the same rule with different names
        let optId =
            Option.map
                (fun (id: Node<string>) ->
                    let valueStr =
                        match isFresh, v'.Value with
                        | false, Bool b -> Some(toLower (string b.Value))
                        | false, Int i -> Some(string i.Value)
                        | false, Id id ->
                            let freeIds = Set.union (freeIds guard) (freeIdsSeq effects)
                            if Set.contains x freeIds then Some id.Value else None
                        | _ -> None

                    match valueStr with
                    | Some s -> Node.Replace($"{id.Value}_{s}", id)
                    | None -> id)
                optId

        let guard = substValueExpr' isFresh (x, v') guard
        let effects = NonEmptyList.map (substValueExpr' isFresh (x, v')) effects
        Node.Replace(GuardedCommand(optId, guard, effects), r)

    | QuantifiedRule(typings, rule) ->
        let rule, typings = substBindings substRuleExpr' (x, v') rule typings
        Node.Replace(QuantifiedRule(typings, rule), r)

    | Choice(op, lhs, rhs) ->
        let lhs = substRuleExpr' isFresh (x, v') lhs
        let rhs = substRuleExpr' isFresh (x, v') rhs
        Node.Replace(Choice(op, lhs, rhs), r)

let inline substRuleExpr (x, v') (r: Node<RuleExpr>) = substRuleExpr' false (x, v') r
