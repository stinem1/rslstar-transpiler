module Syntax.Unparse

open System.Collections.Generic
open System.Text
open FSharpPlus
open AST

let commaSep = ", "

let inline toLower (s: string) = s.ToLower()

let inline concatNodeSeq sep f xs =
    String.concat sep (Seq.map (Node.GetValue >> f) xs)

let unparseQuantifier (q: Quantifier) =
    match q with
    | All -> "all"
    | Exists -> "exists"

let unparseInfixOp (iOp: InfixOp) =
    match iOp with
    | Imp -> "=>"
    | Or -> "\\/"
    | And -> "/\\"
    | Until -> "U"
    | Eq -> "="
    | Neq -> "~="
    | Ge -> ">"
    | Le -> "<"
    | Geq -> ">="
    | Leq -> "<="
    | Add -> "+"
    | Sub -> "-"
    | Mod -> "\\"
    | Mul -> "*"
    | Div -> "/"

let unparsePrefixOp (pOp: PrefixOp) =
    match pOp with
    | Pos -> "+"
    | Neg -> "-"
    | Not -> "~"
    | Global -> "G"
    | Finally -> "F"
    | Next -> "X"

let unparseChoiceOp (cOp: ChoiceOp) =
    match cOp with
    | NonDeterministic -> "[=]"
    | Priority -> "[>]"

type Expr =
    | String of string
    | Type of TypeExpr
    | Value of resetPar: bool * ValueExpr
    | Rule of resetPar: bool * RuleExpr
    | Typing of Typing

let inline addSep (kind: 'a -> Expr) (sep: string) ns (stack: Stack<Expr>) =
    let nsArr = Seq.toArray ns

    for i = nsArr.Length - 1 downto 0 do
        stack.Push(kind (Node.GetValue nsArr[i]))

        if i > 0 then
            stack.Push(String sep)

let inline addPar ([<InlineIfLambda>] f: unit -> unit) (resetPar: bool) (stack: Stack<Expr>) =
    let needsPar = stack.Count <> 0 && not resetPar

    if needsPar then
        stack.Push(String ")")

    f ()

    if needsPar then
        stack.Push(String "(")

let inline unparseExpr' ([<InlineIfLambda>] f: string -> unit) (expr: Expr) =
    let stack = Stack<Expr>(seq { expr })

    while stack.Count > 0 do
        match stack.Pop() with
        | String s -> f s

        | Type ty ->
            match ty with
            | Bot -> f "Any"
            | TBool -> f "Bool"
            | TInt -> f "Int"
            | TId id
            | TSort id -> f id.Value
            | TVariant(vid, cases) ->
                f $"{vid.Value} == "
                addSep String " | " cases stack

            | Function(args, ret) ->
                stack.Push(Type ret.Value)
                stack.Push(String " -> ")
                addSep Type " >< " args stack

            | Generic(indices, ty) ->
                stack.Push(Type ty.Value)
                stack.Push(String " of ")
                addSep Type commaSep indices stack
                stack.Push(String "generic ")

            | Array(index, value) ->
                stack.Push(Type value.Value)
                stack.Push(String " of ")
                stack.Push(Type index.Value)
                stack.Push(String "array ")

            | Subtype(typing, restriction) ->
                let id, ty = typing.Value

                stack.Push(String " |}")
                stack.Push(Value(true, restriction.Value))
                stack.Push(String " :- ")
                stack.Push(Type ty.Value)
                stack.Push(String $"{{| {id.Value} : ")

        | Value(resetPar, v) ->
            match v with
            | Bool b -> f (toLower (string b.Value))
            | Int i -> f (string i.Value)
            | Id id -> f id.Value

            | Disambiguation(value, ty) ->
                stack.Push(String ")")
                stack.Push(Type ty.Value)
                stack.Push(String " : ")
                stack.Push(Value(true, value.Value))
                stack.Push(String "(")

            | EnumeratedArray content ->
                stack.Push(String ".}")
                addSep (tuple2 true >> Value) commaSep content stack
                stack.Push(String "{.")

            | FunctionApp(value, args) ->
                stack.Push(String ")")
                addSep (tuple2 true >> Value) commaSep args stack
                stack.Push(String "(")
                stack.Push(Value(false, value.Value))

            | ArrayApp(value, indices) ->
                let idxArr = Seq.toArray indices

                for i = idxArr.Length - 1 downto 0 do
                    stack.Push(String "]")
                    stack.Push(Value(true, Node.GetValue idxArr[i]))
                    stack.Push(String "[")

                stack.Push(Value(false, value.Value))

            | GenericApp(id, indices) ->
                stack.Push(String ".]")
                addSep (tuple2 true >> Value) commaSep indices stack
                stack.Push(String $"{id.Value}[.")

            | Lambda(typings, body) ->
                stack.Push(String ")")
                stack.Push(Value(true, body.Value))
                stack.Push(String " :-\n    ")
                addSep Typing commaSep typings stack
                stack.Push(String "-\\ ")
                stack.Push(String "(")

            | Quantified(q, typings, restriction) ->
                stack.Push(String ")")
                stack.Push(Value(true, restriction.Value))
                stack.Push(String " :-\n    ")
                addSep Typing commaSep typings stack
                stack.Push(String $"{unparseQuantifier q.Value} ")
                stack.Push(String "(")

            | Infix(op, lhs, rhs) ->
                addPar
                    (fun _ ->
                        stack.Push(Value(false, rhs.Value))
                        stack.Push(String $" {unparseInfixOp op.Value} ")
                        stack.Push(Value(false, lhs.Value)))
                    resetPar
                    stack

            | Prefix(op, expr) ->
                let noOuterParen = stack.Count = 0 || resetPar

                addPar
                    (fun _ ->
                        if noOuterParen then
                            stack.Push(String ")")

                        stack.Push(Value(false, expr.Value))

                        if noOuterParen then
                            stack.Push(String "(")

                        stack.Push(String $"{unparsePrefixOp op.Value} "))
                    resetPar
                    stack

            | Let(id, init, body) ->
                stack.Push(String "\nend")
                stack.Push(Value(true, body.Value))
                stack.Push(String " in\n    ")
                stack.Push(Value(true, init.Value))
                stack.Push(String $"let {id.Value} = ")

            | If(cond, ifTrue, ifFalse) ->
                stack.Push(String "\nend")
                stack.Push(Value(true, ifFalse.Value))
                stack.Push(String "\nelse\n    ")
                stack.Push(Value(true, ifTrue.Value))
                stack.Push(String " then\n    ")
                stack.Push(Value(true, cond.Value))
                stack.Push(String "if ")

        | Rule(resetPar, r) ->
            match r with
            | GuardedCommand(id, guard, effects) ->
                addSep (tuple2 true >> Value) ",\n" effects stack
                stack.Push(String "\n==>\n")
                stack.Push(Value(true, guard.Value))

                match id with
                | Some id -> stack.Push(String $"[{id.Value}]\n")
                | None -> ()

            | QuantifiedRule(typings, rule) ->
                stack.Push(String ")")
                stack.Push(Rule(true, rule.Value))
                stack.Push(String " :-\n    ")
                addSep Typing commaSep typings stack
                stack.Push(String $"{unparseChoiceOp NonDeterministic} ")
                stack.Push(String "(")

            | Choice(op, lhs, rhs) ->
                addPar
                    (fun _ ->
                        let isNonDeterministic = op.Value = NonDeterministic
                        stack.Push(Rule(isNonDeterministic, rhs.Value))
                        stack.Push(String $"\n{unparseChoiceOp op.Value}\n")
                        stack.Push(Rule(isNonDeterministic, lhs.Value)))
                    resetPar
                    stack

        | Typing typing ->
            let ids, ty = typing
            stack.Push(Type ty.Value)
            stack.Push(String " : ")
            addSep String commaSep ids stack

let unparseExpr (e: Expr) =
    let sb = StringBuilder()
    unparseExpr' (fun s -> sb.Append s |> ignore) e
    sb.ToString()

let inline unparseTypeExpr (ty: TypeExpr) = unparseExpr (Type ty)
let inline unparseValueExpr (v: ValueExpr) = unparseExpr (Value(true, v))
let inline unparseRuleExpr (r: RuleExpr) = unparseExpr (Rule(true, r))

let unparseSingleTyping (typing: SingleTyping) =
    let id, ty = typing in $"{id.Value} : {unparseTypeExpr ty.Value}"

let unparseTypeDef (td: TypeDef) =
    match td with
    | Sort id -> id.Value
    | Variant(id, cases) -> unparseTypeExpr (TVariant(id, cases))
    | Abbreviation(id, ty) -> $"{id.Value} = {unparseTypeExpr ty.Value}"

let inline unparseGeneric (id: Node<string>) typings (ty: Node<TypeExpr>) =
    $"{id.Value} [{concatNodeSeq commaSep unparseSingleTyping typings}] : {unparseTypeExpr ty.Value}"

let unparseValueDef (vald: ValueDef) =
    match vald with
    | ValueDef.Single(typing, init) ->
        let optInit =
            match init with
            | Some v -> $" = {unparseValueExpr v.Value}"
            | None -> ""

        $"{unparseSingleTyping typing.Value}{optInit}"

    | ValueDef.Function(signatureId, ty, formalId, args, body) ->
        String.concat
            "\n"
            [ $"{signatureId.Value} : {unparseTypeExpr (Function ty.Value)}"
              $"{formalId.Value}({concatNodeSeq commaSep id args}) is"
              $"    {unparseValueExpr body.Value}" ]

    | ValueDef.Generic(id, typings, ty) -> unparseGeneric id typings ty

let unparseAxiomDef (axd: AxiomDef) =
    let optId =
        match axd.Name with
        | Some id -> $"[{id.Value}] "
        | None -> ""

    $"{optId}{unparseValueExpr axd.Axiom.Value}"

let unparseVariableDef (vard: VariableDef) =
    match vard with
    | Single typing -> unparseSingleTyping typing.Value
    | VariableDef.Generic(id, typings, ty) -> unparseGeneric id typings ty

let unparseLTLAssertionDef (ad: LTLAssertionDef) =
    $"[{ad.Name.Value}] {ad.TransitionSystem.Value} |- {unparseValueExpr ad.Assertion.Value}"

let unparseDefs (sb: StringBuilder) (title: string) (sep: string) (f: 'a -> string) defs =
    match defs with
    | [] -> ()
    | _ ->
        sb.Append $"{title}\n" |> ignore

        for i in 0 .. defs.Length - 1 do

            sb.Append(f (Node.GetValue defs[i])) |> ignore

            if i < defs.Length - 1 then
                sb.Append $"{sep}\n" |> ignore
            else
                sb.Append "\n" |> ignore

        sb.Append "\n" |> ignore

let unparseScheme (scheme: Scheme) : string =
    let sb = StringBuilder()
    sb.Append $"scheme {scheme.Id.Value} = class\n" |> ignore

    unparseDefs sb "type" ",\n" unparseTypeDef scheme.TypeDefs
    unparseDefs sb "value" ",\n" unparseValueDef scheme.ValueDefs
    unparseDefs sb "axiom" ",\n" unparseAxiomDef scheme.AxiomDefs

    match scheme.TransitionSystemDecs with
    | [] -> ()
    | _ ->
        for tsd in scheme.TransitionSystemDecs do
            sb.Append $"transition_system [{tsd.Id.Value}]\n" |> ignore

            unparseDefs sb "variable" ",\n" unparseVariableDef tsd.VariableDefs
            unparseDefs sb "init_constraint" ",\n" unparseValueExpr tsd.InitConstraintDefs
            unparseDefs sb "transition_rules" " [=]\n" unparseRuleExpr tsd.TransitionRuleDefs

            sb.Append "end\n" |> ignore

    unparseDefs sb "ltl_assertion" ",\n" unparseLTLAssertionDef scheme.LTLAssertionDefs

    sb.Append "end\n" |> ignore
    sb.ToString()
