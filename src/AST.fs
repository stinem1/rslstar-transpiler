namespace AST

open FSharpPlus.Data

type Spec = { Env: Env; TsEnvs: Map<Node<string>, TsEnv>; Scheme: Scheme }

and Env =
    { Ty: Types
      Val: Typings
      Var: Typings
      Mem: Definitions }

and TsEnv = { Var: Typings; Mem: Definitions }

and Types = Map<Node<string>, Option<Node<TypeExpr>>>

and Typings = Map<Node<string>, Node<TypeExpr>>

and Definitions = Map<Node<string>, Node<ValueExpr>>

and Scheme =
    { Id: Node<string>
      TypeDefs: List<Node<TypeDef>>
      ValueDefs: List<Node<ValueDef>>
      AxiomDefs: List<Node<AxiomDef>>
      TransitionSystemDecs: List<TransitionSystemDec>
      LTLAssertionDefs: List<Node<LTLAssertionDef>> }

and TypeDef =
    | Sort of id: Node<string>
    | Variant of id: Node<string> * cases: NonEmptyList<Node<string>>
    | Abbreviation of id: Node<string> * ty: Node<TypeExpr>

and ValueDef =
    | Single of typing: Node<SingleTyping> * init: Option<Node<ValueExpr>>
    | Function of
        signatureId: Node<string> *
        ty: Node<FunctionType> *
        formalId: Node<string> *
        args: NonEmptyList<Node<string>> *
        body: Node<ValueExpr>
    | Generic of id: Node<string> * typings: NonEmptyList<Node<SingleTyping>> * ty: Node<TypeExpr>

and AxiomDef = { Name: Option<Node<string>>; Axiom: Node<ValueExpr> }

and TransitionSystemDec =
    { Id: Node<string>
      VariableDefs: List<Node<VariableDef>>
      InitConstraintDefs: List<Node<ValueExpr>>
      TransitionRuleDefs: List<Node<RuleExpr>> }

and VariableDef =
    | Single of typing: Node<SingleTyping>
    | Generic of id: Node<string> * typings: NonEmptyList<Node<SingleTyping>> * ty: Node<TypeExpr>

and LTLAssertionDef = { Name: Node<string>; TransitionSystem: Node<string>; Assertion: Node<ValueExpr> }

and TypeExpr =
    | TBool
    | TInt
    | TSort of Node<string>
    | TVariant of Node<string> * NonEmptyList<Node<string>>
    | TId of Node<string>
    | Function of FunctionType
    | Array of index: Node<TypeExpr> * value: Node<TypeExpr>
    | Generic of indices: NonEmptyList<Node<TypeExpr>> * value: Node<TypeExpr>
    | Subtype of typing: Node<SingleTyping> * restriction: Node<ValueExpr>
    | Bot

and ValueExpr =
    | Bool of value: Node<bool>
    | Int of value: Node<int>
    | Id of value: Node<string>
    | Disambiguation of value: Node<ValueExpr> * ty: Node<TypeExpr>
    | EnumeratedArray of content: List<Node<ValueExpr>>
    | FunctionApp of value: Node<ValueExpr> * args: NonEmptyList<Node<ValueExpr>>
    | ArrayApp of value: Node<ValueExpr> * indices: NonEmptyList<Node<ValueExpr>>
    | GenericApp of id: Node<string> * indices: NonEmptyList<Node<ValueExpr>>
    | Lambda of typings: NonEmptyList<Node<Typing>> * body: Node<ValueExpr>
    | Quantified of quantifier: Node<Quantifier> * typings: NonEmptyList<Node<Typing>> * restriction: Node<ValueExpr>
    | Infix of op: Node<InfixOp> * lhs: Node<ValueExpr> * rhs: Node<ValueExpr>
    | Prefix of op: Node<PrefixOp> * expr: Node<ValueExpr>
    | Let of id: Node<string> * init: Node<ValueExpr> * body: Node<ValueExpr>
    | If of cond: Node<ValueExpr> * ifTrue: Node<ValueExpr> * ifFalse: Node<ValueExpr>

and RuleExpr =
    | GuardedCommand of id: Option<Node<string>> * guard: Node<ValueExpr> * effects: NonEmptyList<Node<ValueExpr>>
    | QuantifiedRule of typings: NonEmptyList<Node<Typing>> * rule: Node<RuleExpr>
    | Choice of op: Node<ChoiceOp> * lhs: Node<RuleExpr> * rhs: Node<RuleExpr>

and FunctionType = NonEmptyList<Node<TypeExpr>> * Node<TypeExpr> // Needed due to constrained type expressions
and Typing = NonEmptyList<Node<string>> * Node<TypeExpr>
and SingleTyping = Node<string> * Node<TypeExpr>

and Quantifier =
    | All
    | Exists

and InfixOp =
    | Imp
    | Or
    | And
    | Until
    | Eq
    | Neq
    | Ge
    | Le
    | Geq
    | Leq
    | Add
    | Sub
    | Mod
    | Mul
    | Div

and PrefixOp =
    | Pos
    | Neg
    | Not
    | Global
    | Finally
    | Next

and ChoiceOp =
    | NonDeterministic
    | Priority
