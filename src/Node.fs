namespace AST

open FSharpPlus.Data

[<CustomEquality; CustomComparison>]
type Node<'a when 'a: comparison> =
    { Span: Span
      Value: 'a }

    interface System.IComparable with
        member this.CompareTo(other: obj) : int =
            match other with
            | :? Node<'a> as other -> compare this.Value other.Value
            | _ -> -1

    override this.Equals(other: obj) : bool =
        match other with
        | :? Node<'a> as other -> this.Value = other.Value
        | _ -> false

    override this.GetHashCode() : int = hash this.Value

    static member inline New(v: 'a, span: Span) : Node<'a> = { Value = v; Span = span }

    static member inline Replace(v: 'a, node: Node<'a>) : Node<'a> = { node with Value = v }

    static member inline NewBasicNode (span: Span) (kind: Node<'a> -> 'b) (v: 'a) : Node<'b> =
        Node.New(kind (Node.New(v, span)), span)

    static member inline GetValue(node: Node<'a>) : 'a = node.Value
    static member inline CommonSpan(n1: Node<'a>, n2: Node<'b>) : Span = fst n1.Span, snd n2.Span

    static member inline CommonSpan({ Head = n; Tail = ns }: NonEmptyList<Node<'a>>) : Span =
        match List.tryLast ns with
        | Some last -> fst n.Span, snd last.Span
        | None -> n.Span

and Span = uint * uint
