namespace Helpers

open FSharpPlus.Data

type MergeResult<'a, 'b> = Validation<DList<'b>, 'a>

type PersistResult<'a, 'b> =
    { Value: 'a
      Errors: DList<'b> }

    static member inline New(v: 'a) : PersistResult<'a, 'b> = { Value = v; Errors = DList.empty }

    static member inline Replace (v: 'a) (res: PersistResult<'c, 'b>) : PersistResult<'a, 'b> =
        { Value = v; Errors = res.Errors }

    static member inline AddErrors (es: DList<'b>) (res: PersistResult<'a, 'b>) : PersistResult<'a, 'b> =
        { res with Errors = DList.append es res.Errors }

    static member inline (<<*)(res: PersistResult<'a, 'b>, inp: PersistResult<'c, 'b>) : PersistResult<'a, 'b> =
        PersistResult.AddErrors inp.Errors res

    static member inline (<<*)(res: PersistResult<'a, 'b>, inp: Result<'c, DList<'b>>) : PersistResult<'a, 'b> =
        match inp with
        | Ok _ -> res
        | Error es -> PersistResult.AddErrors es res

    static member inline (<<*)(res: PersistResult<'a, 'b>, inp: Validation<DList<'b>, _>) : PersistResult<'a, 'b> =
        match inp with
        | Success _ -> res
        | Failure es -> PersistResult.AddErrors es res

[<RequireQualifiedAccess>]
module PartialResult =
    let inline apply (f: 'a -> PersistResult<'c, 'b>) (res: PersistResult<'a, 'b>) : PersistResult<'c, 'b> =
        PersistResult.AddErrors res.Errors (f res.Value)

    let inline appResult (f: 'a -> Result<'a, DList<'b>>) (res: PersistResult<'a, 'b>) : PersistResult<'a, 'b> =
        match f res.Value with
        | Ok v -> PersistResult.Replace v res
        | Error es -> PersistResult.AddErrors es res

    let inline appValidation (f: 'a -> Validation<DList<'b>, 'a>) (res: PersistResult<'a, 'b>) : PersistResult<'a, 'b> =
        match f res.Value with
        | Success x -> PersistResult.Replace x res
        | Failure es -> PersistResult.AddErrors es res

    let inline map (f: 'a -> 'c) (res: PersistResult<'a, 'b>) : PersistResult<'c, 'b> =
        PersistResult.Replace (f res.Value) res

    let inline map2
        (f: 'a -> 'c -> 'd)
        (res1: PersistResult<'a, 'b>)
        (res2: PersistResult<'c, 'b>)
        : PersistResult<'d, 'b> =
        PersistResult.Replace (f res1.Value res2.Value) (PersistResult.AddErrors res1.Errors res2)

    let inline toValidation (res: PersistResult<'a, 'b>) : Validation<DList<'b>, 'a> =
        if res.Errors.IsEmpty then
            Success res.Value
        else
            Failure res.Errors

[<RequireQualifiedAccess>]
module Option =
    let inline appOption (f: 'a -> 'a -> 'a) (x: Option<'a>) (y: Option<'a>) =
        match x, y with
        | Some x, Some y -> Some(f x y)
        | Some expr, None
        | None, Some expr -> Some expr
        | None, None -> None

[<RequireQualifiedAccess>]
module Validation =

    open FSharpPlus

    let inline bind2 f x y : Validation<'Error, 'V> =
        match (x: Validation<'Error, 'T>), (y: Validation<'Error, 'U>) with
        | Success x, Success y -> f x y
        | Failure e1, Failure e2 -> Failure(plus e1 e2)
        | Failure e, Success _
        | Success _, Failure e -> Failure e

    let inline map4 f x y z w : Validation<'Error, 'W> =
        match
            (x: Validation<'Error, 'T>),
            (y: Validation<'Error, 'U>),
            (z: Validation<'Error, 'V>),
            (w: Validation<'Error, 'Q>)
        with
        | Success x, Success y, Success z, Success w -> Success(f x y z w)

        | Failure e1, Failure e2, Failure e3, Failure e4 -> Failure(e1 ++ e2 ++ e3 ++ e4)

        | Failure e, Success _, Success _, Success _
        | Success _, Failure e, Success _, Success _
        | Success _, Success _, Failure e, Success _
        | Success _, Success _, Success _, Failure e -> Failure e

        | Failure e1, Failure e2, Success _, Success _
        | Failure e1, Success _, Failure e2, Success _
        | Failure e1, Success _, Success _, Failure e2
        | Success _, Failure e1, Failure e2, Success _
        | Success _, Failure e1, Success _, Failure e2
        | Success _, Success _, Failure e1, Failure e2 -> Failure(plus e1 e2)

        | Failure e1, Failure e2, Failure e3, Success _
        | Failure e1, Failure e2, Success _, Failure e3
        | Failure e1, Success _, Failure e2, Failure e3
        | Success _, Failure e1, Failure e2, Failure e3 -> Failure(e1 ++ e2 ++ e3)
