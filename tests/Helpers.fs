module Helpers

open System.IO
open Syntax
open TypeCheck.Phase2
open Expecto
open Unfold.Phase2

let getFilesInTestDirs (pathsList: string[][]) =
    pathsList
    |> Array.collect (fun paths ->
        let dir = Array.append [| __SOURCE_DIRECTORY__; "Specs" |] paths |> Path.Combine

        Directory.EnumerateFiles(dir, "*.rsl", SearchOption.AllDirectories)
        |> Array.ofSeq)
    |> Array.sort
    |> List.ofArray


let typecheckCheck (path: string) f =
    match Parse.parseFile path with
    | Ok input -> f (typecheck input)
    | Error errs -> failtestf "Parsing failed with errors: %A" errs

let unfoldCheck (path: string) f =
    match Parse.parseFile path with
    | Ok input ->
        match typecheck input with
        | Ok spec -> f (unfold spec)
        | Error errs -> failtestf "Typecheck failed with errors: %A" errs
    | Error errs -> failtestf "Parsing failed with errors: %A" errs

let countByTag f errors =
    List.map f errors |> List.countBy id |> Map.ofList