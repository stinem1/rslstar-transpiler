module Program

open FSharp.SystemCommandLine
open System.CommandLine.Help
open System.CommandLine.Invocation
open FSharpPlus

open Diagnostic
open Syntax.Parse
open TypeCheck.Phase2
open Unfold.Phase2
open Syntax.Write

[<EntryPoint>]
let main args =
    let inline (>>=) res f =
        Result.bind (f >> Result.mapError Seq.cast<IDiagnostic>) res

    let showHelp (ctx: InvocationContext) =
        ctx.HelpBuilder.Write(HelpContext(ctx.HelpBuilder, ctx.Parser.Configuration.RootCommand, System.Console.Out))

    rootCommand args {
        description "Typechecks or unfolds an RSL* specification"
        inputs (Input.Context())
        setHandler showHelp

        addCommand (
            command "typecheck" {
                description "Typechecks the provided specification"
                inputs (Input.Argument<string>("specification-path", "The path of the specification to be typechecked"))

                setHandler (fun path ->
                    Ok path
                    >>= parseFile
                    >>= typecheck
                    |> either (fun _ -> 0) (printDiagnostics path))
            }
        )

        addCommand (
            command "unfold" {
                description "Unfolds the provided specification"
                inputs (Input.Argument<string>("specification-path", "The path of the specification to be unfolded"))

                setHandler (fun path ->
                    Ok path
                    >>= parseFile
                    >>= typecheck
                    >>= unfold
                    >>= writeToFileWithKind path "unfolded"
                    |> either (fun _ -> 0) (printDiagnostics path)
                    
                    )
            }
        )
    }
