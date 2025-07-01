module Diagnostic

open System
open System.IO
open FSharpPlus

type IDiagnostic =
    abstract Name: string
    abstract Label: string * Option<uint * uint>
    abstract Help: Option<string>

let writeWithColor color (text: string) =
    Console.ForegroundColor <- color
    Console.Write text
    Console.ResetColor()

let findFilePositions (path: string) errors =
    let offsets =
        ResizeArray<int * uint>(Seq.choosei (fun i (_, offset) -> Option.map (tuple2 i) offset) errors)

    let found = Array.create offsets.Count (0u, 0u)
    let mutable currentLine: uint = 1u

    using (new StreamReader(path)) (fun sr ->

        while not sr.EndOfStream do
            let line = sr.ReadLine()
            let lineLength = uint line.Length + 1u

            for i = offsets.Count - 1 downto 0 do
                let idx, offset = offsets[i]

                if offset > lineLength then
                    offsets[i] <- idx, offset - lineLength
                else
                    found[idx] <- currentLine, offset
                    offsets.RemoveAt i

            currentLine <- currentLine + 1u)

    for i = 0 to offsets.Count - 1 do
        let idx, offset = offsets[i]
        found[idx] <- currentLine - 1u, offset

    Seq.foldBack
        (fun (e, offset) (idx, acc) ->
            match offset with
            | Some _ -> idx - 1, (e, Some found[idx]) :: acc
            | None -> idx, (e, None) :: acc)
        errors
        (found.Length - 1, [])
    |> snd

let writeParagraph (leftPadding: string) text =
    Seq.chunkBySize (Console.WindowWidth - leftPadding.Length * 2) text
    |> Seq.iteri (fun i (line: char array) ->
        let padding = if i = 0 then "" else leftPadding
        Console.Write(String.Concat(padding, line, Environment.NewLine)))

let writeError path (name: string) (label, filePos) =
    writeWithColor ConsoleColor.Red $"\u00D7 "

    match filePos with
    | Some(ln, col) ->
        Console.Write $"{name} ("
        let relativePath = Path.GetRelativePath(Directory.GetCurrentDirectory(), path)
        writeWithColor ConsoleColor.Cyan $"\x1B[4m{relativePath}:{ln}:{col}"
        Console.WriteLine ")"

    | None -> Console.WriteLine name

    let arrow = "\u2570\u2500\u25B6 "
    writeWithColor ConsoleColor.Red arrow
    writeParagraph (String.replicate arrow.Length " ") label

let writeHelp help =
    match help with
    | Some msg ->
        Console.WriteLine()
        let title = "help: "
        writeWithColor ConsoleColor.DarkCyan title
        writeParagraph (String.replicate title.Length " ") msg

    | None -> ()

let printDiagnostic path (error: IDiagnostic) filePos =
    writeError path error.Name (fst error.Label, filePos)
    writeHelp error.Help
    Console.WriteLine()

let printDiagnostics path errors =
    Console.OutputEncoding <- Text.Encoding.Unicode

    let sortedErrors =
        Seq.map (fun (error: IDiagnostic) -> error, Option.map snd (snd error.Label)) errors
        |> Seq.sortBy snd

    if Seq.forall (snd >> Option.isNone) sortedErrors then
        Seq.iter (fun (error: IDiagnostic, _) -> printDiagnostic path error None) sortedErrors
    else
        findFilePositions path sortedErrors
        |> Seq.iter (fun (error: IDiagnostic, filePos) -> printDiagnostic path error filePos)

    1
