module Syntax.Write

open System
open System.IO
open FSharpPlus.Data

open AST
open Unparse
open Error

let writeExpr (sw: StreamWriter) (e: Expr) = unparseExpr' (fun s -> sw.Write s) e

let inline writeTypeExpr (sw: StreamWriter) (ty: TypeExpr) = writeExpr sw (Type ty)
let inline writeValueExpr (sw: StreamWriter) (v: ValueExpr) = writeExpr sw (Value(true, v))
let inline writeRuleExpr (sw: StreamWriter) (r: RuleExpr) = writeExpr sw (Rule(true, r))

let writeSingleTyping (sw: StreamWriter) (typing: SingleTyping) =
    let id, ty = typing in
    sw.Write $"{id.Value} : "
    writeTypeExpr sw ty.Value

let writeTypeDef (sw: StreamWriter) (td: TypeDef) =
    match td with
    | Sort id -> sw.Write id.Value
    | Variant(id, cases) -> writeTypeExpr sw (TVariant(id, cases))
    | Abbreviation(id, ty) ->
        sw.Write $"{id.Value} = "
        writeTypeExpr sw ty.Value

let writeGeneric
    (sw: StreamWriter)
    (id: Node<string>)
    (typings: NonEmptyList<Node<SingleTyping>>)
    (ty: Node<TypeExpr>)
    =
    sw.Write $"{id.Value} ["

    Seq.iteri
        (fun i typing ->
            writeSingleTyping sw typing.Value
            if i < typings.Length - 1 then sw.Write commaSep else ())
        typings

    sw.Write "] : "
    writeTypeExpr sw ty.Value

let writeValueDef (sw: StreamWriter) (vald: ValueDef) =
    match vald with
    | ValueDef.Single(typing, init) ->
        writeSingleTyping sw typing.Value

        match init with
        | Some v ->
            sw.Write $" = "
            writeValueExpr sw v.Value
        | None -> ()

    | ValueDef.Function(signatureId, ty, formalId, args, body) ->
        sw.Write $"{signatureId.Value} : "
        writeTypeExpr sw (Function ty.Value)
        sw.Write $"\n{formalId.Value}("

        Seq.iteri
            (fun i (arg: Node<string>) ->
                sw.Write(Node.GetValue arg)
                if i < args.Length - 1 then sw.Write commaSep else ())
            args

        sw.Write ") is\n    "
        writeValueExpr sw body.Value

    | ValueDef.Generic(id, typings, ty) -> writeGeneric sw id typings ty

let writeAxiomDef (sw: StreamWriter) (axd: AxiomDef) =
    match axd.Name with
    | Some id -> sw.Write $"[{id.Value}] "
    | None -> ()

    writeValueExpr sw axd.Axiom.Value

let writeVariableDef (sw: StreamWriter) (vard: VariableDef) =
    match vard with
    | Single typing -> writeSingleTyping sw typing.Value
    | VariableDef.Generic(id, typings, ty) -> writeGeneric sw id typings ty

let writeLTLAssertionDef (sw: StreamWriter) (ad: LTLAssertionDef) =
    sw.Write $"[{ad.Name.Value}] {ad.TransitionSystem.Value} |- "
    writeValueExpr sw ad.Assertion.Value

let writeDefs (sw: StreamWriter) (title: string) (sep: string) (f: StreamWriter -> 'a -> unit) defs =
    match defs with
    | [] -> ()
    | _ ->
        sw.WriteLine title

        for i in 0 .. defs.Length - 1 do

            f sw (Node.GetValue defs[i])

            if i < defs.Length - 1 then
                sw.WriteLine sep
            else
                sw.WriteLine ""

        sw.WriteLine()

let writeToFile path (scheme: Scheme) : Result<unit, SyntaxError list> =
    try
        use sw = File.CreateText path

        sw.WriteLine $"scheme {scheme.Id.Value} = class"

        writeDefs sw "type" ",\n" writeTypeDef scheme.TypeDefs
        writeDefs sw "value" ",\n" writeValueDef scheme.ValueDefs
        writeDefs sw "axiom" ",\n" writeAxiomDef scheme.AxiomDefs

        match scheme.TransitionSystemDecs with
        | [] -> ()
        | _ ->
            for tsd in scheme.TransitionSystemDecs do
                sw.WriteLine $"transition_system [{tsd.Id.Value}]"

                writeDefs sw "variable" ",\n" writeVariableDef tsd.VariableDefs
                writeDefs sw "init_constraint" ",\n" writeValueExpr tsd.InitConstraintDefs
                writeDefs sw "transition_rules" " [=]\n" writeRuleExpr tsd.TransitionRuleDefs

                sw.WriteLine "end"
                sw.WriteLine()

        writeDefs sw "ltl_assertion" ",\n" writeLTLAssertionDef scheme.LTLAssertionDefs

        sw.WriteLine "end"

        Ok()

    with exn ->
        Error [ WriteFile(path, exn.Message) ]

let inline writeToFileWithKind (srcPath: string) (kind: string) (spec: Spec) =
    let newName = String.Concat(Path.GetFileNameWithoutExtension srcPath, "_", kind)

    let newPath =
        Path.Combine(Path.GetDirectoryName srcPath, String.Concat(newName, ".rsl"))

    writeToFile newPath { spec.Scheme with Id = Node.Replace(newName, spec.Scheme.Id) }
