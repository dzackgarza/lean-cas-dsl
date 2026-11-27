



module

public import CasCatalogue.TestSuite
public import Lean.Elab.Frontend

@[expose] public section



















open Lean Elab

namespace CasCatalogue.Tools.Harness

structure Options where
  suite : String := "tests/acceptance"
  report : Option String := none
  manifest : Option String := none
  inventory : String := "CasAcceptance/Permanent/admitted.json"
  computationOnly : Bool := false


def command (o : Options) : String :=
  let manifest := match o.manifest with
    | some file => s!" manifest \"{file}\""
    | none => ""
  let reporting := match o.report with
    | some file => s!" reporting \"{file}\""
    | none => ""
  let computing := if o.computationOnly then " computing" else ""
  s!"#cas_tests \"{o.suite}\"{manifest}{reporting} inventory \"{o.inventory}\"{computing}\n"



def infrastructureReport (o : Options) (reason : String) : IO Unit := do
  let .ok inventory := Json.parse (← IO.FS.readFile o.inventory)
    | throw <| IO.userError "cannot read fixed assertion inventory"
  let .ok (.obj assertions) := inventory.getObjVal? "assertions"
    | throw <| IO.userError "missing fixed assertion inventory"
  let results := assertions.toList.toArray.map fun (identity, _) => Json.mkObj [
    ("file", toJson o.suite), ("id", toJson identity), ("kind", toJson "internal"),
    ("stratum", Json.null),
    ("detail", toJson reason), ("fails", toJson true),
    ("question", toJson ""), ("proposition", toJson "")]
  if let some report := o.report then IO.FS.writeFile report (Json.arr results).pretty

def main (args : List String) : IO UInt32 := do
  let mut o : Options := {}
  let mut rest := args
  while !rest.isEmpty do
    match rest with
    | "--suite" :: dir :: more => o := { o with suite := dir }; rest := more
    | "--report" :: file :: more => o := { o with report := some file }; rest := more
    | "--inventory" :: file :: more => o := { o with inventory := file }; rest := more
    | "--manifest" :: file :: more => o := { o with manifest := some file }; rest := more
    | "--computation-only" :: more => o := { o with computationOnly := true }; rest := more
    | arg :: _ =>
        IO.eprintln s!"cas-harness: unknown argument {arg}\n\
          usage: cas-harness [--suite DIR] [--report FILE] [--manifest FILE] \
          [--inventory FILE] [--computation-only]"
        return 2
    | [] => pure ()

  if let some report := o.report then IO.FS.writeFile report ""
  try
    initSearchPath (← findSysroot)
    unsafe Lean.enableInitializersExecution
    let env ← importModules #[{ module := `CasCatalogue.TestSuite }] {} (loadExts := true)
    let inputCtx := Parser.mkInputContext (command o) "<cas-harness>"
    let state ← IO.processCommands inputCtx {} (Command.mkState env {} {})
    let messages := state.commandState.messages
    for message in messages.toList do
      unless (← message.data.toString).startsWith "resolved:" do
        IO.println (← message.toString)
    if let some report := o.report then
      if (← IO.FS.readFile report).isEmpty then
        infrastructureReport o "runner failed before the suite produced its report"
        return 1
    return if messages.hasErrors then 1 else 0
  catch error =>
    let reason := s!"harness infrastructure failure: {error}"
    IO.eprintln reason
    infrastructureReport o reason
    return 1

end CasCatalogue.Tools.Harness
