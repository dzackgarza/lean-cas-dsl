/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CasCatalogue.TestSuite
public import Lean.Elab.Frontend

@[expose] public section

/-!
# The harness: the suite over a leaves manifest (`specs/architecture.md`, "Acceptance")

`cas-harness [--suite DIR] [--report FILE] [--manifest FILE]` imports, into a fresh environment,
the catalogue and the language, and runs every file of the suite (`tests/acceptance` by default)
with `#cas_tests`, through the registrations of the manifest `FILE` (by default the installed
leaves', `CasCatalogue.Realize.leavesManifest`). The leaves see neither the suite nor the harness:
a leaf is a manifest and the programs it names, imported by nothing (`specs/leaf-registration.md`).
It prints each file's report, writes every result as JSON to the report file, and exits nonzero if
a test is wrong, malformed or invalid. Gaps are its output: the implementations the suite derives.
-/

open Lean Elab

namespace CasCatalogue.Tools.Harness

structure Options where
  suite : String := "tests/acceptance"
  report : Option String := none
  manifest : Option String := none

/-- The suite command the harness elaborates. -/
def command (o : Options) : String :=
  let manifest := match o.manifest with
    | some file => s!" manifest \"{file}\""
    | none => ""
  let reporting := match o.report with
    | some file => s!" reporting \"{file}\""
    | none => ""
  s!"#cas_tests \"{o.suite}\"{manifest}{reporting}\n"

def main (args : List String) : IO UInt32 := do
  let mut o : Options := {}
  let mut rest := args
  while !rest.isEmpty do
    match rest with
    | "--suite" :: dir :: more => o := { o with suite := dir }; rest := more
    | "--report" :: file :: more => o := { o with report := some file }; rest := more
    | "--manifest" :: file :: more => o := { o with manifest := some file }; rest := more
    | arg :: _ =>
        IO.eprintln s!"cas-harness: unknown argument {arg}\n\
          usage: cas-harness [--suite DIR] [--report FILE] [--manifest FILE]"
        return 2
    | [] => pure ()
  initSearchPath (← findSysroot)
  unsafe Lean.enableInitializersExecution
  let env ← importModules #[{ module := `CasCatalogue.TestSuite }] {} (loadExts := true)
  let inputCtx := Parser.mkInputContext (command o) "<cas-harness>"
  let state ← IO.processCommands inputCtx {} (Command.mkState env {} {})
  let messages := state.commandState.messages
  for message in messages.toList do
    unless (← message.data.toString).startsWith "resolved:" do
      IO.println (← message.toString)
  return if messages.hasErrors then 1 else 0

end CasCatalogue.Tools.Harness
