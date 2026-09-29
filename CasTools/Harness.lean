/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CasCatalogue.TestSuite
public import Lean.Elab.Frontend

@[expose] public section

/-!
# The harness: the suite over installed leaves (`specs/architecture.md`, "Acceptance")

`cas-harness [--suite DIR] [--report FILE] LEAF…` imports, into a fresh environment, the
catalogue, the language and exactly the leaf modules `LEAF…`, and runs every file of the suite
(`tests/acceptance` by default) with `#cas_tests`. The leaves see neither the suite nor the
harness: they are imported beside it and depend only on the intake contract, which the harness
checks (`leafBoundaryViolations`) before running anything. It prints each file's report, writes
every result as JSON to `FILE`, and exits nonzero if a leaf breaks the intake contract or a test is
wrong, malformed or invalid. Gaps are its output: the implementations the suite derives.
-/

open Lean Elab

namespace CasCatalogue.Tools.Harness

structure Options where
  suite : String := "tests/acceptance"
  report : Option String := none
  leaves : Array Name := #[]

/-- The suite command the harness elaborates. -/
def command (o : Options) : String :=
  let reporting := match o.report with
    | some file => s!" reporting \"{file}\""
    | none => ""
  s!"#cas_tests \"{o.suite}\"{reporting}\n"

def main (args : List String) : IO UInt32 := do
  let mut o : Options := {}
  let mut rest := args
  while !rest.isEmpty do
    match rest with
    | "--suite" :: dir :: more => o := { o with suite := dir }; rest := more
    | "--report" :: file :: more => o := { o with report := some file }; rest := more
    | leaf :: more =>
        if leaf.startsWith "--" then
          IO.eprintln s!"cas-harness: unknown option {leaf}"; return 2
        o := { o with leaves := o.leaves.push leaf.toName }; rest := more
    | [] => pure ()
  if o.leaves.isEmpty then
    IO.eprintln "usage: cas-harness [--suite DIR] [--report FILE] LEAF…"
    return 2
  initSearchPath (← findSysroot)
  unsafe Lean.enableInitializersExecution
  let env ← importModules
    ((#[`CasCatalogue.TestSuite] ++ o.leaves).map fun m => { module := m }) {} (loadExts := true)
  -- The intake contract first: no leaf imports the suite, the harness or another leaf's root.
  let violations := leafBoundaryViolations env
  unless violations.isEmpty do
    IO.eprintln s!"cas-harness: the leaves break the intake contract:\n{"\n".intercalate
      violations.toList}"
    return 1
  let inputCtx := Parser.mkInputContext (command o) "<cas-harness>"
  let state ← IO.processCommands inputCtx {} (Command.mkState env {} {})
  let messages := state.commandState.messages
  for message in messages.toList do
    unless (← message.data.toString).startsWith "resolved:" do
      IO.println (← message.toString)
  return if messages.hasErrors then 1 else 0

end CasCatalogue.Tools.Harness
