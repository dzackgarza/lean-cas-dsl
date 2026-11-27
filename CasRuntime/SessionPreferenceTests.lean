module

import CasRuntime.Session
import LeanCategories.Catalogue
public meta import Lean.Elab.Command
meta import CasRuntime.Session
meta import LeanCategories.Catalogue

open Lean Elab Command Term CasRuntime CasCompiler



private def sessionDeclaring (file : String) (routes : Array Json) : TermElabM KernelSession := do
  let root ← liftM (m := IO) IO.currentDir
  let manifest := Json.mkObj [
    ("backends", .arr #[Json.mkObj [("name", "peer"), ("command", "true")]]),
    ("registrations", .arr #[Json.mkObj [("operation", "meth.cardinality"),
      ("input", "obj.sets.fin"), ("backend", "peer"), ("preferredRoutes", .arr routes)]])]
  liftM (m := IO) <| IO.FS.createDirAll (root / ".tmp")
  let path := root / ".tmp" / file
  liftM (m := IO) <| IO.FS.writeFile path manifest.compress
  KernelSession.start (some path) (computationOnly := true)

private def readUnits (session : KernelSession) : TermElabM StatementRun := do
  let .ok statement := Parser.runParserCategory (← getEnv) `cas_stmt
      "let G := (Mat₂(ℚ) in Rings)ˣ"
    | throwError "the statement did not parse"
  withoutErrToSorry <| session.run ⟨statement⟩





run_cmd liftTermElabM do
  let environment ← getEnv
  try
    let session ← sessionDeclaring "kernel-preference-leaves.json" #[Json.mkObj [
      ("name", "Units"), ("receiver", "cat.rings"),
      ("route", .arr #["fun.rings.multiplicative_monoid"])]]
    try
      unless session.kernel.rejected.isEmpty do
        throwError "the declared preferred route was rejected: {session.kernel.rejected}"
      let run ← readUnits session
      unless run.outcome.kind == "holds" do
        throwError "the preferred route did not select a reading: {run.outcome.kind} ({run.outcome.detail})"
      let some entry := run.session.source.context.entries.back?
        | throwError "the definition of G was not retained"
      let some value := entry.value
        | throwError "G has no definition"
      let some selected := run.session.source.selections[entry.id]?
        | throwError "the retained definition lost its complete typed source selection"
      unless selected.preferredRoute.map (·.map (·.label)) ==
          some #["fun.rings.multiplicative_monoid"] do
        throwError "the reading does not record its preferred route: {value}"
    finally liftM (m := IO) session.close
  finally setEnv environment



run_cmd liftTermElabM do
  let environment ← getEnv
  try
    let session ← sessionDeclaring "kernel-preference-malformed-leaves.json" #[Json.mkObj [
      ("name", "Units"), ("receiver", "cat.rings"), ("route", .arr #["fun.groups.monoid"])]]
    try
      unless session.kernel.rejected.size == 1 do
        throwError "the malformed preferred route was not rejected: {session.kernel.rejected}"
      let run ← readUnits session
      unless run.outcome.kind == "ambiguous" do
        throwError "a rejected preference selected a reading: {run.outcome.kind} ({run.outcome.detail})"
    finally liftM (m := IO) session.close
  finally setEnv environment
