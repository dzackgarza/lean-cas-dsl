module

import CasRuntime.Session
import LeanCategories.Catalogue
public meta import Lean.Elab.Command
meta import CasRuntime.Session
meta import LeanCategories.Catalogue

open Lean Elab Command Term CasRuntime CasCompiler

/-- A session whose one registration declares the preferred routes `routes`. No backend starts:
nothing is dispatched. -/
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

/- A ring is a monoid along three structural routes (multiplicative, through its additive group,
through semirings) that agree by no registered comparison, so `(Mat₂(ℚ) in Rings)ˣ` is ambiguous
(SourceViewTests). A registration that declares the multiplicative route preferred for `Units`
on rings selects it (constitution C6); the reading records the route. -/
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
      let recorded := (value.find? fun part => match part with
        | .mdata data _ => data.getString `CasCompiler.source.preferredRoute ==
            reprStr #["fun.rings.multiplicative_monoid"]
        | _ => false).isSome
      unless recorded do throwError "the reading does not record its preferred route: {value}"
    finally liftM (m := IO) session.close
  finally setEnv environment

/- A declared route that is not a chain of structural edges from its receiver is malformed, and
its registration is rejected; the reading stays ambiguous. -/
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
