/- Measure the production semantic reader without importing the realization and encoder layers.
This is engineering timing only; the full question benchmark and acceptance remain separate. -/
module

import CasCatalogue.Language
import CasCatalogue.FileItems
meta import CasCatalogue.Language
meta import CasCatalogue.FileItems

open Lean Elab Command Term
open CasCatalogue CasCatalogue.Language

run_cmd liftTermElabM do
  let target := (← IO.getEnv "CAS_BENCH_ASSERTION").getD "matrices.kernel"
  let text ← IO.FS.readFile "tests/acceptance/linear_algebra.cas"
  let mut scope : Language.Scope := {}
  let mut found := false
  for item in items text do
    if found then continue
    let parsed ← match Parser.runParserCategory (← getEnv) `cas_item item with
      | .ok parsed => pure parsed
      | .error error => throwError "benchmark item failed to parse: {error}"
    let (id?, statement) := match parsed with
      | `(cas_item| test $id:ident $_:str : $s:cas_stmt) => (some id.getId.toString, s.raw)
      | `(cas_item| $s:cas_stmt) => (none, s.raw)
      | _ => (none, parsed)
    let started ← IO.monoMsNow
    if id? == some target then
      let trace ← Trace.new
      let closedTerms ← IO.mkRef ({} : Std.HashMap String Value)
      discard <| withCurrHeartbeats <|
        (claim scope statement).run { trace := some trace, closedTerms := some closedTerms }
      IO.println s!"assertion={target} semantic_reading_ms={(← IO.monoMsNow) - started} trace_roots={(← trace.get).size} closed_terms={(← closedTerms.get).size}"
      found := true
    else if let some (name, value) ← letBinding? statement then
      discard <| withCurrHeartbeats <| (claim scope statement).run {}
      IO.println s!"binding={name} semantic_reading_ms={(← IO.monoMsNow) - started}"
      scope := scope.insert name value
  unless found do throwError "benchmark assertion not found: {target}"
