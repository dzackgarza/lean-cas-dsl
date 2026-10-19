/- Engineering timing harness for the admitted linear-algebra assertions.
Run with `CAS_BENCH_ASSERTION=matrices.kernel /usr/bin/time -v lake env lean
benchmarks/question_identity.lean`. The selected assertion is read from the permanent suite.
`CAS_BENCH_ONCE=1` runs once; `CAS_BENCH_IDENTITY_OUT=FILE` saves its full identity. -/
module

import CasCatalogue.TestSuite
meta import CasCatalogue.TestSuite

open Lean Elab Command Term
open CasCatalogue CasCatalogue.Language CasCatalogue.Realize

run_cmd liftTermElabM do
  let target := (← IO.getEnv "CAS_BENCH_ASSERTION").getD "matrices.kernel"
  let text ← IO.FS.readFile "tests/acceptance/linear_algebra.cas"
  let mut scope : CasCatalogue.Language.Scope := {}
  let mut found := false
  for item in CasCatalogue.Language.items text do
    if found then continue
    let parsed ← match Parser.runParserCategory (← getEnv) `cas_item item with
      | .ok parsed => pure parsed
      | .error error => throwError "benchmark item failed to parse: {error}"
    let (id?, statement) := match parsed with
      | `(cas_item| test $id:ident $_:str : $s:cas_stmt) => (some id.getId.toString, s.raw)
      | `(cas_item| $s:cas_stmt) => (none, s.raw)
      | _ => (none, parsed)
    if id? == some target then
      let mut firstIdentity : Option String := none
      let trials := if (← IO.getEnv "CAS_BENCH_ONCE") == some "1" then 1 else 2
      for trial in [:trials] do
        let stages ← IO.mkRef (#[] : Array (String × Nat))
        let question ← withCurrHeartbeats <| interpret scope statement (some stages)
        if let some first := firstIdentity then
          unless question.identity.1 == first do
            throwError "repeated interpretation changed the complete question identity"
        else
          firstIdentity := some question.identity.1
          if let some path := ← IO.getEnv "CAS_BENCH_IDENTITY_OUT" then
            IO.FS.writeFile path question.identity.1
        IO.println s!"trial={trial + 1} assertion={target} trace_roots={question.trace.size} identity_bytes={question.identity.1.utf8ByteSize}"
        for (name, elapsed) in ← stages.get do
          IO.println s!"{name}_ms={elapsed}"
      found := true
    else if let some (name, value) ← letBinding? statement then
      IO.println s!"binding={name}"
      discard <| (claim scope statement).run {}
      scope := scope.insert name value
  unless found do throwError "benchmark assertion not found: {target}"
