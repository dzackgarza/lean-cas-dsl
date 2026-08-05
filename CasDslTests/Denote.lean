/-
Smoke checks for the denotation bridge: every `Domain` constructor denotes,
and denotes a TYPE. A denotation that stops elaborating — a Mathlib rename,
a lost instance — fails the build here, before any registration relies on it.
-/
import CasDsl.Mathlib.Denote

namespace CasDslTests

open Lean Meta Elab Command CasDsl

/-- Elaborate `d.denote` and require the result to be a type. -/
private def checkDenotes (d : Domain) : CommandElabM Unit :=
  liftTermElabM do
    let e ← d.denote
    let t ← inferType e
    unless t.isSort do
      throwError "denotation of {repr d} is not a type: {e} : {t}"

run_cmd
  #[Domain.nat, .int, .rat, .real, .complex, .mod 5, .mod 6,
    .poly .int, .poly .rat, .poly .complex, .poly (.poly .rat),
    .matrix 2 .rat, .matrix 2 (.mod 5), .vector 3 .rat,
    .funcs .real .real, .series .int, .series .rat, .series .real
  ].forM checkDenotes

end CasDslTests
