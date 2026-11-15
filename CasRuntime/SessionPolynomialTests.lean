module

import CasRuntime.Session
import LeanCategories.Catalogue.Semantics.Algebra.NamedRings
import LeanCategories.Catalogue.Semantics.Algebra.NamedCommutativeRings
import LeanCategories.Catalogue.Semantics.Algebra.Polynomials
public meta import Lean.Elab.Command
meta import CasRuntime.Session
meta import LeanCategories.Catalogue.Semantics.Algebra.NamedRings
meta import LeanCategories.Catalogue.Semantics.Algebra.NamedCommutativeRings
meta import LeanCategories.Catalogue.Semantics.Algebra.Polynomials

open Lean Elab Command Term CasRuntime

/- A polynomial equality is read with its ring variable bound by a leading `let`. In a
computation-only session the equality is computed, so with no leaf installed its outcome is
no implementation, not a refusal to compare. -/
run_cmd liftTermElabM do
  let environment ← getEnv
  try
    let session ← KernelSession.start none (computationOnly := true)
    try
      let statement ← match Parser.runParserCategory (← getEnv) `cas_stmt "assert x + 1 = 1 + x in ℚ[x]" with
        | .ok statement => pure statement
        | .error error => throwError "the statement did not parse: {error}"
      let run ← withoutErrToSorry <| session.run ⟨statement⟩
      unless run.outcome.kind == "gap" && (run.outcome.detail.splitOn "NoImplementation").length > 1 do
        throwError "a polynomial equality was not computed: {run.outcome.kind} ({run.outcome.detail})"
    finally liftM (m := IO) session.close
  finally setEnv environment
