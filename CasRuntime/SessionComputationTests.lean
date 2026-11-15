module

import CasRuntime.Session
import LeanCategories.Catalogue.Semantics.Algebra.NamedRings
import LeanCategories.Catalogue.Semantics.Algebra.NamedCommutativeRings
import LeanCategories.Catalogue.Semantics.Algebra.Polynomials
import LeanCategories.Catalogue.Semantics.Foundation.FiniteObjects
import LeanCategories.Catalogue.Semantics.Foundation.Finiteness
public meta import Lean.Elab.Command
meta import CasRuntime.Session
meta import LeanCategories.Catalogue.Semantics.Algebra.NamedRings
meta import LeanCategories.Catalogue.Semantics.Algebra.NamedCommutativeRings
meta import LeanCategories.Catalogue.Semantics.Algebra.Polynomials
meta import LeanCategories.Catalogue.Semantics.Foundation.FiniteObjects
meta import LeanCategories.Catalogue.Semantics.Foundation.Finiteness

open Lean Elab Command Term CasRuntime

/- Questions computed with no leaf installed end in no implementation (constitution C22).
A polynomial equality is read with its ring variable bound by a leading `let`; it is computed,
not refused as a comparison. A property is a proposition with no published predicate; the
kernel does not evaluate its definition. -/
run_cmd liftTermElabM do
  let environment ← getEnv
  try
    let session ← KernelSession.start none (computationOnly := true)
    try
      for text in #["assert x + 1 = 1 + x in ℚ[x]", "assert Fin(3).is_finite()",
          "assert ℤ.is_finite() = false"] do
        let statement ← match Parser.runParserCategory (← getEnv) `cas_stmt text with
          | .ok statement => pure statement
          | .error error => throwError "the statement did not parse: {error}"
        let run ← withoutErrToSorry <| session.run ⟨statement⟩
        unless run.outcome.kind == "gap" && (run.outcome.detail.splitOn "NoImplementation").length > 1 do
          throwError "`{text}` is not a computation without a leaf: {run.outcome.kind} ({run.outcome.detail})"
    finally liftM (m := IO) session.close
  finally setEnv environment
