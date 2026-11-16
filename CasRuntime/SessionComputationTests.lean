module

import CasRuntime.Session
import LeanCategories.Catalogue.Semantics.Algebra.NamedRings
import LeanCategories.Catalogue.Semantics.Algebra.NamedCommutativeRings
import LeanCategories.Catalogue.Semantics.Algebra.Polynomials
import LeanCategories.Catalogue.Semantics.Foundation.FiniteObjects
import LeanCategories.Catalogue.Semantics.Foundation.FiniteSubsetLiterals
import LeanCategories.Catalogue.Semantics.Foundation.Finiteness
import LeanCategories.Catalogue.Semantics.Foundation.Cardinality
import LeanCategories.Catalogue.Semantics.Limits.Registration
import LeanCategories.Catalogue.Semantics.Modules.Bilinear.Valued.Lattices
import LeanCategories.Catalogue.Semantics.Algebra.LinearAlgebra
import LeanCategories.Catalogue.Semantics.Algebra.NumberSystems
public meta import Lean.Elab.Command
meta import CasRuntime.Session
meta import LeanCategories.Catalogue.Semantics.Algebra.NamedRings
meta import LeanCategories.Catalogue.Semantics.Algebra.NamedCommutativeRings
meta import LeanCategories.Catalogue.Semantics.Algebra.Polynomials
meta import LeanCategories.Catalogue.Semantics.Foundation.FiniteObjects
meta import LeanCategories.Catalogue.Semantics.Foundation.FiniteSubsetLiterals
meta import LeanCategories.Catalogue.Semantics.Foundation.Finiteness
meta import LeanCategories.Catalogue.Semantics.Foundation.Cardinality
meta import LeanCategories.Catalogue.Semantics.Limits.Registration
meta import LeanCategories.Catalogue.Semantics.Modules.Bilinear.Valued.Lattices
meta import LeanCategories.Catalogue.Semantics.Algebra.LinearAlgebra
meta import LeanCategories.Catalogue.Semantics.Algebra.NumberSystems

open Lean Elab Command Term CasRuntime

/- Questions computed with no leaf installed end in no implementation (constitution C22).
A polynomial equality is read with its ring variable bound by a leading `let`; it is computed,
not refused as a comparison. A property is a proposition with no published predicate; the
kernel does not evaluate its definition. -/
run_cmd liftTermElabM do
  let environment ← getEnv
  try
    let mut session ← KernelSession.start none (computationOnly := true)
    try
      for text in #["let M := [1, 2; 3, 4] in Mat₂(ℚ)", "let v := (1, 2) in ℚ²",
          "let b := (5, 11) in ℚ²"] do
        let statement ← match Parser.runParserCategory (← getEnv) `cas_stmt text with
          | .ok statement => pure statement
          | .error error => throwError "the statement did not parse: {error}"
        let run ← withoutErrToSorry <| session.run ⟨statement⟩
        unless run.outcome.kind == "holds" do
          throwError "`{text}` is {run.outcome.kind} ({run.outcome.detail}), not holds"
        session := run.session
      for (text, reached) in #[("assert x + 1 = 1 + x in ℚ[x]", "NoImplementation"),
          ("assert Fin(3).is_finite()", "NoImplementation"),
          ("assert ℤ.is_finite() = false", "NoImplementation"),
          -- The apex of a registered presentation is a construction for a leaf: its
          -- cardinality is reached through the structural carrier functor of the form's
          -- category, not through an eliminator inside the apex.
          ("assert |cokernel(to_dual(1))| = 2", "fun.bil_wform.carrier"),
          -- The apex of a binary coproduct is sent as the registered colimit's descriptor at its
          -- objects, so its cardinality is the published method (tests/acceptance/sets.cas).
          ("assert |Fin(2) ⊔ Fin(3)| = 5", "meth.cardinality"),
          -- A matrix's registered application is the published operation of Mat; the kernel
          -- does not evaluate its definition.
          ("assert M(v) = b", "obj.sets.matrices#application")] do
        let statement ← match Parser.runParserCategory (← getEnv) `cas_stmt text with
          | .ok statement => pure statement
          | .error error => throwError "the statement did not parse: {error}"
        let run ← withoutErrToSorry <| session.run ⟨statement⟩
        unless run.outcome.kind == "gap" && (run.outcome.detail.splitOn "NoImplementation").length > 1 &&
            (run.outcome.detail.splitOn reached).length > 1 do
          throwError "`{text}` is not a computation without a leaf: {run.outcome.kind} ({run.outcome.detail})"
    finally liftM (m := IO) session.close
  finally setEnv environment

/- An admitted finite subset keeps the literal and the registered ring operations it is read
with; the kernel opens neither `List.toFinset` nor Mathlib's polynomial addition
(tests/acceptance/polynomials.cas). -/
run_cmd liftTermElabM do
  let environment ← getEnv
  try
    let started ← KernelSession.start none (computationOnly := true)
    try
      let mut session := started
      for text in #["let F := {x - 1} in 𝒫_fin(ℤ[x])", "assert F = F"] do
        let statement ← match Parser.runParserCategory (← getEnv) `cas_stmt text with
          | .ok statement => pure statement
          | .error error => throwError "the statement did not parse: {error}"
        let run ← withoutErrToSorry <| session.run ⟨statement⟩
        if text.startsWith "let" then
          session := run.session
          continue
        unless run.outcome.kind == "gap" && (run.outcome.detail.splitOn "op.rings.add").length > 1 do
          throwError "`{text}` does not reach its elements' operation: {run.outcome.kind} ({run.outcome.detail})"
    finally liftM (m := IO) started.close
  finally setEnv environment
