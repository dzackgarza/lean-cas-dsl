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
import LeanCategories.Catalogue.Semantics.Algebra.Series
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
meta import LeanCategories.Catalogue.Semantics.Algebra.Series

open Lean Elab Command Term CasRuntime

-- These controls explicitly select an empty provider set for each source session.
private def emptyComputationManifest : IO System.FilePath := do
  let root ← IO.currentDir
  IO.FS.createDirAll (root / ".tmp")
  let path := root / ".tmp" / "kernel-computation-empty-leaves.json"
  IO.FS.writeFile path
    (Json.mkObj [("backends", .arr #[]), ("registrations", .arr #[])]).compress
  return path

/- Questions computed with no leaf installed end in no implementation (constitution C22).
A polynomial equality is read with its ring variable bound by a leading `let`; it is computed,
not refused as a comparison. A property is a proposition with no published predicate; the
kernel does not evaluate its definition. -/
run_cmd liftTermElabM do
  let environment ← getEnv
  try
    let mut session ← KernelSession.start (some (← emptyComputationManifest)) (computationOnly := true)
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
          -- The unchanged numbers.gcd question is an explicit computed observation in this
          -- session. Its selected morphism must reach the public demand; native reduction of
          -- the closed GCD expression cannot replace the absent registered computation.
          ("assert gcd(84, 30) = 6", "mor.sets.gcd"),
          -- The apex of a registered presentation is a construction for a leaf: its
          -- cardinality is reached through the structural carrier functor of the form's
          -- category, not through an eliminator inside the apex.
          ("assert |cokernel(to_dual(1))| = 2", "fun.bil_wform.carrier"),
          -- The apex of a binary coproduct is sent as the registered colimit's descriptor at its
          -- objects, so its cardinality is the published method (tests/acceptance/sets.cas).
          ("assert |Fin(2) ⊔ Fin(3)| = 5", "meth.cardinality"),
          -- A matrix's registered application is the published operation of Mat; the kernel
          -- does not evaluate its definition.
          ("assert M(v) = b", "obj.sets.matrices#application"),
          -- The summand family is admitted into the registered summable families
          -- (`summableFamilies`) before the sum takes it; the admitted element keeps that
          -- subobject as its type and the family's data (tests/acceptance/series.cas).
          ("let f := ∑_{n ∈ ℕ} n² · t^n in ℤ[[t]]", "NoImplementation")] do
        let statement ← match Parser.runParserCategory (← getEnv) `cas_stmt text with
          | .ok statement => pure statement
          | .error error => throwError "the statement did not parse: {error}"
        let run ← withoutErrToSorry <| session.run ⟨statement⟩
        unless run.outcome.kind == "gap" && (run.outcome.detail.splitOn "NoImplementation").length > 1 &&
            (run.outcome.detail.splitOn reached).length > 1 do
          throwError "`{text}` is not a computation without a leaf: {run.outcome.kind} ({run.outcome.detail})"
      unless (← session.kernel.dispatches.get).isEmpty do
        throwError "an empty-provider computed question dispatched a registration"
    finally liftM (m := IO) session.close
  finally setEnv environment

/- An admitted finite subset is the literal it admits, sent as the array of its elements, each
retained with the registered ring operations it is read with; the kernel opens neither the
admission, `List.toFinset` nor Mathlib's polynomial addition (tests/acceptance/polynomials.cas).
With no leaf, a question about it stops at the retained value, which has no scalar comparison. -/
run_cmd liftTermElabM do
  let environment ← getEnv
  try
    let started ← KernelSession.start (some (← emptyComputationManifest)) (computationOnly := true)
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
        unless run.outcome.kind == "gap" && run.outcome.detail ==
            "the computed value is retained by its provider and has no scalar comparison" do
          throwError "`{text}` did not keep the admitted literal: {run.outcome.kind} ({run.outcome.detail})"
    finally liftM (m := IO) started.close
  finally setEnv environment

/- A defining leg of a registered limit is that limit's named leg at its maps (constitution C7),
not the apex and not the presentation's definition (C22): the base-change functor's map action on
`C.leg(1)` receives the descriptor `colim.bil_w_form.cokernel#leg` with the limit's map and the
ordinal 1. A real protocol-v2 process answers; its log records each request. -/
run_cmd liftTermElabM do
  let environment ← getEnv
  try
    let contract ← liftM (m := IO) <| CasCatalogue.Backend.packageDir
      CasCatalogue.Backend.contractPackage
    let root ← liftM (m := IO) IO.currentDir
    let python := (← liftM (m := IO) <| IO.FS.realPath contract) / ".venv/bin/python"
    liftM (m := IO) <| IO.FS.createDirAll (root / ".tmp")
    let log := root / ".tmp" / "kernel-leg-peer.log"
    liftM (m := IO) <| IO.FS.writeFile log ""
    let operation := "fun.bil_wform.base_change#map"
    let manifest := Json.mkObj [
      ("backends", .arr #[Json.mkObj [("name", "peer"), ("command", python.toString),
        ("args", .arr #[toJson (root / "scripts/probes/kernel_lift_peer.py").toString,
          toJson log.toString, toJson operation])]]),
      ("registrations", .arr #[Json.mkObj [("operation", toJson operation),
        ("input", "fun.bil_wform.base_change#input"), ("backend", "peer")]])]
    let path := root / ".tmp" / "kernel-leg-leaves.json"
    liftM (m := IO) <| IO.FS.writeFile path manifest.compress
    let mut session ← KernelSession.start (some path)
    try
      for text in #["let C := cokernel(to_dual(1))",
          "let r := map C.leg(1) along «fun.bil_wform.base_change»(ℤ, ℚ)"] do
        let statement ← match Parser.runParserCategory (← getEnv) `cas_stmt text with
          | .ok statement => pure statement
          | .error error => throwError "the statement did not parse: {error}"
        let run ← withoutErrToSorry <| session.run ⟨statement⟩
        unless run.outcome.kind == "holds" do
          throwError "`{text}` is {run.outcome.kind} ({run.outcome.detail}), not holds"
        session := run.session
      let requests := ((← liftM (m := IO) <| IO.FS.readFile log).splitOn "\n").filter (!·.isEmpty)
      let some line := requests.head? | throwError "the base change's map action was not dispatched"
      let .ok request := Json.parse line | throwError "the peer log is malformed: {line}"
      let .ok arguments := (request.getObjValD "context").getObjValAs? (Array Json) "arguments"
        | throwError "the map action has no arguments: {line}"
      let leg := arguments.back?.getD .null
      unless (leg.getObjValAs? String "ctor").toOption == some "colim.bil_w_form.cokernel#leg" &&
          ((leg.getObjValD "args").getArr?.toOption.bind (·.back?)) == some (toJson (1 : Nat)) do
        throwError "the map action did not receive C's leg 1: {line}"
    finally liftM (m := IO) session.close
  finally setEnv environment

/- A statement that names nothing registered and nothing bound is invalid source, and its outcome
names the identifier. It is not an internal failure of the kernel (FR-029, outcome separation). -/
run_cmd liftTermElabM do
  let environment ← getEnv
  try
    let session ← KernelSession.start (some (← emptyComputationManifest)) (computationOnly := true)
    try
      let statement ← match Parser.runParserCategory (← getEnv) `cas_stmt
          "assert undeclaredName = 1 in ℤ" with
        | .ok statement => pure statement
        | .error error => throwError "the statement did not parse: {error}"
      let run ← withoutErrToSorry <| session.run ⟨statement⟩
      unless run.outcome.kind == "invalid" &&
          (run.outcome.detail.splitOn "undeclaredName").length > 1 do
        throwError "a statement with an unknown name is {run.outcome.kind} \
          ({run.outcome.detail}), not invalid source that names it"
    finally liftM (m := IO) session.close
  finally setEnv environment

/- A statement that uses a name whose own definition did not read has that definition's outcome,
and its detail names the definition and gives the reason. The name is not an unknown name. -/
run_cmd liftTermElabM do
  let environment ← getEnv
  try
    let mut session ← KernelSession.start (some (← emptyComputationManifest)) (computationOnly := true)
    try
      let mut kinds := #[]
      let mut details := #[]
      for text in #["let unreadDefinition := undeclaredName + 1 in ℤ",
          "assert unreadDefinition = 1 in ℤ"] do
        let statement ← match Parser.runParserCategory (← getEnv) `cas_stmt text with
          | .ok statement => pure statement
          | .error error => throwError "the statement did not parse: {error}"
        let run ← withoutErrToSorry <| session.run ⟨statement⟩
        kinds := kinds.push run.outcome.kind
        details := details.push run.outcome.detail
        session := run.session
      unless kinds == #["invalid", "invalid"] do
        throwError "a use of an unread definition has outcomes {kinds} ({details})"
      let some detail := details[1]? | throwError "the use reported nothing"
      unless (detail.splitOn "unreadDefinition").length > 1 &&
          (detail.splitOn "did not read").length > 1 &&
          (detail.splitOn "undeclaredName").length > 1 do
        throwError "the use of an unread definition does not name it and its reason: {detail}"
    finally liftM (m := IO) session.close
  finally setEnv environment

/- `X ⊆ Y` for two named sets is a typing judgement: it is settled by a chain of registered
inclusions of `X` in `Y` (tests/acceptance/numbers.cas, `numbers.containments`), and a conjunction
of such judgements is settled when each is. With no chain the judgement is not established; it is
not a false statement. -/
run_cmd liftTermElabM do
  let environment ← getEnv
  try
    let session ← KernelSession.start (some (← emptyComputationManifest)) (computationOnly := true)
    try
      for (text, kind) in #[("assert ℤ ⊆ ℚ and ℚ ⊆ ℝ and ℝ ⊆ ℂ", "holds"),
          ("assert ℕ ⊆ ℂ", "holds"), ("assert ℤ ⊆ ℕ", "invalid")] do
        let statement ← match Parser.runParserCategory (← getEnv) `cas_stmt text with
          | .ok statement => pure statement
          | .error error => throwError "the statement did not parse: {error}"
        let run ← withoutErrToSorry <| session.run ⟨statement⟩
        unless run.outcome.kind == kind do
          throwError "`{text}` is {run.outcome.kind} ({run.outcome.detail}), not {kind}"
    finally liftM (m := IO) session.close
  finally setEnv environment
