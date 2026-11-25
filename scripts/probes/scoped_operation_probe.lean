module

import CasRuntime.Session
import LeanCategories.Catalogue.Semantics.Algebra.NamedRings
import LeanCategories.Catalogue.Semantics.Algebra.ComputationDerivations
import LeanCategories.Catalogue.Semantics.Foundation.FiniteObjects
import LeanCategories.Catalogue.Semantics.Foundation.Cardinality
import LeanCategories.Catalogue.Semantics.Algebra.CyclicQuotients
import LeanCategories.Catalogue.Semantics.Modules.CatalogueRegistration
public meta import Lean.Elab.Command
meta import CasRuntime.Session
meta import LeanCategories.Catalogue.Semantics.Algebra.NamedRings
meta import LeanCategories.Catalogue.Semantics.Algebra.ComputationDerivations
meta import LeanCategories.Catalogue.Semantics.Foundation.FiniteObjects
meta import LeanCategories.Catalogue.Semantics.Foundation.Cardinality
meta import LeanCategories.Catalogue.Semantics.Algebra.CyclicQuotients
meta import LeanCategories.Catalogue.Semantics.Modules.CatalogueRegistration

open Lean Elab Command Term CasRuntime CasCompiler CasCatalogue CasCatalogue.Backend

/- Scoped declarations use the original public statement reader and kernel session. The
hypothetical ring and module have no provider values; their uniform source operations and
hypotheses must remain usable with their original bindings after shadowing. -/
run_cmd liftTermElabM do
  let environment ← getEnv
  let root ← liftM (m := IO) IO.currentDir
  let manifest := root / ".tmp" / "kernel-session-declarations.json"
  liftM (m := IO) <| IO.FS.createDirAll (root / ".tmp")
  liftM (m := IO) <| IO.FS.writeFile manifest
    (Json.mkObj [("backends", .arr #[]), ("registrations", .arr #[])]).compress
  let runStatement : KernelSession → String → TermElabM StatementRun := fun session text => do
    let statement ← match Parser.runParserCategory (← getEnv) `cas_stmt text with
      | .ok statement => pure statement
      | .error error => throwError "the scoped statement did not parse: {error}"
    withoutErrToSorry <| session.run ⟨statement⟩
  let read : SourceSession → String → TermElabM SourceTerm := fun source text => do
    let expression ← match Parser.runParserCategory (← getEnv) `cas_term text with
      | .ok expression => pure expression
      | .error error => throwError "the scoped expression did not parse: {error}"
    withoutErrToSorry <| source.read ⟨expression⟩
  let mut session ← KernelSession.start (some manifest)
  try
    for text in #[
        "let R ∈ Rings",
        "let M ∈ Modules(R)",
        "let x ∈ R",
        "let y : R",
        "let h : x = y",
        "assert x = y",
        "let saved := h",
        "assert R ∈ Rings",
        "assert M ∈ Modules(R)",
        "assert x ∈ R",
        "let Q := ℚ ∈ Rings",
        "assert Q ∈ Rings"] do
      let step ← runStatement session text
      unless step.outcome.kind == "holds" do
        throwError "`{text}` is {step.outcome.kind}: {step.outcome.detail}"
      session := step.session
    let #[ring, module_, x, y, hypothesis, saved, concrete] := session.source.context.entries
      | throwError "the public declarations lost or added source bindings"
    for entry in #[ring, module_, x, y] do
      unless entry.role == .parameter && entry.value.isNone do
        throwError "a hypothetical source parameter became a definition or axiom"
    unless hypothesis.role == .hypothesis && hypothesis.value.isNone &&
        saved.role == .definition && saved.value.isSome &&
        concrete.role == .definition && concrete.value.isSome do
      throwError "hypotheses and concrete definitions lost their native declaration kinds"
    unless #[ring, module_, x, y, hypothesis].all (fun entry =>
        (session.value? entry.id).isNone) do
      throwError "a hypothetical input acquired an unsolicited computational value"
    session.source.context.withOpen fun bindings => do
      let expected ← Meta.mkEq bindings[2]!.expression bindings[3]!.expression
      unless ← Meta.isDefEq (← Meta.inferType bindings[4]!.expression) expected do
        throwError "the local hypothesis changed its original operands"
      let some value := (← bindings[5]!.expression.fvarId!.getDecl).value?
        | throwError "the source proof alias was not retained as a definition"
      unless value == bindings[4]!.expression do
        throwError "the source proof alias replaced the original local hypothesis"
    let some selected := session.source.categoryFor module_.id
      | throwError "the dependent hypothetical object lost its selected category"
    selected.bundle.withOpen fun bindings expression => do
      let some original := bindings.find? (·.id == ring.id)
        | throwError "the selected module category lost its original scalar binding"
      unless expression.containsFVar original.expression.fvarId! do
        throwError "the selected module category replaced its actual scalar parameter"
    let sum ← read session.source "x + y in R"
    sum.source.withOpen fun bindings expression => do
      for id in #[x.id, y.id] do
        let some original := bindings.find? (·.id == id)
          | throwError "a uniform source operation lost its original element"
        unless expression.containsFVar original.expression.fvarId! do
          throwError "a uniform source operation substituted a hypothetical operand"
    let beforeShadow := session.source
    let shadow ← runStatement session "let R ∈ Rings"
    unless shadow.outcome.kind == "holds" do
      throwError "a new scoped ring did not read: {shadow.outcome.detail}"
    session := shadow.session
    let some newRing := session.source.context.entries.back?
      | throwError "the shadowing declaration disappeared"
    unless newRing.userName == ring.userName && newRing.id != ring.id &&
        beforeShadow.context.entries.size == 7 do
      throwError "shadowing changed an earlier binding or its persistent scope"
    let identity ← read session.source "id(M)"
    unless identity.category.any (·.role == .morphism) do
      throwError "the hypothetical module lost its uniform identity operation"
    identity.source.withOpen fun bindings expression => do
      let some original := bindings.find? (·.id == module_.id)
        | throwError "the uniform identity lost its source module"
      let expected ← Meta.mkAppM ``Quiver.Hom #[original.expression, original.expression]
      unless ← Meta.isDefEq (← Meta.inferType expression) expected do
        throwError "the uniform identity no longer has the original module as both endpoints"
    for text in #["assert M ∈ Modules(R)", "let bad ∈ Modules(x)"] do
      let step ← runStatement session text
      unless step.outcome.fails &&
          step.session.source.context.entries.size == session.source.context.entries.size do
        throwError "a mismatched scoped category was accepted or changed the source scope"
    unless (← session.kernel.dispatches.get).isEmpty do
      throwError "a scoped declaration or typing judgement dispatched a computation"
    -- Keep the actual Environment unchanged while opening a new native source scope.
    -- A second runtime session would conflict with its existing initialized snapshot.
    let fresh ← SourceSession.empty session.kernel.ledger.owners.identities
    for (text, name) in #[("assert R ∈ Rings", "R"), ("let leaked := h", "h")] do
      let statement ← match Parser.runParserCategory (← getEnv) `cas_stmt text with
        | .ok statement => pure statement
        | .error error => throwError "the fresh-scope statement did not parse: {error}"
      let rejected ← try
          discard <| withoutErrToSorry <| fresh.readStatement ⟨statement⟩
          pure false
        catch error =>
          unless CasCatalogue.Exception.isUnknownSourceName error name do throw error
          pure true
      unless rejected && fresh.context.entries.isEmpty do
        throwError "a scoped assumption escaped into an independent source session"
  finally
    liftM (m := IO) session.close
    setEnv environment

