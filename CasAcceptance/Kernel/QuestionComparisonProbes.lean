/- Copyright (c) 2026 Dzack Garza. Released under Apache 2.0 license. -/
module

import CasCatalogue.QuestionComparison
import LeanCategories.Catalogue.Semantics
meta import CasCatalogue.QuestionComparison
meta import LeanCategories.Catalogue.Semantics

open Lean Meta Elab Command Term
open CasCatalogue CasCatalogue.Language CasCatalogue.Realize

/- Engineering checks of retained syntax and record comparison. The identifiers below
are inert fixture data: no semantic row, mathematical assertion or acceptance record
is authored, registered or admitted by this module. -/
run_cmd liftTermElabM do
  let read (stx : Syntax) : TermElabM Expr := do
    instantiateMVars (← elabTermAndSynthesize stx none)
  let zero := mkNatLit 0
  let one := mkNatLit 1
  let two := mkNatLit 2
  let proof ← read (← `(Eq.refl (0 : Nat)))
  let otherProof ← read (← `(Eq.symm (Eq.refl (0 : Nat))))
  let differentProof ← read (← `(Eq.refl (1 : Nat)))
  let route : Array EdgeRef := #[.functor ⟨"comparison.first"⟩, .functor ⟨"comparison.second"⟩]
  let source : ParameterPresentation := {
    source := ⟨"comparison.object"⟩
    sourceCategory := ⟨"comparison.source"⟩
    targetCategory := ⟨"comparison.target"⟩
    params := #[zero, one]
    route := route
    applications := #[one, two]
    carrierRoute := #[route[0]!]
    identifications := #[``Eq.refl]
    object := zero
    image := one
    identity := proof }
  unless ← QuestionIdentity.equivalentParameterPresentation source
      { source with identity := otherProof } do
    throwError "a source presentation retained incidental proof syntax"
  let changes : Array ParameterPresentation := #[
    { source with source := ⟨"comparison.otherObject"⟩ },
    { source with sourceCategory := ⟨"comparison.otherSource"⟩ },
    { source with targetCategory := ⟨"comparison.otherTarget"⟩ },
    { source with params := #[one, zero] },
    { source with route := route.reverse },
    { source with applications := #[two, one] },
    { source with carrierRoute := #[route[1]!] },
    { source with identifications := #[``Eq.symm] },
    { source with object := one },
    { source with image := two },
    { source with identity := differentProof }]
  for changed in changes do
    if ← QuestionIdentity.equivalentParameterPresentation source changed then
      throwError "a full selected parameter presentation field disappeared"
  let secondSource := { source with source := ⟨"comparison.secondObject"⟩ }
  let parameterNode := Node.parameterEquivalence (mkConst ``Nat) one #[source, secondSource]
  let reordered := Node.parameterEquivalence (mkConst ``Nat) one
    #[secondSource, { source with identity := otherProof }]
  unless ← QuestionIdentity.equivalentNode parameterNode reordered do
    throwError "parameter source enumeration order changed meaning"
  if ← QuestionIdentity.equivalentNode parameterNode
      (.parameterEquivalence (mkConst ``Nat) one #[source, source]) then
    throwError "parameter presentation comparison lost multiplicities or a distinct source"
  let retained := Node.retainedRoute source.sourceCategory source.targetCategory
    route #[one, two] zero
  for changed in #[
      Node.retainedRoute source.targetCategory source.targetCategory route #[one, two] zero,
      Node.retainedRoute source.sourceCategory source.sourceCategory route #[one, two] zero,
      Node.retainedRoute source.sourceCategory source.targetCategory route.reverse #[one, two] zero,
      Node.retainedRoute source.sourceCategory source.targetCategory route #[two, one] zero,
      Node.retainedRoute source.sourceCategory source.targetCategory route #[one, two] one] do
    if ← QuestionIdentity.equivalentNode retained changed then
      throwError "a retained structural application, endpoint or route was erased"
  let applied := Node.operationApply ⟨"comparison.operation"⟩ #[zero] #[one] two zero
  if ← QuestionIdentity.equivalentNode applied
      (.operationApply ⟨"comparison.operation"⟩ #[] #[zero, one] two zero) then
    throwError "declaration parameters and operation operands lost their boundary"
  let presentation := Node.presentationApply ⟨"comparison.presentation"⟩ #[zero] false one two zero
  for changed in #[
      Node.presentationApply ⟨"comparison.presentation"⟩ #[zero] true one two zero,
      Node.presentationApply ⟨"comparison.presentation"⟩ #[zero] false two one zero,
      Node.presentationApply ⟨"comparison.presentation"⟩ #[one] false one two zero] do
    if ← QuestionIdentity.equivalentNode presentation changed then
      throwError "a presentation's parameters, orientation or exact endpoints disappeared"
  let firstTrace := Std.HashMap.ofArray #[(zero, retained), (one, parameterNode)]
  let reorderedTrace := Std.HashMap.ofArray #[(one, reordered), (zero, retained)]
  unless ← QuestionIdentity.equivalentTrace firstTrace reorderedTrace do
    throwError "trace insertion order changed the retained request"
  let duplicateProofKeys := Std.HashMap.ofArray #[(proof, retained), (otherProof, retained)]
  let oneProofKey := Std.HashMap.ofArray #[(proof, retained)]
  if ← QuestionIdentity.equivalentTrace duplicateProofKeys oneProofKey then
    throwError "proof-irrelevant trace keys silently removed a retained operation"
  let question : Question := .judgement "comparison" #[zero] #[] #[``Nat]
  let claim := Claim.judged question (mkConst ``True) (some true) "display"
  let prepared : TypedQuestion := {
    claim := claim, trace := firstTrace, identity := ("cached identity", "display"),
    mathematicalRevision := "revision label" }
  let relabeled := { prepared with
    trace := reorderedTrace
    identity := ("different cached identity", "other display")
    mathematicalRevision := "other label" }
  unless ← QuestionIdentity.equivalentTypedQuestion prepared relabeled do
    throwError "cached fingerprints, display text or revision labels replaced direct comparison"
  for changed in #[
      { prepared with claim := .judged question (mkConst ``False) (some true) "display" },
      { prepared with claim := .judged question (mkConst ``True) (some false) "display" },
      { prepared with trace := firstTrace.insert zero presentation }] do
    if ← QuestionIdentity.equivalentTypedQuestion prepared changed then
      throwError "one cached fingerprint concealed a changed evaluated claim or operation tree"

/- Compare two actual complete reader requests, including their selected structure and
operation traces. This observes reading mechanics and evaluates no mathematical answer. -/
run_cmd withoutModifyingEnv <| liftTermElabM do
  let .ok statement := Parser.runParserCategory (← getEnv) `cas_stmt
      "assert |Fin(3) in FiniteSets| = 3"
    | throwError "the complete-reading comparison fixture did not parse"
  let first ← interpret {} statement
  let second ← interpret {} statement
  unless ← QuestionIdentity.equivalentTypedQuestion first second do
    throwError "two complete readings of the same selected request compare differently"

/- The extended trace schema carries derived category bundles, selected construction
arguments and every chosen lift/cell component. These inert records exercise retention,
not the mathematics or execution of any registered construction. -/
run_cmd liftTermElabM do
  let zero := mkNatLit 0
  let one := mkNatLit 1
  let two := mkNatLit 2
  let proof ← instantiateMVars (← elabTermAndSynthesize (← `(Eq.refl (0 : Nat))) none)
  let alternate ← instantiateMVars
    (← elabTermAndSynthesize (← `(Eq.symm (Eq.refl (0 : Nat)))) none)
  let different ← instantiateMVars (← elabTermAndSynthesize (← `(Eq.refl (1 : Nat))) none)
  let context : CategoryContext := {
    expression := .construct ⟨"comparison.context"⟩ #[.category (.atom ⟨"comparison.base"⟩)]
    bundle := mkConst ``Nat }
  let otherBundle := { context with bundle := mkConst ``Int }
  let otherExpression := { context with expression := .atom ⟨"comparison.base"⟩ }
  let route : Array EdgeRef := #[.functor ⟨"comparison.route"⟩]
  let constructors : Array ConstructorId := #[⟨"comparison.first"⟩, ⟨"comparison.second"⟩]
  let retainedLift := Node.selectedLift ⟨"comparison.lift"⟩ #[zero] one two proof
  unless ← QuestionIdentity.equivalentNode retainedLift
      (.selectedLift ⟨"comparison.lift"⟩ #[zero] one two alternate) do
    throwError "a selected lift retained the implementation of the same proof"
  let changes : Array (Node × Node) := #[
    (.contextualRoute context context route #[zero] one false,
      .contextualRoute otherBundle context route #[zero] one false),
    (.contextualRoute context context route #[zero] one false,
      .contextualRoute context context route #[zero] one true),
    (.contextualComposition context zero one zero one two,
      .contextualComposition otherExpression zero one zero one two),
    (.contextualComposition context zero one zero one two,
      .contextualComposition context zero one zero two two),
    (.contextualArrow context zero one two, .contextualArrow context zero two one),
    (.contextualIdentity context zero, .contextualIdentity otherBundle zero),
    (.structuredProjection zero "leg" none, .structuredProjection zero "leg" (some 0)),
    (.structuredProjection zero "leg" (some 0), .structuredProjection zero "leg" (some 1)),
    (.construction ⟨"comparison.construction"⟩ #[zero] one,
      .construction ⟨"comparison.construction"⟩ #[one] one),
    (.constructionMap ⟨"comparison.construction"⟩ #[zero] one two zero,
      .constructionMap ⟨"comparison.construction"⟩ #[zero] two one zero),
    (.categoryParameter ⟨"comparison.category"⟩ #[zero],
      .categoryParameter ⟨"comparison.category"⟩ #[one]),
    (.functorParameter ⟨"comparison.functor"⟩ #[zero],
      .functorParameter ⟨"comparison.functor"⟩ #[one]),
    (.cartesian ⟨"comparison.transport"⟩ #[zero] one two "hom",
      .cartesian ⟨"comparison.transport"⟩ #[one] one two "hom"),
    (.cartesian ⟨"comparison.transport"⟩ #[zero] one two "hom",
      .cartesian ⟨"comparison.transport"⟩ #[zero] two two "hom"),
    (.cartesian ⟨"comparison.transport"⟩ #[zero] one two "source",
      .cartesian ⟨"comparison.transport"⟩ #[zero] one two "target"),
    (.coreObject context zero, .coreObject otherBundle zero),
    (.coreIso context zero one one two, .coreIso context zero one two one),
    (retainedLift, .selectedLift ⟨"comparison.lift"⟩ #[one] one two proof),
    (retainedLift, .selectedLift ⟨"comparison.lift"⟩ #[zero] one two different),
    (.liftProjection zero "inclusion", .liftProjection zero "object"),
    (.liftFactor zero one two proof, .liftFactor zero two two proof),
    (.liftFactor zero one two proof, .liftFactor zero one two different),
    (.cellComponent ⟨"comparison.cell"⟩ #[zero] constructors false one,
      .cellComponent ⟨"comparison.cell"⟩ #[zero] constructors.reverse false one),
    (.cellComponent ⟨"comparison.cell"⟩ #[zero] constructors false one,
      .cellComponent ⟨"comparison.cell"⟩ #[zero] constructors true one),
    (.cellEndpoint ⟨"comparison.cell"⟩ #[zero] constructors false false one,
      .cellEndpoint ⟨"comparison.cell"⟩ #[zero] constructors false true one)]
  for (before, after) in changes do
    if ← QuestionIdentity.equivalentNode before after then
      throwError "a derived context, selected construction, lift or cell field was erased"

/- Failure labels are stage data, not a precedence over tags nested in diagnostics. -/
run_cmd liftTermElabM do
  for outer in Stratum.all do
    for inner in Stratum.all do
      let failure : TermElabM Unit :=
        throwStratum outer (MessageData.tagged inner.tag "nested cause")
      let (kind, conflicts, execution) ← tryCatchRuntimeEx
        (failure *> pure (InterpretationFailureKind.invalid, false, ExecutionOutcome.holds))
        fun error => return (Exception.interpretationKind error,
          Exception.hasConflictingStrata error, ← executionFailure error)
      if outer == inner then
        let expected := match outer with
          | .invalid => InterpretationFailureKind.invalid
          | .semanticAmbiguity => .ambiguous
          | _ => .internal
        unless kind == expected && !conflicts do
          throwError "repeated context tags changed the original failure kind"
        let executionKind := match outer with
          | .noImplementation | .ambiguousRealization => "gap"
          | .unavailable => "unavailable"
          | .malformed => "malformed"
          | _ => "internal"
        unless execution.toOutcome.kind == executionKind do
          throwError "execution accepted a semantic label or changed a computational stratum"
      else
        unless kind == .internal && conflicts && execution.toOutcome.kind == "internal" do
          throwError "conflicting failure tags were resolved by tag precedence"
  let legacy : TermElabM Unit := throwSemanticAmbiguity
    (MessageData.tagged Stratum.semanticAmbiguity.tag "same semantic ambiguity")
  let kind ← tryCatchRuntimeEx (legacy *> pure InterpretationFailureKind.internal)
    fun error => pure (Exception.interpretationKind error)
  unless kind == .ambiguous do
    throwError "the two public ambiguity spellings became conflicting failure kinds"
  let conflict : TermElabM Unit := throwSemanticAmbiguity
    (MessageData.tagged Stratum.noImplementation.tag "computation failure")
  let kind ← tryCatchRuntimeEx (conflict *> pure InterpretationFailureKind.invalid)
    fun error => pure (Exception.interpretationKind error)
  unless kind == .internal do
    throwError "a computational exception acquired a semantic label from its context"
  let textOnly : TermElabM Unit := throwError "not a valid call: arbitrary diagnostic text"
  let kind ← tryCatchRuntimeEx (textOnly *> pure InterpretationFailureKind.invalid)
    fun error => pure (Exception.interpretationKind error)
  unless kind == .internal do
    throwError "diagnostic text was mistaken for a mathematical invalidity judgment"
  let mixed : Language.M Bool := throwStratum .noImplementation
    (MessageData.tagged Stratum.invalid.tag "nested semantic cause")
  for trial in #[parameterCompatible mixed,
      (do discard <| optionalReading mixed; pure false)] do
    let propagated ← tryCatchRuntimeEx (trial.run {} *> pure false)
      fun error => pure (Exception.interpretationKind error == .internal)
    unless propagated do
      throwError "a speculative reader swallowed a mixed-stage error as inapplicability"
