module

import CasCatalogue.Realize
import LeanCategories.Catalogue.Semantics
meta import CasCatalogue.Realize
meta import LeanCategories.Catalogue.Semantics

open Lean Meta Elab Term CasCatalogue CasCatalogue.Language CasCatalogue.Realize

/- Engineering checks of the public ordered product-point encoding. Component
data are arbitrary owned tokens; no leaf runs and no mathematical answer is asserted. -/
run_elab do
  let .ok parsed := Parser.runParserCategory (← getEnv) `cas_term "(1, 2) in ℚ²"
    | throwError "the product-point probe did not parse"
  let trace ← CasCatalogue.Trace.new
  discard <| (eval {} parsed).run { trace := some trace }
  let state ← registryState
  let snapshot ← trace.get
  let mut checked := false
  for (value, node) in snapshot.toArray do
    let .productMediator categoryId presentation domain left right := node | continue
    let some category := state.categories.find? (·.id == categoryId)
      | throwError "the product-point category is absent"
    let cone ← mkAppM ``CategoryTheory.Limits.LimitCone.cone #[presentation]
    let apex ← mkAppM ``CategoryTheory.Limits.Cone.pt #[cone]
    let harness ← Harness.empty
    let component := fun formal token => ({
      form := Form.canonicalMorphism category,
      payload := WirePayload.computed formal (.opaque "engineering-owner" 23 token) } : Wire)
    let first := component left "first retained point"
    let second := component right "second retained point"
    harness.results.modify (·.insert left first |>.insert right second)
    let raw := Json.arr #[first.json, second.json]
    let actual ← realize harness trace "the complete ordered product point" value
    unless actual.json == raw && actual.morphismFramed &&
        actual.owner? == first.owner? && actual.value == value do
      throwError "the product point changed its component data, framing, owner or formal value"
    let (framed, _) ← frameMorphismData harness trace domain apex actual
    unless framed == raw do
      throwError "the ordered product point was wrapped as a graph over its generalized domain"
    -- Existing accepted endpoint comparisons must still be applied once. Their
    -- computational tokens make neither an equality claim nor a representation law.
    let source ← realizeEndpoint harness trace "the fixed generalized domain" domain
    let target ← realizeEndpoint harness trace "the fixed product target" apex
    let opaqueData := fun token => Backend.ComputationalValue.encode (.opaque token)
    let sourceBackward := opaqueData "retained domain comparison"
    let targetForward := opaqueData "retained target comparison"
    let source := { source with endpointPresentation := some {
      comparison := (← mkAppM ``CategoryTheory.Iso.refl #[domain]),
      forward := opaqueData "domain inverse", backward := sourceBackward } }
    let target := { target with endpointPresentation := some {
      comparison := (← mkAppM ``CategoryTheory.Iso.refl #[apex]),
      forward := targetForward, backward := opaqueData "target inverse" } }
    let cold ← Harness.empty
    cold.results.modify (·.insert left first |>.insert right second
      |>.insert domain source |>.insert apex target)
    let presented ← realize cold trace "the product point with retained endpoint comparisons" value
    let compose := fun a b => Json.mkObj [("ctor", toJson "compose"), ("args", Json.arr #[a, b])]
    let expected := compose (compose sourceBackward raw) targetForward
    unless presented.json == expected && presented.owner? == first.owner? do
      throwError "the product point omitted or reordered a complete endpoint presentation"
    let (framedAgain, _) ← frameMorphismData cold trace domain apex presented
    unless framedAgain == expected do
      throwError "later callable framing repeated a product point's endpoint presentations"
    checked := true
    break
  unless checked do throwError "the probe did not exercise a typed product mediator"
  logInfo "PASS: ordered product-point data, live ownership and complete endpoint presentations"
