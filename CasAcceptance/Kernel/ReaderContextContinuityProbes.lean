module

import CasCatalogue.Language
meta import CasCatalogue.Language
import LeanCategories.Catalogue.Semantics.Independent.ScalarAndFormExtensions
meta import LeanCategories.Catalogue.Semantics.Independent.ScalarAndFormExtensions

open Lean Meta Elab Term CasCatalogue CasCatalogue.Language

/- A selected carrier action binds the complete source category, including structure
parameters that occur through projections, and retains the original whole arrow. -/
run_elab do
  let .ok parsed := Parser.runParserCategory (← getEnv) `cas_term "degenerate_plane_map()"
    | throwError "the registered complete map did not parse"
  let trace ← Trace.new
  (show M Unit from do
    let original ← eval {} parsed
    let (originalMap, _, _, originalContext, _, _) ← morphismContext original
    let mapped ← carrierMorphism original
    let (mappedMap, _, _, _, _, _) ← morphismContext mapped
    let some (.contextualRoute source _ route applications receiver true) ← trace.node? mappedMap
      | throwError "the carrier action lost its original complete arrow"
    unless !route.isEmpty && route.size == applications.size &&
        applications.all (fun action => !action.hasMVar && !action.hasLevelMVar) &&
        (← withTransparency .all <| isDefEq source.bundle originalContext.bundle) &&
        (← isDefEq receiver originalMap) do
      throwError "the carrier action changed its complete source or ordered applications"
    unless !mappedMap.hasMVar && !mappedMap.hasLevelMVar && (← isTypeCorrect mappedMap) do
      throwError "the complete carrier action is not a closed typed map").run { trace := some trace }

/- Closed data parameters reread inside a binder keep their original global point.
This mechanism works without tracing and cannot admit an arbitrary stage variable. -/
run_elab do
  let parse (text : String) : TermElabM Syntax := do
    let .ok parsed := Parser.runParserCategory (← getEnv) `cas_term text
      | throwError "the staged parameter source did not parse"
    return parsed
  let rowSyntax ← parse "[1, 0] in RectangularMatrices(1, 2, (ℚ in CommutativeRings))"
  let stageSyntax ← parse "ℚ in Sets"
  (show M Unit from do
    let row ← eval {} rowSyntax
    let .element original X := row | throwError "the matrix is not a closed point"
    let target ← semanticObject X
    let stage ← eval {} stageSyntax
    let staged ← withReader (fun context => { context with stage := some stage }) (restage row)
    let .element point _ := staged | throwError "staging lost the matrix point"
    let recovered ← closedParameterPoint point target
    unless recovered == original do
      throwError "staging replaced the exact original parameter point"
    let actual ← typedParameter target staged
    let expected ← typedParameter target row
    unless !actual.hasMVar && !actual.hasLevelMVar &&
        (← isDefEq (← inferType actual) target) && (← isDefEq actual expected) do
      throwError "staging changed the complete typed declaration parameter"
    let genericPoint ← identityAt X
    let accepted ← parameterCompatible do
      discard <| typedParameter target (.element genericPoint X)
      pure true
    unless !accepted do
      throwError "a generalized variable was admitted as closed declaration data").run {}

/- A selected action on an arrow gives both endpoints the same retained object
view as that action on the original objects. It must not rediscover a carrier path. -/
run_elab do
  let parse (text : String) : TermElabM Syntax := do
    let .ok parsed := Parser.runParserCategory (← getEnv) `cas_term text
      | throwError "the mapped endpoint source did not parse"
    return parsed
  let scalarSyntax ← parse "ZMod(5) in CommutativeRings"
  let scope : Scope := ({} : Scope).insert `Scommutative scalarSyntax
  let mapSyntax ← parse
    "map integerCoefficients(Scommutative) along «fun.commutative_rings.ring»()"
  let viewSyntax ← parse "view Scommutative along «fun.commutative_rings.ring»()"
  let sourceViewSyntax ← parse "view (ℤ in CommutativeRings) along «fun.commutative_rings.ring»()"
  (show M Unit from do
    let selectedSource ← carrierObject (← eval scope sourceViewSyntax)
    let selectedTarget ← carrierObject (← eval scope viewSyntax)
    let (_, _, _, _, source, target) ← morphismContext (← eval scope mapSyntax)
    for (endpoint, selected) in #[(source, selectedSource), (target, selectedTarget)] do
      unless ← identityCarrierView (← carrierObject endpoint) selected do
        throwError "the mapped endpoint lost the independently selected carrier view"
      let .object _ _ _ _ (some (_, original, route, _, arguments)) := endpoint
        | throwError "the mapped endpoint lost its full selected action"
      unless route == #[.functor ⟨"fun.commutative_rings.ring"⟩] && arguments.size == 1 do
        throwError "the mapped endpoint lost its actual edge or parameter application"
      let (replayed, _) ← retainedActions (← registryState)
        (← semanticObject original) route arguments
      unless ← isDefEq replayed (← semanticObject endpoint) do
        throwError "the retained action does not give the complete mapped endpoint").run {}

/- A numeral's chosen arithmetic owner does not suppress a named set's independent
order binding. Explicit structure selections and nearer same-name bindings remain fixed. -/
run_elab do
  let parse (text : String) : TermElabM Syntax := do
    let .ok parsed := Parser.runParserCategory (← getEnv) `cas_term text
      | throwError "the named-operation source did not parse"
    return parsed
  let predicate ← parse "{n ∈ ℤ | n^2 ≤ 9}"
  let selectedRing ← parse "ℤ in Rings"
  (show M Unit from do
    discard <| eval {} predicate
    let carrier ← carrierObject (← eval {} selectedRing)
    let genericPoint ← identityAt carrier
    let selectedAccepted ← withReader (fun context => { context with stage := some carrier }) do
      parameterCompatible do
        discard <| applyOperation "≤" #[.element genericPoint carrier, .nat 9] carrier
        pure true
    unless !selectedAccepted do
      throwError "an explicitly selected ring acquired an unrelated order operation"
    let state ← registryState
    let residue ← object state "ZMod" #[.nat 5] none
    let .element _ source ← toElement (.nat 2) residue
      | throwError "the registered residue numeral lost its selected source"
    let receiver := retainObjectContext residue #[source]
    let some monoids := state.categories.find? (·.id == CategoryId.monoids)
      | throwError "the accepted monoid category is absent"
    let sources ← operationSourceValues receiver (some (monoids.expression, "·"))
    let selectedSources ← operationSourceValues source (some (monoids.expression, "·"))
    unless !selectedSources.isEmpty && sources.size == selectedSources.size &&
        (sources.zip selectedSources).all (fun (left, right) => left.sameSource right) do
      throwError "a nearer multiplication binding reopened unrelated named refinements").run {}

/- Partial views complete only missing binding metadata. Their exact retained
category declaration and all complete selected structures remain checked. -/
run_elab do
  let state ← registryState
  let some rings := state.categories.find? (·.id == CategoryId.rings)
    | throwError "the partial-view control has no registered ring category"
  let some sets := state.categories.find? (·.id == CategoryId.sets)
    | throwError "the partial-view control has no second registered category"
  unless rings.declaration != sets.declaration do
    throwError "the category-declaration negative does not distinguish its declarations"
  let trace ← Trace.new
  (show M Unit from do
    let original ← object state "ℤ" #[] (some rings)
    let .object handle category (some binding) none viewData := original
      | throwError "the partial-view control lost its complete named binding"
    let some node@(.object ..) ← trace.node? handle
      | throwError "the partial-view control has no actual named producer"
    Trace.checkProducerRecord handle node
    let marker := Value.nat 37
    let partialView := retainObjectContext (.object handle category none none none) #[marker]
    let restored ← recognize state handle category #[partialView, original]
    unless restored.sameSelection original &&
        (sourceParameterValues restored).any (·.sameSource partialView) &&
        (sourceParameterValues restored).any (·.sameSource marker) do
      throwError "a correct partial view lost its complete binding or retained context"
    let completed ← recognize state handle category #[partialView]
    unless completed.sameSelection original &&
        (sourceParameterValues completed).any (·.sameSource partialView) do
      throwError "an isolated partial view did not recover its authenticated binding"
    let wrongCategory := { category with declaration := sets.declaration }
    let malformed := retainObjectContext (.object handle wrongCategory none none none) #[marker]
    let differentSelection := Value.object handle category (some binding) (some original) viewData
    for known in #[#[original, malformed], #[malformed], #[original, differentSelection]] do
      let rejected ← try
        discard <| recognize state handle category known
        pure false
      catch error =>
        if CasCatalogue.Exception.isSemanticAmbiguity error then pure true else throw error
      unless rejected do
        throwError "partial-view completion erased a conflicting retained declaration or selection"
    ).run { trace := some trace }
