/- Copyright (c) 2026 Dzack Garza. Released under Apache 2.0 license. -/
module

import CasCatalogue.Language
meta import CasCatalogue.Language

/-! Engineering controls for reusing complete closed file readings across an actual stage. -/

open Lean Meta Elab Command Term CasCatalogue CasCatalogue.Language

run_cmd liftTermElabM <| withoutErrToSorry <| withCurrHeartbeats do
  let parse (text : String) : TermElabM Syntax := do
    let .ok parsed := Parser.runParserCategory (← getEnv) `cas_term text
      | throwError "the closed-binding control did not parse"
    return parsed
  let body ← parse "2 in (ℤ in Rings)"
  let reference ← parse "fixedPoint"
  let scope : Language.Scope := ({} : Language.Scope).insert `fixedPoint body
  let cache ← IO.mkRef ({} : Std.HashMap String Value)
  let trace ← Trace.new
  let context : Ctx := { trace := some trace, closedTerms := some cache }
  let original ← (eval scope reference).run context
  let .element globalPoint target := original
    | throwError "the complete closed binding is not a global point"
  let stage ← (eval {} (← parse "Fin(2) in Sets")).run {}
  let stagePoint ← (identityAt stage).run {}
  let staged ← (eval scope reference).run
    { context with stage := some stage, bound := [(`x, .element stagePoint stage)] }
  let .element point retainedTarget := staged
    | throwError "reading the closed binding at a stage lost its point"
  unless retainedTarget.sameSource target do
    throwError "staging a closed binding replaced its complete selected target"
  let some (.morphismComposition category _ retained _ _ _) ← trace.node? point
    | throwError "the staged reading did not retain the original global point"
  unless category == CategoryId.sets && retained == globalPoint do
    throwError "staging replaced the actual complete global point"
  let some cached := (← cache.get)[shown body]?
    | throwError "the complete closed binding was not retained for reuse"
  unless cached.sameSource original do
    throwError "a staged point overwrote its original global reading"
  let mapSyntax ← parse "(t ↦ t) in (ℤ in Sets) → (ℤ in Sets)"
  let closedMap ← (eval {} mapSyntax).run context
  let some cachedMap := (← cache.get)[shown mapSyntax]?
    | throwError "the complete closed map was not retained for reuse"
  unless cachedMap.sameSource closedMap do
    throwError "closed-map reuse changed its actual full endpoints or provenance"

run_cmd liftTermElabM <| withoutErrToSorry <| withCurrHeartbeats do
  let parse (text : String) : TermElabM Syntax := do
    let .ok parsed := Parser.runParserCategory (← getEnv) `cas_term text
      | throwError "the dependent-binding control did not parse"
    return parsed
  let scope : Language.Scope := ({} : Language.Scope).insert `dependentValue (← parse "x")
  let scope := scope.insert `indirectValue (← parse "dependentValue")
  let reference ← parse "indirectValue"
  let stage ← (eval {} (← parse "Fin(2) in Sets")).run {}
  let identity ← (identityAt stage).run {}
  let constant ← elabTermAndSynthesize
    (← `(TypeCat.ofHom (fun (_ : Fin 2) => (0 : Fin 2)))) none
  unless !(← withTransparency .all <| isDefEq identity constant) do
    throwError "the bound-name control has no distinct generalized points"
  let cache ← IO.mkRef ({} : Std.HashMap String Value)
  let trace ← Trace.new
  for original in #[identity, constant] do
    let expected : Value := .element original stage
    let context : Ctx := {
      trace := some trace, closedTerms := some cache, stage := some stage
      bound := [(`x, expected)] }
    unless usesBoundNames scope context.bound reference do
      throwError "a transitive reference lost its actual bound dependency"
    let actual ← (eval scope reference).run context
    unless actual.sameSource expected do
      throwError "closed reading reuse captured another actual bound value"
  if (← cache.get).contains (shown reference) then
    throwError "a stage-dependent file binding entered the closed reading cache"

/- A member-family application keeps its independently fixed complete result owner. -/
run_cmd liftTermElabM <| withoutErrToSorry <| withCurrHeartbeats do
  let state ← registryState
  let some category := state.categories.find? (·.id == CategoryId.bilWForm)
    | throwError "the member-family control has no formed category"
  let some pairing := state.morphisms.find? (·.name == "formed_pairing")
    | throwError "the member-family control has no registered family"
  let expected ← elabTermAndSynthesize
    (← `(LeanCategories.Modules.Bilinear.Valued.BilWFormCat (CommRingCat.of ℤ))) none
  withLocalDeclD `actualOwner expected fun owner => do
    let trace ← Trace.new
    let selected := Value.object owner category none none none
    let family ← (invariantOf pairing selected).run { trace := some trace }
    let .morphism _ _ _ _ (some (source, target)) := family
      | throwError "the selected complete family lost its endpoints"
    let point ← (identityAt source).run { trace := some trace }
    let .ok receiverSyntax := Parser.runParserCategory (← getEnv) `cas_term "receiver"
      | throwError "the complete receiver reference failed to parse"
    let .ok operandSyntax := Parser.runParserCategory (← getEnv) `cas_term "operand"
      | throwError "the complete operand reference failed to parse"
    let context : Ctx := {
      trace := some trace, stage := some source
      bound := [(`receiver, selected), (`operand, .element point source)] }
    let .element result actualTarget ←
        (callWith {} receiverSyntax pairing.name #[operandSyntax]).run context
      | throwError "the selected complete family did not form an applied point"
    unless actualTarget.sameSource target do
      throwError "member-family application replaced its independently fixed result context"
    let some (domain, codomain) := homEnds? (← inferType result)
      | throwError "the actual family result has no complete Hom endpoints"
    unless (← isTypeCorrect result) &&
        (← isDefEq domain (← (semanticObject source).run context)) &&
        (← isDefEq codomain (← (semanticObject target).run context)) do
      throwError "member-family application changed its original domain or selected target"
