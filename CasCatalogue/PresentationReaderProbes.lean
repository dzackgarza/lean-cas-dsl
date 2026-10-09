module

import CasCatalogue.Language
meta import CasCatalogue.Language

open Lean Meta Elab Command Term
open CasCatalogue CasCatalogue.Language

/- Generic reader mechanics: closed accepted presentations with distinguished generators
retain their registered orientation and endpoints in both directions. -/
run_cmd liftTermElabM do
  let state ← registryState
  let mut checked := 0
  for entry in state.presentations do
    let declaration ← mkConstWithFreshMVarLevels entry.declaration
    if (← inferType declaration).isForall then continue
    let some source := state.objects.find? (·.id == entry.source) | continue
    if (← setOf state source).generator.isNone then continue
    let some category := state.categories.find? (·.id == source.category) | continue
    let arrow ← mkAppM ``CategoryTheory.Iso.hom #[declaration]
    let some (actualSource, _) := homEnds? (← inferType arrow)
      | throwError "a registered presentation has no actual source object"
    let sourceValue ← (recognize state actualSource category).run {}
    let carrier ← (carrierObject sourceValue).run {}
    let .object _ _ (some (base, _)) _ _ := carrier | continue
    if base.generator.isNone then continue
    let text := s!"map generator(chosen) along {entry.name}"
    let .ok claimSyntax := Parser.runParserCategory (← getEnv) `cas_stmt
      s!"assert implemented {text}"
      | throwError "the presentation statement failed to parse"
    discard <| (claim {} claimSyntax).run { bound := [(`chosen, sourceValue)] }
    let .ok syntaxValue := Parser.runParserCategory (← getEnv) `cas_term text
      | throwError "the generic presentation surface failed to parse"
    let trace ← Trace.new
    let forward ← (eval {} syntaxValue).run
      { trace := some trace, bound := [(`chosen, sourceValue)] }
    let .element mapValue _ := forward
      | throwError "a presentation did not return an element"
    unless !mapValue.hasMVar && (← isTypeCorrect mapValue) do
      throwError "the presentation forward map is outside its declared signature"
    let .ok backSyntax := Parser.runParserCategory (← getEnv) `cas_term
      s!"map selected back along {entry.name}"
      | throwError "the inverse presentation surface failed to parse"
    let .element inverseValue _ ← (eval {} backSyntax).run
        { trace := some trace, bound := [(`selected, forward)] }
      | throwError "an inverse presentation did not return an element"
    unless !inverseValue.hasMVar && (← isTypeCorrect inverseValue) do
      throwError "the inverse presentation map is outside its declared signature"
    checked := checked + 1
  unless checked > 0 do throwError "no accepted closed generator presentation was read"
