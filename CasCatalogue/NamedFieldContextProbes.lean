module

import CasCatalogue.Language
meta import CasCatalogue.Language

open Lean Meta Elab Term CasCatalogue CasCatalogue.Language

/- The accepted map supplies a full structured coefficient object. Reading its point keeps
that provenance and the original registered map, rather than inventing a carrier identity. -/
run_elab do
  let state ← registryState
  for text in #["F9x_constants(2)", "F9y_constants(2)"] do
    let .ok parsed := Parser.runParserCategory (← getEnv) `cas_term text
      | throwError "the supplied-field input did not parse"
    let trace ← Trace.new
    discard <| (eval {} parsed).run { trace := some trace }
    let name := (text.splitOn "(").head!
    let some entry := state.morphisms.find? (·.name == name)
      | throwError "the registered map is absent"
    let mut retained := false
    let mut context := false
    for (_, node) in (← trace.get).toArray do
      match node with
      | .namedMorphism id params =>
          if id == entry.id && params.isEmpty then retained := true
      | .parameterEquivalence _ _ sources =>
          if !sources.isEmpty then context := true
      | _ => pure ()
    unless retained && context do
      throwError "the map lost its original identity or full supplied structured context"

    let semantic ← instantiateFresh entry.declaration
    let type ← inferType semantic
    let some source := match type.getAppFn.constName?, type.getAppArgs with
        | some ``Quiver.Hom, #[_, _, x, _] => some x
        | _, _ => none
      | throwError "the original map has no full source"
    let some sets := state.categories.find? (·.id == CategoryId.sets)
      | throwError "the set category is absent"
    let rejected ← try
      discard <| (recognize state source sets).run {}
      pure false
    catch error =>
      if (← Outcome.ofException error).kind == "invalid" then pure true else throw error
    unless rejected do
      throwError "an unsupported bare carrier acquired a structured source without context"
