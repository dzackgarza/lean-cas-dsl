module

import CasCatalogue.Language
meta import CasCatalogue.Language

open Lean Meta Elab Command Term
open CasCatalogue CasCatalogue.Language

/- b0-typed-application: a supplied power-object target retains its selected base before
the predicate is read. These checks judge reader mechanics, not values of primitives. -/
run_cmd liftTermElabM do
  let .ok binding := Parser.runParserCategory (← getEnv) `cas_stmt "let f := x in ℚ[x]"
    | throwError "the polynomial binding did not parse"
  let some (name, value) ← letBinding? binding | throwError "the binding is absent"
  let scope : Language.Scope := ({} : Language.Scope).insert name value
  let .ok term := Parser.runParserCategory (← getEnv) `cas_term "∫ f dx"
    | throwError "the primitive expression did not parse"
  let rings ← (ringBindings scope term).run {}
  let readTarget := fun (text : String) => do
    let .ok stx := Parser.runParserCategory (← getEnv) `cas_term text
      | throwError "the explicit result context did not parse"
    (eval {} stx).run {}
  let target ← readTarget "𝒫(ℚ[x])"
  let trace ← Trace.new
  let result ← (eval scope term none (some target)).run { bound := rings, trace := some trace }
  let .element hom retained := result | throwError "the result is not a generalized element"
  unless retained.declarations == target.declarations && retained.terms == target.terms do
    throwError "the declared application discarded its supplied complete result context"
  let some (_, base) ← (powerSetOf? result).run {}
    | throwError "the result lost its power-object base"
  let .object _ _ (some (row, _)) _ _ := base
    | throwError "the explicit base declaration was erased"
  let generic := Value.element (← (identityAt base).run {}) base
  let some (_, _, _, address) ← (applicationOf? generic).run {}
    | throwError "the explicitly selected base lost its published callable"
  unless row.id.raw == "obj.sets.polynomials" && address == row.applicationAddress do
    throwError "the result context selected a different callable declaration"
  let some (_, actualTarget) := homEnds? (← inferType hom)
    | throwError "the result has no actual categorical target"
  unless ← isDefEq actualTarget (← (semanticObject target).run {}) do
    throwError "the result changed its original declared target"
  for (term, _) in (← trace.get).toArray do
    unless !term.hasMVar && !term.hasLevelMVar && (← isTypeCorrect term) do
      throwError "the contextual reading retained incomplete or ill-typed data"

  -- Erasing the supplied declaration cannot recover its callable from a bare carrier.
  let .object handle category .. := base | throwError "the selected base is not an object"
  let bare ← withTransparency .all <| whnf handle
  let anonymous := Value.object bare category none none none
  let generic := Value.element (← (identityAt anonymous).run {}) anonymous
  if (← (applicationOf? generic).run {}).isSome then
    throwError "an unselected carrier acquired a callable declaration"

  -- A supplied result context constrains the original signature; it cannot replace it.
  let incompatible ← readTarget "𝒫(ℤ[x])"
  let rejected ← try
    discard <| (eval scope term none (some incompatible)).run { bound := rings }
    pure false
  catch error =>
    if Exception.stratum? error == some .invalid then pure true else throw error
  unless rejected do throwError "an incompatible result context changed the declared operation"
