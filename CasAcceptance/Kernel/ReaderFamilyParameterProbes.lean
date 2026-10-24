/- Copyright (c) 2026 Dzack Garza. Released under Apache 2.0 license. -/
module

import CasCatalogue.Language
meta import CasCatalogue.Language
import LeanCategories.Catalogue.Semantics.Foundation.FiniteOrders
meta import LeanCategories.Catalogue.Semantics.Foundation.FiniteOrders
import LeanCategories.Catalogue.Semantics.Independent.ScalarAndFormExtensions
meta import LeanCategories.Catalogue.Semantics.Independent.ScalarAndFormExtensions

/-! Engineering controls for the public named-family reader. The independently
registered objects and morphisms supply all mathematical structures and maps.
These checks retain the exact binding, whole signature and declared data. -/

open Lean Meta Elab Command Term CasCatalogue CasCatalogue.Language

run_cmd liftTermElabM <| withoutErrToSorry do
  let state ← registryState
  let parse (text : String) : TermElabM Syntax := do
    let .ok term := Parser.runParserCategory (← getEnv) `cas_term text
      | throwError "the named-family input did not parse: {text}"
    return term
  let mut selected := #[]
  for (name, declaration) in #[("FinOrder", ``CasCatalogue.Foundation.FiniteOrders.ordinary),
      ("ReverseFinOrder", ``CasCatalogue.Foundation.FiniteOrders.reverse)] do
    withCurrHeartbeats do
      let value ← (eval {} (← parse s!"{name}(5)")).run {}
      let .object handle category (some (row, _)) .. := value
        | throwError "a separately named refinement was not an object"
      unless row.name == name && row.refines.isSome && category.id == CategoryId.linearOrders do
        throwError "the separately named refinement lost its selected row"
      let expected ← mkAppM declaration #[mkNatLit 5]
      unless ← withTransparency .all <| isDefEq handle expected do
        throwError "the refined object changed its full selected structure"
      selected := selected.push handle
  if ← withTransparency .all <| isDefEq selected[0]! selected[1]! then
    throwError "distinct selected orders were identified through their common carrier"
  let candidates := objectBindings state "Fin" none
  unless !candidates.isEmpty && candidates.all (·.refines.isNone) do
    throwError "a named refinement displaced an existing unrefined default"

run_cmd liftTermElabM <| withoutErrToSorry <| withCurrHeartbeats do
  let state ← registryState
  let parse (text : String) : TermElabM Syntax := do
    let .ok term := Parser.runParserCategory (← getEnv) `cas_term text
      | throwError "the dependent family input did not parse: {text}"
    return term
  let mut scope : Language.Scope := {}
  for (name, text) in #[("Q", "ℚ in CommutativeRings"),
      ("row", "[1, 0] in RectangularMatrices(1, 2, Q)")] do
    scope := scope.insert name.toName (← parse text)
  let some entry := state.morphisms.find? (·.name == "row_linear_map")
    | throwError "the independently registered row map is absent"
  let trace ← Trace.new
  let value ← (eval scope (← parse "row_linear_map(2, Q, row)")).run { trace := some trace }
  let (hom, source, target, context, _, _) ← (morphismContext value).run {}
  CategoryContext.checkMorphism context hom source target
  unless !hom.hasMVar && !hom.hasLevelMVar && (← isTypeCorrect hom) do
    throwError "the complete row map retained unresolved parameters"
  let q ← (eval scope (← parse "Q")).run {}
  let row ← (eval scope (← parse "row")).run {}
  let qHandle ← (semanticObject q).run {}
  let constant ← mkConstWithFreshMVarLevels entry.declaration
  let (parameters, _, _) ← forallMetaTelescopeReducing (← inferType constant)
  unless parameters.size == 3 do throwError "the complete row signature changed"
  discard <| isDefEq parameters[0]! (mkNatLit 2)
  discard <| isDefEq parameters[1]! qHandle
  let matrix ← (typedParameter (← inferType parameters[2]!) row).run {}
  let expected ← mkAppM entry.declaration #[mkNatLit 2, qHandle, matrix]
  unless ← withTransparency .all <| isDefEq hom expected do
    throwError "the row data parameter was not retained in the complete map"
  let some (.namedMorphism address _) ← trace.node? hom
    | throwError "the complete row map lost its selected callable address"
  unless address == entry.id.raw do
    throwError "a different primitive address replaced the selected row map"
