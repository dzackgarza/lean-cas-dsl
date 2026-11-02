/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCategories.Catalogue.Semantics
public import CasCatalogue.Semantic
public meta import LeanCategories.Catalogue.Semantics
public meta import CasCatalogue.Semantic

@[expose] public section

/-!
# Constructor-induced comparison acceptance

The independently registered ring-carrier comparison is interpreted through `Arr`, `Core`, and
nested combinations, without registering the resulting cells. Each resulting natural
isomorphism is checked at a fixed ring object. The source declaration must remain in its proof,
and a missing constructor interface or a cell with unrelated endpoints is rejected.

A fresh constructor registration using an existing mathematical construction exercises the
same generic consumer without adding an ID-specific case to it.
-/

open CategoryTheory Lean Meta Elab Term Command

namespace CasCatalogue.ConstructorComparisonProbes

run_cmd liftTermElabM do
  let state ← registryState
  let some cell := state.cells.find? (·.id.raw == "cmp.rings.carrier")
    | throwError "the ring-carrier comparison is not registered"
  let some arrow := state.constructor? ConstructorId.arrow
    | throwError "the arrow constructor is not registered"
  let fresh : ConstructorId := ⟨"ctor.probe.independent_arrows"⟩
  let extension := { arrow with id := fresh }
  validateConstructor extension
  let extended := { state with constructors := state.constructors.push extension }
  let contexts : Array (Array ConstructorId) := #[#[], #[ConstructorId.arrow],
    #[ConstructorId.core], #[ConstructorId.arrow, ConstructorId.core],
    #[ConstructorId.core, ConstructorId.arrow], #[fresh, ConstructorId.core]]
  for constructors in contexts do
    let source := RouteComparison.mapCategory constructors cell.source
    let target := RouteComparison.mapCategory constructors cell.target
    let leftRefs := RouteComparison.mapRefs constructors cell.left
    let rightRefs := RouteComparison.mapRefs constructors cell.right
    let some leftEdges := extended.routeEdges? source target leftRefs
      | throwError "the constructor did not derive its left structural route"
    let some rightEdges := extended.routeEdges? source target rightRefs
      | throwError "the constructor did not derive its right structural route"
    let left : Route := { source, target, steps := leftEdges }
    let right : Route := { source, target, steps := rightEdges }
    let #[witness] := extended.comparisonWitnessesFrom left right
      | throwError "the mapped routes do not have exactly their accepted comparison"
    unless witness.cell == cell.id && witness.constructors == constructors &&
        witness.before.isEmpty && witness.after.isEmpty do
      throwError "the derived comparison lost its exact constructor provenance"
    let mut receiver := Lean.mkConst ``CasCatalogue.Algebra.NamedRings.ringIntegers
    for constructor in constructors.reverse do
      receiver ← if constructor == ConstructorId.core then
        mkAppM ``CategoryTheory.Core.mk #[receiver]
      else
        mkAppM ``CategoryTheory.Arrow.mk
          #[← mkAppM ``CategoryTheory.CategoryStruct.id #[receiver]]
    let #[comparison] ← Semantic.validateRouteComparisons extended #[witness] (some receiver)
      | throwError "the derived comparison did not retain one typed proof"
    unless (comparison.find? (·.isConstOf cell.declaration)).isSome do
      throwError "the constructor comparison discarded its accepted source cell"
    if comparison.hasMVar || comparison.hasLevelMVar then
      throwError "the constructor comparison lost selected parameters"
    let component ← mkAppHere ``CategoryTheory.Iso.app #[comparison, receiver]
    check component
    let withoutCell := { extended with cells := extended.cells.filter (·.id != cell.id) }
    unless (withoutCell.comparisonWitnessesFrom left right).isEmpty do
      throwError "constructor actions inferred a comparison without its accepted source cell"
    if let some constructor := constructors[0]? then
      let incomplete := { extended with
        constructors := extended.constructors.map fun (entry : ConstructorEntry) =>
          if entry.id == constructor then { entry with compositionComparison := none } else entry }
      unless (incomplete.comparisonWitnessesFrom left right).isEmpty do
        throwError "constructor comparison omitted its required composition interface"
  -- Empty composites use the accepted identity comparison, not an assumed strict action.
  for constructor in #[ConstructorId.arrow, ConstructorId.core] do
    let source ← Semantic.routeFunctor state cell.left
    let identity ← identityOnSourceOf source
    let comparison ← Semantic.constructorRouteComparison state constructor #[] identity
    let some row := state.constructor? constructor | throwError "missing constructor"
    let some name := row.identityComparison | throwError "missing identity comparison"
    unless (comparison.find? (·.isConstOf name)).isSome do
      throwError "an empty constructor route discarded its accepted identity comparison"
    check comparison
  -- Retained prefix and suffix whiskering apply the same cell in the full context.
  let contextual : RouteComparison := {
    cell := cell.id
    constructors := #[ConstructorId.arrow]
    before := #[.constructMap ConstructorId.arrow (.functor FunctorId.commutativeRingsRings)]
    after := #[.constructMap ConstructorId.arrow (.functor FunctorId.setsList)] }
  let receiver ← mkAppM ``CategoryTheory.Arrow.mk #[← mkAppM
    ``CategoryTheory.CategoryStruct.id #[Lean.mkConst ``CasCatalogue.Algebra.NamedCommutativeRings.integers]]
  let #[comparison] ← Semantic.validateRouteComparisons state #[contextual] (some receiver)
    | throwError "contextual comparison did not produce one complete isomorphism"
  unless (comparison.find? (·.isConstOf ``CategoryTheory.Functor.isoWhiskerLeft)).isSome &&
      (comparison.find? (·.isConstOf ``CategoryTheory.Functor.isoWhiskerRight)).isSome do
    throwError "contextual comparison lost one side of its accepted whiskering"
  -- A well-typed isomorphism about another functor is not a route comparison.
  let unrelated := { state with cells := state.cells.map fun entry =>
    if entry.id == cell.id then
      { entry with declaration := `CasCatalogue.Foundation.Lists.listReverseCell }
    else entry }
  let accepted ← try
    discard <| Semantic.routeComparison unrelated { cell := cell.id }
    pure true
  catch _ => pure false
  if accepted then throwError "a comparison with unrelated complete endpoints was accepted"

/- The comparison of formed-module carriers has dependent scalar and value parameters.
The incoming lattice and outgoing fibre inclusion must bind the same full parameters, also
when all three segments are acted on by registered constructors. -/
run_cmd liftTermElabM do
  let state ← registryState
  let some cell := state.cells.find? (·.id.raw == "cell.bilin_module.carrier_routes")
    | throwError "the formed-module carrier comparison is absent"
  for constructors in #[#[], #[ConstructorId.arrow], #[ConstructorId.core],
      #[ConstructorId.arrow, ConstructorId.core], #[ConstructorId.core, ConstructorId.arrow]] do
    let witness : RouteComparison := {
      cell := cell.id
      constructors
      before := RouteComparison.mapRefs constructors
        #[.functor ⟨"fun.integral_lattice.forget_form"⟩]
      after := RouteComparison.mapRefs constructors
        #[.functor ⟨"fun.modules.fibre_inclusion"⟩] }
    let mut receiver ← elabTermAndSynthesize (← `(LeanCategories.Lattices.Valued.e8Lattice)) none
    for constructor in constructors.reverse do
      receiver ← if constructor == ConstructorId.core then
        mkAppM ``CategoryTheory.Core.mk #[receiver]
      else
        mkAppM ``CategoryTheory.Arrow.mk
          #[← mkAppM ``CategoryTheory.CategoryStruct.id #[receiver]]
    let #[comparison] ← Semantic.validateRouteComparisons state #[witness] (some receiver)
      | throwError "the dependent contextual comparison did not retain one proof"
    if comparison.hasMVar || comparison.hasLevelMVar then
      throwError "the dependent contextual comparison lost complete selected parameters"
    check comparison

end CasCatalogue.ConstructorComparisonProbes
