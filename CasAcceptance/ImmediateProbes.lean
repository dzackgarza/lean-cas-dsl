/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CasAcceptance.Standard
public meta import CasAcceptance.Standard

@[expose] public section

/-!
# Acceptance for `cc-immediate` (CC-IMMEDIATE, #53 §5)

* A leaf may not register a structural functor that is already a composite: `Lattice → Mod_R`
  defined as the inclusion into formed modules followed by their forgetful functor is rejected,
  and the diagnostic names the existing composite.
* A method may not be declared below its lowest generating level: a "formed-module cardinality"
  defined as the one cardinality pulled back along the structural route is rejected, naming
  `meth.cardinality` and the route.
* Controls: the registered rows, re-validated, pass, including a second port with the same
  endpoints as an existing route (the ring's additive port).
-/

open CategoryTheory Lean Meta Elab Command
open LeanCategories LeanCategories.Lattices.Valued
open CasCatalogue.Lattices.Valued.CatalogueRegistration
open CasCatalogue.Modules.Bilinear.Valued.CatalogueRegistration
open CasCatalogue.Modules.CatalogueRegistration

namespace CasCatalogue.ImmediateProbes

noncomputable section

universe u

/-- `Lattice(R,W) → Mod_R`, written out as the composite it is. -/
def latticeToModules (R : Type u) [CommRing R] (W : Type u) [AddCommGroup W] [Module R W] :
    latticeCategory R W ⟶ Modules.Mathlib.ModulesOf (RingCat.of R) :=
  ((isLattice R W).ι ⋙ LeanCategories.Modules.Bilinear.Valued.forget R W).toCatHom

def LatticeToModulesExpr : FunctorExpr Lattices.Valued.Catalogue.Lattice Modules.Modules :=
  .atomic ⟨"fun.probe.lattice_to_modules"⟩

def latticeToModulesRealization (R : Type u) [CommRing R] (W : Type u) [AddCommGroup W]
    [Module R W] :
    FunctorRealization LatticeToModulesExpr (latticeCategory R W)
      (Modules.Mathlib.ModulesOf (RingCat.of R)) (latticeToModules R W).toFunctor :=
  { sourceRealization := latticeRealization R W
    targetRealization := modulesRealization (RingCat.of R) }

/-- A "formed-module cardinality": the one cardinality pulled back along the structural route. -/
def bilinCardinality (R : Type u) [CommRing R] (W : Type u) [AddCommGroup W] [Module R W] :
    Constructors.core (bilinModuleCategory R W) ⥤
      CasCatalogue.Foundation.Cardinality.cardinalsCategory.{u} :=
  Functor.core ((bilinModuleForgetDeclaration R W).toFunctor ⋙
      modulesFibreInclusionDeclaration.{u, u} (RingCat.of R) ⋙
      modulesUnderlyingDeclaration.{u, u}) ⋙
    CasCatalogue.Foundation.Cardinality.setsCardinality.{u}

end

run_cmd liftTermElabM do
  let state ← registryState
  let failure (check : MetaM Unit) : MetaM (Option String) := do
    try check; pure none
    catch err => pure (some (← err.toMessageData.toString))
  -- A composite registered as a new structural functor is rejected, naming the composite.
  let duplicate : FunctorEntry :=
    { id := ⟨"fun.probe.lattice_to_modules"⟩
      source := Lattices.Valued.Catalogue.Lattice
      target := Modules.Modules
      declaration := ``latticeToModules
      realization := ``latticeToModulesRealization
      expression := LatticeToModulesExpr
      structural := true }
  match ← failure (validateRegistryEntryDeclaration (.functor duplicate)) with
  | some message =>
      unless message.contains "fun.lattice.forget_form ⋙ fun.bilin_module.forget" do
        throwError "the rejection does not name the existing composite: {message}"
  | none => throwError "a duplicate structural composite was accepted"
  -- A method below its generating level is rejected, naming the method and the route.
  let some bilin := state.categories.find? (·.id.raw == "cat.bilin_module")
    | throwError "cat.bilin_module is not registered"
  let probeFunctor : FunctorEntry :=
    { id := ⟨"fun.probe.bilin_cardinality"⟩
      source := .construct ⟨"ctor.core"⟩ #[.category bilin.expression]
      target := CasCatalogue.Foundation.Cardinality.Cardinals
      declaration := ``bilinCardinality
      realization := ``bilinCardinality
      expression := .atomic ⟨"fun.probe.bilin_cardinality"⟩ }
  let probeState := { state with functors := state.functors.push probeFunctor }
  let lowMethod : MethodEntry :=
    { id := ⟨"meth.probe.bilin_cardinality"⟩, name := "cardinality", owner := bilin.expression
      functor := probeFunctor.id, shape := .isoInvariant }
  match ← failure (validateMethodEntry probeState lowMethod) with
  | some message =>
      unless message.contains "meth.cardinality" &&
          message.contains "fun.bilin_module.forget ⋙ fun.modules.fibre_inclusion" do
        throwError "the rejection does not name the method and route: {message}"
  | none => throwError "a method below its generating level was accepted"
  -- Controls: registered rows re-validate.
  for id in ["fun.lattice.forget_form", "fun.rings.additive_group", "fun.modules.underlying"] do
    let some row := state.functor? ⟨id⟩ | throwError "{id} is not registered"
    if let some message ← failure (validateRegistryEntryDeclaration (.functor row)) then
      throwError "registered row {id} fails re-validation: {message}"
  for method in state.methods do
    if let some message ← failure (validateRegistryEntryDeclaration (.method method)) then
      throwError "registered method {method.id.raw} fails re-validation: {message}"

end CasCatalogue.ImmediateProbes
