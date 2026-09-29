/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CasLeaves.Lattices.Valued.Actions
public import CasCatalogue.ResolveSyntax
public meta import CasLeaves.Lattices.Valued.Actions
public meta import CasCatalogue.ResolveSyntax

@[expose] public section

/-!
# CC-ACTION acceptance: lattices to sets by composition

`Lattice(ℤ, ℤ) → BilinModule(ℤ, ℤ) → Mod_ℤ → ∫ᶜ Mod → Sets` is formed by ordinary composition of
registered functors, both as a `FunctorExpr` and as an executable action; no lattice-to-set
functor or action is registered. The composite action on a concrete lattice returns the same set
handle as applying the four actions in turn, and by `RealizedAction.comp` its denotation is the
composite Mathlib functor applied to the lattice's denotation.
-/

open CategoryTheory
open LeanCategories.Modules.Bilinear.Valued LeanCategories.Lattices.Valued
open CasCatalogue.Foundation.Actions CasCatalogue.Modules.Actions
open CasCatalogue.Modules.CatalogueRegistration
open CasCatalogue.Modules.Bilinear.Valued.Actions CasCatalogue.Lattices.Valued.Actions

namespace CasCatalogue.Lattices.Valued.ActionProbes

/-- The composite as a symbolic functor expression: ordinary composition of registered functors. -/
def latticeToSetsExpr :
    FunctorExpr Lattices.Valued.Catalogue.Lattice Foundation.Sets :=
  .comp Lattices.Valued.Catalogue.LatticeFormForget
    (.comp Modules.Bilinear.Valued.Catalogue.BilinModuleForget
      (.comp Modules.ModulesFibreInclusionExpr Modules.ModulesUnderlyingExpr))

/-- The composite action: ordinary composition of the four registered actions. -/
noncomputable def latticeToSets := formForgetAction.comp (forgetAction.comp
  (fibreInclusionAction.comp underlyingAction))

/-- Its denotation is the composite functor applied to the lattice, through the pasted square
(CC-ACTION, spec §8). -/
noncomputable def latticeToSets_denote (L : LatticeGramHandle) :
    setDenotation.obj (latticeToSets.obj L) ≅
      (modulesUnderlyingDeclaration.{0, 0}.obj
        ((modulesFibreInclusionDeclaration.{0, 0} (RingCat.of ℤ)).obj
          ((forget ℤ ℤ).obj ((isLattice ℤ ℤ).ι.obj (latticeGramDenotation.obj L))))) :=
  latticeToSets.objIso L

/-- The `A₂` root lattice. -/
def a2 : LatticeGramHandle := ⟨⟨2, !![2, -1; -1, 2]⟩, by decide⟩

/-- The `E₈` lattice, by its Cartan matrix. -/
def e8 : LatticeGramHandle :=
  ⟨⟨8, !![ 2, -1,  0,  0,  0,  0,  0,  0;
           -1,  2, -1,  0,  0,  0,  0,  0;
            0, -1,  2, -1,  0,  0,  0, -1;
            0,  0, -1,  2, -1,  0,  0,  0;
            0,  0,  0, -1,  2, -1,  0,  0;
            0,  0,  0,  0, -1,  2, -1,  0;
            0,  0,  0,  0,  0, -1,  2,  0;
            0,  0, -1,  0,  0,  0,  0,  2]⟩, by decide⟩

/-- The isometry of `A₂` exchanging the two simple roots. -/
def a2Swap : GramIsometry a2.form a2.form := ⟨!![0, 1; 1, 0], by decide⟩

/-- The same isometry, as a morphism handle of lattices. -/
noncomputable def a2SwapHom : @Quiver.Hom LatticeGramHandles _ a2 a2 :=
  InducedCategory.homMk (ObjectProperty.homMk (gramDenotation.map a2Swap.toHom))

#guard (exec% (latticeToSets.obj a2) : SetHandle) == .intPow 2
#guard (exec% (latticeToSets.obj e8) : SetHandle) == .intPow 8
#guard (exec% (latticeToSets.obj a2) : SetHandle) ==
  exec% (underlyingAction.obj (fibreInclusionAction.obj (forgetAction.obj (formForgetAction.obj a2))))
#guard (exec% (latticeToSets.obj e8) : SetHandle) ==
  exec% (underlyingAction.obj (fibreInclusionAction.obj (forgetAction.obj (formForgetAction.obj e8))))

/- The composite morphism action computes: the swap acts on `ℤ²` by exchanging coordinates, and
agrees with applying the four morphism actions in turn. -/
#guard List.ofFn (n := 2) ((exec% (latticeToSets.map a2SwapHom)).hom ![3, 5]) == [5, 3]
#guard List.ofFn (n := 2) ((exec% (latticeToSets.map a2SwapHom)).hom ![3, 5]) ==
  List.ofFn (n := 2) ((exec% (underlyingAction.map (fibreInclusionAction.map (forgetAction.map
    (formForgetAction.map a2SwapHom))))).hom ![3, 5])

/-- A registered functor that is not the one the action realizes. -/
noncomputable def wrongFunctorAction := fibreInclusionAction

open Lean Meta Elab Command in
run_cmd
  liftTermElabM do
    let state ← registryState
    -- No lattice-to-set functor is registered: the composite is the only route.
    if state.functors.any fun f =>
        f.source.syntacticEq Lattices.Valued.Catalogue.Lattice &&
          f.target.syntacticEq Foundation.Sets then
      throwError "a lattice-to-set functor is registered"
    -- Every factor of the composite carries a registered action.
    for id in [FunctorId.latticeFormForget, FunctorId.bilinModuleForget,
        FunctorId.modulesFibreInclusion, FunctorId.modulesUnderlying] do
      unless state.actions.any (·.edge == .functor id) do
        throwError "registered functor {id.raw} carries no action"
    let rejects (entry : RegistryEntry) : MetaM Bool := do
      try
        validateRegistryEntryDeclaration entry
        pure false
      catch _ => pure true
    -- An action is accepted only for the functor it realizes.
    unless ← rejects (.action
        { id := ⟨"act.probe.wrong_functor"⟩, edge := .functor FunctorId.modulesUnderlying
          realization := ``wrongFunctorAction }) do
      throwError "the fibre inclusion's action was accepted for the underlying-set functor"
    unless ← rejects (.action
        { id := ⟨"act.probe.not_an_action"⟩, edge := .functor FunctorId.modulesUnderlying
          realization := ``a2 }) do
      throwError "a non-action was accepted as an action"
    unless ← rejects (.action
        { id := ⟨"act.probe.unregistered"⟩, edge := .functor ⟨"fun.probe.unregistered"⟩
          realization := ``underlyingAction }) do
      throwError "an action for an unregistered functor was accepted"
    -- Positive control.
    if ← rejects (.action
        { id := ⟨"act.probe.control"⟩, edge := .functor FunctorId.modulesUnderlying
          realization := ``underlyingAction }) then
      throwError "the underlying-set action was rejected"

end CasCatalogue.Lattices.Valued.ActionProbes
