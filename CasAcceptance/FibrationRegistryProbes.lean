/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCategories.Catalogue.Semantics.Modules.CatalogueRegistration
public meta import LeanCategories.Catalogue.Semantics.Modules.CatalogueRegistration
public import CasCatalogue.Registry.Extension
public meta import CasCatalogue.Registry.Extension

@[expose] public section

/-!
# Negative probes for the registered module fibration

The registry accepts the fibre inclusion, reindexing and total category of a family only as
the canonical realizations of the registered family (`Catalogue/FamilyFibration.lean`). Each
probe below builds a well-typed but mathematically different realization and checks that
registration rejects it.
-/

namespace CasCatalogue.Modules.FibrationRegistryProbes
open LeanCategories LeanCategories.Modules

open CategoryTheory LeanCategories CasCatalogue CasCatalogue.Modules.CatalogueRegistration

noncomputable section

universe u

/-- A constant functor posing as the fibre inclusion `ι_R`. -/
def constantInclusion (R : RingCat.{u}) :
    Modules.Mathlib.ModulesOf.{u, u} R ⥤ modulesTotalCategory.{u, u} :=
  (Functor.const _).obj
    ((modulesFamilyRealization.{u, u}.fibreInclusionFunctor R).obj (ModuleCat.of R R))

def constantInclusionRealization (R : RingCat.{u}) :
    FunctorRealization Modules.ModulesFibreInclusionExpr (Modules.Mathlib.ModulesOf.{u, u} R)
      modulesTotalCategory.{u, u} (constantInclusion R) :=
  { sourceRealization := modulesRealization R
    targetRealization := modulesTotalRealization }

/-- A constant functor posing as restriction of scalars. -/
def constantReindex (R S : RingCat.{u}) :
    Modules.Mathlib.ModulesOf.{u, u} S ⥤ Modules.Mathlib.ModulesOf.{u, u} R :=
  (Functor.const _).obj (ModuleCat.of R R)

def constantReindexRealization (R S : RingCat.{u}) :
    FunctorRealization Modules.ModulesReindexExpr (Modules.Mathlib.ModulesOf.{u, u} S)
      (Modules.Mathlib.ModulesOf.{u, u} R) (constantReindex R S) :=
  { sourceRealization :=
      modulesFamilyRealization.{u, u}.fibreRealization S
        (arguments := #[.variable ParameterId.s]) (.ringS S)
    targetRealization := modulesRealization R }

/-- A single fibre posing as the total category. -/
def fibreAsTotal (R : RingCat.{u}) := Modules.Mathlib.ModulesOf.{u, u} R

def fibreAsTotalRealization (R : RingCat.{u}) :
    CategoryRealization Modules.ModulesTotal (fibreAsTotal R) := {}

end

open Lean Meta Elab Command in
run_cmd
  liftTermElabM do
    let rejects (entry : RegistryEntry) : MetaM Bool := do
      try
        validateRegistryEntryDeclaration entry
        pure false
      catch _ => pure true
    unless ← rejects (.functor
        { id := FunctorId.modulesFibreInclusion, source := Modules.Modules
          target := Modules.ModulesTotal
          declaration := ``constantInclusion, realization := ``constantInclusionRealization
          expression := Modules.ModulesFibreInclusionExpr }) do
      throwError "a constant functor was accepted as the fibre inclusion"
    unless ← rejects (.functor
        { id := FunctorId.modulesReindex, source := Modules.ModulesAtS
          target := Modules.Modules
          declaration := ``constantReindex, realization := ``constantReindexRealization
          expression := Modules.ModulesReindexExpr }) do
      throwError "a constant functor was accepted as restriction of scalars"
    unless ← rejects (.category
        { id := CategoryId.modulesTotal, declaration := ``fibreAsTotal
          expression := Modules.ModulesTotal, realization := ``fibreAsTotalRealization }) do
      throwError "a single fibre was accepted as the total category"
    -- Positive controls: the canonical rows pass the same validation.
    if ← rejects (.functor
        { id := FunctorId.modulesFibreInclusion, source := Modules.Modules
          target := Modules.ModulesTotal
          declaration := ``modulesFibreInclusionDeclaration
          realization := ``modulesFibreInclusionRealization
          expression := Modules.ModulesFibreInclusionExpr }) then
      throwError "the canonical fibre inclusion was rejected"
    if ← rejects (.functor
        { id := FunctorId.modulesReindex, source := Modules.ModulesAtS
          target := Modules.Modules
          declaration := ``modulesReindexDeclaration
          realization := ``modulesReindexRealization
          expression := Modules.ModulesReindexExpr }) then
      throwError "the canonical reindexing was rejected"
    if ← rejects (.category
        { id := CategoryId.modulesTotal, declaration := ``modulesTotalCategory
          expression := Modules.ModulesTotal, realization := ``modulesTotalRealization }) then
      throwError "the canonical total category was rejected"

end CasCatalogue.Modules.FibrationRegistryProbes
