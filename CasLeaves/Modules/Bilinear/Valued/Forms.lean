/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CasCatalogue.Leaf
public import CasLeaves.Modules.Actions
public import CasLeaves.Lattices.Valued.Actions
public import CasCatalogue.Semantics.Lattices.Valued.CatalogueRegistration
public import CasCatalogue.Semantics.Lattices.Valued.Property
public import Mathlib.LinearAlgebra.BilinearForm.Hom
public meta import CasCatalogue.Leaf
public meta import CasCatalogue.Semantics.Lattices.Valued.CatalogueRegistration
public meta import CasCatalogue.Semantics.Lattices.Valued.Property

@[expose] public section

/-!
# Formed modules by their form (specimen, CC-ACTION)

A formed module is a module with a map out of `M ⊗ M` (`BilinModuleCat.ofBilinMap`, Mathlib's
`TensorProduct.lift`). Here a handle is a free module `ℤⁿ` with a Mathlib bilinear map on it, given
by its formula — not by a Gram matrix. The leaf declares only its immediate structure:

* the realizer of `BilinModule(ℤ, ℤ)` by forms, and the forgetful functor to modules on it (keep the
  rank); cardinality, rank and the rest arrive by composition;
* the lattice property decided on forms (`ℤⁿ` is projective; symmetry is checked on the standard
  basis, `LinearMap.BilinForm.ext_basis`); a formed module proved to be a lattice is re-typed by the
  core (`CasCatalogue.refine`) into `Lattice(ℤ, ℤ)` as the same handle, which realizes it, with the
  inclusion of lattices into formed modules realized by forgetting the proof.
-/

open CategoryTheory
open LeanCategories.Modules.Bilinear.Valued LeanCategories.Lattices.Valued
open CasCatalogue.Modules.Actions

namespace CasCatalogue.Modules.Bilinear.Valued.Forms

/-- A `ℤ`-valued bilinear form on `ℤⁿ`, as a Mathlib bilinear map. -/
structure FormHandle where
  rank : ℕ
  form : LinearMap.BilinForm ℤ (Fin rank → ℤ)

/-- Formed modules by form, with the isometries of their denotations. -/
abbrev FormHandles : Type :=
  InducedCategory (BilinModuleCat ℤ ℤ) fun a : FormHandle => BilinModuleCat.ofBilinMap a.form

noncomputable def formDenotation : FormHandles ⥤ BilinModuleCat ℤ ℤ := inducedFunctor _

/-- The forgetful functor on forms: keep the rank. -/
noncomputable def formForgetAction :
    RealizedAction (forget ℤ ℤ) formDenotation freeModuleDenotation :=
  RealizedAction.induced _ FormHandle.rank fun _ => rfl

/-- Symmetry of a bilinear form on `ℤⁿ`, decided on the standard basis. -/
def decideSymm {n : ℕ} (B : LinearMap.BilinForm ℤ (Fin n → ℤ)) :
    Decision (∀ x y, B x y = B y x) :=
  (Decision.ofDecidable (∀ i j : Fin n,
      B (Pi.single i 1) (Pi.single j 1) = B (Pi.single j 1) (Pi.single i 1))).map
    ⟨fun h x y => by
      have : B = B.flip := LinearMap.BilinForm.ext_basis (Pi.basisFun ℤ (Fin n)) fun i j => by
        simpa using h i j
      exact LinearMap.congr_fun₂ this x y,
    fun h i j => h _ _⟩

/-- The lattice property of a formed module by form. -/
def decideLattice (a : FormHandle) : Decision (isLattice ℤ ℤ (formDenotation.obj a)) :=
  (decideSymm a.form).map
    ⟨fun h => ⟨inferInstanceAs (Module.Projective ℤ (Fin a.rank → ℤ)), h⟩, fun h => h.2⟩

/-- The decider of `clf.bilin_module.lattice` on forms. -/
def latticeDecider :
    Decider (Lattices.Valued.Property.latticeClassifier ℤ ℤ) formDenotation where
  decide a := (decideLattice a).map (Classifier.holds_ofProperty _ _).symm

/-- Formed modules proved to be lattices, as lattices. -/
noncomputable def latticeDenotation : Refined formDenotation (isLattice ℤ ℤ) ⥤ LatticeCat ℤ ℤ :=
  refinedDenotation formDenotation (isLattice ℤ ℤ)

/-- The inclusion of lattices into formed modules: forget the proof. -/
noncomputable def latticeForgetAction :
    RealizedAction (isLattice ℤ ℤ).ι latticeDenotation formDenotation :=
  refinedInclusion formDenotation (isLattice ℤ ℤ)

end CasCatalogue.Modules.Bilinear.Valued.Forms

namespace CasCatalogue

register_leaf
  { backend := "lean"
    contributions := [
  .realizer
  { id := ⟨"rz.bilin_module.form"⟩, category := ⟨"cat.bilin_module"⟩, backend := "lean"
    denotation := `CasCatalogue.Modules.Bilinear.Valued.Forms.formDenotation },
  .action
  { id := ⟨"act.bilin_module.forget.form"⟩, edge := .functor FunctorId.bilinModuleForget
    realization := `CasCatalogue.Modules.Bilinear.Valued.Forms.formForgetAction },
  .decider
  { id := ⟨"dec.bilin_module.lattice.form"⟩, classifier := ClassifierId.bilinModuleLattice
    realization := `CasCatalogue.Modules.Bilinear.Valued.Forms.latticeDecider },
  .realizer
  { id := ⟨"rz.lattice.form_refined"⟩, category := ⟨"cat.lattice"⟩, backend := "lean"
    denotation := `CasCatalogue.Modules.Bilinear.Valued.Forms.latticeDenotation },
  .action
  { id := ⟨"act.lattice.forget_form.form_refined"⟩, edge := .functor FunctorId.latticeFormForget
    realization := `CasCatalogue.Modules.Bilinear.Valued.Forms.latticeForgetAction }] }

end CasCatalogue
