/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CasCatalogue.Leaf
public import CasLeaves.Modules.Bilinear.Valued.Actions
public import LeanCategories.Catalogue.Semantics.Lattices.Valued.CatalogueRegistration
public meta import CasCatalogue.Leaf
public meta import LeanCategories.Catalogue.Semantics.Lattices.Valued.Catalogue

@[expose] public section

/-!
# Lean-native realizations of integer lattices (CC-ACTION)

A `ℤ`-valued lattice on `ℤⁿ` is realized by a symmetric Gram matrix; its denotation is the formed
module of the Gram matrix together with the lattice property (projective carrier, symmetric form).
Only the inclusion `Lattice(ℤ, ℤ) ⥤ BilinModule(ℤ, ℤ)` (`fun.lattice.forget_form`) carries an
action here: lattices reach modules and sets through the registered actions of that chain, and no
lattice-to-set action is registered (CC-ACTION acceptance).
-/

open CategoryTheory
open LeanCategories.Modules.Bilinear.Valued LeanCategories.Lattices.Valued
open CasCatalogue.Modules.Bilinear.Valued.Actions

namespace CasCatalogue.Lattices.Valued.Actions

/-- A symmetric Gram matrix: a realization of a lattice over `ℤ` with values in `ℤ`. -/
structure LatticeGramHandle where
  form : GramHandle
  symm : form.gram.IsSymm

/-- The lattice handle of an integer matrix given by its rows, symmetric by evaluation. -/
def LatticeGramHandle.ofRows (n : ℕ) (rows : List (List ℤ))
    (symm : decide (GramHandle.ofRows n rows).gram.IsSymm = true) : LatticeGramHandle :=
  ⟨GramHandle.ofRows n rows, of_decide_eq_true symm⟩

/-- A symmetric Gram matrix gives a symmetric form. -/
theorem toLinearMap₂'_symm {n : ℕ} (G : Matrix (Fin n) (Fin n) ℤ) (h : G.IsSymm)
    (x y : Fin n → ℤ) : Matrix.toLinearMap₂' ℤ G x y = Matrix.toLinearMap₂' ℤ G y x := by
  rw [Matrix.toLinearMap₂'_apply', Matrix.toLinearMap₂'_apply', Matrix.dotProduct_mulVec,
    dotProduct_comm, ← Matrix.vecMul_transpose, h.eq]

/-- The lattice a symmetric Gram matrix denotes: the Gram form, which is a lattice because `ℤⁿ`
is free (hence projective) and the Gram matrix is symmetric. -/
noncomputable def LatticeGramHandle.denote (a : LatticeGramHandle) : LatticeCat ℤ ℤ :=
  ⟨gramDenotation.obj a.form,
    ⟨inferInstanceAs (Module.Projective ℤ (Fin a.form.rank → ℤ)),
      toLinearMap₂'_symm a.form.gram a.symm⟩⟩

/-- Integer lattices by symmetric Gram matrix, with the isometries of their denotations. -/
abbrev LatticeGramHandles : Type := InducedCategory (LatticeCat ℤ ℤ) LatticeGramHandle.denote

/-- The denotation in `Lattice(ℤ, ℤ)`. -/
noncomputable def latticeGramDenotation : LatticeGramHandles ⥤ LatticeCat ℤ ℤ := inducedFunctor _

/-- The inclusion of lattices into formed modules on handles: forget the symmetry certificate. -/
noncomputable def formForgetAction :
    RealizedAction (isLattice ℤ ℤ).ι latticeGramDenotation gramDenotation :=
  RealizedAction.induced _ LatticeGramHandle.form fun _ => rfl

register_leaf
  { backend := "lean"
    contributions := [
  .action
  { id := ⟨"act.lattice.forget_form.int_gram"⟩
    edge := .functor FunctorId.latticeFormForget
    realization := `CasCatalogue.Lattices.Valued.Actions.formForgetAction },
  .realizer
  { id := ⟨"rz.lattice.int_gram"⟩, category := ⟨"cat.lattice"⟩, backend := "lean"
    denotation := `CasCatalogue.Lattices.Valued.Actions.latticeGramDenotation }] }

end CasCatalogue.Lattices.Valued.Actions
