/- Independent mathematical question source; not an admitted acceptance record. -/
module

public import LeanCategories.Catalogue.Semantics.Modules.Bilinear.Valued.Kernels
public import LeanCategories.Lattices.Valued.Standard

@[expose] public section

open CategoryTheory
open LeanCategories.Modules.Bilinear.Valued
open CasCatalogue.Modules.Bilinear.Valued.Kernels

namespace B0AcceptanceFormedKernel

noncomputable def selected : BilinModuleCat ℤ ℤ :=
  LeanCategories.Lattices.Valued.e8Lattice.obj

noncomputable def selectedMap : selected ⟶ selected := 𝟙 selected

/-- The independently specified structured observation, before computation. -/
noncomputable def question : Prop :=
  (∀ x : kernelSubmodule selectedMap, x.1 = 0) ∧
  (∀ x : kernelSubmodule selectedMap,
    BilinModuleCat.underlyingMap (formedKernelInclusion selectedMap)
      (show (formedKernel selectedMap).carrier from x) = x.1) ∧
  (∀ x y : kernelSubmodule selectedMap,
    (formedKernel selectedMap).pairing
      (show (formedKernel selectedMap).carrier from x)
      (show (formedKernel selectedMap).carrier from y) =
        selected.pairing x.1 y.1) ∧
  (∀ x y : kernelSubmodule selectedMap,
    (formedKernel selectedMap).pairing
      (show (formedKernel selectedMap).carrier from x)
      (show (formedKernel selectedMap).carrier from y) = (0 : ℤ)) ∧
  ((forget ℤ ℤ).map (formedKernelInclusion selectedMap) ≫
    (forget ℤ ℤ).map selectedMap = 0) ∧
  (∀ (T : ModuleCat ℤ) (h : T ⟶ (forget ℤ ℤ).obj selected),
    h ≫ (forget ℤ ℤ).map selectedMap = 0 →
    ∃! k : T ⟶ (forget ℤ ℤ).obj (formedKernel selectedMap),
      k ≫ (forget ℤ ℤ).map (formedKernelInclusion selectedMap) = h)

end B0AcceptanceFormedKernel
