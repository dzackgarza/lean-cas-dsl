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

/-- The fixed universal observation instantiated at the actual reconstructed
formed domain and its actual defining inclusion, not substituted canonical data. -/
noncomputable def reconstructedUniversalQuestion
    (D : BilinModuleCat ℤ ℤ) (i : D ⟶ selected) : Prop :=
  ∀ (T : ModuleCat ℤ) (h : T ⟶ (forget ℤ ℤ).obj selected),
    h ≫ (forget ℤ ℤ).map selectedMap = 0 →
    ∃! k : T ⟶ (forget ℤ ℤ).obj D,
      k ≫ (forget ℤ ℤ).map i = h

/-- Direct application of the existing public equalizer universal theorem.
The premise must concern the actual reconstructed inclusion over the fixed map. -/
theorem reconstructedUniversalQuestion_of_isLimit
    (D : BilinModuleCat ℤ ℤ) (i : D ⟶ selected)
    (condition : (forget ℤ ℤ).map i ≫ (forget ℤ ℤ).map selectedMap = 0)
    (hs : CategoryTheory.Limits.IsLimit
      (CategoryTheory.Limits.KernelFork.ofι ((forget ℤ ℤ).map i) condition)) :
    reconstructedUniversalQuestion D i := by
  intro T h annihilated
  have equalized : h ≫ (forget ℤ ℤ).map selectedMap = h ≫ 0 := by
    simpa using annihilated
  simpa using CategoryTheory.Limits.Fork.IsLimit.existsUnique hs h equalized

/-- Transport existing universal data to the actual reconstructed domain and
inclusion using its checked comparison over the fixed ambient module. -/
theorem reconstructedUniversalQuestion_of_comparison
    (D : BilinModuleCat ℤ ℤ) (i : D ⟶ selected)
    (s : CategoryTheory.Limits.KernelFork ((forget ℤ ℤ).map selectedMap))
    (hs : CategoryTheory.Limits.IsLimit s)
    (e : (forget ℤ ℤ).obj D ≅ s.pt)
    (fac : e.hom ≫ CategoryTheory.Limits.Fork.ι s = (forget ℤ ℤ).map i) :
    reconstructedUniversalQuestion D i := by
  let transported := CategoryTheory.Limits.IsKernel.isoKernel
    ((forget ℤ ℤ).map selectedMap) ((forget ℤ ℤ).map i) hs e fac
  exact reconstructedUniversalQuestion_of_isLimit D i _ transported

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
