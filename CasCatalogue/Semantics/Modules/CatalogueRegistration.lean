module

public import CasCatalogue.Registry.Extension
public import CasCatalogue.Semantics.Modules.Expressions
public import LeanCategories.Modules.Mathlib
public import LeanCategories.Modules.TruncatedResolutions
public import LeanCategories.Modules.Total
public import CasCatalogue.FamilyFibration
public import CasCatalogue.Semantics.Foundation.CatalogueRegistration
public meta import CasCatalogue.Registry.Extension
public meta import CasCatalogue.Semantics.Modules.Expressions
public meta import CasCatalogue.Semantics.Modules.Catalogue
public meta import CasCatalogue.Semantics.Foundation.Expressions

@[expose] public section

namespace CasCatalogue.Modules.CatalogueRegistration
open LeanCategories LeanCategories.Modules

noncomputable section

open CategoryTheory
open LeanCategories CasCatalogue

universe u
universe v
universe w

noncomputable def modulesFamilyRealization :
    CategoryFamilyRealization.{max u (w + 1), w, u, u + 1}
      CategoryFamilyId.modules .ring (P := RingCat.{u}) where
  transport := Modules.Mathlib.moduleCatRestrictScalarsPseudofunctor.{u, w}
  transportSemantics := .restrictionOfScalars
/-- The registered `modules` family denotes the restriction-of-scalars fibration: its total
category is `ModulesOverRings` and its reindexing is restriction of scalars (CC-FIB). -/
theorem modulesFamilyRealization_total :
    modulesFamilyRealization.{u, w}.total = ModulesOverRings.{u, w} :=
  rfl

theorem modulesFamilyRealization_reindex {R S : RingCat.{u}} (φ : R ⟶ S) :
    modulesFamilyRealization.{u, w}.reindex φ = ModuleCat.restrictScalars.{w} φ.hom :=
  rfl

noncomputable def modulesRealization (R : RingCat.{u}) :
    CategoryRealization Modules.Modules (Modules.Mathlib.ModulesOf.{u, w} R) where
  familyFibre := some (.mk (modulesFamilyRealization.{u, w}) {
    parameter := R
    parameterQuotation := .ringR R
    category_eq := by rfl })

/-! ### The module fibration (CC-FIB)

The total category, fibre inclusion and reindexing are the canonical realizations of the
registered `modules` family (`Catalogue/FamilyFibration.lean`); restriction of scalars is
reindexing, not a registered edge between two fibres. The underlying-set functor is registered
once, on the total category. -/

/-- The total category `∫ᶜ Mod` of the registered module family. -/
noncomputable def modulesTotalCategory :=
  modulesFamilyRealization.{u, w}.totalCat

noncomputable def modulesTotalRealization :
    CategoryRealization Modules.ModulesTotal modulesTotalCategory.{u, w} := {}

noncomputable def modulesFibreInclusionDeclaration (R : RingCat.{u}) :=
  modulesFamilyRealization.{u, w}.fibreInclusionFunctor R

noncomputable def modulesFibreInclusionRealization (R : RingCat.{u}) :=
  modulesFamilyRealization.{u, w}.fibreInclusionRealization R
    (arguments := #[.variable ParameterId.r]) (.ringR R)

noncomputable def modulesReindexDeclaration {R S : RingCat.{u}} (φ : R ⟶ S) :=
  modulesFamilyRealization.{u, w}.reindexFunctor φ

noncomputable def modulesReindexRealization {R S : RingCat.{u}} (φ : R ⟶ S) :=
  modulesFamilyRealization.{u, w}.reindexRealization ParameterMorphismId.phi φ
    (source := #[.variable ParameterId.r]) (target := #[.variable ParameterId.s])
    (.ringR R) (.ringS S)

/-- The underlying-set functor of the total module category, into `Sets`. -/
noncomputable def modulesUnderlyingDeclaration :
    modulesTotalCategory.{u, w} ⥤ Foundation.Mathlib.Sets.{w} :=
  ModulesOverRings.underlying.{u, w}

noncomputable def modulesUnderlyingRealization :
    FunctorRealization Modules.ModulesUnderlyingExpr modulesTotalCategory.{u, w}
      Foundation.Mathlib.Sets.{w} modulesUnderlyingDeclaration :=
  { sourceRealization := modulesTotalRealization
    targetRealization := Foundation.CatalogueRegistration.setsRealization }

noncomputable def freeCoverFamilyTransport :
    Pseudofunctor
      (LocallyDiscrete (Discrete (Σ _R : CommRingCat.{u}, Nat))ᵒᵖ)
      (Cat.{u, u + 1}) :=
  discreteFamilyTransport.{u + 1, u, u + 1}
    (P := Σ _R : CommRingCat.{u}, Nat)
    (fun (parameter : Σ _R : CommRingCat.{u}, Nat) =>
      letI := parameter.1.commRing
      (Cat.of (FreeCover parameter.1 (Fin parameter.2)) : ObjCat.{u + 1, u}))

noncomputable def freeCoverFamilyRealization :
    CategoryFamilyRealization.{u + 1, u, u + 1, u + 1}
      CategoryFamilyId.freeCover .commRingNat
      (P := Discrete (Σ _R : CommRingCat.{u}, Nat)) where
  transport := freeCoverFamilyTransport
  transportSemantics := .discrete

noncomputable def basedModuleFamilyTransport :
    Pseudofunctor
      (LocallyDiscrete (Discrete (Σ _R : CommRingCat.{u}, Nat))ᵒᵖ)
      (Cat.{u, u + 1}) :=
  discreteFamilyTransport.{u + 1, u, u + 1}
    (P := Σ _R : CommRingCat.{u}, Nat)
    (fun (parameter : Σ _R : CommRingCat.{u}, Nat) =>
      letI := parameter.1.commRing
      (Cat.of (BasedModule parameter.1 (Fin parameter.2)) : ObjCat.{u + 1, u}))

noncomputable def basedModuleFamilyRealization :
    CategoryFamilyRealization.{u + 1, u, u + 1, u + 1}
      CategoryFamilyId.basedModule .commRingNat
      (P := Discrete (Σ _R : CommRingCat.{u}, Nat)) where
  transport := basedModuleFamilyTransport
  transportSemantics := .discrete

noncomputable def coordFamilyTransport :
    Pseudofunctor
      (LocallyDiscrete (Discrete (Σ _R : CommRingCat.{u}, Nat))ᵒᵖ)
      (Cat.{u, u + 1}) :=
  discreteFamilyTransport.{u + 1, u, u + 1}
    (P := Σ _R : CommRingCat.{u}, Nat)
    (fun (parameter : Σ _R : CommRingCat.{u}, Nat) =>
      letI := parameter.1.commRing
      (Cat.of (Coord parameter.1 (Fin parameter.2)) : ObjCat.{u + 1, u}))

noncomputable def coordFamilyRealization :
    CategoryFamilyRealization.{u + 1, u, u + 1, u + 1}
      CategoryFamilyId.coord .commRingNat
      (P := Discrete (Σ _R : CommRingCat.{u}, Nat)) where
  transport := coordFamilyTransport
  transportSemantics := .discrete

noncomputable def freeCoverIndexedFamilyTransport :
    Pseudofunctor
      (LocallyDiscrete
        (Discrete (Σ _R : CommRingCat.{u}, Type v))ᵒᵖ)
      (Cat.{max u v, max (u + 1) (v + 1)}) :=
  discreteFamilyTransport.{max (u + 1) (v + 1), max u v, max (u + 1) (v + 1)}
    (P := Σ _R : CommRingCat.{u}, Type v)
    (fun parameter =>
      letI := parameter.1.commRing
      Cat.of (FreeCover parameter.1 parameter.2))

noncomputable def freeCoverIndexedFamilyRealization :
    CategoryFamilyRealization.{max (u + 1) (v + 1), max u v,
      max (u + 1) (v + 1), max (u + 1) (v + 1)}
      CategoryFamilyId.freeCoverIndexed .commRingIndexType
      (P := Discrete (Σ _R : CommRingCat.{u}, Type v)) where
  transport := freeCoverIndexedFamilyTransport
  transportSemantics := .discrete

noncomputable def basedModuleIndexedFamilyTransport :
    Pseudofunctor
      (LocallyDiscrete
        (Discrete (Σ _R : CommRingCat.{u}, Type v))ᵒᵖ)
      (Cat.{max u v, max (u + 1) (v + 1)}) :=
  discreteFamilyTransport.{max (u + 1) (v + 1), max u v, max (u + 1) (v + 1)}
    (P := Σ _R : CommRingCat.{u}, Type v)
    (fun parameter =>
      letI := parameter.1.commRing
      Cat.of (BasedModule parameter.1 parameter.2))

noncomputable def basedModuleIndexedFamilyRealization :
    CategoryFamilyRealization.{max (u + 1) (v + 1), max u v,
      max (u + 1) (v + 1), max (u + 1) (v + 1)}
      CategoryFamilyId.basedModuleIndexed .commRingIndexType
      (P := Discrete (Σ _R : CommRingCat.{u}, Type v)) where
  transport := basedModuleIndexedFamilyTransport
  transportSemantics := .discrete

noncomputable def coordIndexedFamilyTransport :
    Pseudofunctor
      (LocallyDiscrete
        (Discrete (Σ _R : CommRingCat.{u}, Type v))ᵒᵖ)
      (Cat.{max u v, max (u + 1) (v + 1)}) :=
  discreteFamilyTransport.{max (u + 1) (v + 1), max u v, max (u + 1) (v + 1)}
    (P := Σ _R : CommRingCat.{u}, Type v)
    (fun parameter =>
      letI := parameter.1.commRing
      Cat.of (Coord parameter.1 parameter.2))

noncomputable def coordIndexedFamilyRealization :
    CategoryFamilyRealization.{max (u + 1) (v + 1), max u v,
      max (u + 1) (v + 1), max (u + 1) (v + 1)}
      CategoryFamilyId.coordIndexed .commRingIndexType
      (P := Discrete (Σ _R : CommRingCat.{u}, Type v)) where
  transport := coordIndexedFamilyTransport
  transportSemantics := .discrete

noncomputable def freeCoverCategory (R : Type u) [CommRing R] (n : Nat) : ObjCat.{u + 1, u} :=
  Cat.of (FreeCover R (Fin n))

noncomputable def basedModuleCategory (R : Type u) [CommRing R] (n : Nat) : ObjCat.{u + 1, u} :=
  Cat.of (BasedModule R (Fin n))

noncomputable def coordCategory (R : Type u) [CommRing R] (n : Nat) : ObjCat.{u + 1, u} :=
  Cat.of (Coord R (Fin n))

noncomputable def freeCoverIndexedCategory (R : Type u) [CommRing R] (I : Type v) :
    ObjCat.{max (u + 1) (v + 1), max u v} :=
  Cat.of (FreeCover R I)

noncomputable def basedModuleIndexedCategory (R : Type u) [CommRing R] (I : Type v) :
    ObjCat.{max (u + 1) (v + 1), max u v} :=
  Cat.of (BasedModule R I)

noncomputable def coordIndexedCategory (R : Type u) [CommRing R] (I : Type v) :
    ObjCat.{max (u + 1) (v + 1), max u v} :=
  Cat.of (Coord R I)

noncomputable def freeCoverRealization (R : Type u) [CommRing R] (n : Nat) :
    CategoryRealization Modules.FreeCoverExpr (freeCoverCategory R n) where
  familyFibre := some (.mk freeCoverFamilyRealization {
    parameter := ⟨CommRingCat.of R, n⟩
    parameterQuotation := .commRingNat (CommRingCat.of R) n
    category_eq := by rfl })

noncomputable def basedModuleRealization (R : Type u) [CommRing R] (n : Nat) :
    CategoryRealization Modules.BasedModuleExpr (basedModuleCategory R n) where
  familyFibre := some (.mk basedModuleFamilyRealization {
    parameter := ⟨CommRingCat.of R, n⟩
    parameterQuotation := .commRingNat (CommRingCat.of R) n
    category_eq := by rfl })

noncomputable def coordRealization (R : Type u) [CommRing R] (n : Nat) :
    CategoryRealization Modules.CoordExpr (coordCategory R n) where
  familyFibre := some (.mk coordFamilyRealization {
    parameter := ⟨CommRingCat.of R, n⟩
    parameterQuotation := .commRingNat (CommRingCat.of R) n
    category_eq := by rfl })

noncomputable def freeCoverIndexedRealization (R : Type u) [CommRing R] (I : Type v) :
    CategoryRealization Modules.FreeCoverIndexedExpr (freeCoverIndexedCategory R I) where
  familyFibre := some (.mk freeCoverIndexedFamilyRealization {
    parameter := ⟨CommRingCat.of R, I⟩
    parameterQuotation := .commRingIndexTypeRI (CommRingCat.of R) I
    category_eq := by rfl })

noncomputable def basedModuleIndexedRealization (R : Type u) [CommRing R] (I : Type v) :
    CategoryRealization Modules.BasedModuleIndexedExpr (basedModuleIndexedCategory R I) where
  familyFibre := some (.mk basedModuleIndexedFamilyRealization {
    parameter := ⟨CommRingCat.of R, I⟩
    parameterQuotation := .commRingIndexTypeRI (CommRingCat.of R) I
    category_eq := by rfl })

noncomputable def coordIndexedRealization (R : Type u) [CommRing R] (I : Type v) :
    CategoryRealization Modules.CoordIndexedExpr (coordIndexedCategory R I) where
  familyFibre := some (.mk coordIndexedFamilyRealization {
    parameter := ⟨CommRingCat.of R, I⟩
    parameterQuotation := .commRingIndexTypeRI (CommRingCat.of R) I
    category_eq := by rfl })
noncomputable def freeModulesRealization (R : RingCat.{u}) :
    CategoryRealization Modules.FreeModules (Modules.Mathlib.free R).total :=
  { familyFibre := none }
noncomputable def finitelyGeneratedModulesRealization (R : RingCat.{u}) :
    CategoryRealization Modules.FinitelyGeneratedModules
      (Modules.Mathlib.finitelyGenerated R).total := { familyFibre := none }
noncomputable def finiteRankModulesRealization (R : RingCat.{u}) :
    CategoryRealization Modules.FiniteRankModules
      (Modules.Mathlib.finiteRank R).total := { familyFibre := none }

noncomputable def basedModuleToFreeCoverRealization (R : Type u) [CommRing R] (n : Nat) :
    FunctorRealization Modules.BasedModuleToFreeCoverExpr
      (basedModuleCategory R n) (freeCoverCategory R n)
      (basedModuleToFreeCover R (Fin n)) :=
  { sourceRealization := basedModuleRealization R n
    targetRealization := freeCoverRealization R n }

noncomputable def fromBasedModuleRealization (R : Type u) [CommRing R] (n : Nat) :
    FunctorRealization Modules.FromBasedModuleExpr
      (basedModuleCategory R n) (coordCategory R n)
      (Coord.fromBasedModule R (Fin n)) :=
  { sourceRealization := basedModuleRealization R n
    targetRealization := coordRealization R n }

noncomputable def coordForgetRealization (R : Type u) [CommRing R] (n : Nat) :
    FunctorRealization Modules.CoordForgetExpr
      (coordCategory R n) (Modules.Mathlib.ModulesOf (RingCat.of R))
      (Coord.forget R (Fin n)) :=
  { sourceRealization := coordRealization R n
    targetRealization := modulesRealization (RingCat.of R) }

noncomputable def basedModuleToFreeCoverDeclaration (R : Type u) [CommRing R] (n : Nat) :
    basedModuleCategory R n ⟶ freeCoverCategory R n :=
  (basedModuleToFreeCover R (Fin n)).toCatHom

noncomputable def fromBasedModuleDeclaration (R : Type u) [CommRing R] (n : Nat) :
    basedModuleCategory R n ⟶ coordCategory R n :=
  (Coord.fromBasedModule R (Fin n)).toCatHom

noncomputable def coordForgetDeclaration (R : Type u) [CommRing R] (n : Nat) :
    coordCategory R n ⟶ Modules.Mathlib.ModulesOf (RingCat.of R) :=
  (Coord.forget R (Fin n)).toCatHom

noncomputable def freeCoverForgetIndexedRealization (R : Type u) [CommRing R] (I : Type v) :
    FunctorRealization Modules.FreeCoverForgetExpr
      (freeCoverIndexedCategory R I)
    (Modules.Mathlib.ModulesOf.{u, max u v} (RingCat.of R))
      (FreeCover.forget R I) :=
  { sourceRealization := freeCoverIndexedRealization R I
    targetRealization := modulesRealization.{u, max u v} (RingCat.of R) }

noncomputable def basedModuleForgetIndexedRealization (R : Type u) [CommRing R] (I : Type v) :
    FunctorRealization Modules.BasedModuleForgetExpr
      (basedModuleIndexedCategory R I)
    (Modules.Mathlib.ModulesOf.{u, max u v} (RingCat.of R))
      (BasedModule.forget R I) :=
  { sourceRealization := basedModuleIndexedRealization R I
    targetRealization := modulesRealization.{u, max u v} (RingCat.of R) }

noncomputable def freeCoverForgetIndexedDeclaration (R : Type u) [CommRing R] (I : Type v) :
    freeCoverIndexedCategory R I ⥤ Modules.Mathlib.ModulesOf.{u, max u v} (RingCat.of R) :=
  FreeCover.forget R I

noncomputable def basedModuleForgetIndexedDeclaration (R : Type u) [CommRing R] (I : Type v) :
    basedModuleIndexedCategory R I ⥤ Modules.Mathlib.ModulesOf.{u, max u v} (RingCat.of R) :=
  BasedModule.forget R I

/-! The indexed registrations keep ring and index universes independent. -/
universe uR uI

example (R : Type uR) [CommRing R] (I : Type uI) :
    CategoryRealization Modules.FreeCoverIndexedExpr
      (freeCoverIndexedCategory R I) :=
  freeCoverIndexedRealization R I

example (R : Type uR) [CommRing R] (I : Type uI) :
    CategoryRealization Modules.BasedModuleIndexedExpr
      (basedModuleIndexedCategory R I) :=
  basedModuleIndexedRealization R I

example (R : Type uR) [CommRing R] :
    CategoryRealization Modules.CoordIndexedExpr
      (coordIndexedCategory R (Nat → Nat)) :=
  coordIndexedRealization R (Nat → Nat)

noncomputable def freeRealization (R : RingCat.{u}) :
    ClassifierRealization Modules.Modules ClassifierId.modulesFree
      (Modules.Mathlib.ModulesOf R) (Modules.Mathlib.free R) :=
  { hostRealization := modulesRealization R, totalRealization := {} }
noncomputable def finitelyGeneratedRealization (R : RingCat.{u}) :
    ClassifierRealization Modules.Modules ClassifierId.modulesFinitelyGenerated
      (Modules.Mathlib.ModulesOf R) (Modules.Mathlib.finitelyGenerated R) :=
  { hostRealization := modulesRealization R, totalRealization := {} }
noncomputable def finiteRankRealization (R : RingCat.{u}) :
    ClassifierRealization Modules.Modules ClassifierId.modulesFiniteRank
      (Modules.Mathlib.ModulesOf R) (Modules.Mathlib.finiteRank R) :=
  { hostRealization := modulesRealization R, totalRealization := {} }

normalized_registry .categoryFamily
  { id := CategoryFamilyId.modules,
    schema := .ring
    realization := `CasCatalogue.Modules.CatalogueRegistration.modulesFamilyRealization
    transport := `LeanCategories.Modules.Mathlib.moduleCatRestrictScalarsPseudofunctor
    transportSemantics := .restrictionOfScalars }

normalized_registry .categoryFamily
  { id := CategoryFamilyId.freeCover,
    schema := .commRingNat
    realization := `CasCatalogue.Modules.CatalogueRegistration.freeCoverFamilyRealization
    transport := `CasCatalogue.Modules.CatalogueRegistration.freeCoverFamilyTransport
    transportSemantics := .discrete }
normalized_registry .categoryFamily
  { id := CategoryFamilyId.basedModule,
    schema := .commRingNat
    realization := `CasCatalogue.Modules.CatalogueRegistration.basedModuleFamilyRealization
    transport := `CasCatalogue.Modules.CatalogueRegistration.basedModuleFamilyTransport
    transportSemantics := .discrete }
normalized_registry .categoryFamily
  { id := CategoryFamilyId.coord,
    schema := .commRingNat
    realization := `CasCatalogue.Modules.CatalogueRegistration.coordFamilyRealization
    transport := `CasCatalogue.Modules.CatalogueRegistration.coordFamilyTransport
    transportSemantics := .discrete }
normalized_registry .categoryFamily
  { id := CategoryFamilyId.freeCoverIndexed,
    schema := .commRingIndexType
    realization := `CasCatalogue.Modules.CatalogueRegistration.freeCoverIndexedFamilyRealization
    transport := `CasCatalogue.Modules.CatalogueRegistration.freeCoverIndexedFamilyTransport
    transportSemantics := .discrete }
normalized_registry .categoryFamily
  { id := CategoryFamilyId.basedModuleIndexed,
    schema := .commRingIndexType
    realization := `CasCatalogue.Modules.CatalogueRegistration.basedModuleIndexedFamilyRealization
    transport := `CasCatalogue.Modules.CatalogueRegistration.basedModuleIndexedFamilyTransport
    transportSemantics := .discrete }
normalized_registry .categoryFamily
  { id := CategoryFamilyId.coordIndexed,
    schema := .commRingIndexType
    realization := `CasCatalogue.Modules.CatalogueRegistration.coordIndexedFamilyRealization
    transport := `CasCatalogue.Modules.CatalogueRegistration.coordIndexedFamilyTransport
    transportSemantics := .discrete }

normalized_registry .classifier
  { id := ClassifierId.modulesFree,
    declaration := `LeanCategories.Modules.Mathlib.free
    host := Modules.Modules
    realization := `CasCatalogue.Modules.CatalogueRegistration.freeRealization}
normalized_registry .classifier
  { id := ClassifierId.modulesFinitelyGenerated,
    declaration := `LeanCategories.Modules.Mathlib.finitelyGenerated
    host := Modules.Modules
    realization := `CasCatalogue.Modules.CatalogueRegistration.finitelyGeneratedRealization}
normalized_registry .classifier
  { id := ClassifierId.modulesFiniteRank,
    declaration := `LeanCategories.Modules.Mathlib.finiteRank
    host := Modules.Modules
    realization := `CasCatalogue.Modules.CatalogueRegistration.finiteRankRealization}

normalized_registry .category
  { id := CategoryId.modulesR,
    declaration := `LeanCategories.Modules.Mathlib.ModulesOf
    expression := Modules.Modules
    realization := `CasCatalogue.Modules.CatalogueRegistration.modulesRealization}
normalized_registry .category
  { id := CategoryId.freeModules,
    declaration := `LeanCategories.Modules.Mathlib.FreeModules
    expression := Modules.FreeModules
    realization := `CasCatalogue.Modules.CatalogueRegistration.freeModulesRealization}
normalized_registry .category
  { id := CategoryId.finitelyGeneratedModules
    declaration := `LeanCategories.Modules.Mathlib.FinitelyGeneratedModules
    expression := Modules.FinitelyGeneratedModules
    realization := `CasCatalogue.Modules.CatalogueRegistration.finitelyGeneratedModulesRealization}
normalized_registry .category
  { id := CategoryId.finiteRankModules,
    declaration := `LeanCategories.Modules.Mathlib.FiniteRankModules
    expression := Modules.FiniteRankModules
    realization := `CasCatalogue.Modules.CatalogueRegistration.finiteRankModulesRealization}

normalized_registry .category
  { id := CategoryId.freeCover,
    declaration := `CasCatalogue.Modules.CatalogueRegistration.freeCoverCategory
    expression := Modules.FreeCoverExpr
    realization := `CasCatalogue.Modules.CatalogueRegistration.freeCoverRealization }
normalized_registry .category
  { id := CategoryId.basedModule,
    declaration := `CasCatalogue.Modules.CatalogueRegistration.basedModuleCategory
    expression := Modules.BasedModuleExpr
    realization := `CasCatalogue.Modules.CatalogueRegistration.basedModuleRealization }
normalized_registry .category
  { id := CategoryId.coord,
    declaration := `CasCatalogue.Modules.CatalogueRegistration.coordCategory
    expression := Modules.CoordExpr
    realization := `CasCatalogue.Modules.CatalogueRegistration.coordRealization }
normalized_registry .category
  { id := CategoryId.freeCoverIndexed,
    declaration := `CasCatalogue.Modules.CatalogueRegistration.freeCoverIndexedCategory
    expression := Modules.FreeCoverIndexedExpr
    realization := `CasCatalogue.Modules.CatalogueRegistration.freeCoverIndexedRealization }
normalized_registry .category
  { id := CategoryId.basedModuleIndexed,
    declaration := `CasCatalogue.Modules.CatalogueRegistration.basedModuleIndexedCategory
    expression := Modules.BasedModuleIndexedExpr
    realization := `CasCatalogue.Modules.CatalogueRegistration.basedModuleIndexedRealization }
normalized_registry .category
  { id := CategoryId.coordIndexed,
    declaration := `CasCatalogue.Modules.CatalogueRegistration.coordIndexedCategory
    expression := Modules.CoordIndexedExpr
    realization := `CasCatalogue.Modules.CatalogueRegistration.coordIndexedRealization }

normalized_registry .functor
  { id := FunctorId.basedModuleToFreeCover,
    source := Modules.BasedModuleExpr
    target := Modules.FreeCoverExpr
    declaration := `CasCatalogue.Modules.CatalogueRegistration.basedModuleToFreeCoverDeclaration
    realization :=
      `CasCatalogue.Modules.CatalogueRegistration.basedModuleToFreeCoverRealization
    expression := Modules.BasedModuleToFreeCoverExpr
    structural := true }
normalized_registry .functor
  { id := FunctorId.fromBasedModule,
    source := Modules.BasedModuleExpr
    target := Modules.CoordExpr
    declaration := `CasCatalogue.Modules.CatalogueRegistration.fromBasedModuleDeclaration
    realization := `CasCatalogue.Modules.CatalogueRegistration.fromBasedModuleRealization
    expression := Modules.FromBasedModuleExpr }
normalized_registry .functor
  { id := FunctorId.coordForget,
    source := Modules.CoordExpr
    target := Modules.Modules
    declaration := `CasCatalogue.Modules.CatalogueRegistration.coordForgetDeclaration
    realization := `CasCatalogue.Modules.CatalogueRegistration.coordForgetRealization
    expression := Modules.CoordForgetExpr
    structural := true }
normalized_registry .functor
  { id := FunctorId.freeCoverForget,
    source := Modules.FreeCoverIndexedExpr
    target := Modules.Modules
    declaration := `CasCatalogue.Modules.CatalogueRegistration.freeCoverForgetIndexedDeclaration
    realization :=
      `CasCatalogue.Modules.CatalogueRegistration.freeCoverForgetIndexedRealization
    expression := Modules.FreeCoverForgetExpr
    structural := true }
normalized_registry .functor
  { id := FunctorId.basedModuleForget,
    source := Modules.BasedModuleIndexedExpr
    target := Modules.Modules
    declaration := `CasCatalogue.Modules.CatalogueRegistration.basedModuleForgetIndexedDeclaration
    realization :=
      `CasCatalogue.Modules.CatalogueRegistration.basedModuleForgetIndexedRealization
    expression := Modules.BasedModuleForgetExpr
    structural := true }

normalized_registry .category
  { id := CategoryId.modulesTotal,
    declaration := `CasCatalogue.Modules.CatalogueRegistration.modulesTotalCategory
    expression := Modules.ModulesTotal
    realization := `CasCatalogue.Modules.CatalogueRegistration.modulesTotalRealization }
normalized_registry .functor
  { id := FunctorId.modulesFibreInclusion,
    source := Modules.Modules
    target := Modules.ModulesTotal
    declaration :=
      `CasCatalogue.Modules.CatalogueRegistration.modulesFibreInclusionDeclaration
    realization :=
      `CasCatalogue.Modules.CatalogueRegistration.modulesFibreInclusionRealization
    expression := Modules.ModulesFibreInclusionExpr
    structural := true }
normalized_registry .functor
  { id := FunctorId.modulesReindex,
    source := Modules.ModulesAtS
    target := Modules.Modules
    declaration := `CasCatalogue.Modules.CatalogueRegistration.modulesReindexDeclaration
    realization := `CasCatalogue.Modules.CatalogueRegistration.modulesReindexRealization
    expression := Modules.ModulesReindexExpr }
normalized_registry .functor
  { id := FunctorId.modulesUnderlying,
    source := Modules.ModulesTotal
    target := Foundation.Sets
    declaration := `CasCatalogue.Modules.CatalogueRegistration.modulesUnderlyingDeclaration
    realization := `CasCatalogue.Modules.CatalogueRegistration.modulesUnderlyingRealization
    expression := Modules.ModulesUnderlyingExpr
    structural := true }

end
end CasCatalogue.Modules.CatalogueRegistration
