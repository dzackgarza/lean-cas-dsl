/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CasCatalogue.Realization
public import Mathlib.CategoryTheory.FiberedCategory.Grothendieck

@[expose] public section

/-!
# The fibration denoted by a registered family

specs/computational-core.md CC-FIB: a registered family is admissible only as an encoding of
a fibration. A `CategoryFamilyRealization` carries a pseudofunctor
`transport : LocallyDiscrete Pᵒᵖ ⥤ᵖ Cat`; the fibration it denotes is the projection of its
(contravariant) Grothendieck construction `∫ᶜ transport → P`, a cartesian fibration
(Mathlib's `IsFibered (CoGrothendieck.forget _)`). This file names that data on every family
realization:

* `total` — the total category `∫ᶜ transport`;
* `projection` — the cartesian fibration `total ⥤ P`;
* `fibreInclusion p` — the fibre inclusion `ι_p : fibre p ⥤ total` (Mathlib's
  `CoGrothendieck.ι`), with `ι_p ⋙ projection` constant at `p`;
* `reindex φ` — the reindexing functor `φ^* : fibre q ⥤ fibre p` along `φ : p ⟶ q`; the
  cartesian lift of `φ` at `(q, y)` is `CoGrothendieck.cartesianLift`, with domain
  `(p, φ^* y)` (`reindex_obj_eq_domainCartesianLift`).

"Change of fibre" in a family is therefore reindexing along a morphism of the base, not an
edge between two applications of the family.
-/

namespace CasCatalogue
open LeanCategories

open CategoryTheory Opposite Pseudofunctor

universe uObj uHom uParamHom uParameterType

namespace CategoryFamilyRealization

variable {identifier : CategoryFamilyId} {schema : CategoryFamilySchema}
  {P : Type uParameterType}
  (realization : CategoryFamilyRealization.{uObj, uHom, uParamHom, uParameterType}
    identifier schema (P := P))

/-- The total category of the fibration a family denotes: the contravariant Grothendieck
construction of its transport. -/
abbrev total : Type _ :=
  letI := realization.parameterCategory
  CoGrothendieck realization.transport

/-- The projection of the total category to the base: a cartesian fibration. -/
abbrev projection :
    letI := realization.parameterCategory
    realization.total ⥤ P :=
  letI := realization.parameterCategory
  CoGrothendieck.forget realization.transport

/-- The projection is a cartesian fibration. -/
theorem projection_isFibered :
    letI := realization.parameterCategory
    realization.projection.IsFibered := by
  let _ := realization.parameterCategory
  change (CoGrothendieck.forget realization.transport).IsFibered
  infer_instance

/-- The inclusion of the fibre over `p` into the total category. -/
abbrev fibreInclusion (p : P) : realization.fibre p ⥤ realization.total :=
  letI := realization.parameterCategory
  CoGrothendieck.ι realization.transport p

/-- The fibre inclusion lands over `p`. -/
theorem fibreInclusion_comp_projection (p : P) :
    letI := realization.parameterCategory
    realization.fibreInclusion p ⋙ realization.projection = (Functor.const _).obj p := by
  let _ := realization.parameterCategory
  exact CoGrothendieck.comp_const realization.transport p

/-- Reindexing along a morphism of the base: the transport of the fibration. -/
abbrev reindex {p q : P} (φ : letI := realization.parameterCategory; p ⟶ q) :
    realization.fibre q ⥤ realization.fibre p :=
  letI := realization.parameterCategory
  (realization.transport.map φ.op.toLoc).toFunctor

/-- The domain of the cartesian lift of `φ` at `(q, y)` is `(p, φ^* y)`. -/
theorem reindex_obj_eq_domainCartesianLift {p q : P}
    (φ : letI := realization.parameterCategory; p ⟶ q) (y : realization.fibre q) :
    letI := realization.parameterCategory
    (⟨p, (realization.reindex φ).obj y⟩ : realization.total) =
      CoGrothendieck.domainCartesianLift (F := realization.transport) y φ :=
  rfl


end CategoryFamilyRealization


namespace CategoryFamilyRealization

/-! ## Registry realizations of the fibration

The registry places every category in `ObjCat`, whose object universe dominates its hom
universe. The total category has objects in `max uP uObj uHom` and morphisms in
`max uParamHom uHom`, so it is an `ObjCat` when the base is a large category
(`P : Type (uParamHom + 1)`, `Category.{uParamHom} P`), as for every registered schema. -/

variable {identifier : CategoryFamilyId} {schema : CategoryFamilySchema}
  {P : Type (uParamHom + 1)}
  (realization : CategoryFamilyRealization.{uObj, uHom, uParamHom, uParamHom + 1}
    identifier schema (P := P))

/-- The total category as an object of `Cat`. -/
def totalCat : ObjCat.{max (uParamHom + 1) uObj uHom, max uHom uParamHom} :=
  letI := realization.parameterCategory
  Cat.of (CoGrothendieck realization.transport)

/-- The fibre inclusion as a functor into `totalCat`. -/
def fibreInclusionFunctor (p : P) : realization.fibre p ⥤ realization.totalCat :=
  realization.fibreInclusion p

/-- The canonical realization of the symbolic family fibre over quoted arguments. -/
def fibreRealization (p : P) {arguments : Array ParameterExpr}
    (quotation : CategoryFamilyParameterQuotation schema arguments p) :
    CategoryRealization.{uObj, uHom, uParamHom, uParamHom + 1}
      (.familyApp identifier arguments) (realization.fibre p) where
  familyFibre := some (.mk realization
    (show CategoryFamilyFibreWitness (realization.fibre p) realization (arguments := arguments)
      from { parameter := p, parameterQuotation := quotation, category_eq := rfl }))

/-- The canonical realization of `FunctorExpr.familyFibreInclusion`. Registry validation
requires a registered fibre inclusion to be exactly this term for the registered family
realization. -/
def fibreInclusionRealization (p : P) {arguments : Array ParameterExpr}
    (quotation : CategoryFamilyParameterQuotation schema arguments p) :
    FunctorRealization
      (.familyFibreInclusion identifier arguments) (realization.fibre p) realization.totalCat
      (realization.fibreInclusionFunctor p) where
  sourceRealization := realization.fibreRealization p quotation
  targetRealization := {}

/-- The reindexing functor between fibres, as a functor of `Cat` objects. -/
def reindexFunctor {p q : P} (φ : letI := realization.parameterCategory; p ⟶ q) :
    realization.fibre q ⥤ realization.fibre p :=
  realization.reindex φ

/-- The canonical realization of `FunctorExpr.familyReindex` along a symbolic morphism
`φ : p ⟶ q` between quoted parameters. -/
def reindexRealization (morphism : ParameterMorphismId) {p q : P}
    (φ : letI := realization.parameterCategory; p ⟶ q)
    {source target : Array ParameterExpr}
    (sourceQuotation : CategoryFamilyParameterQuotation schema source p)
    (targetQuotation : CategoryFamilyParameterQuotation schema target q) :
    FunctorRealization
      (.familyReindex identifier morphism source target) (realization.fibre q)
      (realization.fibre p) (realization.reindexFunctor φ) where
  sourceRealization := realization.fibreRealization q targetQuotation
  targetRealization := realization.fibreRealization p sourceQuotation
end CategoryFamilyRealization

end CasCatalogue
