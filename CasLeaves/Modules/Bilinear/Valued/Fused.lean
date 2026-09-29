/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CasCatalogue.Leaf
public import CasLeaves.Modules.Bilinear.Valued.Actions
public import CasCatalogue.Semantics.Foundation.Cardinality
public import CasLeaves.Foundation.Cardinality
public meta import CasCatalogue.Leaf
public meta import CasCatalogue.Semantics.Modules.Catalogue
public meta import CasCatalogue.Semantics.Modules.Bilinear.Valued.Catalogue

@[expose] public section

/-!
# A fused backend realization of formed-module cardinality (CC-ROUTE, CC-TRUST)

A backend answers "the cardinality of this Gram form" in one call, never building the underlying
set. It is registered as a second realization of the one semantic composite
`card ∘ Core(U_set ∘ ι_ℤ ∘ U_mod)`, keyed by that composite — not as a new `cardinality` of formed
modules — and, being unproved, as a trusted assertion.
-/

open CategoryTheory
open LeanCategories CasCatalogue.Modules.Bilinear.Valued.Actions
open CasCatalogue.Foundation.Cardinality CasCatalogue.Modules.CatalogueRegistration
open CasCatalogue.Modules.Bilinear.Valued.CatalogueRegistration

namespace CasCatalogue.Modules.Bilinear.Valued.Fused

/-- The backend's fused cardinality of a Gram form: `ℤ⁰` has one element, `ℤⁿ` for `n > 0` is
countable. -/
def fusedCardinality :
    TrustedImplementation (C := LeanCategories.Modules.Bilinear.Valued.BilinModuleCat ℤ ℤ)
      ((bilinModuleForgetDeclaration ℤ ℤ).toFunctor ⋙
        modulesFibreInclusionDeclaration.{0, 0} (RingCat.of ℤ) ⋙
        modulesUnderlyingDeclaration.{0, 0})
      setsCardinality.{0} gramDenotation cardinalDenotation where
  obj g := if g.rank = 0 then .finite 1 else .aleph0

/-- The same composite, realized by a backend that returns the rank it used as a certificate;
the checker compares it with the handle, and acceptance is proved to imply the answer. -/
def certifiedCardinality :
    CertifiedImplementation (C := LeanCategories.Modules.Bilinear.Valued.BilinModuleCat ℤ ℤ)
      ((bilinModuleForgetDeclaration ℤ ℤ).toFunctor ⋙
        modulesFibreInclusionDeclaration.{0, 0} (RingCat.of ℤ) ⋙
        modulesUnderlyingDeclaration.{0, 0})
      setsCardinality.{0} gramDenotation cardinalDenotation where
  obj g := cardinalityOf (.intPow g.rank)
  Certificate := ℕ
  certificate g := g.rank
  check g n := n == g.rank
  sound g _ := congrArg Discrete.mk (cardinalityOf_denote (.intPow g.rank))

end CasCatalogue.Modules.Bilinear.Valued.Fused

namespace CasCatalogue

register_leaf
  { backend := "lean"
    contributions := [
  .implementation
  { id := ⟨"impl.bilin_module.cardinality.fused"⟩, method := ⟨"meth.cardinality"⟩
    route := #[.functor FunctorId.bilinModuleForget, .functor FunctorId.modulesFibreInclusion,
      .functor FunctorId.modulesUnderlying]
    realization := `CasCatalogue.Modules.Bilinear.Valued.Fused.fusedCardinality
    backend := "probe-backend"
    trust := .trustedAssertion },
  .implementation
  { id := ⟨"impl.bilin_module.cardinality.certified"⟩, method := ⟨"meth.cardinality"⟩
    route := #[.functor FunctorId.bilinModuleForget, .functor FunctorId.modulesFibreInclusion,
      .functor FunctorId.modulesUnderlying]
    realization := `CasCatalogue.Modules.Bilinear.Valued.Fused.certifiedCardinality
    backend := "probe-certifying-backend"
    trust := .certificateChecked }] }

end CasCatalogue
