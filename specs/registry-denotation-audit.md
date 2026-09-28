# Registry denotation audit (`cc-p0-denotation-audit`)

Plan node: [`cc-p0-denotation-audit`](computational-core-plan.md). Requirements:
[CC-TRUE and CC-FIB](computational-core.md#cc-true--every-semantic-notion-is-standard-mathematics-from-step-0).
Revision audited: `eb00e55` (plus the documentation commit `07b4895`). Sources read:
`CasCatalogue/{Syntax,Realization,Interpretation}.lean`,
`CasCatalogue/Registry/{Entry,Extension}.lean`,
`CategoryTheory/OneCat/{Classifier,CategoricalPullback}.lean`, every
`normalized_registry .categoryFamily` registration, and FOUNDATIONS §§5, 13, 15, 19.

Verdicts:

- **exact** — the Lean datum denotes the stated mathematics, and registration checks it;
- **exact, unchecked** — the intended denotation is standard, but registration does not force it;
- **wrong object** — the datum denotes standard mathematics, but not the object FOUNDATIONS
  defines;
- **no denotation** — no precise mathematical object is stated.

## 1. Entry kinds and syntax constructors

| Kind / constructor | Denotation | Source | Verdict |
| --- | --- | --- | --- |
| `NamedCategoryEntry` | a category \(\mathcal C\in\mathfrak{Cat}\), with `realization` a witness that the expression evaluates to the declared `ObjCat` | FOUNDATIONS §1 | exact |
| `CategoryExpr.atom` | a named category | §1 | exact |
| `CategoryExpr.opaque`, `OpaqueCategoryEntry`, `StructuralPortEntry`, `FunctorExpr.opaquePort` | a category supplied only through chosen functors ("ports") out of it; the category's own construction is withheld | none stated | **no denotation** as a mathematical notion. "Opaque" is an engineering status, not mathematics. Each opaque entry must state which category it is (by citation) and each port which functor; the `reason : String` field records neither |
| `ClassifierEntry`, `Classifier C` (`OneCat/Classifier.lean`) | a morphism \(p:\mathcal E\to\mathcal C\) in \(\mathfrak{Cat}\), an object of \(\mathfrak{Cat}_{/\mathcal C}\) | FOUNDATIONS Def. 5.1; [BS07, §2.4] | exact (Def. 5.1 deliberately imposes no fibration condition) |
| `PropertyClassifier` | full and faithful \(p\) | FOUNDATIONS §6; [BS07, §2.4] | exact, unchecked in one respect: the docstring says repleteness is required "when available", but no field requires it, so the type admits non-replete full subcategories. Whether §6 requires repleteness was not re-read for this audit. |
| `StructureClassifier` | faithful \(p\) | §6; [BS07, §2.4] | exact |
| `CategoryExpr.classifierTotal`, `FunctorExpr.classifierForget` | the total category \(\mathcal E\) and the projection \(p\) | Def. 5.1 | exact |
| `CategoryExpr.refine`, `RefinementRealization`, `Classifier.reindex` | the reindexing \(F^{*}\mathcal E=\mathcal D\times_{\mathcal C}\mathcal E\) of a classifier along \(F:\mathcal D\to\mathcal C\), realized by Mathlib's `CategoricalPullback` (the 2-categorical pullback) | Def. 5.2 last paragraph; FOUNDATIONS §7 | exact for the pullback (registration requires `Classifier.reindex`). **Unchecked:** `baseToHost` is an arbitrary functor; `validateRefinementDeclarationRealization` does not require it to be the structural route from the base expression to the classifier's host. A refinement can therefore denote the pullback along the wrong functor. |
| `Reindexed` (the structure type) | a 2-commutative square | — | the type admits any square, not only a pullback; safe only because registration demands `Classifier.reindex`. |
| `FunctorEntry`, `FunctorExpr.atomic` | a functor between the realized endpoints | §1 | exact for endpoints. `FunctorRealization` records the endpoint realizations and the functor, but not the functor's *identity* as the declared one. Whether registration ties the realized functor to `declaration` is checked in `validateFunctorDeclarationRealization` (`Extension.lean`, l. 849), which this audit did not read in full. |
| `FunctorExpr.identity`, `FunctorExpr.comp` | identity and composition in \(\mathfrak{Cat}\); `evalFunctor` composes with `⋙` after checking the middle category by equality | §1 | exact. Composite evaluation fails (returns `none`) when the two middle `ObjCat`s are not *equal*; an equivalence between them is not used. That is correct for strict composition, and it is where CC-COHERE comparisons will be needed. |
| `NatTransExpr` (`identity`, `atomic`, `vcomp`, `hcomp`) | natural transformations with vertical and horizontal composition | Mathlib `NatTrans` | exact |
| `CategoryFamilyEntry`, `CategoryFamilyRealization`, `CategoryExpr.familyApp` | a pseudofunctor \(\mathrm{LocallyDiscrete}(P^{\mathrm{op}})\to\mathbf{Cat}\), and `familyApp` its value at a parameter | Mathlib `Pseudofunctor`; FOUNDATIONS §13.2 | the *type* is exact: a pseudofunctor out of \(P^{\mathrm{op}}\) is a contravariant family, whose Grothendieck construction is a cartesian fibration over \(P\). The entry does not name that fibration, and "parameterized family" is the only name it has. **See §2 for the families.** |
| `CategoryExpr.familyTotal`, `FunctorExpr.familyFibreInclusion`, `FunctorExpr.familyReindex` (added 2026-09-28) | the total category \(\int^{\mathrm c}\) of the family's transport, the fibre inclusion \(\iota_p\), and reindexing \(\varphi^{*}\) along a symbolic base morphism | Mathlib `Pseudofunctor.CoGrothendieck`, `CoGrothendieck.ι`; FOUNDATIONS §13.2 | exact: registration requires the canonical realizations `CategoryFamilyRealization.totalCat`, `fibreInclusionRealization`, `reindexRealization` of the registered family (`CasCatalogue/FamilyFibration.lean`; negative probes in `Modules/FibrationRegistryProbes.lean`). Contravariant families only; covariant families are open. |
| `FibrationEntry` (`.fibration`, added 2026-09-28) | a functor \(p:\mathcal E\to\mathcal B\) with a proof that it is a cartesian (`Functor.IsFibered`) or cocartesian (`Functor.IsCofibered`) fibration | FOUNDATIONS §31.1–31.2; Mathlib `FiberedCategory` | exact: registration checks that `evidence` proves the stated variance of exactly the realized projection (negative probes in `CasCatalogue/FibrationRegistration.lean`). Registered: `fib.modules` (cartesian, \(\int^{\mathrm c}\mathrm{Mod}\to\mathbf{Ring}\)), `fib.modules_ext` (cocartesian, \(\int\mathrm{Mod}\to\mathbf{CommRing}\)), `fib.bilin_forms` (cocartesian, \(p:\mathbf{Bil}\to\int\mathrm{Mod}\)). The discrete `bilWForm`/`bilinModule` families remain registered as the superseded coproduct encodings until their consumers move to `fib.bilin_forms`. |
| `CategoryExpr.construct`, `ConstructorEntry` (added 2026-09-28) | the value of a registered typed category constructor (a Lean definition `ObjCat → … → ObjCat`) at its arguments | Mathlib `Arrow`, `Core`, `Over`, `Under`, `Functor.Elements`, `ObjectProperty.FullSubcategory`, functor categories; #54 §1 | exact: registration requires the category to be definitionally the semantics applied to the registered denotations of its arguments (negative probe `coreAsArrows`) |
| `CategoryFamilySchema`, `ParameterExpr`, `ParameterSort`, `ParameterKindId` | the parameter category \(P\) and a symbolic presentation of its objects | — | **no denotation** beyond \(P\): the schema is a closed enumeration of six parameter *types*. Its five discrete schemas fix \(P\) to a discrete category (§2), so the schema, not the mathematics, chooses the base. |
| `CategoryFamilyTransportSemantics` (`restrictionOfScalars`, `discrete`) | a label of the transport's variance | — | a tag, not mathematics; the variance is already determined by the pseudofunctor. |

## 2. Registered families

Exactly one registered family names a nondiscrete base. The other eighteen are
`discreteFamilyTransport` over `Discrete P`, the pseudofunctor induced by a *function*
\(P\to\mathbf{Cat}\). Its Grothendieck construction is the coproduct
\(\coprod_{p\in P}\mathcal C_p\) over the discrete category on \(P\). That is honest
mathematics, but it forgets every morphism of the base. So wherever FOUNDATIONS defines
functoriality in the base, these entries denote the **wrong object**.

| Family | Schema, base \(P\) | Fibre | Registered denotation | FOUNDATIONS object | Verdict |
| --- | --- | --- | --- | --- | --- |
| `modules` | `ring`: \(\mathbf{Ring}\) | \(R\text{-}\mathbf{Mod}\) | Mathlib `RingCat.moduleCatRestrictScalarsPseudofunctor`; its Grothendieck construction is the cartesian fibration \(\int_R R\text{-}\mathbf{Mod}\to\mathbf{Ring}\) | §13.2, restriction-of-scalars variance | **exact** |
| `bilinModule` | `commRingModule`: discrete on \(\{(R,W)\}\) | \(\mathbf{Bil}_{R,W}\) | \(\coprod_{(R,W)}\mathbf{Bil}_{R,W}\) | §15.2 fibres, with change of values \(u_*\) (§15.5) and base change \(S\otimes_R-\) (§15.6) | **wrong object**: both transports of §15.5–15.6 are absent |
| `quadModule` | as above | \(\mathbf{Quad}_{R,W}\) | coproduct | §15.4–15.6 | **wrong object**, as above |
| `bilWForm` | `commRing`: discrete on \(\{R\}\) | `BilWFormCat R` | coproduct over rings | §15 with a varying value module (fibre not read in full) | **wrong object** (no base change); fibre's exact definition to be confirmed |
| `quadWForm` | `commRing` | `QuadWFormCat R` | coproduct | §15 | **wrong object**, as above |
| `lattice`, `finiteProjectiveLattice`, `finiteFreeLattice` | `commRingModule` | lattices over \(R\) with values in \(W\) | coproduct | §19.2 (\(R\) Dedekind, values in \(R\)); valued generalizations in the lattice source files | **wrong object**, and **open base**: which ring maps preserve the lattice conditions (finite projectivity is preserved by extension of scalars; nondegeneracy over the fraction field needs \(K\to L\), so injective maps of domains) is a mathematical choice not yet made |
| `integralLattice`, `evenLattice` | `commRing` | \(\mathbf{Lat}\) variants | coproduct | §19.5: even lattices are *reindexings of the evenness classifier along* \(\mathbf{Lat}_{\mathbb Z}\to\mathbf{SymBil}_{\mathbb Z,\mathbb Z}\) | **wrong kind**: FOUNDATIONS makes even lattices a classifier refinement over \(\mathbb Z\), not a family over all commutative rings |
| `unimodularLattice`, `fractionFieldPerfectFiniteProjectiveLattice` | `domain`: discrete on \(\{(R,\ \mathrm{IsDomain}\ R)\}\) | lattice variants | coproduct over domains | §19.1–19.5 require a Dedekind domain; unimodularity is §19.5's perfectness classifier | **wrong base** (domain, not Dedekind) and **wrong kind** for unimodular (a refinement, per §19.5) |
| `coordLattice` | `commRingNat`: discrete on \(\{(R,n)\}\) | coordinatized lattices | coproduct | §21 (Gram descriptions) | **wrong object** if §21 defines base change (not read in full) |
| `genFrame`, `basisFrame` | `commRingNat` | \(\operatorname{GenFrame}_n(R)\), \(\operatorname{BasisFrame}_n(R)\) | coproduct | §13.5: loci in the comma category \((R^n\downarrow R\text{-}\mathbf{Mod})\). Extension of scalars preserves surjections (right exactness) and isomorphisms, so both vary covariantly in \(R\) | **wrong object**: the cocartesian transport exists and is absent. Discreteness in \(n\) is correct: a map \(R^n\to R^m\) does not carry frames to frames |
| `coord` | `commRingNat` | \(\operatorname{Coord}_n(R)\) | coproduct | §13.6 | **wrong object**, as for frames |
| `genFrameIndexed`, `basisFrameIndexed`, `coordIndexed` | `commRingIndexType`: discrete on \(\{(R,I)\}\), \(I\) a type | arbitrary-index versions | coproduct | §13.5–13.6 with index set \(I\) | **wrong object** in \(R\), as above. The index is a *type*, taken up to equality; the mathematically meaningful base is the groupoid of sets and bijections (a bijection \(I\cong J\) transports frames), so equality is also too coarse in \(I\) |

## 3. Findings

1. **One family out of nineteen names the fibration FOUNDATIONS defines.** `modules` is
   exact. The other eighteen are coproducts over a discrete set of parameters and cannot
   express change of rings, change of value module, or reindexing of an index set. By
   CC-FIB, "the lattices over \(R\) with values in \(W\)" must be the fibre of a stated
   fibration, and at present it is a component of a coproduct.
2. **The schema chooses the base, not the mathematics.** `CategoryFamilySchema` is a closed
   enumeration of parameter types, five of them wrapped in `Discrete`. A family cannot
   declare its correct base (e.g. the total module category with its morphisms) without
   adding a schema case.
3. **Lattice families are refinements registered as families.** FOUNDATIONS §19.5 defines even
   and unimodular lattices as reindexings of classifiers; per §4 every lattice family is. As families over all commutative
   rings (`evenLattice`) or domains (`unimodularLattice`), they denote a different object.
4. **The lattice base is weaker than FOUNDATIONS.** `domain` requires `IsDomain`; §19.1
   requires a Dedekind domain.
5. **Refinement `baseToHost` is unchecked** (§1). A refinement's pullback can be taken along
   a functor other than the structural route.
   *Partly repaired 2026-09-28:* when the base is the classifier's host, `baseToHost` must be
   the identity (negative probe `badLatticesRefinement`); a base other than the host must be
   reindexed along a registered functor from the base to the host (negative probe
   `badIntegralFormsRefinement`, a constant section); `cat.integral_forms` is the first such
   refinement, the pullback of `Bil` along the regular section `R ↦ (R, R)`. Registering the first refinement
   (`cat.lattices_over_rings`) also exposed that the refinement validator checked the
   classifier datum where its total category belongs; fixed in the same change.
6. **Opaque categories and ports have no denotation.** They must cite the category and
   functors they stand for, or be removed from the semantic catalogue.
7. **Property classifiers do not require repleteness.**

## 4. Mathematical determinations (owner rulings, 2026-09-28)

These were first posed here as "decisions". They are not: the mathematics determines each
of them, and the specification's job is to state it correctly. Recorded as determined:

- **Forms.** \(\mathbf{Bil}\) and \(\mathbf{Quad}\) are fibred over the total module category
  over \(\mathbf{CommRing}\), whose morphisms are \((\varphi:R\to S,\ u:S\otimes_R W\to W')\),
  with transport \(u_*\circ(S\otimes_R-)\) (FOUNDATIONS §15.5–15.6). This is a covariant
  pseudofunctor, so forms form a **cocartesian** fibration. The ambient flexible category
  is the bilinear-module category \(\mathbf{Bil}\), its total category.
- **Lattices are not a fibration and are not closed under base change.** A lattice is an
  object of \(\mathbf{Bil}\) satisfying conditions (finite projectivity, nondegeneracy over
  the fraction field, integrality, …). Each condition is a **classifier on \(\mathbf{Bil}\)**
  (a property, reindexed where needed), and "lattices" is the resulting refinement of
  \(\mathbf{Bil}\), not a family over rings. Base change, cokernels (hence discriminant
  forms), and morphisms such as \(L\to L^{\#}\) and \(L\to L^{*}\) are formed in
  \(\mathbf{Bil}\), where they exist. Whether a condition survives a given base change is a
  **theorem** about that classifier along that map, never registry structure. So the seven
  lattice families (`lattice`, `finiteProjectiveLattice`, `finiteFreeLattice`,
  `integralLattice`, `evenLattice`, `unimodularLattice`,
  `fractionFieldPerfectFiniteProjectiveLattice`) are **wrong kind**: each must become a
  refinement of \(\mathbf{Bil}\) (or of its fibre over a fixed base) by the relevant
  classifiers.
- **Integrality and modularity are conditions on the maps \(L\to L^{\#I}\).** The metric
  \(I\)-dual is \(L^{\#I}:=\ker\bigl(L_K\to\operatorname{Hom}_R(L,K/I)\bigr)\), already defined
  in `LeanCategories/Lattices/Valued/IdealDual.lean` (`fractionalIdealDual`, `idealDual`).
  - *\(I\)-integrality:* the canonical map \(L\to L_K\) factors through \(L^{\#I}\), i.e. a
    map \(L\to L^{\#I}\) exists over \(L_K\) (`IsIIntegral`, equivalent to
    `CanonicalMapLiftsToIdealDual` by `isIIntegral_iff_canonicalMapLiftsToIdealDual`).
    Integrality is the case \(I=R\): the map \(L\to L^{\#R}\).
  - *\(I\)-modularity:* that factorization is an isomorphism, \(L=L^{\#I}\) (`IsIModular`).
    Metric unimodularity (FOUNDATIONS §18, \(L^{\#R}=L\)) is the case \(I=R\).

  Both are properties of objects of \(\mathbf{Bil}\) (over the lattice base), so they are
  classifiers on \(\mathbf{Bil}\), not category families.

  *Transport to quadratic forms, and evenness.* The theory transports from bilinear to
  quadratic forms along the diagonal functor
  \[
  \Delta:\mathbf{Bil}_{R,W}\longrightarrow\mathbf{Quad}_{R,W},\qquad
  (M,b)\longmapsto\bigl(M,\;q_b(v):=b(v,v)\bigr).
  \]
  Evenness of \((L,b)\) is the \(I=2R\) case of the transported \(I\)-integrality, evaluated at
  \(\Delta(L,b)\): \(q_b(L)\subseteq 2R\). So `evenLattice` is not a separate notion. It is the
  reindexing along \(\Delta\) of the quadratic-side classifier at \(I=2R\), and it is
  re-expressed that way. The quadratic-side definitions (the transported \(I\)-dual and
  \(I\)-modularity on \(\mathbf{Quad}\)) are written in FOUNDATIONS §17 as this transport
  before the code changes.
- **Frames are abandoned.** "Frame" conflicts with its standard meaning (a framed manifold
  is a framed bundle), so `genFrame`, `basisFrame`, `coord`, and their `Indexed` versions
  do not denote the intended notion, and neither do FOUNDATIONS §13.5–13.6 and
  `LeanCategories.Modules.Framed`. The intended theory is **resolutions**: a presentation of
  a module is an augmented resolution (possibly infinite), the classical presentation
  \(F_1\to F_0\to M\to 0\) is its 2-truncation, and these should be instances of a general
  theory of resolutions (projective/free, simplicial, cofibrant replacement, or
  comonadic/bar resolutions [Weibel, *An Introduction to Homological Algebra*, Ch. 2 (projective
  resolutions) and Ch. 8 (simplicial methods, cotriple resolutions)]). A framed bundle is then a bundle with a resolution satisfying further conditions,
  of which the trivialization condition is one; stating the full set with sources is
  `cc-resolutions`' work. A chosen basis (\(\operatorname{Coord}_n\)'s
  objects) is the degenerate case of a free resolution of length zero.

Consequences for `cc-fib`: register \(\mathbf{Bil}\) and \(\mathbf{Quad}\) as cocartesian
fibrations over the total module category; re-express the seven lattice families as
classifier refinements of \(\mathbf{Bil}\); retire the six frame families, and FOUNDATIONS
§13.5–13.6, in favour of a resolutions section (a new node, `cc-resolutions`, whose
mathematics must be stated before any code).

## 5. Coverage

Read in full: the files listed at the top, and every family registration. Not read in full:
`validateFunctorDeclarationRealization` and the other validators of `Extension.lean`
beyond the refinement validator; the fibre definitions of `BilWFormCat`, `QuadWFormCat`
and `CoordLatticeCat`; FOUNDATIONS §§17, 21, 83–86. Conclusions about those are marked in
the tables. Confidence in §2's structural finding (discrete versus nondiscrete bases) is
high: it is read directly from each registration's `P := Discrete …` and
`discreteFamilyTransport`.

## 6. `cc-fib` route for forms, from reuse search (2026-09-28)

Searched the live `formalization-corpus` API (`scripts/formalization_corpus.py search`) for:
`BilinForm baseChange`, `QuadraticForm baseChange`, `bilinear form fibration`,
`category of quadratic modules`, `QuadraticModuleCat`, `Pseudofunctor Grothendieck ModuleCat`,
`moduleCatExtendScalarsPseudofunctor`, `IsCocartesian`, `IsStronglyCocartesian`,
`cocartesian fibration`, `displayed category`, `Pseudofunctor.Grothendieck`,
`Grothendieck isStronglyCocartesian`, `opfibration`.

Found and reused:

- Mathlib `CategoryTheory/Bicategory/Grothendieck.lean` (`Pseudofunctor.Grothendieck`,
  `CoGrothendieck`) and `CategoryTheory/FiberedCategory/Cocartesian.lean`
  (`IsCocartesian`, `IsStronglyCocartesian`);
- this repository's `ForMathlib/GrothendieckCocartesian.lean`: strongly cocartesian lifts
  for every covariant `Pseudofunctor.Grothendieck` (the dual of Mathlib's cartesian case);
- this repository's `Lattices/Valued/BaseChange.lean`: `baseChangeBilWForm` with its
  identity and composition isomorphisms, and `Modules/Bilinear/Valued/Total.lean`:
  `BilWFormCat R`, the change-of-values Grothendieck construction over `ModuleCat R`;
- Mathlib `LinearMap.BilinMap.baseChange`, `QuadraticModuleCat` (fixed `R`, values in `R`),
  and the coherence pattern of `CommRingCat.moduleCatExtendScalarsPseudofunctor`.

Reference implementations, not imported: `sinhp/LeanFibredCategories` and `sinhp/HoTTLean`
(Lean 4 Grothendieck fibrations and displayed categories), UniMath (Rocq) displayed
categories and `GrothendieckConstruction/IsOpfibration.v`, and 1Lab bifibrations.

Not found under any formulation: forms over varying rings as a fibration or pseudofunctor.

Route: add the three pseudofunctor coherence laws (associativity and the two unit laws)
for `baseChangeBilWFormCompositionIso` and `baseChangeBilWFormIdentityIso` at their owner
`BaseChange.lean`, following Mathlib's `extendScalars_assoc'`, `extendScalars_id_comp` and
`extendScalars_comp_id`; assemble `R ↦ BilWFormCat R` with `LocallyDiscrete.mkPseudofunctor`;
the total forms category is its `Pseudofunctor.Grothendieck`, and cocartesianness is the
existing `ForMathlib` theorem. No new fibration theory and no second total-category
definition is authored.

**Delivered (forms over rings).** `Lattices/Valued/BaseChangeCoherence.lean` proves the
associativity and both unit laws for the existing base-change isomorphisms
(`baseChangeBilWForm_assoc`, `_id_comp`, `_comp_id`, via the module-level identities
`cancelBaseChange_assoc`, `cancelBaseChange_id_left`, `cancelBaseChange_id_right`);
`Lattices/Valued/BaseChangePseudofunctor.lean` assembles `bilinBaseChangePseudofunctor`
on `LocallyDiscrete CommRingCat`, defines `BilinFormsOverRings` as its Grothendieck
construction (fibre over `R` = `BilWFormCat R`), and obtains strong cocartesianness of base
change from the existing `ForMathlib` theorem. Additional searches before the coherence
proofs: `cancelBaseChange`, `cancelBaseChange assoc`, `baseChange baseChange tensor assoc`,
`extendScalarsComp`, `BilinMap.baseChange`, `base change pseudofunctor coherence`,
`IsScalarTower tensor cancel`, `pseudofunctor extension of scalars associativity`, and the
broader fibration queries (`Grothendieck construction`, `cartesian fibration`,
`cocartesian lift`, `bifibration`, `category of elements`, `fibred category`,
`Beck-Chevalley`, `indexed category`, and `repo:infinity-cosmos` fibration/cartesian/
isofibration/Grothendieck). No source states these coherence laws; TauCeti's affine group
scheme base change records them as unproved. Remaining for `cc-fib`: `Quad` (same pattern),
the seven lattice families re-expressed as classifier refinements of `Bil`, and the registry
entries for the new fibration.

**Correction: the forms fibration is a fibration over the module fibration.** `BilWFormCat R`
is not a category parameterized by `W`; it is the fibre over `R` of the composite
`Bil →p ∫Mod →q CommRing`, with `p⁻¹(R, W) = Bil_{R,W}` and `q⁻¹(R) = R-Mod`, where `∫Mod`
carries extension of scalars (the cocartesian module fibration,
`CommRingCat.moduleCatExtendScalarsPseudofunctor`). `BilinFormsOverRings` (`26d5a17`)
has the right total category and the composite `q ∘ p`, but it does not construct `p`,
and its docstring's framing ("fibre over `R` is `BilWFormCat R`") repeats the
parameterized-family reading.

The route to `p` is not a hand-built comparison but the universal property of the
Grothendieck construction as an (op)lax colimit (the 2-adjunction `∫ ⊣` straightening):
a pseudofunctor `Φ : ∫Mod → Cat`, `(R, W) ↦ Bil_{R,W}`, is the same as a lax cocone on
`R ↦ R-Mod` — fibrewise functors `Φ_R : R-Mod → Cat` (`valueFibers R`), transition
2-cells `Φ_R ⇒ Φ_S ∘ (S ⊗_R -)` (base change of forms), and their coherence (proved in
`BaseChangeCoherence.lean`). Then `Bil := ∫ Φ`, `p` is its projection, `BilWFormCat R` is
its pullback along the fibre inclusion, and `q ∘ p` is cocartesian by composition.

Search (formalization-corpus API): `GrothendieckEquiv`, `Grothendieck of Grothendieck`,
`Grothendieck sigma equivalence`, `Grothendieck construction associativity`,
`Grothendieck Fubini`, `pseudofunctor on Grothendieck construction`,
`composition of cocartesian fibrations`, `IsStronglyCocartesian comp functor`,
`pullback of fibration is fibration`, `Grothendieck.pre`, `straightening unstraightening`.
Found: Mathlib `Grothendieck.functorFrom` (strict `F : C ⥤ Cat` only); UniMath
`Bicategories/Grothendieck/{Unit,Counit,FibrationToPseudoFunctor}.v` (the biadjunction, as a
reference implementation); HoTTLean `attic/ForMathlib/GrothendieckEquiv.lean` and
`sinhp/displayed_categories` (straightening, pullback of fibrations), to be read before use;
UniMath `DisplayedCats/Fibrations.v` (composition of cocartesian fibrations). Residue: the
pseudofunctor analogue of `functorFrom` (a pseudofunctor out of `Pseudofunctor.Grothendieck`
from a lax cocone), as generic `ForMathlib` glue following UniMath.

**Delivered (`p`, 2026-09-28).** The route above was replaced by FOUNDATIONS Proposition
31.2b, which needs no pseudofunctor on `∫Mod` (the lax-cocone theorem stays filed in
COMPLAINTS). `Lattices/Valued/ValueFibration.lean` builds the strong transformation
`valueProjectionTrans : bilinBaseChangePseudofunctor ⟶ moduleCatExtendScalarsPseudofunctor`
(components `valueProjection R`, identity naturality, coherence from
`extendScalarsComp_hom_app_eq`/`extendScalarsId_hom_app_eq`), sets
`p = BilinFormsOverRings.values := Grothendieck.map valueProjectionTrans` with
`p ⋙ q = BilinFormsOverRings.ring` by `rfl`, and proves `p.IsCofibered` from the generic
`Pseudofunctor.Grothendieck.isCofibered_map`. Generic residue, each filed in COMPLAINTS
(LC-11) and proved in `ForMathlib`: `Functor.IsCofibered` (`Cofibered.lean`), the transfer
lemma `Functor.IsStronglyCocartesian.map_of_exists`, `Grothendieck.isStronglyCocartesian_of_isIso_fiber`,
`LocallyDiscrete.mkStrongTrans`, and Proposition 31.2b itself
(`GrothendieckMapCocartesian.lean`). The fibre equivalence `Fiber p (R, W) ≌ BilinModuleCat R W` is
`BilinFormsOverRings.fibreEquivalence` (`ForMathlib/GrothendieckFibers.lean`). Not yet constructed: the `Quad`
analogue (`cc-quad-basechange`), the lattice refinements, and the registry entries.
