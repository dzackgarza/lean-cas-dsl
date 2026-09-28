LA='LeanCategories.Algebra'; LF='LeanCategories.Foundation'; AN='LeanCategories.Analytic'
cats=[
("ringPoints","cat.ring_points",f"{LA}.RingPoints.{{0}}","elements of commutative rings"),
("ufdPoints","cat.ufd_points",f"{LA}.UFDPoints.{{0}}","elements of unique factorization domains"),
("pidPoints","cat.pid_points",f"{LA}.PIDPoints.{{0}}","elements of principal ideal domains"),
("euclideanPoints","cat.euclidean_points",f"{LA}.EuclideanPoints.{{0}}","elements of euclidean domains"),
("polyPoints","cat.poly_points",f"{LA}.PolyPoints.{{0}}","polynomials over commutative rings"),
("domainPolyPoints","cat.domain_poly_points",f"{LA}.DomainPolyPoints.{{0}}","polynomials over domains"),
("ufdPolyPoints","cat.ufd_poly_points",f"{LA}.UFDPolyPoints.{{0}}","polynomials over unique factorization domains"),
("fieldPolyPoints","cat.field_poly_points",f"{LA}.FieldPolyPoints.{{0}}","polynomials over fields"),
("matrixPoints","cat.matrix_points",f"{LA}.MatrixPoints.{{0}}","square matrices over commutative rings"),
("enumerations","cat.enumerations",f"{LF}.Enumerations.{{0}}","sets with an order of their elements"),
("finiteLists","cat.finite_lists",f"{LF}.FiniteLists.{{0}}","finite subsets presented as duplicate-free lists"),
("ringFiniteLists","cat.ring_finite_lists",f"{LF}.RingFiniteLists.{{0}}","finite subsets of commutative rings"),
("multisetPoints","cat.multiset_points",f"{LF}.MultisetPoints.{{0}}","multisets"),
("complexPoints","cat.complex_points",f"{AN}.ComplexPoints","points of ℂ"),
("realPoints","cat.real_points",f"{AN}.RealPoints","points of ℝ"),
("functionPoints","cat.function_points",f"{AN}.FunctionPoints.{{0}}","functions between sets"),
("realFunctionPoints","cat.real_function_points",f"{AN}.RealFunctionPoints","real functions"),
("schemesOverQ","cat.schemes_over_q","LeanCategories.Schemes.SchemesOverRationals","schemes over ℚ"),
("factorizations","cat.values.factorizations",f"{LA}.UFD.factorizationSets.{{0}}.Elements","sets of factorizations"),
("gcdValues","cat.values.gcds",f"{LA}.UFD.gcdSets.{{0}}.Elements","greatest common divisors"),
("propositions","cat.values.propositions","Discrete Prop","truth values"),
("polyValues","cat.values.polynomials",f"(Core.inclusion CommRingCat.{{0}} ⋙ {LA}.polyCarrier.{{0}}).Elements","polynomials"),
("polySetValues","cat.values.polynomial_sets",f"(Core.inclusion CommRingCat.{{0}} ⋙ {LA}.polyCarrier.{{0}} ⋙ {LF}.powersetFunctor).Elements","sets of polynomials"),
("degrees","cat.values.degrees","Discrete (WithBot ℕ)","degrees"),
("matrixSetValues","cat.values.matrix_sets",f"(Core.inclusion CommRingCat.{{0}} ⋙ {LA}.Poly.squareMatrices.{{0}} ⋙ {LF}.powersetFunctor).Elements","sets of square matrices"),
("rootValues","cat.values.roots",f"(Core.inclusion {LA}.DomainCat.{{0}} ⋙ {LA}.domainToCommRing ⋙ {LA}.ringCarrier ⋙ {LF}.multisetFunctor).Elements","multisets of roots"),
("ringValues","cat.values.ring_elements",f"(Core.inclusion CommRingCat.{{0}} ⋙ {LA}.ringCarrier.{{0}}).Elements","ring elements"),
("naturals","cat.values.naturals","Discrete ℕ","natural numbers"),
("vectorSetValues","cat.values.vector_sets",f"(Core.inclusion CommRingCat.{{0}} ⋙ {LA}.Mat.vectors.{{0}} ⋙ {LF}.powersetFunctor).Elements","sets of vectors"),
("subsetOperations","cat.values.subset_operations",f"{LF}.ambientSubsetOperations.{{0}}.Elements","operations on subsets"),
("sequenceValues","cat.values.sequences",f"(Core.inclusion (Type) ⋙ {LF}.seqFunctor.{{0}}).Elements","partial sequences"),
("pointPredicateValues","cat.values.point_predicates",f"{LF}.pointPredicates.{{0}}.Elements","predicates on elements"),
("subsetPredicateValues","cat.values.subset_predicates",f"{LF}.subsetPredicates.{{0}}.Elements","predicates on subsets"),
("approximationValues","cat.values.approximations","Discrete (ℚ → Set (ℚ × ℚ))","sets of approximations"),
("limitValues","cat.values.limits","Discrete (EReal → Set EReal)","sets of limits"),
("integralValues","cat.values.integrals","Discrete (ℝ → ℝ → ℝ)","definite integrals"),
("taylorValues","cat.values.taylor","Discrete (ℕ → Polynomial ℝ)","Taylor polynomials"),
]
EXIST={"subobjectsSets":("Constructed.SubobjectsSets","CasCatalogue.Catalogue.ConstructorRegistration.subobjectsSetsCategory.{0}","CasCatalogue.Catalogue.ConstructorRegistration.subobjectsSetsRealization"),
 "coreSubobjectsSets":("Foundation.Subsets.CoreSubobjectsSets","CasCatalogue.Foundation.Subsets.coreSubobjectsSetsCategory.{0}","CasCatalogue.Foundation.Subsets.coreSubobjectsSetsRealization"),
 "subsetPredicates":("Foundation.Subsets.SubsetPredicates","CasCatalogue.Foundation.Subsets.subsetPredicatesCategory.{0}","CasCatalogue.Foundation.Subsets.subsetPredicatesCategoryRealization")}
funs=[
("euclideanToPid","fun.euclidean_points.pid","euclideanPoints","pidPoints",f"{LA}.euclideanPointsToPID.{{0}}",True),
("pidToUfd","fun.pid_points.ufd","pidPoints","ufdPoints",f"{LA}.pidPointsToUFD.{{0}}",True),
("ufdToRing","fun.ufd_points.ring","ufdPoints","ringPoints",f"{LA}.ufdPointsToRing.{{0}}",True),
("domainPolyToPoly","fun.domain_poly_points.poly","domainPolyPoints","polyPoints",f"{LA}.domainPolyToPoly.{{0}}",True),
("ufdPolyToDomainPoly","fun.ufd_poly_points.domain_poly","ufdPolyPoints","domainPolyPoints",f"{LA}.ufdPolyToDomainPoly.{{0}}",True),
("ufdPolyToUfd","fun.ufd_poly_points.ufd_points","ufdPolyPoints","ufdPoints",f"{LA}.ufdPolyToUFDPoints.{{0}}",True),
("fieldPolyToDomainPoly","fun.field_poly_points.domain_poly","fieldPolyPoints","domainPolyPoints",f"{LA}.fieldPolyToDomainPoly.{{0}}",True),
("fieldPolyToEuclidean","fun.field_poly_points.euclidean_points","fieldPolyPoints","euclideanPoints",f"{LA}.fieldPolyToEuclideanPoints.{{0}}",True),
("finiteListsToEnumerations","fun.finite_lists.enumeration","finiteLists","enumerations",f"{LF}.listSequence.{{0}}",True),
("enumerationsToSubsets","fun.enumerations.subset","enumerations","subobjectsSets",f"{LF}.enumerationRange.{{0}}",True),
("ringFiniteListsForget","fun.ring_finite_lists.forget","ringFiniteLists","finiteLists",f"{LF}.ringFiniteListsForget.{{0}}",True),
("realToComplex","fun.real_points.complex","realPoints","complexPoints",f"{AN}.realToComplex",True),
("realFunctionToFunction","fun.real_function_points.function","realFunctionPoints","functionPoints",f"{AN}.realFunctionToFunction",True),
("factor","fun.ufd_points.factor","ufdPoints","factorizations",f"{LA}.UFD.factor.{{0}}",False),
("gcd","fun.ufd_points.gcd","ufdPoints","gcdValues",f"{LA}.UFD.gcd.{{0}}",False),
("isPrime","fun.ufd_points.is_prime","ufdPoints","propositions",f"{LA}.UFD.isPrime.{{0}}",False),
("derivative","fun.poly_points.derivative","polyPoints","polyValues",f"{LA}.Poly.derivativeMethod.{{0}}",False),
("antiderivative","fun.poly_points.antiderivative","polyPoints","polySetValues",f"{LA}.Poly.antiderivativesMethod.{{0}}",False),
("deg","fun.poly_points.deg","polyPoints","degrees",f"{LA}.Poly.degreeMethod.{{0}}",False),
("companion","fun.poly_points.companion_matrix","polyPoints","matrixSetValues",f"{LA}.Poly.companionMethod.{{0}}",False),
("roots","fun.domain_poly_points.roots","domainPolyPoints","rootValues",f"{LA}.Poly.rootsMethod.{{0}}",False),
("det","fun.matrix_points.det","matrixPoints","ringValues",f"{LA}.Mat.detMethod.{{0}}",False),
("trace","fun.matrix_points.trace","matrixPoints","ringValues",f"{LA}.Mat.traceMethod.{{0}}",False),
("charpoly","fun.matrix_points.charpoly","matrixPoints","polyValues",f"{LA}.Mat.charpolyMethod.{{0}}",False),
("inverse","fun.matrix_points.inverse","matrixPoints","matrixSetValues",f"{LA}.Mat.inverseMethod.{{0}}",False),
("matrixRank","fun.matrix_points.rank","matrixPoints","naturals",f"{LA}.Mat.rankMethod.{{0}}",False),
("matrixKer","fun.matrix_points.ker","matrixPoints","vectorSetValues",f"{LA}.Mat.kernelMethod.{{0}}",False),
("union","fun.subsets.union","coreSubobjectsSets","subsetOperations",f"{LF}.subsetUnion.{{0}}",False),
("intersect","fun.subsets.intersect","coreSubobjectsSets","subsetOperations",f"{LF}.subsetInter.{{0}}",False),
("diff","fun.subsets.diff","coreSubobjectsSets","subsetOperations",f"{LF}.subsetDiff.{{0}}",False),
("symdiff","fun.subsets.symdiff","coreSubobjectsSets","subsetOperations",f"{LF}.subsetSymmDiff.{{0}}",False),
("subset","fun.subsets.subset","coreSubobjectsSets","subsetPredicates",f"{LF}.subsetOf.{{0}}",False),
("nth","fun.enumerations.nth","enumerations","sequenceValues",f"{LF}.nth.{{0}}",False),
("sum","fun.ring_finite_lists.sum","ringFiniteLists","ringValues",f"{LF}.finiteSum.{{0}}",False),
("prod","fun.ring_finite_lists.prod","ringFiniteLists","ringValues",f"{LF}.finiteProd.{{0}}",False),
("multisetContains","fun.multiset_points.contains","multisetPoints","pointPredicateValues",f"{LF}.multisetContains.{{0}}",False),
("multisetCard","fun.multiset_points.cardinality","multisetPoints","naturals",f"{LF}.multisetCard.{{0}}",False),
("multisetEquals","fun.multiset_points.set_eq","multisetPoints","subsetPredicateValues",f"{LF}.multisetEquals.{{0}}",False),
("multisetSubset","fun.multiset_points.subset","multisetPoints","subsetPredicateValues",f"{LF}.multisetSubsetOf.{{0}}",False),
("re","fun.complex_points.re","complexPoints","realPoints",f"{AN}.re",False),
("im","fun.complex_points.im","complexPoints","realPoints",f"{AN}.im",False),
("bar","fun.complex_points.bar","complexPoints","complexPoints",f"{AN}.conj",False),
("abs","fun.complex_points.abs","complexPoints","realPoints",f"{AN}.abs",False),
("approximate","fun.complex_points.approximate","complexPoints","approximationValues",f"{AN}.approximations",False),
("image","fun.function_points.image","functionPoints","subobjectsSets",f"{AN}.image.{{0}}",False),
("limit","fun.real_function_points.limit","realFunctionPoints","limitValues",f"{AN}.limits",False),
("integral","fun.real_function_points.definite_integral","realFunctionPoints","integralValues",f"{AN}.integral",False),
("taylor","fun.real_function_points.taylor_expansion","realFunctionPoints","taylorValues",f"{AN}.taylor",False),
]
# (method id, name, owner key, functor key, shape)
meths=[("factor","factor","ufdPoints","factor","object"),("gcd","gcd","ufdPoints","gcd","object"),("is_prime","is_prime","ufdPoints","isPrime","object"),
("derivative","derivative","polyPoints","derivative","object"),("antiderivative","antiderivative","polyPoints","antiderivative","object"),
("deg","deg","polyPoints","deg","object"),("companion_matrix","companion_matrix","polyPoints","companion","object"),
("roots","roots","domainPolyPoints","roots","object"),
("det","det","matrixPoints","det","object"),("trace","trace","matrixPoints","trace","object"),("charpoly","charpoly","matrixPoints","charpoly","object"),
("inverse","inverse","matrixPoints","inverse","object"),("matrix_rank","rank","matrixPoints","matrixRank","object"),("matrix_ker","ker","matrixPoints","matrixKer","object"),
("union","union","subobjectsSets","union","isoInvariant"),("intersect","intersect","subobjectsSets","intersect","isoInvariant"),
("diff","diff","subobjectsSets","diff","isoInvariant"),("symdiff","symdiff","subobjectsSets","symdiff","isoInvariant"),("subset","subset","subobjectsSets","subset","isoInvariant"),
("nth","nth","enumerations","nth","object"),("sum","sum","ringFiniteLists","sum","object"),("prod","prod","ringFiniteLists","prod","object"),
("multiset_contains","contains","multisetPoints","multisetContains","object"),("multiset_cardinality","cardinality","multisetPoints","multisetCard","object"),
("multiset_set_eq","set_eq","multisetPoints","multisetEquals","object"),
("multiset_subset","subset","multisetPoints","multisetSubset","object"),
("complex_re","re","complexPoints","re","object"),("complex_im","im","complexPoints","im","object"),("bar","bar","complexPoints","bar","object"),("abs","abs","complexPoints","abs","object"),
("approximate","approximate","complexPoints","approximate","object"),("image","image","functionPoints","image","object"),
("limit","limit","realFunctionPoints","limit","object"),("definite_integral","definite_integral","realFunctionPoints","integral","object"),
("taylor_expansion","taylor_expansion","realFunctionPoints","taylor","object")]
def cap(s): return s[0].upper()+s[1:]
out=[]
w=out.append
w('''/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CasCatalogue.Leaves.Foundation.Subsets
public import LeanCategories.Algebra.Concrete.MatrixElements
public import LeanCategories.Foundation.SetOperations
public import LeanCategories.Analytic.Points
public import LeanCategories.Schemes.OverRationals
public meta import CasCatalogue.Registry.Extension
public meta import CasCatalogue.ConstructorCatalogue
public meta import CasCatalogue.Leaves.Foundation.Subsets

@[expose] public section

/-!
# Elements of structured objects, sets, and function spaces (`cc-dsl-migration`)

The categories, structural functors and methods of the notebook surface's element-level
universe, registered from `lean-categories` (`LeanCategories.Foundation.IsoElements`,
`…Algebra.Concrete.{Ring,Polynomial,Matrix}Elements`, `…Foundation.SetOperations`,
`…Analytic.Points`, `…Schemes.OverRationals`):

* points of classes of rings (euclidean ⊆ PID ⊆ UFD ⊆ commutative rings), of polynomial rings
  and matrix rings, with the structural functors between them (inclusions of classes; `K[X]` is
  euclidean, `R[X]` is a UFD over a UFD);
* enumerations, finite enumerated subsets (over rings: `sum`, `prod`), multisets;
* points of `ℂ`, `ℝ`, and of function spaces;
* the value categories of the methods (categories of elements of the value functors).

Each method row names the functor whose object map is the operation (Mathlib's function, or the
set of admissible answers where the answer is a choice). This module is generated from one table;
it holds registrations only (generated by `scripts/gen_elements_catalogue.py`).
-/

open CategoryTheory

namespace CasCatalogue

namespace CategoryId''')
for n,i,t,d in cats: w(f'def {n} : CategoryId := ⟨"{i}"⟩')
w('end CategoryId\n\nnamespace FunctorId')
for n,i,s,tg,t,st in funs: w(f'def {n} : FunctorId := ⟨"{i}"⟩')
w('end FunctorId\n\nnamespace Elements\n')
for n,i,t,d in cats: w(f'def {cap(n)} : CategoryExpr := .atom CategoryId.{n}')
def expr(k): return EXIST[k][0] if k in EXIST else cap(k)
def catdecl(k): return EXIST[k][1] if k in EXIST else f'{k}Category'
def catreal(k): return EXIST[k][2] if k in EXIST else f'{k}Realization'
for n,i,s,tg,t,st in funs: w(f'def {cap(n)}Expr : FunctorExpr {expr(s)} {expr(tg)} := .atomic FunctorId.{n}')
w('\nnoncomputable section\n')
for n,i,t,d in cats:
    ty = 'LeanCategories.ObjCat.{1, 1}' if n=='functionPoints' else 'LeanCategories.ObjCat'
    w(f'/-- The category of {d}. -/\ndef {n}Category : {ty} := Cat.of ({t})')
    w(f'def {n}Realization : CategoryRealization {cap(n)} {n}Category := {{}}')
for n,i,s,tg,t,st in funs:
    w(f'def {n}Declaration : {catdecl(s)} ⥤ {catdecl(tg)} := {t}')
    w(f'def {n}Realization : FunctorRealization {cap(n)}Expr {catdecl(s)} {catdecl(tg)} {n}Declaration :=')
    w(f'  {{ sourceRealization := {catreal(s)}, targetRealization := {catreal(tg)} }}')
w('\nend\n\nend Elements\n\nopen Elements\n')
P='CasCatalogue.Elements.'
for n,i,t,d in cats:
    w(f'normalized_registry .category\n  {{ id := CategoryId.{n}, declaration := `{P}{n}Category\n    expression := {cap(n)}, realization := `{P}{n}Realization }}')
for n,i,s,tg,t,st in funs:
    w(f'normalized_registry .functor\n  {{ id := FunctorId.{n}, source := {expr(s)}, target := {expr(tg)}\n    declaration := `{P}{n}Declaration, realization := `{P}{n}Realization\n    expression := {cap(n)}Expr{", structural := true" if st else ""} }}')
for mid,name,own,fk,shape in meths:
    w(f'normalized_registry .method\n  {{ id := ⟨"meth.{mid}"⟩, name := "{name}", owner := {expr(own)}\n    functor := FunctorId.{fk}, shape := .{shape} }}')
w('\nend CasCatalogue')
open(__import__('pathlib').Path(__file__).resolve().parents[1] / 'CasCatalogue/Leaves/Elements.lean','w').write('\n'.join(out)+'\n')
