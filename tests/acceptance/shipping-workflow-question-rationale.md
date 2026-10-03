# Independently fixed shipment workflow questions

These new proposals supplement existing questions without changing the original
17 `.cas` files, Permanent JSON, or question seals. They were written from public
mathematical source and elementary mathematical arguments before candidate
execution. They do not admit themselves or establish execution success.

## Returned polynomial values

`shipping_polynomial_workflow.cas` selects Z[x], factors x²+x−2, and uses the
actual returned factors twice: evaluation inside a finite sum, and a product
binder whose result feeds polynomial evaluation, coefficient change to Q,
roots, and the quadratic companion matrix. Thus comparing a displayed factor
list alone cannot satisfy the connected workflow. Distinctness of the two
linear factors makes a finite set adequate for this first example.

The independent identity (x−1)(x+2)=x²+x−2 proves the factorization; primitive
monic linear factors are normalized irreducibles in Z[x]. At 3 they give 2 and
5, with sum 7 and product 10. The inclusion Z→Q preserves all coefficients.
The roots in Q are exactly 1 and −2, by absence of zero divisors. The companion
matrix is [[0,2],[1,−1]], so det(tI−C)=t²+t−2, det(C)=−2 and tr(C)=−1.
Sources: Dummit–Foote, *Abstract Algebra*, Chapter 9 (polynomial rings,
evaluation and unique factorization); the elementary determinant formula.

A second example −x²+2x−1=−(x−1)² requires full factorization with polynomial
unit −1 and two occurrences of x−1. Its returned reconstruction is then evaluated
at 3 (−4), its degree observed (2), and its coefficients changed to Q before
roots ({1}). A factor set alone loses the required multiplicity. The source
`LeanCategories/Catalogue/Semantics/Algebra/Polynomials.lean` publishes
`factorization`, `unit`, `product` and their exact parameter types;
`factorization_product` supplies a mathematical reconstruction law. No
computational result was consulted for any expected value.

## Selected arrows and structured results

`shipping_structured_workflow.cas` obtains the actual selected underlying
Z-module M from E8 by its public structural functors. The identity on this
module has kernel {0} with its actual inclusion, and cokernel M/M with its
actual projection. Both actual resulting modules have rank 0 and cardinality
1. Inclusion and projection are applied to their actual domains, and the
defining compositions with the selected identity are observed. Source:
Dummit–Foote Chapter 10 (modules and quotient modules); public
`Modules/Operations.lean` (`ker`, `domain`, `inclusion`, `coker`, `projection`,
`codomain`). This is the smallest connected example and supplements, rather
than substitutes for, the existing formed-kernel selected-pairing assertions
in `b0_formed_kernel.cas`.

The selected sign kernel in S3 must inherit the abelian group operation of
its three-element cyclic domain. Existing questions already fix its cardinality
and actual defining leg. Source: Dummit–Foote Chapters 1 and 3.

## Reusable transported elements and calculus values

For F9x=F3[X]/(X²+1) and F9y=F3[Y]/(Y²+Y+2), the prescribed comparison sends
x to y+2 and its inverse sends y to x+1. Direct reduction modulo the defining
polynomials proves the forward square equals 2, the inverse satisfies the
target polynomial, and forward followed by inverse returns x. Both directions
retain their selected presentations and the same explicit comparison. Source:
the polynomial quotient universal property (Dummit–Foote Chapter 9).

The public smooth derivative returns a smooth function. Applying the returned
derivative of sin at 0 yields cos(0)=1; differentiating the returned smooth
function again and applying at 0 yields −sin(0)=0. Sources: Mathlib
`Real.deriv_sin`, `Real.deriv_cos`, `Real.cos_zero`, `Real.sin_zero`; public
`Algebra/Calculus.lean` (`smoothDerivative`, its smooth codomain).

No compiler, candidate interpreter, runtime answer, leaf, contract, or kernel
implementation was used to fix these questions. Compilation and execution
belong to the scheduled execution role; syntax/interface defects must be
reported without changing the mathematical questions to accommodate answers.
