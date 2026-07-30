/-
The standard universe: the category graph, the method catalogue, the
profile rules, the capability routes and the audit representatives that the
prelude ships (DESIGN.md §Standard universe).

Everything here is REGISTRATION DATA — literal arrays, handed to the
checked adders by the `run_cmd` lines at the end of each section. There is
no engine code in this module: a new category, presentation family, method
or backend route is added by registering more data, never by editing the
resolver or the router. A clash fails `lake build`.

Two load-bearing separations are visible in the layout below:

- methods are declared on the category where the mathematics first makes
  sense (`factor` on FactorizationElems, `annihilator` on Modules) and
  reach objects only by membership + registered inclusion edges — there is
  no forwarding declaration anywhere in this file;
- routes are a separate section, the only place naming a backend; deleting
  every route in it would remove no method from any object, only the
  ability to run them.

The universe ships one DELIBERATE capability gap (semantically available,
no route): `det`/`inverse` on matrices whose entry domain is not ℚ —
Mat₂(ℤ/5) is the audit representative. It is an honest backlog item and is
asserted as such by the proofs at the end of this file. (The previous gaps
— `factor` on ℤ[x] and `nth` on ℚ — were routed in round three, #18/#17.)
Repairing a gap by narrowing a category, adding a capability-shaped
category, or registering a route to an operation that does not implement
it is forbidden (DESIGN.md §Decisions inherited from the anti-drift
record, 4).
-/
import CasDsl.Register
import CasDsl.Route
-- the backends are imported for their registered OP SIGNATURES: route
-- registration below is checked against them, so they must precede §4
import CasDsl.Native
import CasDsl.Backends.Sage

namespace CasDsl.Std

open Lean Elab Command

/-! ## Fixture presentations

Shared by the audit representatives, the proofs at the end of this module
and `CasDslTests/Std.lean`, so all three talk about the same objects. -/

/-- `x^3 − 2x + 1 ∈ ℤ[x]` — the notebook's polynomial before the embedding
into ℚ[x]. -/
def polyZ : Obj :=
  .elem (.poly .int) (Value.mkPoly .int #[.int 1, .int (-2), .int 0, .int 1])

/-- The same polynomial after `map p to ℚ[x]`. -/
def polyQ : Obj :=
  .elem (.poly .rat) (Value.mkPoly .rat #[.rat 1, .rat (-2), .rat 0, .rat 1])

/-- `[1, 2; 3, 4] ∈ Mat₂(ℚ)`. -/
def mat2Q : Obj :=
  .elem (.matrix 2 .rat) (.mat 2 .rat #[#[.rat 1, .rat 2], #[.rat 3, .rat 4]])

/-- `{1, 2, 3}` — SPEC.md §Finite sets' `A`, and the factor of the product
and powerset representatives. -/
def finSet123 : SetPresentation := .finite .int #[.int 1, .int 2, .int 3]

/-- `n ↦ 2n` in `ℕ → ℕ` — SPEC.md §Set comprehensions' `e`, whose image is
the progression `{0, 2, 4, ...}`. -/
def doubling : Obj :=
  .elem (.funcs .nat .nat) (.func .nat .nat `n (Value.mkPoly .int #[.int 0, .int 2]))

/-- `2 + 2i ∈ ℂ` — SPEC.md §Exact number systems' `z`. Written in normal form
by hand, like the polynomial fixtures above: a FIXTURE states the value it
means, while every value the surface produces goes through `Value.mkAlg`. -/
def z2plus2i : Obj := .elem .complex (.alg 2 2 (-1))

/-- `√2 ∈ ℝ` — the real surd the acceptance proofs route the complex methods
on, and a fixture like the one above. -/
def sqrt2 : Obj := .elem .real (.alg 0 1 2)

/-- The same cubic after SPEC.md's `q := map p to ℂ[x]`, where it splits. The
coefficients are the integers `map` was given: ℤ ⊆ ℂ moves no data. -/
def polyC : Obj :=
  .elem (.poly .complex) (Value.mkPoly .complex #[.int 1, .int (-2), .int 0, .int 1])

/-- SPEC.md §Subspaces and spans' `W` — `span_QQ{(1,0,1), (0,1,1)} ≤ ℚ³`,
already in the reduced echelon form `Value.mkSpanBasis` puts a span in (the
leading ones sit in columns 0 and 1), like the other fixtures here. -/
def spanW : SetPresentation :=
  .span 3 #[.vec 3 .rat #[.rat 1, .rat 0, .rat 1],
            .vec 3 .rat #[.rat 0, .rat 1, .rat 1]]

/-- `[1, 2; 3, 4] ∈ Mat₂(ℤ/5)` — the deliberate-gap representative (#17):
exact linear algebra over a finite field is meaningful (`MatrixElems`), and
only ℚ-entry matrices are routed. -/
def mat2Mod5 : Obj :=
  .elem (.matrix 2 (.mod 5)) (.mat 2 (.mod 5)
    #[#[Value.mkMod 5 1, Value.mkMod 5 2], #[Value.mkMod 5 3, Value.mkMod 5 4]])

/-! ## 1 · The category graph

`parents` are the registered inclusion edges; params ride along them
unchanged. The graph is mathematical structure only: no node names an
implementation, a backend, or a current capability limit. The docs are
user-facing — they are what `#capabilities` prints. -/

private def stdCategories : Array CatDecl := #[
  { name := `Sets,
    doc := "sets: cardinality, membership, and equality of presentations" },
  { name := `CountableSets, parents := #[`Sets],
    doc := "sets equipped with a registered enumeration (countable), so their \
elements can be indexed" },
  { name := `FiniteSets, parents := #[`CountableSets],
    doc := "sets presented by an explicit finite list of elements" },
  { name := `CommRingElems,
    doc := "elements of a commutative ring" },
  { name := `FactorizationElems, parents := #[`CommRingElems],
    doc := "elements of a unique factorization domain: a factorization into \
irreducibles exists and is unique up to units and order" },
  { name := `EuclideanElems, parents := #[`FactorizationElems],
    doc := "elements of a euclidean domain (a division algorithm, hence also \
a UFD)" },
  { name := `Modules,
    doc := "modules over a commutative ring" },
  { name := `SmallModules, parents := #[`Modules],
    doc := "modules small enough to present by explicit finite data" },
  { name := `MatrixElems,
    doc := "square matrices over a commutative ring; params (size, entry domain)" },
  -- Polynomials are a STRUCTURAL view, not a divisibility one: `deg` and
  -- `roots` are meaningful for a polynomial over any commutative ring,
  -- including rings where `factor` is not. It therefore carries no parent
  -- edge — ℤ[x] reaches `factor` through FactorizationElems and `deg`
  -- through here, and neither membership implies the other.
  { name := `PolynomialElems,
    doc := "elements of a univariate polynomial ring; params (the ring)" },
  -- Functions were a pure elaboration surface until the image arrived
  -- (SPEC.md's `e.image()`): what a map does to a whole set is a
  -- computability question, so it is a method, and a method needs a category
  -- to own it. Nothing else about functions became registry data.
  { name := `FunctionElems,
    doc := "elements of a function domain src → tgt; params (that domain)" },
  -- The complex plane's own operations. ℝ ⊆ ℂ, so an element of ℝ inhabits
  -- this category too — its real part is itself, its imaginary part is 0, and
  -- it is its own conjugate. No parent edge: re/im/conjugation/modulus are
  -- structure of ℂ and of nothing above it in this graph.
  { name := `ComplexElems,
    doc := "elements of ℂ, or of a subfield of it that this slice presents \
(ℝ): the real and imaginary parts, conjugation and the modulus; params (the \
domain the element was presented in)" },
  -- SPEC.md §Subspaces and spans writes `let W := span_QQ{u₁, u₂} \leq ℚ³ in
  -- QQ-Mod`, and the name is taken from it verbatim. At this stage it is an
  -- ASCRIPTION TAG — the same standing `ℝ → ℝ` had before ℝ was inhabited:
  -- the membership it states is real and checked, but the CATEGORY (its
  -- morphisms, its limits, the subobject lattice `≤` really lives in) is
  -- deferred to CategoryGraph per the trajectory ruling. Nothing here may
  -- grow into that ontology; what it owns is `dim`.
  -- SPEC.md §Differentials writes `let X := Spec ℚ[x] in Schemes/ℚ`, and the
  -- name is taken from it verbatim. An ASCRIPTION TAG at this stage, the
  -- standing `QQ-Mod` has: the membership it states is real and checked, and
  -- the CATEGORY — its morphisms, its sheaves, the relative differentials
  -- that really live over it — is deferred to CategoryGraph per the
  -- trajectory ruling. It owns no method at all: everything SPEC.md does with
  -- a scheme here is display.
  { name := `«Schemes/QQ»,
    doc := "schemes over ℚ. SPEC.md's own name for the category an affine \
scheme `Spec R` is ascribed to; at this stage an ascription TAG, with the \
categorical structure deferred to CategoryGraph" },
  { name := `«QQ-Mod»,
    doc := "ℚ-modules. SPEC.md's own name for the category a subspace of ℚⁿ \
is a subobject of; at this stage an ascription TAG carrying `dim`, with the \
categorical structure deferred to CategoryGraph" }
]

run_cmd stdCategories.forM registerCategory!

/-! ## 2 · The method catalogue

Each declaration names the category where the operation first makes sense —
NOT the categories that can currently execute it. `annihilator` is declared
once, on `Modules`; `SmallModules` deliberately carries no declaration of
its own, so the notebook's fixture receives it purely through the registered
inclusion edge. -/

private def stdMethods : Array MethodDecl := #[
  { id := `factor, receiver := `FactorizationElems,
    resultDoc := "a factorization: a unit and irreducible factors with multiplicity",
    doc := "factor into irreducibles/primes with multiplicity" },
  { id := `gcd, receiver := `FactorizationElems, arity := 1,
    argDoc := "another element of the same ring",
    resultDoc := "a greatest common divisor, up to units",
    doc := "a greatest common divisor — unique up to units in a UFD, which is \
where the operation first makes sense" },
  { id := `is_prime, receiver := `FactorizationElems,
    resultDoc := "a boolean",
    doc := "primality in the NORMALIZED sense: is this element irreducible AND \
the normalized representative of its associate class? In ℤ that is the ordinary \
'is a prime number', so −7 answers FALSE — it is irreducible, but 7 is the \
normalized representative of {7, −7}. Declared where irreducibility first makes \
sense: the elements of a UFD" },
  -- SPEC.md §Differentials' `(d/dx)(f)`, and the same operation `d(f)` wraps
  -- as a 1-form. Declared on PolynomialElems because differentiating is a
  -- STRUCTURAL read of a polynomial — it makes sense over any coefficient
  -- ring, including ones where factorization does not
  { id := `derivative, receiver := `PolynomialElems,
    resultDoc := "a polynomial over the same coefficient ring",
    doc := "the formal derivative d/dx: the coefficient of xⁱ becomes i·cᵢ, \
shifted down by one. Exact coefficient arithmetic, so it is NATIVE and no \
backend is asked — there is nothing here for one to get wrong" },
  -- SPEC.md §Indefinite integration's `∫ f dx`. Declared beside `derivative`
  -- for the same reason, and its RESULT is the whole point: the complete set
  -- of primitives, a COSET of the constants, not one primitive with a
  -- convention about which
  { id := `antiderivative, receiver := `PolynomialElems,
    resultDoc := "the coset `F + K` of ALL primitives, where K is the \
constants of the ring",
    doc := "the indefinite integral ∫ f dx: the complete set of primitives, \
which is a coset of ker(d/dx). Exact coefficient arithmetic (cᵢ/(i+1) shifted \
up by one), so it is NATIVE — and routed where the division lands somewhere \
this slice presents" },
  { id := `deg, receiver := `PolynomialElems,
    resultDoc := "a nonnegative integer (the zero polynomial has no degree)",
    doc := "the degree: the largest exponent carrying a nonzero coefficient" },
  { id := `roots, receiver := `PolynomialElems,
    resultDoc := "the set of roots lying in the polynomial's own coefficient ring",
    doc := "the set of roots IN THE COEFFICIENT RING — an empty result means \
the polynomial has no root there, not that none exists in an extension" },
  { id := `det, receiver := `MatrixElems,
    resultDoc := "a scalar of the entry domain",
    doc := "the determinant" },
  { id := `inverse, receiver := `MatrixElems,
    resultDoc := "a matrix over the entry domain (or its fraction field)",
    doc := "the multiplicative inverse, when it exists" },
  -- SPEC.md §Vectors and matrices' `M.rank()` and `M.ker()`
  { id := `rank, receiver := `MatrixElems,
    resultDoc := "a nonnegative integer, at most the size of the matrix",
    doc := "the rank: the dimension of the row (equivalently column) space" },
  { id := `ker, receiver := `MatrixElems,
    resultDoc := "the subspace {v : M v = 0} of the matrix's own vector space",
    doc := "the KERNEL of the matrix read as a linear map — the vectors it \
sends to zero, presented as a subspace by a basis" },
  -- SPEC.md §A composed computation's `C.trace()` and `C.charpoly()`
  { id := `trace, receiver := `MatrixElems,
    resultDoc := "a scalar of the entry domain",
    doc := "the trace: the sum of the diagonal entries, which is also the sum \
of the eigenvalues with multiplicity" },
  { id := `charpoly, receiver := `MatrixElems,
    resultDoc := "a monic polynomial of the matrix's own size, over the entry domain",
    doc := "the characteristic polynomial det(xI − M)" },
  -- …and the matrix a polynomial names
  { id := `companion_matrix, receiver := `PolynomialElems,
    resultDoc := "a square matrix of the polynomial's own degree",
    doc := "the companion matrix: the matrix whose characteristic polynomial \
is this one. Which of the four LAYOUTS a backend uses is its own convention — \
they are similar matrices, so the size, the trace, the determinant and the \
characteristic polynomial are the same for all of them" },
  -- …and the one method a subspace owns
  { id := `dim, receiver := `«QQ-Mod»,
    resultDoc := "a nonnegative integer",
    doc := "the dimension: the number of vectors in a basis" },
  { id := `annihilator, receiver := `Modules,
    resultDoc := "an ideal of the base ring",
    doc := "the annihilator ideal of the module" },
  { id := `nth, receiver := `CountableSets, arity := 1,
    argDoc := "a nonnegative index (0-based)",
    resultDoc := "the element at that index",
    doc := "the element at an index of the REGISTERED enumeration of this set \
(for ℤ: 0, 1, −1, 2, −2, …; for ℚ: the Cantor zigzag 0, 1, −1, 1/2, −1/2, 2, \
−2, 1/3, …) — a documented, revisitable choice, never a claim that the set is \
intrinsically ordered that way" },
  { id := `cardinality, receiver := `Sets,
    resultDoc := "a cardinal (finite n, or ℵ₀)",
    doc := "the number of elements" },
  { id := `contains, receiver := `Sets, arity := 1,
    argDoc := "a candidate element",
    resultDoc := "a boolean",
    doc := "membership of an element in the set" },
  { id := `set_eq, receiver := `Sets, arity := 1,
    argDoc := "another set",
    resultDoc := "a boolean",
    doc := "equality of two sets, by presentation normalization (a documented \
ceiling, not a general decision procedure)" },
  { id := `subset, receiver := `Sets, arity := 1,
    argDoc := "another set",
    resultDoc := "a boolean",
    doc := "inclusion: every element of the receiver is an element of the \
argument — the same judgment `X ∈ 𝒫(A)` asks" },
  -- The binary set operations are declared where they first make sense: on
  -- SETS, all of them, whatever presentation. Only explicit finite ones are
  -- routed, so `ℤ ∪ A` is the honest structured gap.
  { id := `union, receiver := `Sets, arity := 1,
    argDoc := "another set", resultDoc := "a set",
    doc := "the union of two sets" },
  { id := `intersect, receiver := `Sets, arity := 1,
    argDoc := "another set", resultDoc := "a set",
    doc := "the intersection of two sets" },
  { id := `diff, receiver := `Sets, arity := 1,
    argDoc := "another set", resultDoc := "a set",
    doc := "the difference A \\ B: the elements of A that are not in B" },
  { id := `symdiff, receiver := `Sets, arity := 1,
    argDoc := "another set", resultDoc := "a set",
    doc := "the symmetric difference A △ B = (A \\ B) ∪ (B \\ A)" },
  -- SPEC.md §A composed computation's `∑_{a ∈ roots} a` and `∏`. Declared on
  -- FINITE sets, not on Sets: aggregation is a finite algebraic operation,
  -- and the sum over an infinite set is a limit this slice has no notion of —
  -- so `∑_{n ∈ ℕ} n` is honestly not a method of ℕ rather than a missing
  -- route. Documented residue: a BOUNDED progression is finite but presents
  -- as `progression`, which enters at CountableSets (a pattern cannot see the
  -- bound), so it misses this specificity exactly as it misses FiniteSets.
  { id := `sum, receiver := `FiniteSets,
    resultDoc := "an element of the domain the set's elements share",
    doc := "the sum of the elements, each counted once — SPEC.md's \
`∑_{x ∈ X} x`. The empty sum is 0" },
  { id := `prod, receiver := `FiniteSets,
    resultDoc := "an element of the domain the set's elements share",
    doc := "the product of the elements, each counted once — SPEC.md's \
`∏_{x ∈ X} x`. The empty product is 1" },
  -- SPEC.md §Exact number systems' complex methods. `bar` and `|·|` are the
  -- surface's own spellings of conjugation and the modulus.
  { id := `re, receiver := `ComplexElems,
    resultDoc := "a real number",
    doc := "the real part" },
  { id := `im, receiver := `ComplexElems,
    resultDoc := "a real number",
    doc := "the imaginary part — the REAL coefficient of i, so `(2 + 2i).im()` \
is 2 and not 2i" },
  { id := `bar, receiver := `ComplexElems,
    resultDoc := "an element of the same domain",
    doc := "complex conjugation; a real number is its own conjugate" },
  { id := `abs, receiver := `ComplexElems,
    resultDoc := "a nonnegative real number",
    doc := "the modulus |z| — the bars are its surface spelling, and on a real \
number it is the absolute value" },
  -- SPEC.md's `map √2 to ℝ/O(1/10^{10})`. Declared where the exact numbers
  -- live, which is where asking for a decimal first makes sense; ROUTED for
  -- the reals only (§4), so a complex receiver is an honest gap rather than a
  -- projection nobody asked for.
  { id := `approximate, receiver := `ComplexElems, arity := 1,
    argDoc := "the requested absolute tolerance ε — an exact positive rational",
    resultDoc := "a decimal presentation certified to lie within ε of the exact \
value, carrying that value and the tolerance that was requested",
    doc := "the decimal presentation of an exact number to a requested absolute \
tolerance. `ℝ/O(ε)` is SUGAR for that request and NOT a quotient — |a - b| < ε \
is not transitive, so there are no classes — and the exact value is kept, not \
replaced. Which numeric strategy meets the tolerance (interval, ball, adaptive) \
is the backend's own business and is named nowhere in this surface" },
  -- SPEC.md §Elementary calculus' three analysis operations, all declared on
  -- FunctionElems: each is asked of a FUNCTION, and each answers with an
  -- exact value or a series rather than with anything approximate
  { id := `limit, receiver := `FunctionElems, arity := 1,
    argDoc := "the point the variable runs to — an exact rational, or one of \
the symbolic constants (π, ∞)",
    resultDoc := "an exact value",
    doc := "the limit of the function's body as its variable runs to a point. \
TRUSTED: there is no finite exact computation on this side that decides a \
limit, so what is checked of the reply is its KIND — an exact value, never a \
decimal. This surface claims no epsilon-delta semantics and ℝ gains none; the \
limit is an OPERATION whose answer is exact or a refusal" },
  { id := `definite_integral, receiver := `FunctionElems, arity := 2,
    argDoc := "the lower and upper bounds",
    resultDoc := "an exact value",
    doc := "the definite integral of the body between two bounds. TRUSTED in \
the same sense the limit is, and refused rather than approximated when the \
answer is not one of the exact values this slice presents" },
  { id := `taylor_expansion, receiver := `FunctionElems, arity := 1,
    argDoc := "the point to expand about",
    resultDoc := "a formal power series, known to a documented number of terms",
    doc := "the Taylor expansion about a point, as a formal power series in \
t. TRUSTED in the sense the limit and the definite integral are — no finite \
exact computation on this side decides an expansion — with one check more \
than they get: every coefficient must come back an exact RATIONAL, and one \
that does not is refused rather than turned into a decimal. The number of \
terms is a documented CEILING of this slice, not something the call \
negotiates: a truncation past it is a loud refusal naming it" },
  { id := `image, receiver := `FunctionElems,
    resultDoc := "the set of values the function takes on its source",
    doc := "the image of the SOURCE domain — the set `f(src)`, which is what \
`f(ℕ)` denotes as well" }
]

run_cmd stdMethods.forM registerMethod!

/-! ## 3 · Profile rules — which categories an object inhabits

Rules record only the MOST SPECIFIC membership: `FiniteSets ≤ CountableSets
≤ Sets` means a finite set already reaches `nth`, `cardinality` and
`contains` through the closure, so a redundant direct membership would only
be a second place to get the mathematics wrong.

Memberships are stated at their true strength: ℤ[x] is a UFD but NOT
euclidean, and ℤ/n is a commutative ring that is not a domain. Weakening or
strengthening either one to make a route apply is exactly the drift this
design forbids. -/

private def stdProfileRules : Array ProfileRule := #[
  -- ring elements
  { pattern := .elemOf (.exact .int), cat := `EuclideanElems, slots := #[.elemDom] },
  { pattern := .elemOf (.polyOver (.exact .rat)), cat := `EuclideanElems,
    slots := #[.elemDom] },
  -- ℂ[x] is euclidean for the reason ℚ[x] is: ℂ is a field. It is where
  -- SPEC.md's `map p to ℂ[x]` lands, and where a cubic finally splits
  { pattern := .elemOf (.polyOver (.exact .complex)), cat := `EuclideanElems,
    slots := #[.elemDom] },
  -- ℤ[x] is a UFD, not a euclidean domain
  { pattern := .elemOf (.polyOver (.exact .int)), cat := `FactorizationElems,
    slots := #[.elemDom] },
  -- …and every polynomial, over any coefficient domain, is a polynomial:
  -- an INDEPENDENT membership, which is why `deg` reaches ℤ[x] and ℚ[x]
  -- alike without either category claiming the other's structure
  { pattern := .elemOf (.polyOver .anyDom), cat := `PolynomialElems,
    slots := #[.elemDom] },
  -- ℤ/n is a commutative ring; for composite n it is not a domain, so its
  -- elements stop at CommRingElems — and `factor`, declared strictly below
  -- on FactorizationElems, correctly does not reach them.
  -- CEILING: the moduli this slice exercises are registered one at a time.
  -- `DomainPattern.anyMod` (added for the embedding rules below) could match
  -- every modulus in ONE rule, but a profile rule must state membership at its
  -- true strength and that strength differs per modulus — ℤ/5 is a field while
  -- ℤ/6 is not even a domain — so a blanket rule would have to state one of
  -- them wrongly. An unregistered modulus has no profile at all, which
  -- resolves as an honest `notApplicable` — never a wrong membership.
  { pattern := .elemOf (.exact (.mod 5)), cat := `CommRingElems, slots := #[.elemDom] },
  -- an affine scheme is the object SPEC.md ascribes to Schemes/ℚ, and that is
  -- the ONLY membership it has: it is not a set, not a ring element, and
  -- nothing here may give it one
  { pattern := .specObj, cat := `«Schemes/QQ» },
  -- matrices carry their instantiation data
  { pattern := .elemOf (.matrixOver .anyDom), cat := `MatrixElems,
    slots := #[.matSize, .matEntry] },
  -- a function element carries the arrow it was declared over
  { pattern := .elemOf .anyFuncs, cat := `FunctionElems, slots := #[.elemDom] },
  -- elements of ℂ, and of ℝ inside it. Registered one domain at a time for
  -- the reason ℤ/n is: membership is stated at its true strength, and the
  -- ones NOT registered here (an integer, a rational) are a missed
  -- specificity rather than a claim — `3.re()` is the honest "not a method of
  -- any category this object belongs to", and `|3|` with it.
  { pattern := .elemOf (.exact .complex), cat := `ComplexElems, slots := #[.elemDom] },
  { pattern := .elemOf (.exact .real), cat := `ComplexElems, slots := #[.elemDom] },
  -- ℕ, ℤ and ℚ as objects, and the same domains used as sets
  { pattern := .domainIs (.exact .nat), cat := `CountableSets, slots := #[.setDom] },
  { pattern := .domainSetOf (.exact .nat), cat := `CountableSets, slots := #[.setDom] },
  { pattern := .domainIs (.exact .int), cat := `CountableSets, slots := #[.setDom] },
  { pattern := .domainSetOf (.exact .int), cat := `CountableSets, slots := #[.setDom] },
  -- ℚ is countable: the deliberate `nth` gap below is a MISSING ROUTE, not
  -- a weaker category
  { pattern := .domainIs (.exact .rat), cat := `CountableSets, slots := #[.setDom] },
  { pattern := .domainSetOf (.exact .rat), cat := `CountableSets, slots := #[.setDom] },
  -- ℤ[x] and ℚ[x] AS SETS, which is what `p ∈ ℤ[x]` asks about. Countable is
  -- their true strength (a polynomial is a finite tuple over a countable
  -- domain) and is stated one coefficient domain at a time for the reason
  -- ℤ/n is: `polyOver anyDom` would also claim it of ℝ[x], which is false.
  -- `nth` therefore becomes an honest GAP here — no enumeration of ℤ[x] is
  -- registered — and never a narrower category.
  { pattern := .domainIs (.polyOver (.exact .int)), cat := `CountableSets,
    slots := #[.setDom] },
  { pattern := .domainIs (.polyOver (.exact .rat)), cat := `CountableSets,
    slots := #[.setDom] },
  -- ℂ[x] is a set too, and an UNCOUNTABLE one: `Sets` is its true strength,
  -- so `p ∈ ℂ[x]` is decided and `ℂ[x][3]` is not even applicable
  { pattern := .domainIs (.polyOver (.exact .complex)), cat := `Sets },
  -- SPEC.md's `ℝ[[t]]` and `ℤ[[t]]` AS SETS, which is what `Tf ∈ ℝ[[t]]` asks
  -- of them. `Sets` is their true strength and nothing narrower: a formal
  -- power series is an arbitrary SEQUENCE of coefficients, so the ring is
  -- UNCOUNTABLE — the standing ℂ[x] already has. Registered one coefficient
  -- domain at a time for the reason ℤ/n is
  { pattern := .domainIs (.exact (.series .int)), cat := `Sets },
  { pattern := .domainIs (.exact (.series .rat)), cat := `Sets },
  { pattern := .domainIs (.exact (.series .real)), cat := `Sets },
  -- ℝ and ℂ as objects, and used as sets. `Sets` is their true strength and
  -- nothing narrower: both are UNCOUNTABLE, so `nth` — declared on
  -- CountableSets — correctly does not reach them, and `ℝ.cardinality()`
  -- routes and then reports that this slice cannot state it, rather than
  -- answering ℵ₀. What they DO answer is membership: `√2 ∈ ℝ`, `2 + 2i ∈ ℂ`.
  { pattern := .domainIs (.exact .real), cat := `Sets },
  { pattern := .domainSetOf (.exact .real), cat := `Sets },
  { pattern := .domainIs (.exact .complex), cat := `Sets },
  { pattern := .domainSetOf (.exact .complex), cat := `Sets },
  -- an arithmetic progression is countable; a BOUNDED one is finite, but
  -- `PresPattern.progression` cannot see the bound, so it enters at
  -- CountableSets — a missed specificity, never a false claim
  { pattern := .progression .anyDom, cat := `CountableSets, slots := #[.setDom] },
  { pattern := .finiteSet, cat := `FiniteSets, slots := #[.setDom] },
  -- `A × B` and `𝒫(A)` are DENOTED sets: a pattern over one presentation
  -- cannot see the factors, and their strength is exactly what the factors
  -- decide (𝒫 of a finite set is finite, 𝒫(ℤ) is uncountable), so the only
  -- membership statable here is `Sets`. A missed specificity, never a false
  -- claim — the same reason a bounded progression enters at CountableSets.
  { pattern := .productSet, cat := `Sets },
  { pattern := .powersetSet, cat := `Sets },
  -- `ℂ - ℚ` is a set and nothing narrower, for the same reason: its strength
  -- is whatever the two domains decide
  { pattern := .domainDiffSet, cat := `Sets },
  -- A subspace of ℚⁿ is a SET whose elements are vectors, so `∈`, `=` and `⊆`
  -- reach it through the ordinary set hierarchy — and it is COUNTABLE (a
  -- subspace of ℚⁿ is), which is its true strength. `nth` is then the honest
  -- gap ℤ[x] already carries: no enumeration of a subspace is registered.
  { pattern := .spanSet, cat := `CountableSets },
  -- a coset of the constants is a SET whose elements are polynomials, and it
  -- is COUNTABLE (it is in bijection with the kernel, and ℚ is). `nth` is then
  -- the honest gap ℤ[x] and the subspace already carry
  { pattern := .cosetSet, cat := `CountableSets },
  -- …and it is the object SPEC.md ascribes to QQ-Mod, which is where `dim`
  -- lives. Two INDEPENDENT memberships, exactly like a polynomial's: being a
  -- set does not make it a module, and neither implies the other
  { pattern := .spanSet, cat := `«QQ-Mod» },
  -- the module fixture: ℤ/n as a ℤ-module, in the PROPER subcategory only.
  -- `Modules` membership arrives through the inclusion edge, which is what
  -- makes `annihilator` a real inheritance demonstration.
  { pattern := .cyclicMod, cat := `SmallModules, slots := #[.const (.dom .int)] }
]

run_cmd stdProfileRules.forM registerProfileRule!

/-! ## 3b · Functors — receiver transport

A functor is what carries a method declared on one category to a receiver of
another: `F.cardinality()` on the module fixture resolves as
`UnderlyingSet(F).cardinality()`. Registration is data, exactly like a profile
rule, and `source`/`target` are category names — nothing here names a backend
or an implementation.

The resolver consults these only where round one found NOTHING, so registering
a functor can never take a method away from an object that already had it:
`annihilator` still reaches the fixture directly through `SmallModules ≤
Modules`, and the acceptance proofs below assert exactly that. -/

private def stdFunctors : Array FunctorDecl := #[
  { name := `UnderlyingSet, source := `Modules, target := `Sets,
    objMap := .cyclicToFiniteSet,
    doc := "the forgetful functor to underlying sets: a module presented by \
explicit finite data becomes the finite set of its elements, so the set \
methods (cardinality, contains, nth) apply to it" }
]

run_cmd stdFunctors.forM registerFunctor!

/-! ## 3c · Preferred canonical maps — the coercions the surface may insert

The preferred canonical maps of the standard universe, and the whole content
of `ℤ ⊆ ℚ` as the surface understands it: `map p to ℚ[x]`, a matrix literal
of integers ascribed to Mat₂(ℚ), `1 + 1/2`, and `let x := 7 in ℤ/5` all
coerce through exactly these rules. The engine knows none of these facts —
unregister a rule and the corresponding `map` stops working, with the honest
"there is no preferred canonical map" error (`CasDslTests/CanonicalMaps.lean`
proves it).

A canonical map is a preferred choice, not necessarily an injection (design
review 2026-07-30): the inclusions are monomorphisms, while ℤ → ℤ/n is the
ring quotient — supplied by its universal property, as cokernels and other
canonical choices would be. There is deliberately no rule out of ℚ —
`ℚ → ℤ` is not defined everywhere, and the partial `ℕ ← ℤ` reading stays an
engine-level CHECK rather than becoming a registered map — and none for the
coefficient- or entry-wise image of a rule, which `coerceValue` induces
structurally instead. -/

private def stdCanonicalMaps : Array CanonicalMap := #[
  { src := .exact .nat, tgt := .exact .int, op := .identity,
    doc := "ℕ ⊆ ℤ: an element of ℕ already IS an integer (they share the \
`Value.int` representation), so the injection moves no data" },
  { src := .exact .nat, tgt := .exact .rat, op := .intToRat,
    doc := "ℕ ⊆ ℚ: the composite of ℕ ⊆ ℤ ⊆ ℚ, registered explicitly because \
the coercion layer takes ONE hop (it does not compose rules)" },
  { src := .exact .int, tgt := .exact .rat, op := .intToRat,
    doc := "ℤ ⊆ ℚ: the fraction field of ℤ — the notebook's `map p to ℚ[x]` \
is this rule applied coefficient-wise" },
  { src := .exact .int, tgt := .anyMod, op := .intToMod,
    doc := "ℤ → ℤ/n for EVERY modulus n (one rule, by `anyMod`): the ring \
quotient — an integer naming its residue class, which is what an ascription \
such as `let x := 7 in ℤ/5` inserts" },
  -- SPEC.md §Exact number systems' chain `ℤ ⊆ ℚ and ℚ ⊆ ℝ and ℝ ⊆ ℂ`. The
  -- TRANSITIVE CLOSURE is registered, exactly as ℕ ⊆ ℚ is registered next to
  -- ℕ ⊆ ℤ and ℤ ⊆ ℚ: the coercion layer takes one hop, so the closure is what
  -- makes both `assert ℚ ⊆ ℝ` and `map p to ℂ[x]` (coefficient-wise ℤ → ℂ)
  -- work — and leaving a pair out would be a hole `#canonical_maps` displays
  -- while the ⊆-chain asserted its absence away.
  -- Every one of them is `identity`: an element of ℚ, ℝ or ℂ this slice can
  -- present is carried by the SAME `Value` in all of them (a rational stays a
  -- rational, an exact algebraic value stays itself), so the inclusion moves
  -- no data — the reason ℕ ⊆ ℤ is `identity` too.
  { src := .exact .nat, tgt := .exact .real, op := .identity,
    doc := "ℕ ⊆ ℝ: a natural number is a real number" },
  { src := .exact .int, tgt := .exact .real, op := .identity,
    doc := "ℤ ⊆ ℝ: an integer is a real number" },
  { src := .exact .rat, tgt := .exact .real, op := .identity,
    doc := "ℚ ⊆ ℝ: SPEC.md's own chain link — every rational IS a real, and \
the value presenting it does not change" },
  { src := .exact .nat, tgt := .exact .complex, op := .identity,
    doc := "ℕ ⊆ ℂ: a natural number is a complex number" },
  { src := .exact .int, tgt := .exact .complex, op := .identity,
    doc := "ℤ ⊆ ℂ: an integer is a complex number — applied coefficient-wise \
this is SPEC.md's `map p to ℂ[x]`" },
  { src := .exact .rat, tgt := .exact .complex, op := .identity,
    doc := "ℚ ⊆ ℂ: a rational is a complex number" },
  { src := .exact .real, tgt := .exact .complex, op := .identity,
    doc := "ℝ ⊆ ℂ: the other link of SPEC.md's chain — a real number is a \
complex number with no imaginary part" }
]

run_cmd stdCanonicalMaps.forM registerCanonicalMap!

/-! ## 4 · Capability routes — what can currently be executed

The computability layer. Every pattern below is disjoint from its siblings
for the same method, so every route ships at priority 0: selection never
depends on a tie-break. The `opId`s are exactly the operations
`Native.run` and the Sage adapter implement — and that is CHECKED, not a
convention: each backend registers the receiver signatures of its ops
(`OpSig`), and `registerRoute!` fails the build for a route naming an
undeclared op or a pattern its op does not accept (design review
2026-07-30).

One family of routes is deliberately ABSENT and must stay absent:

- `det`/`inverse` on matrices with entry domain other than ℚ: the
  `matrixOver (exact rat)` patterns below are the whole routed family, so
  a matrix over ℤ/5 resolves (MatrixElems) and then reports the honest
  structured gap. `Mat₂(ℤ/5).det()` is the acceptance proof's gap. -/

private def stdRoutes : Array Route := #[
  -- factorization
  { method := `factor, pattern := .elemOf (.exact .int),
    backend := `sage, opId := "factor_int" },
  { method := `factor, pattern := .elemOf (.polyOver (.exact .rat)),
    backend := `sage, opId := "factor_poly_q" },
  { method := `factor, pattern := .elemOf (.polyOver (.exact .int)),
    backend := `sage, opId := "factor_poly_z" },
  -- over ℂ the factors are linear: SPEC.md's own `q := map p to ℂ[x]`
  { method := `factor, pattern := .elemOf (.polyOver (.exact .complex)),
    backend := `sage, opId := "factor_poly_c" },
  -- gcd: routed for ℤ only. It stays meaningful on every UFD element, so
  -- `p.gcd(q)` in ℤ[x] is the honest structured gap the audit lists
  { method := `gcd, pattern := .elemOf (.exact .int),
    backend := `sage, opId := "gcd_int" },
  -- primality, routed for ℤ; irreducibility in ℤ[x] is the honest gap
  { method := `is_prime, pattern := .elemOf (.exact .int),
    backend := `sage, opId := "is_prime_int" },
  -- degree is a structural read of the coefficient array: native, exact,
  -- and defined over every coefficient domain
  { method := `deg, pattern := .elemOf (.polyOver .anyDom),
    backend := `native, opId := "poly_deg" },
  -- the derivative is coefficient arithmetic this engine owns outright, so it
  -- is native and defined over every coefficient domain — nothing about it is
  -- a computability question a backend could answer better
  { method := `derivative, pattern := .elemOf (.polyOver .anyDom),
    backend := `native, opId := "poly_derivative" },
  -- …and the antiderivative DIVIDES, so it is routed for the two coefficient
  -- rings whose fraction field this slice presents. Over ℤ/n it is the honest
  -- capability gap `det` over ℤ/5 already is: meaningful, not executable
  { method := `antiderivative, pattern := .elemOf (.polyOver (.exact .int)),
    backend := `native, opId := "poly_antiderivative" },
  { method := `antiderivative, pattern := .elemOf (.polyOver (.exact .rat)),
    backend := `native, opId := "poly_antiderivative" },
  -- roots in the coefficient ring; ℤ[x] and ℚ[x] are routed, and a
  -- polynomial over ℤ/n is the honest gap
  { method := `roots, pattern := .elemOf (.polyOver (.exact .int)),
    backend := `sage, opId := "roots_poly_z" },
  { method := `roots, pattern := .elemOf (.polyOver (.exact .rat)),
    backend := `sage, opId := "roots_poly_q" },
  -- …and in ℂ, where a nonzero polynomial splits: `x² − 2` has its two
  -- irrational roots here and nowhere below
  { method := `roots, pattern := .elemOf (.polyOver (.exact .complex)),
    backend := `sage, opId := "roots_poly_c" },
  -- exact matrix algebra over ℚ
  { method := `det, pattern := .elemOf (.matrixOver (.exact .rat)),
    backend := `sage, opId := "mat_det_q" },
  { method := `inverse, pattern := .elemOf (.matrixOver (.exact .rat)),
    backend := `sage, opId := "mat_inv_q" },
  -- …and the two reads of a ℚ matrix's reduced row echelon form, which the
  -- subspace presentation already owns: the rank is its row count and the
  -- kernel its free columns, so both are exact NATIVE decisions. Only ℚ
  -- entries are routed, so Mat₂(ℤ/5) carries the same honest gap `det` does
  { method := `rank, pattern := .elemOf (.matrixOver (.exact .rat)),
    backend := `native, opId := "mat_rank" },
  { method := `ker, pattern := .elemOf (.matrixOver (.exact .rat)),
    backend := `native, opId := "mat_ker" },
  { method := `dim, pattern := .spanSet, backend := `native, opId := "span_dim" },
  -- the trace is a structural read of the diagonal, so it is native and
  -- defined over every entry domain — Mat₂(ℤ/5) has one even where `det`
  -- gaps, which is exactly the separation of the two judgments
  { method := `trace, pattern := .elemOf (.matrixOver .anyDom),
    backend := `native, opId := "mat_trace" },
  -- the characteristic polynomial and the companion matrix are Sage's, with
  -- the reply CHECKED against this call's receiver (monic of the matrix's
  -- size; the polynomial's own degree and trace)
  { method := `charpoly, pattern := .elemOf (.matrixOver (.exact .rat)),
    backend := `sage, opId := "mat_charpoly_q" },
  { method := `companion_matrix, pattern := .elemOf (.polyOver (.exact .rat)),
    backend := `sage, opId := "poly_companion_q" },
  -- modules
  { method := `annihilator, pattern := .cyclicMod,
    backend := `native, opId := "annihilator_cyclic" },
  -- enumeration: exactly the presentations `Native.run "nth"` implements —
  -- ℕ, ℤ, progressions, and explicit finite lists
  { method := `nth, pattern := .domainIs (.exact .nat), backend := `native, opId := "nth" },
  { method := `nth, pattern := .domainSetOf (.exact .nat), backend := `native, opId := "nth" },
  { method := `nth, pattern := .domainIs (.exact .int), backend := `native, opId := "nth" },
  { method := `nth, pattern := .domainSetOf (.exact .int), backend := `native, opId := "nth" },
  { method := `nth, pattern := .domainIs (.exact .rat), backend := `native, opId := "nth" },
  { method := `nth, pattern := .domainSetOf (.exact .rat), backend := `native, opId := "nth" },
  { method := `nth, pattern := .progression .anyDom, backend := `native, opId := "nth" },
  { method := `nth, pattern := .finiteSet, backend := `native, opId := "nth" },
  -- set operations; `anySet` also accepts a domain used as a set
  { method := `cardinality, pattern := .anySet, backend := `native, opId := "cardinality" },
  { method := `contains, pattern := .anySet, backend := `native, opId := "contains" },
  { method := `set_eq, pattern := .anySet, backend := `native, opId := "set_eq" },
  { method := `subset, pattern := .anySet, backend := `native, opId := "subset" },
  -- the binary operations build an explicit element list, so only explicit
  -- finite receivers are routed: `ℤ ∪ A` resolves and then gaps honestly
  { method := `union, pattern := .finiteSet, backend := `native, opId := "set_union" },
  { method := `intersect, pattern := .finiteSet, backend := `native,
    opId := "set_intersect" },
  { method := `diff, pattern := .finiteSet, backend := `native, opId := "set_diff" },
  { method := `symdiff, pattern := .finiteSet, backend := `native, opId := "set_symdiff" },
  { method := `sum, pattern := .finiteSet, backend := `native, opId := "set_sum" },
  { method := `prod, pattern := .finiteSet, backend := `native, opId := "set_prod" },
  -- the complex plane: structural reads of the exact form `a + b√d`, which
  -- the engine genuinely decides, so they are native and exact
  { method := `re, pattern := .elemOf (.exact .complex), backend := `native, opId := "alg_re" },
  { method := `re, pattern := .elemOf (.exact .real), backend := `native, opId := "alg_re" },
  { method := `im, pattern := .elemOf (.exact .complex), backend := `native, opId := "alg_im" },
  { method := `im, pattern := .elemOf (.exact .real), backend := `native, opId := "alg_im" },
  { method := `bar, pattern := .elemOf (.exact .complex), backend := `native,
    opId := "alg_conj" },
  { method := `bar, pattern := .elemOf (.exact .real), backend := `native,
    opId := "alg_conj" },
  { method := `abs, pattern := .elemOf (.exact .complex), backend := `native,
    opId := "alg_abs" },
  { method := `abs, pattern := .elemOf (.exact .real), backend := `native,
    opId := "alg_abs" },
  -- SPEC.md's numerical approximation, routed for the exact REALS. The
  -- backend owns arbitrary-precision evaluation and picks its own strategy;
  -- what comes back is a certificate, verified exactly on this side
  -- (`Value.mkApprox`). A ℂ receiver is the deliberate gap next to
  -- `det` over ℤ/5: a real decimal is not a presentation of a complex number,
  -- and projecting to one would answer a question nobody asked
  { method := `approximate, pattern := .elemOf (.exact .real),
    backend := `sage, opId := "approx_real" },
  -- the image: presented for a constant map, and for a linear map on ℕ (an
  -- arithmetic progression). Anything else is a loud refusal at execution —
  -- a partiality WITHIN the routed shape, like the zero polynomial's degree
  { method := `image, pattern := .elemOf .anyFuncs, backend := `native,
    opId := "func_image" },
  -- the three analysis operations are the backend's: a symbolic limit, a
  -- symbolic definite integral and a Taylor expansion are exactly what this
  -- side has no exact computation for, which is why they are ROUTED rather
  -- than native — and why ALL THREE replies are trusted rather than certified
  -- (the Taylor expansion with one extra check: its coefficients must be
  -- exact rationals)
  { method := `limit, pattern := .elemOf .anyFuncs, backend := `sage,
    opId := "sym_limit" },
  { method := `definite_integral, pattern := .elemOf .anyFuncs, backend := `sage,
    opId := "sym_definite_integral" },
  { method := `taylor_expansion, pattern := .elemOf .anyFuncs, backend := `sage,
    opId := "sym_taylor" }
]

run_cmd stdRoutes.forM registerRoute!

/-! ## 5 · Audit representatives

`#capability_gaps` crosses the declared methods with these concrete
presentations (the documented ceiling: representatives, not all conceivable
objects). Labels are human-facing and appear verbatim in the audit. -/

private def stdRepresentatives : Array Representative := #[
  ("ℤ", .domainObj .int),
  ("ℚ", .domainObj .rat),
  ("ℕ", .domainObj .nat),
  ("360 ∈ ℤ", .elem .int (.int 360)),
  ("x^3 − 2x + 1 ∈ ℤ[x]", polyZ),
  ("sample q ∈ ℚ[x]", polyQ),
  ("[1,2;3,4] ∈ Mat₂(ℚ)", mat2Q),
  ("[1,2;3,4] ∈ Mat₂(ℤ/5)", mat2Mod5),
  -- ℤ[x] AS A SET: countable, with no registered enumeration, so the audit
  -- carries the `nth` gap
  ("ℤ[x]", .domainObj (.poly .int)),
  -- a polynomial over a ring whose roots are not routed: `deg` is structural
  -- and works, `roots` is the gap
  ("x + 1 ∈ ℤ/5[x]", .elem (.poly (.mod 5))
    (Value.mkPoly (.mod 5) #[Value.mkMod 5 1, Value.mkMod 5 1])),
  ("ℤ/4 as ℤ-module", .cyclicModule 4),
  ("Spec ℚ[x]", .specOf (.poly .rat)),
  ("x^3 + ℚ ⊆ ℚ[x]", .setObj (.coset (Value.mkPoly .rat #[.rat 0, .rat 0, .rat 0, .rat 1]) .rat)),
  ("{0,2,4,…}", .setObj (.arithProg .int (.int 0) (.int 2) none)),
  -- the two DENOTED sets: countable/counted by cardinal arithmetic, and
  -- carrying the honest gaps for every operation that would need an element
  -- list (the binary operations, and `nth`)
  ("{1,2,3} × {1,2,3}", .setObj (.product finSet123 finSet123)),
  ("𝒫({1,2,3})", .setObj (.powerset finSet123)),
  ("n ↦ 2n ∈ ℕ → ℕ", doubling),
  -- the complex plane: an element (whose four methods route) and ℂ itself,
  -- which is a set — an UNCOUNTABLE one, so the binary set operations gap on
  -- it exactly as they do on ℤ
  -- the subspace: a countable SET (so `∈`, `=` and `⊆` reach it) that is also
  -- the QQ-Mod object carrying `dim`, and carries the `nth` gap ℤ[x] does
  ("span_ℚ{(1,0,1), (0,1,1)} ≤ ℚ³", .setObj spanW),
  ("2 + 2i ∈ ℂ", z2plus2i),
  ("√2 ∈ ℝ", sqrt2),
  ("ℂ", .domainObj .complex),
  ("ℤ[[t]]", .domainObj (.series .int))
]

run_cmd stdRepresentatives.forM registerRepresentative!

/- Every shipped fixture is in NORMAL FORM. Decoding runs a value through its
normalizing constructors, so a value that survives the wire codec unchanged is
exactly one whose parts are their own `mkAlg`/`mkPoly`/`mkMod` images — one
round trip is the whole check, and it covers fixtures added later (a surd
COEFFICIENT inside a polynomial included). Worth checking because these are
the objects `#capability_gaps` ships: `2 + 2i` written out of normal form
renders `2 + 2i√4` and compares unequal to its own value. -/
run_cmd do
  let vals := (representatives (← getEnv)).flatMap fun (label, o) =>
    match o with
    | .elem _ v => #[(label, v)]
    | .setObj (.finite _ es) => es.map ((label, ·))
    | _ => #[]
  for (label, v) in vals do
    unless (Codec.valueFromJson (Codec.valueToJson v)).toOption == some v do
      throwError s!"the representative '{label}' is not in normal form: \
{v.render} does not survive its own codec"

/-! ## 6 · Proofs of the universe

These run at ELABORATION time, so a registration mistake fails the build
rather than the notebook. They are stated as one reusable action so
`CasDslTests/Std.lean` can re-run the identical claims against the
*imported* environment — which additionally proves the registries survive
the olean round trip that the kernel's session cache depends on. -/

/-- The transport step of a resolution, as the name of the functor that
produced it (`none` = the method arrived without transport). Asserted
explicitly everywhere below: "resolves" and "resolves *directly*" are
different claims, and round two must never blur them. -/
private def transportOf (res : Resolution) : Option Name :=
  res.viaFunctor.map (·.functor)

/-- `m` is semantically available on `o` through the inheritance chain `via`
(after transport along `functor?`, when given), and routes to `backend`. -/
def expectRouted (env : Environment) (o : Obj) (m : Name) (via : List Name)
    (backend : Name) (functor? : Option Name := none) : CommandElabM Unit := do
  match resolveMethod env o m with
  | .error e => throwError s!"{m} is not available on {o.presentation}: {repr e}"
  | .ok res =>
    unless res.via == via do
      throwError s!"{m} on {o.presentation} arrived via {res.via}, expected {via}"
    unless transportOf res == functor? do
      throwError s!"{m} on {o.presentation} was transported by {repr (transportOf res)}, \
expected {repr functor?}"
    match routeFor env res (res.concreteReceiver o) with
    | .chosen r =>
        unless r.backend == backend do
          throwError s!"{m} on {o.presentation} routed to '{r.backend}', expected '{backend}'"
    | .gap _ =>
        throwError s!"{m} on {o.presentation} has no route, expected backend '{backend}'"
    | .ambiguousRoutes rs =>
        throwError s!"{m} on {o.presentation} matched {rs.size} routes tied on priority"

/-- `m` is semantically available on `o` through `via` and has NO route: a
deliberate, structured capability gap. Both halves are asserted, because
the separation of the two judgments is the whole point. -/
def expectGap (env : Environment) (o : Obj) (m : Name) (via : List Name)
    (functor? : Option Name := none) : CommandElabM Unit := do
  match resolveMethod env o m with
  | .error e =>
      throwError s!"{m} must stay AVAILABLE on {o.presentation}; a missing route may \
never remove it: {repr e}"
  | .ok res =>
    unless res.via == via do
      throwError s!"{m} on {o.presentation} arrived via {res.via}, expected {via}"
    unless transportOf res == functor? do
      throwError s!"{m} on {o.presentation} was transported by {repr (transportOf res)}, \
expected {repr functor?}"
    match routeFor env res (res.concreteReceiver o) with
    | .gap g =>
        unless g.semanticVia == via do
          throwError s!"the gap for {m} on {o.presentation} recorded via {g.semanticVia}"
    | .chosen r =>
        throwError s!"{m} on {o.presentation} unexpectedly routed to '{r.backend}'/{r.opId}; \
this gap is deliberate"
    | .ambiguousRoutes rs =>
        throwError s!"{m} on {o.presentation} matched {rs.size} routes tied on priority"

/-- `m` does not reach `o` at all: it is declared strictly below every
category `o` inhabits and no registered functor carries it there, so it must
not leak upward — nor sideways along a functor. -/
def expectNotApplicable (env : Environment) (o : Obj) (m : Name)
    : CommandElabM Unit := do
  match resolveMethod env o m with
  | .error (.notApplicable ..) => pure ()
  | .error e =>
      throwError s!"{m} on {o.presentation} failed with {repr e}, expected notApplicable"
  | .ok res =>
      let how := match transportOf res with
        | some f => s!"transported by functor '{f}'"
        | none => "by membership or inheritance"
      throwError s!"{m} leaked to {o.presentation} from category \
'{res.decl.receiver}' ({how})"

/-- The claims the standard universe exists to make true. -/
def acceptanceProofs (env : Environment) : CommandElabM Unit := do
  -- EuclideanElems ≤ FactorizationElems carries `factor` to integers, and
  -- the developer routed it to sage
  expectRouted env (.elem .int (.int 360)) `factor [`FactorizationElems] `sage
  -- THE inheritance demo: `annihilator` is declared only on Modules and
  -- reaches the fixture through SmallModules ≤ Modules — DIRECTLY, with no
  -- transport, even though a functor out of Modules is registered: round one
  -- wins unconditionally, so round two can never take this method away
  expectRouted env (.cyclicModule 4) `annihilator [`Modules] `native (functor? := none)
  -- ℚ is countable and, since round three (#17), enumerable: the Cantor
  -- zigzag is its registered convention, so `nth` routes
  expectRouted env (.domainObj .rat) `nth [] `native
  -- THE central separation: `det` is meaningful on any MatrixElems member,
  -- and only ℚ-entry matrices are routed — Mat₂(ℤ/5) is the honest gap
  expectRouted env mat2Q `det [] `sage
  expectGap env mat2Mod5 `det []
  -- SPEC.md §Vectors and matrices: `rank` and `ker` are reads of the reduced
  -- row echelon form, so they are NATIVE — and routed for ℚ entries only, so
  -- Mat₂(ℤ/5) carries exactly the gap `det` does
  expectRouted env mat2Q `rank [] `native
  expectRouted env mat2Q `ker [] `native
  expectGap env mat2Mod5 `rank []
  expectGap env mat2Mod5 `ker []
  -- SPEC.md §A composed computation: the TRACE is a structural read of the
  -- diagonal, so it is native and reaches every entry domain — Mat₂(ℤ/5) has
  -- one where `det` gaps, which is the separation of the two judgments in one
  -- object. The characteristic polynomial and the companion matrix are the
  -- backend's, over ℚ
  expectRouted env mat2Q `trace [] `native
  expectRouted env mat2Mod5 `trace [] `native
  expectRouted env mat2Q `charpoly [] `sage
  expectGap env mat2Mod5 `charpoly []
  expectRouted env polyQ `companion_matrix [] `sage
  -- …and a ℤ[x] polynomial carries the honest gap: the op is registered for
  -- ℚ[x], and `map r to ℚ[x]` is one explicit step away
  expectGap env polyZ `companion_matrix []
  -- neither leaks off its own receiver
  expectNotApplicable env polyQ `trace
  expectNotApplicable env mat2Q `companion_matrix
  -- SPEC.md §Subspaces and spans: the subspace is a countable SET (so `∈`,
  -- `=` and `⊆` reach it through the ordinary hierarchy) and INDEPENDENTLY
  -- the QQ-Mod object that owns `dim` — neither membership implies the other
  expectRouted env (.setObj spanW) `contains [`Sets] `native
  expectRouted env (.setObj spanW) `set_eq [`Sets] `native
  expectRouted env (.setObj spanW) `subset [`Sets] `native
  expectRouted env (.setObj spanW) `cardinality [`Sets] `native
  expectRouted env (.setObj spanW) `dim [] `native
  -- …and no enumeration of a subspace is registered, so `nth` is the honest
  -- gap ℤ[x] carries, not a narrower category
  expectGap env (.setObj spanW) `nth []
  -- `dim` does not leak to the sets that are not modules, nor to a matrix
  expectNotApplicable env (.setObj finSet123) `dim
  expectNotApplicable env mat2Q `dim
  -- ℤ[x] is a UFD, so `factor` is meaningful where the polynomial lives —
  -- and since round three (#18) it is routed there, not only on ℚ[x]
  expectRouted env polyZ `factor [] `sage
  -- no upward leak: ℤ/5 elements are CommRingElems, `factor` lives below
  expectNotApplicable env (.elem (.mod 5) (Value.mkMod 5 2)) `factor
  -- gcd is declared where gcds exist — on UFD elements — and routed for ℤ
  expectRouted env (.elem .int (.int 84)) `gcd [`FactorizationElems] `sage
  -- …so an ℤ[x] gcd is available and NOT executable: an honest backlog item,
  -- exactly like det over ℤ/5, never a reason to move the declaration
  expectGap env polyZ `gcd []
  -- the two polynomial reads are INDEPENDENT memberships: `deg` arrives
  -- through PolynomialElems with no inheritance step, on both rings, while
  -- `factor` above arrived through the divisibility side
  expectRouted env polyZ `deg [] `native
  expectRouted env polyQ `deg [] `native
  expectRouted env polyZ `roots [] `sage
  expectRouted env polyQ `roots [] `sage
  -- SPEC.md §Polynomials: over ℂ the same two operations are routed to their
  -- own ops — which is where the cubic splits and where `x² − 2` has roots
  expectRouted env polyC `factor [`FactorizationElems] `sage
  expectRouted env polyC `roots [] `sage
  expectRouted env polyC `deg [] `native
  -- a polynomial over ℤ/5 is still a polynomial: `deg` is a structural read
  -- and routes, `roots` is not implemented there and gaps
  expectRouted env (.elem (.poly (.mod 5)) (Value.mkPoly (.mod 5) #[Value.mkMod 5 1]))
    `deg [] `native
  expectGap env (.elem (.poly (.mod 5)) (Value.mkPoly (.mod 5) #[Value.mkMod 5 1]))
    `roots []
  -- SPEC.md §Differentials: the derivative is a STRUCTURAL read like `deg`,
  -- so it arrives through PolynomialElems with no inheritance step and routes
  -- natively over every coefficient ring — including the ℤ/5 one where
  -- `roots` gaps, which is the two judgments visible in one object
  expectRouted env polyZ `derivative [] `native
  expectRouted env polyQ `derivative [] `native
  expectRouted env (.elem (.poly (.mod 5)) (Value.mkPoly (.mod 5) #[Value.mkMod 5 1]))
    `derivative [] `native
  -- …and it does not leak to a ring element that is not a polynomial
  expectNotApplicable env (.elem .int (.int 360)) `derivative
  -- SPEC.md §Indefinite integration: the ANTIDERIVATIVE divides, so it routes
  -- over ℤ[x] and ℚ[x] and carries the honest gap over ℤ/5[x] — the two
  -- judgments separated in one method, exactly as `det` separates them
  expectRouted env polyZ `antiderivative [] `native
  expectRouted env polyQ `antiderivative [] `native
  expectGap env (.elem (.poly (.mod 5)) (Value.mkPoly (.mod 5) #[Value.mkMod 5 1]))
    `antiderivative []
  -- …and the coset it returns is a SET like any other: counted, compared and
  -- tested for membership through the ordinary hierarchy, with `nth` the gap
  -- ℤ[x] carries
  expectRouted env (.setObj (.coset (Value.mkPoly .rat #[.rat 0, .rat 1]) .rat))
    `cardinality [`Sets] `native
  expectRouted env (.setObj (.coset (Value.mkPoly .rat #[.rat 0, .rat 1]) .rat))
    `contains [`Sets] `native
  expectRouted env (.setObj (.coset (Value.mkPoly .rat #[.rat 0, .rat 1]) .rat))
    `set_eq [`Sets] `native
  expectGap env (.setObj (.coset (Value.mkPoly .rat #[.rat 0, .rat 1]) .rat)) `nth []
  -- SPEC.md's `Spec ℚ[x] in Schemes/ℚ` is an ascription TAG and owns NOTHING:
  -- it is not a set, so none of the set methods reach it. That is the whole
  -- claim, and it is asserted rather than assumed
  expectNotApplicable env (.specOf (.poly .rat)) `cardinality
  expectNotApplicable env (.specOf (.poly .rat)) `contains
  expectNotApplicable env (.specOf (.poly .rat)) `derivative
  -- `deg` is a polynomial question and does not leak to the ring's elements
  -- at large: an integer is not a polynomial here
  expectNotApplicable env (.elem .int (.int 360)) `deg
  -- ℤ[x] AS A SET is countable, which is what `p ∈ ℤ[x]` asks of it…
  expectRouted env (.domainObj (.poly .int)) `contains [`Sets] `native
  -- …and no enumeration of it is registered, so `nth` is the honest gap
  expectGap env (.domainObj (.poly .int)) `nth []
  -- a finite set reaches `cardinality` through FiniteSets ≤ CountableSets ≤ Sets
  expectRouted env (.setObj (.finite .int #[.int 1, .int 2, .int 3])) `cardinality
    [`CountableSets, `Sets] `native
  -- THE transport demo: `cardinality` is declared on Sets, which the module
  -- fixture does not inhabit; it arrives by transporting the receiver along
  -- the forgetful functor and routes against the IMAGE (a finite set)
  expectRouted env (.cyclicModule 4) `cardinality [`CountableSets, `Sets] `native
    (functor? := `UnderlyingSet)
  expectRouted env (.cyclicModule 4) `contains [`CountableSets, `Sets] `native
    (functor? := `UnderlyingSet)
  expectRouted env (.cyclicModule 4) `nth [`CountableSets] `native
    (functor? := `UnderlyingSet)
  -- SPEC.md §Finite sets: the binary operations are declared on Sets and
  -- routed for explicit finite receivers…
  expectRouted env (.setObj finSet123) `union [`CountableSets, `Sets] `native
  expectRouted env (.setObj finSet123) `intersect [`CountableSets, `Sets] `native
  expectRouted env (.setObj finSet123) `diff [`CountableSets, `Sets] `native
  expectRouted env (.setObj finSet123) `symdiff [`CountableSets, `Sets] `native
  expectRouted env (.setObj finSet123) `subset [`CountableSets, `Sets] `native
  -- SPEC.md §A composed computation: Σ and Π are declared on FINITE sets, so
  -- they arrive DIRECTLY on a finite set's own profile entry…
  expectRouted env (.setObj finSet123) `sum [] `native
  expectRouted env (.setObj finSet123) `prod [] `native
  -- …and do not reach ℤ at all: the sum over an infinite set is a limit this
  -- slice has no notion of, which is a different statement from "no route"
  expectNotApplicable env (.domainObj .int) `sum
  expectNotApplicable env (.domainObj .int) `prod
  -- …so a union with an infinite presentation on the LEFT is available and
  -- not executable: the honest gap, exactly like det over ℤ/5
  expectGap env (.domainObj .int) `union [`Sets]
  -- a denoted set is a set: it is counted and included…
  expectRouted env (.setObj (.powerset finSet123)) `cardinality [] `native
  expectRouted env (.setObj (.product finSet123 finSet123)) `cardinality [] `native
  expectRouted env (.setObj (.powerset finSet123)) `contains [] `native
  -- …the operations needing an element list of it are the honest gaps…
  expectGap env (.setObj (.product finSet123 finSet123)) `union []
  -- …and `nth` does not even reach it: `Sets` is the only membership a
  -- pattern over one presentation can state for a denoted set, and `nth`
  -- is declared strictly below, on CountableSets
  expectNotApplicable env (.setObj (.powerset finSet123)) `nth
  -- SPEC.md §Ellipses' `n.is_prime()`: declared where primes exist, routed
  -- for ℤ — so irreducibility in ℤ[x] is available and not executable
  expectRouted env (.elem .int (.int 7)) `is_prime [`FactorizationElems] `sage
  expectGap env polyZ `is_prime []
  -- SPEC.md's `e.image()`: the image is the one method functions own natively
  expectRouted env doubling `image [] `native
  -- …and SPEC.md §Elementary calculus' three, which are the backend's
  expectRouted env doubling `limit [] `sage
  expectRouted env doubling `definite_integral [] `sage
  expectRouted env doubling `taylor_expansion [] `sage
  -- none of them leaks off a function receiver
  expectNotApplicable env (.elem .int (.int 360)) `limit
  expectNotApplicable env polyQ `taylor_expansion
  -- …and it does not leak to the values a function takes
  expectNotApplicable env (.elem .int (.int 360)) `image
  -- SPEC.md §Exact number systems: the complex plane's four methods, on ℂ and
  -- on the ℝ inside it, natively — they are structural reads of `a + b√d`
  for m in [`re, `im, `bar, `abs] do
    expectRouted env z2plus2i m [] `native
    expectRouted env sqrt2 m [] `native
  -- …and they do NOT reach the domains whose membership in ℂ is a missed
  -- specificity rather than a registration: `3.re()` and `|3|` say so
  expectNotApplicable env (.elem .int (.int 3)) `re
  expectNotApplicable env (.elem .int (.int 3)) `abs
  -- SPEC.md's `map √2 to ℝ/O(1/10^{10})`: asking for a decimal is meaningful
  -- for every exact number, and only the REALS are routed — so ℂ is a
  -- structured gap exactly like det over ℤ/5, and never a silent projection
  expectRouted env sqrt2 `approximate [] `sage
  expectGap env z2plus2i `approximate []
  -- ℝ and ℂ are sets, and uncountable ones: membership routes, indexing is
  -- not even applicable (`nth` is declared on CountableSets)
  -- …and `Sets` is where they enter, so `contains` is declared DIRECTLY on
  -- their profile entry rather than inherited (ℤ reaches it through
  -- CountableSets ≤ Sets, and that difference is the point of recording via)
  expectRouted env (.domainObj .complex) `contains [] `native
  expectRouted env (.domainObj .real) `contains [] `native
  expectNotApplicable env (.domainObj .real) `nth
  -- SPEC.md §Elementary calculus: a series RING is a set — uncountable, like
  -- ℂ[x] — so membership routes and indexing is not even applicable
  expectRouted env (.domainObj (.series .int)) `contains [] `native
  expectNotApplicable env (.domainObj (.series .int)) `nth

run_cmd acceptanceProofs (← getEnv)

end CasDsl.Std
