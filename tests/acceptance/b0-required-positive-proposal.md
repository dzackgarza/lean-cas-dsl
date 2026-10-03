# Remaining fixed B0 positive questions

These are mathematical admission proposals for the already required examples in
the B0 plan. They do not introduce coverage or release any row. Original admitted
assertions remain unchanged. Input mathematics: `lean_categories` `b249ca2`, the
approved SPEC, and the sources cited below. No expected value comes from a candidate.

## Lattice ranks

`rank(A₂)=2` is already present as `lattices.rank.a2` in the fixed inventory.
Its selected negative Cartan form and base ring Z must remain attached to the
question; observing the cardinality of its carrier is a different question.

The owed E₈ question is rank_Z(E₈)=8. Independently, define
E₈ as the vectors in R⁸ which are either all integers or all half-integers,
and whose coordinate sum is an even integer, with the standard inner product
(negated if the accepted lattice convention requires it). It contains D₈,
the even-sum integer vectors, which has rank 8, and is contained in (1/2)Z⁸,
also rank 8; thus rank 8 follows. Source: Conway–Sloane, SPLAG, Chapter 4,
the E₈ lattice. The named accepted object and its presentation must determine
executable spelling: no E₈ object name was found in the accepted catalogue at
`b249ca2`, so inventing a downstream object would violate semantic authority.

## Group kernels with defining inclusions

Fix S₃=Perm({0,1,2}) with composition. The sign homomorphism to Z/2 sends even
permutations to 0 and odd permutations to 1. Its kernel is
{identity,(012),(021)}=A₃, cardinality 3, with the inclusion A₃ ↪ S₃.
The trivial homomorphism S₃ → Z/2 has kernel S₃, cardinality 6, with identity
inclusion. The identity homomorphism S₃ → S₃ has kernel the trivial subgroup,
cardinality 1, with its unique inclusion. Each observation concerns a group
subobject with that actual arrow, rather than a bare set returned by computation.
Each defining inclusion composes with its specified map to the zero map and
satisfies the kernel universal property. Source: Dummit–Foote, Abstract Algebra,
Chapter 3 §1, kernels and quotient groups; Chapter 1 §3, symmetric groups.

The count assertions alone do not check the inclusion: acceptance must also
identify its domain/codomain and the commuting equation for the specific map.
An inclusion-free result is malformed even if its cardinality is correct.
The accepted `b249ca2` catalogue has group subobjects and their inclusion
interface, but no named S₃, sign or trivial map found. Those accepted input
declarations are needed before executable assertions can be written without
inventing downstream semantics.

## Abelian property

The cyclic additive group Z/3 is abelian: addition of residue classes commutes.
S₃ is not abelian: (01)(12) and (12)(01) are the two different 3-cycles.
The owed questions are respectively `is_abelian(Z/3)=true` and
`is_abelian(S₃)=false`, on those selected group structures, retaining their
carriers. Source: Dummit–Foote, Chapter 1 §§1–3. A backend property answer
cannot replace either object by a refined host. `is_abelian` is group-restricted
in the accepted catalogue; the named ring Z/3 is not silently a selected group.
Executable spelling requires an accepted named group or actual selected route.

## Formed-module carrier cardinality

The original `lattices.card.a2` already asks the cardinality of rootA(2), an
object of `BilWFormCat Z` with carrier Z², value module Z and its negative
Cartan form. Its answer is aleph_0. The original `lattices.card.a0` has answer
1, despite its value module Z being infinite. The latter distinguishes the
carrier cardinality from cardinality of the form's target module.

The existing unadmitted `formed_modules.cas` proposals have correct independent
answers as well, directly against accepted `b249ca2`:
`A_dual(0)` is the unique vector in Q⁰, hence cardinality 1;
`A_dual(2)` contains the injective image of Z² (`castLinear_mem_dual`),
and is contained in countable Q², hence cardinality aleph_0.
Its value module is Q, even at rank zero. The existing file's cited later
revision is unnecessary as mathematical provenance: the objects and injection
are present in accepted `LeanCategories/Lattices/Integral.lean` at `b249ca2`.
Source: Conway–Sloane, SPLAG, Chapter 2 §2.2; countability of Q and finite
products, infinitude of Z. The restriction of the rational form remains data.

## Nonidentity F₉ presentation transport

Let P=F₃[X]/(X²+1) and Q=F₃[Y]/(Y²+Y+2), with their quotient generators
x and y. Both quadratics have no root in F₃ (evaluate at 0,1,2), so each
quotient is a field with nine elements. Define phi:P → Q by x ↦ y+2,
fixing F₃. In Q,
(y+2)²+1=y²+y+2=0; the assignment is well defined.
Its inverse sends y ↦ x+1: (x+1)²+(x+1)+2=x²+1=0 in P.
The composites send x to x and y to y, so this is the prescribed nonidentity
presentation comparison, not equality of generators or equality of objects.

The owed transport observation is phi(x)=y+2. Additionally phi(x²)=2 and
phi(x+1)=y; these distinguish actual transport from copying a generator.
The structured result retains phi and its source/target presentations.
Source: the universal property of polynomial quotients, and arithmetic in F₃
(Dummit–Foote, Chapter 9, polynomial rings and quotient rings).
No named accepted quotient presentations or this comparison were found in
`b249ca2`'s catalogue, so the executable syntax consumes a missing accepted
mathematical release rather than a kernel-authored substitution.

## Submission and remaining operation inputs

These fixed mathematical questions and independently justified answers are
ready for independent admission assessment. They are not a declaration that
the required computational path ran. Executable assertion construction consumes
the accepted named objects/maps/presentations above; exit trials additionally
consume a frozen compatible kernel/contract/old-leaf tuple. Neither dependency
prevents authoring or assessing the full original interpretation proposal.
