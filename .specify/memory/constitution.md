# lean-cas-dsl Constitution

**Status:** normative project constitution

## Core Principles

C0 states the product and its guiding commitments. C1–C13 and C15 specify its mathematical,
computational and user-facing invariants. The [authority and scope](#authority-and-scope),
[obligation classes](#obligation-classes) and [formal contract](#formal-contract-and-notation)
below fix their interpretation. Contributor obligations and their concrete enforcement belong to
Governance; they remain binding without being substituted for the product definition.

### C0. A growing categorical language for mathematical research

lean-cas-dsl must provide a usable computer-algebra language in which a mathematician defines
objects, states propositions, constructs and composes maps, performs calculations, and uses the
resulting mathematical objects in subsequent work. Its interfaces and compositions come from
independently formalized categorical mathematics. Computational providers realize the operations
specified by that mathematics. The product must support ordinary mathematical notebook and
research work through a coherent mathematical context, familiar notation and readable results.

Its defining improvement is **how mathematical capabilities grow**. Within the accepted
extension mechanisms, a new mathematical construction supplies its genuinely new formal data and
immediate relationships. The generic
language mechanism derives the applicable interfaces and compositions. A new generic operation
reaches existing objects to which it applies without editing their old implementations.
Computational growth supplies implementations of these independently defined obligations.
Neither direction of growth may require maintaining a second mathematical hierarchy downstream
or repeatedly repairing the same consequence in each leaf. The supported mechanisms must cover
the independently required mathematical scope; declaring a smaller fragment does not meet that
obligation.

The following commitments define the product through implementation changes:

- **Mathematical structure determines what can be asked.** An object has every interface
  warranted by its accepted constructions and hypotheses, including simultaneous structures
  and parameterized families. Operations are stated at their actual mathematical generality.
  Installing, removing or breaking a computational provider cannot change those meanings,
  interfaces or domains. C1, C3, C4 and C6 specify these obligations.
- **Objects, maps and selected structure remain first-class.** A result can include a subobject,
  a family, a quotient, a map, a chosen presentation or a universal construction. Its required
  defining maps, parameters, actions and comparisons must remain usable in subsequent
  constructions. The intended higher categorical scope and admitted infinite objects cannot
  be replaced by the representational limits of a particular runtime. C5, C7 and C8 specify
  the required preservation and admissible reductions.
- **The public language expresses substantial connected mathematics.** Its independently fixed
  contract includes definitions and propositions; exact arithmetic and explicitly qualified
  approximation; sets, comprehensions and infinite descriptions; typed functions and
  morphisms; polynomial and linear algebra; relative differentials, primitives, limits and
  series; and composition of the resulting constructions. These are mathematical capabilities,
  not a permanently closed catalogue of examples or an assertion that every possible question
  is decidable. C6, C11 and C15 preserve their required scope and semantics.
- **Execution answers a previously fixed mathematical question.** Formal definitions and laws,
  their correct interpretation, and correctness of a computed answer are distinct obligations.
  A computational leaf can return a wrong value but cannot redefine what the value was meant
  to compute, which laws apply, or what counts as the correct answer. Its data are computational
  claims rather than new mathematical axioms. C1, C2 and C9–C10 fix this trust boundary.
- **Research workflows must actually work through composition.** A result is an input to the
  next calculation, with the same selected mathematics and the promised usable interface.
  The delivered system must execute the complete independently required workflows, including
  later uses, required mixed-provider compositions and independent extensions. A declaration
  catalogue, an isolated demonstration or a correct report of missing computation does not
  deliver such a workflow. C8 and C11–C13 specify the positive requirements.
- **The ordinary interaction speaks mathematics.** Users must be able to discover applicable
  operations, work in mathematical notation, read mathematical answers and inspect their
  assumptions, chosen presentations and actual computational provenance. Ordinary expressions
  must not require backend names or private implementation vocabulary. C3 and C15 specify
  this user-facing contract.

For example, the requirement for an orthogonal group or stabilizer is its complete applicable
mathematical interface, including a later-added generic operation. The requirement for a
constructed kernel includes the selected ambient data and defining map needed by subsequent
uses. The original primitive-calculation workflow requires the specified family of primitives,
followed by restriction by an initial-value condition and use of the chosen result. These
examples identify the general obligations; special-casing their displayed specimens does not
satisfy them.

**Source basis:** [first public product definition][S46]; [original mathematical SPEC][S16];
[owner's growth and trust requirements][S3]; [fundamental-model chapter, §§1–9][S5];
[higher mathematical foundations][S12]; [mathematical generality][S27].

### C1. All mathematical authority is independently categorical

Every admitted public mathematical judgment must be derivable from the independently accepted
definitions and construction rules in **M**, under its explicit context: `M; Γ ⊢ J`. Those rules
fix its complete meaning, type and required categorical structure. Methods and predicates are
expressed by the appropriate formal mathematical constructions, including the required higher
morphisms where applicable. A backend name, Python class, implementation filter, registry label
or successful computation cannot supply a missing mathematical rule.

A constructed object, parameter instance or local hypothetical object need not have its own
pre-existing catalogue row. Its meaning comes from applying the accepted rules with the actual
parameters and assumptions. Requiring an enumerated declaration for every instance would defeat
the intended language and its infinite families.

There is one mathematical presentation: intrinsic objects, chosen presentations, families,
classifiers, sections, computational operations and higher comparisons belong to that same
independently owned mathematics. An implementation index is engineering data; a second
presentation/capability ontology with independent mathematical standing is prohibited. Genuine
basis and generator data are mathematical structures, not exceptions handed to a backend to
define.

Computations are requests to evaluate independently defined constructions or invariants, or to
solve lift or section problems, in this same mathematical diagram and on their specified
domains. Their prescribed answers have the mathematical codomains and selected structure fixed
there. Computational provenance or evidence does not by itself create a separate mathematical
codomain; whether a provider realizes the prescribed answer remains a separate correctness
obligation.

This constrains semantic authority, not the number of data structures. Compiler representations,
indexes and derived views are permissible when their interpretation remains fixed by the same
mathematical source and the required preservation is established.

For every provider or implementation-only change `u`,

$$
u(M,P,A)=(M,P,A).
$$

This is an authority restriction: these changes cannot redefine the mathematics, its intended
public reading or the independent expected answers. It does not prohibit authorized
implementation changes to the machinery that consumes them.

Independent formalization must be mathematically auditable against its stated sources and
intended definitions. Typechecking a convenient but wrong definition does not establish that it
is the intended mathematics. The historical requirement excludes `sorry` and project-created
axioms used to assume the desired result; legitimate hypotheses belong in the statement.

The independently owned formal API must also specify the **abstract computational obligations**:
what data and operations implement a construction, their dependent signatures, and how they
compose. Backend independence does not restrict it to bare noncomputable definitions from which
a downstream kernel must discover an execution model. Concrete invocation, encoding and provider
selection are engineering responsibilities. Supplying those mechanisms must not become authority
to redefine the abstract obligation.

The independent authorship and permitted-input requirements implementing this separation are
specified under [Governance](#independent-authorship-and-permitted-inputs-c1-c9-c10). They remain
mandatory; repository separation alone does not establish independence.

**Source basis:** [May ownership record][S1]; [July one-diagram correction][S2]; [September
owner record][S3]; [October computational-API correction][S4]; [categorical foundations and computation][S12];
[pre-migration author and
repository boundaries][S36]; [maintained permitted-input rules][S9].

### C2. Implementations cannot choose the obligation they satisfy

The specification, permitted representation interpretation and correctness relation must be
fixed independently of the candidate. A provider chooses private data structures and algorithms
within the released computational contract. The mathematical meaning of their admissible public
relationship to the requested construction is independently fixed. A need for a new mathematical
interpretation is not permission for the provider or downstream interpreter to author it.

The quantifier order is:

$$
\text{independently fix }(M,J,\operatorname{Req}_{M,J});
\quad\text{then assess }I\text{ against }\operatorname{Req}_{M,J}.
$$

It is not `for each I, choose a relation that makes I correct`. The failure of the latter is
elementary: for any total function `I`, define `R_I(x,y)` to mean `y = I(x)`. Then `R_I(x,I(x))`
holds for every `x` by reflexivity, including when `I` gives the wrong answer to the intended
problem. A proof of this statement supplies no relationship to that problem. The same defect
occurs if a leaf defines its own denotation, checker, comparison or expected result and the
system accepts that definition as authoritative.

This requirement does not silently replace the historical
opaque-computation/independent-assessment evidence model with mandatory proof-carrying results.
Any change to that evidence model must be stated separately. In either model, a supplier's
self-authored proposition cannot become the standard against which that supplier is judged.

In particular, the laws in a formal definition do not automatically become proof-producing
fields of every external reply. The independent API must distinguish mathematical laws from the
computational data and operations an implementation supplies. Decoding a numeral produces that
numeral; it does not prove it is the cardinality of the object asked about. Computational
representations cannot be cast into law-bearing formal structures by assuming the missing proof.

**Source basis:** [September owner record][S3]; [October fundamental-model chapter, §§3–5][S5].
The logical counterexample above is proved directly.

### C3. Mathematical meaning is independent of computational availability

For fixed **M**, **P**, mathematical context `Γ` and question `q`, every choice of provider set,
registration order, cache state and execution outcome must leave its mathematical readings
unchanged:

$$
\operatorname{Read}_{M,P}^{L_1,c_1}(\Gamma,q)
=\operatorname{Read}_{M,P}^{L_2,c_2}(\Gamma,q)
=\operatorname{Read}_{M,P}(\Gamma,q).
$$

Removing all providers may make a meaningful operation unavailable for execution; it cannot
remove that operation from the language, change its domain or select a different meaning.
Installing a fast implementation cannot resolve a mathematical ambiguity. A backend failure
cannot prove mathematical invalidity.

Ordinary mathematical expressions specify the mathematics, not a backend or algorithm.
Implementation identity may be inspected through diagnostics; it is not something the user must
insert into a mathematical expression to obtain its meaning.

The fixed-context qualification matters: different legitimate choices returned by a
choice-producing operation can give later bindings different selected data. The law does not
equate those different contexts. It prohibits computational availability or failure from
choosing or rewriting the mathematical reading within the same context.

The formalization of the set of readings is distinct from an algorithm that computes it. This
article does not assert decidability for arbitrary mathematical theories. Within the promised
supported language, incomplete search or exhausted inspection must not be presented as a proof
that there is no valid reading.

The promised resolution-completeness argument for the declared supported calculus remains
required. Its assumptions, admitted constructions and retained selected data must be explicit
and independently justified. A claim of finite reachable enclosure must establish that property;
a merely non-increasing well-founded measure or a quotient that discards required comparison
maps does not discharge it. Replacing an algorithm may replace its obsolete proof, but may not
replace the completeness obligation with a search heuristic or an arbitrary-theory
undecidability caveat.

**Source basis:** [June feasibility reversal][S6]; [original July design][S7]; [September owner
record][S3]; [maintained resolution obligation][S9]; [preserved resolution acceptance][S44].

### C4. Mathematical growth automatically supplies interfaces and compositions

For constructions and operations admitted by the accepted formal interface, every new
construction must acquire the interfaces that follow from its mathematical structure. Every new
generic operation must become available on existing applicable objects.
The new extension supplies its new mathematics or computation; it does not repeat consequences
already owed by the common formal interpretation. This is the required growth mechanism across
mathematical domains and providers.

Mathematical applicability, structural propagation and inheritance must be determined by the
accepted categorical constructions and their exact hypotheses. Per-leaf forwarding, class
ancestry, a method-resolution order, a shortest path or the existence of a backend routine must
not determine that mathematics. Generated classes and ordinary dispatch may execute already
fixed rules without becoming their semantic authority.

For an accepted generic operation `o` and an object `X`,

$$
\operatorname{Applicable}_M(o,X)
\Longrightarrow
o\in\operatorname{PublicInterface}_{M,P}(X),
$$

independently of the quality or availability of the leaf implementation. Adding an applicable
generic operation reaches existing objects through the common formal interface without editing
each old provider. The owner's original examples include orthogonal groups, their subgroups and
stabilizers: an implementation must not leave such an object without its mathematically entailed
group or stabilizer interface.

Availability alone is insufficient. When an operation is the accepted composite of existing
operations, generic composition must apply those operations to the actual selected data,
transport arguments and results through the prescribed comparisons, and preserve the declared
result interface and later uses. Correct realization is conditional on the supplied
implementations fulfilling the independently fixed prerequisite obligations; registration alone
does not establish fulfillment. The generic mechanism must not require new per-object forwarding
or operation-specific cases. A genuinely missing algorithm remains missing execution, not a
missing mathematical method; it remains owed wherever the accepted workload requires it.

This requires an adequate deterministic generic mechanism. It leaves open whether that mechanism
is an interpreter, compiler or ordinary generated/library composition. Replacing it with
hand-written CAS APIs for each domain would lose the requirement.

The prohibition concerns class ancestry or method order deciding mathematics. It does not forbid
generated classes or ordinary library dispatch as execution machinery when the independent
categorical interpretation has already fixed the meaning and required comparisons.

Conservative mathematical growth preserves existing fully selected meanings while adding
applicable operations. It need not preserve the uniqueness of an underspecified surface
expression when genuinely new mathematical routes create an ambiguity; selecting the old route
by implementation priority would conceal that ambiguity.

A consumed view of the accepted mathematical declarations must be a faithful generic projection
of that source. A hand-maintained mirror or whitelist must not become a second authority that
silently omits admitted declarations or requires per-declaration kernel repair. Checking
duplicates alone does not establish completeness. An independently fixed acceptance inventory is
a different object; it must not be confused with an implementation-owned restriction on
mathematical availability.

Within the accepted structural calculus, a new category declares its actual immediate structural
functors, actions, parameters and required comparisons. Their composites are derived, and
operations retain their declared generating owner. A redundant primitive declaration of the same
intended structural functor with no new mathematical content must be rejected with the existing
composite identified. Sharing endpoints or being reachable does not establish sameness;
genuinely different structures and comparisons must remain distinct. Being a functor alone does
not grant inherited application: the accepted structural-admissibility rule and the operation's
actual domain govern it.

**Source basis:** [July inherited-composition correction][S2]; [September owner examples][S3];
[October growth-mechanism chapter][S5]; [October projection requirement][S20]; [immediate
functors, generating ownership and structural admissibility][S40].

### C5. Selected mathematical data cannot be erased

A judgment includes its selected category, parameters, structure, maps, comparisons and
coherence. Sharing a carrier, object label, pair of endpoints or theorem name is insufficient to
identify two judgments. Mathematical equality, isomorphism, presentation equivalence, occurrence
identity and reference identity are different relations.

For an accepted classifier $p:E\to C$, membership of $X\in C$ in the corresponding structured
category means a specified lift of $X$, equivalently a point of its homotopy fiber, with the
prescribed comparison data. A statement that the fiber is inhabited cannot replace the actual
chosen data required by a later use. Simultaneous structures use the homotopy limit of their
complete specified compatibility diagram, under the foundation's size and existence hypotheses.
A classifier need not be a fibration; reindexing a classifier does not by itself supply
transport of each chosen structure along arbitrary morphisms.

For every admissible translation `T` between representations of a judgment, the independent
meaning must be preserved:

$$
\operatorname{Meaning}_{M,P}(T(J))
=\operatorname{Meaning}_{M,P}(J).
$$

The comparison establishing preservation must retain all selected data and the observation asked
for. The equality here is a specification of preservation, not permission to erase distinctions
by choosing a coarser quotient. A proof that two propositions are both true, or a matching
Boolean result, does not identify the mathematical questions they express.

Generalized points retain their stage: a point `S → X` is not silently changed into an element
obtained from an invented terminal object or underlying carrier. Parameter changes use the
accepted variance, reindexing and comparison data. A noninvertible comparison cannot be used as
an isomorphism.

A declaration dependent on earlier parameters is interpreted as a section of the corresponding
mathematical family over its context. The family's base, admitted parameter maps, variance and
required comparison data are part of its meaning. For example, the regular-module assignment
$R\mapsto {}_RR$ is a section of the specified module family over its admitted base of rings;
its codomain varies with $R$. Parameter changes must use the mathematical data supplied for that
family.

An operation that asks for a choice, such as a generating family, returns a point of its
independently specified choice fiber. Different valid choices need not be equal. Their actual
chosen data must be retained for subsequent uses. This is distinct from a question that already
prescribes a particular basis, comparison or lift: an implementation cannot replace that choice
with a convenient one and call the question unchanged.

**Source basis:** [May object/presentation distinction][S1]; [July selected fibers and
cells][S2]; [morphism/matrix correction][S8]; [classifiers and dependent families][S12];
[preserved mathematical constraints][S9].

### C6. Domains and ambiguity are mathematical judgments

An operation is meaningful only on its independently declared domain, with its required
structures and hypotheses established by the accepted mathematics. A surrounding desired
operation does not authorize changing the reading of an argument to make the operation apply. A
runtime exception, absent realization, timeout or malformed reply cannot establish that an input
lies outside that domain.

Distinct unresolved mathematical readings remain distinct. Computational convenience cannot
choose one. A negative semantic judgment requires the grounds prescribed by **M** and **P**; a
failure to obtain such grounds remains a failure to establish the judgment.

An `unknown` computational outcome is an inability to establish the requested result, not a
third mathematical truth value or permission to decide a predicate by convention. Session
assumptions remain explicit hypotheses; introducing a hypothetical mathematical object is not an
assertion of a new library theorem.

Exact and approximate requests have distinct meanings. A required tolerance and the associated
independently specified error relation are part of an approximation request. An implementation
cannot silently substitute a floating approximation for an exact answer, relax the tolerance, or
declare the mathematical request invalid because its algorithm cannot meet that tolerance.
Historical notation for an approximation is not permission to invent a literal mathematical
quotient with no formal meaning.

This preserves the historical distinction between inversion on units and an invented inverse on
a bare monoid, and between a selected structure and a convenient Lean instance on the same
carrier. The general contract consumes independently supplied evidence; it does not authorize an
interpreter to invent subject-mathematical lemmas.

Numeral interpretation must follow the accepted category-specific construction and its
initial-object maps where that construction is defined. A host-language literal or fallback
conversion cannot create a numeral where the accepted mathematics supplies none. Admission to a
subobject or domain requires the prescribed evidence at reading time; a generic variable must
not be implicitly restricted merely because a requested operation needs it in that domain. These
are mathematical domain requirements, not a blanket ban on programming constructs such as Lean's
`partial def` in a parser, elaborator or encoder.

**Source basis:** [July mathematical-role ruling][S2]; [procedural-unknown clarification][S10];
[approximation contract][S11]; [later domain requirements][S9]; [numeral, admission and
mathematical-totality rules][S36].

### C7. Transport, lifts and higher coherence require their actual data

A functor supplies its declared action; it does not by itself supply a reverse lift,
preservation of every limit, a selected representative or a chosen coherent extension. Every
requested construction uses the accepted hypotheses and chosen data for that construction.

A result advertised as a universal construction must supply the required apex, defining maps and
factorization operations in their specified relationship. If a later computation needs a chosen
cell, comparison or lift, a mere existence proposition is insufficient for that use. No blanket
strictification, quotient, truncation or “all cycles are identity” assumption may replace the
required higher information.

The intended foundation retains infinity categories, functors, general natural transformations
and higher modifications through the appropriate mapping objects. The independent development
must supply a suitable model or model-independent interface of the intended
$(\infty,2)$-categorical universe, with explicit size and existence hypotheses and morphism
conventions for structured categories. Where structure is specified by extensions of
operation-built diagrams, its full boundaries, selected fillers and their matching compatibility
belong to the meaning. Existence of the individual fillers does not establish their required
compatibility.

The intended higher mathematical universe cannot be defined by the limits of an
ordinary-category or strict two-dimensional execution model. Such a model is a scoped
interpretation of the intended mathematics, with the required adequacy justification, not a
license to remove higher objects, natural transformations, modifications or coherence from the
public specification.

For a reduction `r`, the independent authority must provide the appropriate adequacy statement
for every observation, action, composition, substitution and later continuation that the public
contract promises after the reduction, including the uses required by C8. A reduction justified
only for one observation remains confined to that use; it does not establish preservation of a
richer interface. The implementation cannot infer adequacy from its need for a simpler
representation. Symbolic or lazy retention is allowed when it preserves the entire required
interface and selected information.

**Source basis:** [July higher-foundation correction][S2]; [first FOUNDATIONS][S12]; [later
higher-scope correction][S13]; [October 29 reduction and subsequent-use requirements][S29].

### C8. Constructed objects and maps remain usable through subsequent mathematics

Execution is directed at the already fixed complete judgment. The actual returned computational
data and its maps, comparisons, parameters and dependencies remain associated through every
required subsequent use. These are candidate computational views of the requested mathematics;
associating them correctly does not prove that a wrong provider supplied the requested
mathematical construction. Correct realization of the composition has the conditional meaning
stated above, while the delivered system still owes the actual required successful computations.

A later use cannot substitute a separately reconstructed object merely because its formal
expression or serialized label matches. An alternative evaluation or recomputation strategy is
permissible only when it preserves the selected data, required identities and lifetime behavior,
and dependent subsequent uses under the independently specified relation. This is a preservation
requirement, not a universal prohibition on computing a value again.

For every permitted continuation `k`, the obligation is for the complete computation `k(J)`,
using the actual result of `J`, with the selected transport where its presentation changes.
Correctness of an isolated scalar observation does not discharge this requirement.

Where **M** independently fixes a representation interpretation, implementation correctness
requires the corresponding action and observation equations for the whole declared interface.
The representation interpretation is not a leaf-defined escape hatch. A valid wire shape or
endpoint label proves neither those equations nor the universal property.

This article does not require foreign handles, one process per leaf, a particular intermediate
language or runtime decoding. It applies equally to native values, CAS objects, generated
programs and independently justified persistent artifacts.

Complete interfaces may be lazy, callable or symbolic. They must support the admitted infinite
or nonenumerable objects and index families where those are part of the required specification;
finite carrier, finite rank, finite support, finite presentation and finite diagram are distinct
hypotheses and cannot be silently interchanged. Retaining a diagram and its public actions does
not mean enumerating every element or cell. An approximation or finite replacement is a
different mathematical construction unless the required comparison and adequacy are
independently supplied.

**Source basis:** [October complete-interface chapter, §§6–8][S5]; [mathematical generality and
infinite inputs][S27]; [public-constructor and later-use requirement][S14]; [preserved result
boundary][S9].

### C9. Independent acceptance preserves the complete question

For every admitted assertion identity `a`, acceptance fixes its complete selected question
`Q_a`, expected mathematical relation and required execution status independently of candidate
behavior. An implementation-only revision must preserve these:

$$
(Q_a,E_a,\operatorname{Required}_a)_{\text{after}}
=(Q_a,E_a,\operatorname{Required}_a)_{\text{before}}.
$$

This does not freeze serialization, syntax spelling or an erroneous old reader record. Their
correction must be justified independently against the unchanged mathematical question. A hash
can reveal a change; it cannot establish mathematical equivalence or confer authority to admit
the new record.

Expected answers must not be obtained from the implementation under assessment. Acceptance
authors' actual inputs must preserve their required independence. Assigning another role label
to an already exposed agent does not restore that independence.

**Source basis:** [September independent-assessment requirement][S3]; [October
question-preservation chapter, §9][S5]; [preserved independent acceptance][S9].

### C10. Evidence has distinct obligations and cannot certify itself

Formal mathematical validity, correct interpretation, correct lowering, structural interface
admission, actual dispatch, and mathematical correctness of a returned answer are different
claims. A demonstration of one discharges another only through an independently justified
implication with its hypotheses met.

In particular:

$$
\operatorname{WellTyped}(J)\not\Rightarrow\operatorname{Executed}(J),
\qquad
\operatorname{WellFormedReply}(r)\not\Rightarrow\operatorname{CorrectAnswer}_{M,J}(r).
$$

The first non-implication is witnessed by a well-typed question with no implementation. The
second is witnessed by a well-shaped reply carrying the wrong scalar value. Passing a finite
independent suite establishes the tested outcomes; it is not a proof of every possible
computation. That limitation does not reduce the required suite or permit a missing positive
result to count as success.

A candidate cannot install its own evaluator or accepted references as authority and then cite
their approval. Separate source authorship, permitted inputs and authoritative advancement
remain explicit. Packaging both components into one build is not by itself proof that the
required independence survives.

Evidence binds the actual compatible mathematical, language, contract, implementation and
assessment revisions used. Successes from incompatible revision combinations cannot be assembled
into one acceptance claim. An unchanged declaration name or fingerprint does not establish that
its definition or intended question is unchanged.

**Source basis:** [September owner evidence model][S3]; [October evidence distinctions,
§§2,4–5,9,13][S5]; [Lean reference on proof validity and statement meaning][S15].

### C11. The delivered language performs complete mathematical research workflows

The delivered system must support the complete mathematical activities required by its accepted
public-language and computational scope. Definitions, calculations, assertions, structured
results and subsequent uses must work together in the research environment. Success of a parser,
a registry, a single engine call or a formal theorem alone cannot replace those activities.

Let **W** be the independently fixed required workload, including the specified observations,
later uses, extension cases and budgets. Completion requires the original obligations for every
member:

$$
\operatorname{Complete}(K,L;M,P,A)
\Longrightarrow
\forall w\in W,\ \operatorname{RequiredOutcome}(w;K,L,M,P,A).
$$

The candidate does not choose **W** from the operations it happens to support. Missing,
unreadable, unsupported, infrastructure-failed and not-reached cases remain in the denominator.
A required successful computation is not discharged by a correct rejection.

A soundness-only condition would be inadequate: an implementation that never returns a result
satisfies “every result it returns is correct” vacuously. The constitution therefore includes
actual required positive computations, complete constructions and later uses, as well as
semantic safety and protected negative cases.

A replacement must preserve the full already required product: mathematical language and
discoverability, generic composition and extension, actual objects and maps, mixed-provider
interoperability where required, notebook/research use and the independently fixed computational
scope. A successful miniature example cannot redefine that scope.

**Source basis:** [original mathematical SPEC][S16]; [September convergence requirement][S17];
[October full-functioning-system obligation][S5]; [current fixed acceptance scope][S18].

### C12. Independent extensions compose through the common mathematical interface

Independently authored mathematical and computational extensions must interoperate through the
accepted formal mathematics and released public contract. A construction supplied by a new
producer must be usable by an existing consumer through that contract, including its required
maps, selected structures and subsequent operations. A new applicable generic operation must
reach existing constructions without private knowledge of their implementations.

The invariant is interoperability without private knowledge and generic growth without
per-domain repair. It is not a requirement that implementations never share private code or a
CAS session. Conversely, co-location does not excuse a producer that must modify every consumer
or disclose its private representation to make the construction usable.

The structural or compositional justification must establish the claimed generic property;
successful specimens alone do not establish it. The prescribed independent extension trials,
frozen baselines and consequences of accommodation edits remain mandatory under
[Governance](#independent-extension-evidence-c12).

**Source basis:** [September growth requirement][S3]; [constructor-use clarification][S14];
[independence/additive-baseline requirement][S18]; [structural justification and independent
selection][S17]; [maintained extension-trial procedure][S38].

### C13. Failure and lifecycle behavior cannot alter mathematics

Semantic invalidity, mathematical ambiguity, missing implementation, engine failure, malformed
data, internal interpreter failure and a wrong answer remain different outcomes. No retry,
fallback, restart or cache hit may change the selected question to conceal a failure.

Every object or computation exposed for later use must obey its declared identity and lifetime.
Failure must not publish an incomplete successful construction, resurrect an invalid reference
or silently substitute a fresh construction for the selected one. Implementations choose how to
meet these requirements. The current ticket, snapshot and session machinery is not itself
constitutional.

**Source basis:** [original notebook/pipeline contract][S7]; [actual-question and
result-preservation requirements][S9]; [later declared lifecycle contract][S19].

### C15. Mathematical notation, discovery and inspection serve research use

Ordinary input and output expose the requested mathematics, with the promised mathematical
rendering and a usable text form. A user must not need private backend vocabulary or source-code
inspection to understand the result. The selected mathematical operation, assumptions, chosen
presentations, provenance and computational limitations must be available through the prescribed
inspection interface.

Mathematical documentation must state the operation at the widest generality justified by its
authoritative definition and hypotheses. A particular receiver or a stronger-hypothesis
algorithm cannot be presented as its general mathematical meaning. Computational inspection must
identify the actual invoked routine and verified primary documentation where applicable; when
external documentation is unavailable, it must expose the relevant adapter or implementation
source as the fallback. A convention or presentation choice that qualifies an answer must appear
with the affected result in the promised mathematical notation; burying it in a separate
diagnostic is insufficient. Such disclosure does not give the provider authority to choose truth
values or redefine the question.

Formatting, tracing and inspection must preserve the selected mathematical question and respect
the declared execution/lifecycle semantics; they cannot change its meaning or fabricate an
execution outcome. A clearer diagnostic remains evidence of a gap when a positive computation is
required. A synthetic demonstration or stale stored notebook output cannot establish a claim of
actual researcher use or executed delivery.

This preserves the user-facing requirement without declaring a particular MIME bundle, notebook
magic, Python client, logging option or renderer architecture eternal. Specific surface choices,
including roots and multiplicities, exact approximation semantics, binders and differentials,
remain part of the independently fixed mathematical language contract and its authorized
revisions.

That public-language contract must remain complete and discoverable in its authoritative
specification. Referring to **P** does not migrate every rule of the original SPEC into this
document or license silently dropping one. Definitions and propositions, comprehensions, typed
functions, relative differentials, primitives and their ambiguity, subobjects and ellipses must
retain their applicable independently fixed semantics through any specification migration.
Historical syntax may be corrected through the authorized product contract; implementation
convenience is not such a correction.

**Source basis:** [mathematical rendering requirement][S23]; [inspectable structural-map
interface][S24]; [reported owner interface ruling][S25]; [actual research-use finding][S26];
[early documentation and choice-disclosure contract][S39]; [original mathematical language
specification][S16].

## Authority, scope and formal contract

### Authority and scope

This file is the canonical, version-controlled constitution of lean-cas-dsl. It states the
requirements that every implementation, replacement architecture, contribution and acceptance
claim must satisfy. Its mandatory rules are expressed by “must”, “must not”, and the quantified
obligations below.

The owner explicitly requested a permanent repository constitution on 2026-11-04. This is a
specific exception to the earlier policy that repository documents contain only issue pointers.
The complete constitution must remain in the repository. It must not be replaced by a pointer,
omitted during a merge, or removed as part of a documentation migration. Its preservation does
not depend on the architecture, programming language, process layout or planning tool.

The constitution governs engineering choices; it does not replace independent mathematical
authority. All mathematical definitions, categorical structures, laws and abstract computational
obligations must be independently formalized and auditable. The currently designated formal
mathematical development is **lean-categories**, as assigned in the owner's mathematical authority
and API-ownership requirements. A change of physical repository layout does not transfer that
authority to the CAS or a leaf. A downstream implementation or this document's notation cannot
supply missing mathematics. [S3] [S4]

Implementation plans, work orders, diagnostics, completion evidence and architectural proposals
remain in their owning GitHub issues. Those records specialize the requirements to an authorized
task; neither an agent-authored plan nor an existing implementation can amend this constitution.
Applicable owner instructions retain their authority. A change to a constitutional requirement
must be recorded explicitly under the amendment rules below.

An explicit owner instruction governs immediately; recording or committing it makes it durable
rather than creating its authority. An assistant proposal is not an owner instruction, and a
question is not automatically a new requirement. Existing authorization must be exercised
without requesting it again. A claimed need for an owner decision must identify the specific
undecided choice outside that authorization. [S35]

The constitution specifies conformance obligations. It is not a declaration that the existing
implementation conforms, nor a substitute for the independent formal definitions and proofs
those obligations require.

### Obligation classes

The constitution contains three different kinds of obligation, whose quantifiers must remain
distinct:

1. **Semantic and authority safety:** for every provider behavior at the permitted
   computational interface, including well-formed wrong answers, the mathematical
   language, selected question and independent assessment authority must remain
   protected. This guarantee cannot assume that the provider is correct.
2. **Correct computational composition:** when supplied implementations satisfy
   the independently fixed prerequisite obligations, the generic mechanism must
   preserve those obligations through the specified composition and later uses.
   Composition alone does not establish correctness of a primitive answer.
3. **Actual delivery:** the designated delivered implementation/provider
   combination must perform the complete independently required positive workload
   and extension behavior. A conditional theorem about hypothetical correct
   providers cannot substitute for those actual outcomes.

Safety requirements govern every permitted operation. Conditional preservation requirements
govern the supported constructions and their composition. Delivery requirements govern the
claimed completed product; they are not an invented prerequisite requiring the product to exist
before authorized construction can proceed. Each obligation retains its full scope.

Implementation-only changes must preserve these requirements across revisions. An independently
justified mathematical correction changes the accepted specification explicitly; an
implementation failure cannot make that correction for it. “Permanent” does not make an
erroneous historical mathematical definition immutable.

The constitution fixes mathematical meaning, authority, required user capabilities and
completion. A plan chooses representations, algorithms, languages, libraries, processes and
deployment. Current owner-selected engineering policies remain binding within their scope unless
explicitly changed; they are listed separately below rather than disguised as mathematical
necessities.

### Formal contract and notation

Let **M** denote an independently accepted, versioned categorical formalization, **P** the
independently fixed public mathematical language contract, and **A** the independently authored
accepted question/expectation corpus. Let **K** be a candidate interpreter/compiler/runtime and
**L** its computational providers. These are roles, not a prescribed number of repositories or
processes.

Write `Read(M,P,Γ,q)` for the mathematical readings of question `q` in the fixed mathematical
context `Γ`. A reading is a complete selected judgment: context, typed operands, categories and
parameters, selected structures, operation or composite, hypotheses, comparison/coherence data,
result family and the requested relation or observation. “Complete” means all data on which that
judgment depends, not a fixed record layout. Write `Req(M,J)` for the independently fixed
computational obligation associated with judgment `J`; its content is supplied by the
authoritative definitions and language contract, never by the provider under assessment.
`Run(K,L,J)` is actual execution and is not identified with a proof of `Req(M,J)`.

The statements below are quantified specification obligations. Their formalization must
instantiate the symbols using independently accepted definitions and establish the stated
property of the actual interpretation or computational mechanism. Introducing an unconstrained
`Correct` or `Realizes` parameter, or assuming the desired property as an axiom, does not
discharge an obligation. The mathematical authority must fix the statement before the
implementation is assessed. The formulas in this document are not themselves machine-checked
proofs about the present code.

## Implementation freedom and existing policies

The articles do not select an AST, interpreter rather than compiler, free-monad encoding, native
rather than foreign execution, number of processes, wire format, cache or transaction
implementation, physical repository layout, CAS distribution, or code-size target. Every
existing implementation component and agent-selected plan remains a candidate for replacement. A
replacement must satisfy the complete obligations; changing the means does not change the task.

The following existing policies are distinct from the cross-architecture articles. They remain
applicable within their recorded scope. A proposal changing one must identify the change
explicitly and retain the constitutional requirements; calling it an implementation detail does
not silently repeal it.

| Current policy | Requirement and scope | Source |
| --- | --- | --- |
| Mathematical and leaf-code separation | New mathematics is formalized independently upstream. A computational leaf does not ship new Lean code. A native kernel does not by itself change that leaf rule; requiring providers to ship Lean modules does. | Original owner message 6 [S3] |
| Established computational implementations | The existing leaf-writing policy requires glue over established engines and existing research implementations, naming the actual engine and routine, without hand-rolling algorithms as part of that leaf contribution. Reuse supplies computation, not mathematical authority or proof of answers. This does not create a ban on every separately authorized research assignment, but neither general implementation freedom nor the constitution supplies authorization for new algorithm work. | Original owner message 6 [S3]; maintained leaf-writing policy [S36] |
| Computational evidence | Ordinary opaque results are assessed against independent mathematical expectations. Leaf-supplied claims, certificates, checkers, proofs, denotations, identifications and self-tests must not serve as semantic authority or correctness evidence; the independently authored permanent suite supplies correctness evidence about computed answers. Mandatory proof-producing replies are not current admission requirements. Changing this evidence boundary, including adopting a certificate-primary model, requires an explicit policy amendment; a leaf still cannot define its own correctness criterion. | Owner evidence distinction [S3]; maintained evidence policy [S9] |
| Independent harness | The independent harness owns acceptance execution. Leaf packages do not import or run that suite; their private tests do not become acceptance evidence. Particular executable names and transport formats remain implementation choices under the assigned work order. | Maintained leaf and acceptance boundary [S36] |
| Delivery inputs | Own-organization delivery consumes the required latest-main dependencies and records the actual compatible revisions. Fixed diagnostic revision combinations remain valid for controlled comparisons; they do not become independent delivery targets. | Maintained delivery policy [S9] |
| Authorized computational scope | The complete currently assigned workload, including its connected computations, extension trials, observations and budgets, remains due. The V1 inventory and broader full-B0 obligation are distinct; neither historical counts nor proposed future algorithms silently change the assigned denominator. | V1 acceptance [S18]; full B0 [S30] |
| B0 authority during construction | The October 10 ruling makes role separation a conduct requirement: B0 acceptance does not wait on removing credentials capable of broader access. This removes that technical gate, not the restrictions on crossing roles or the requirement for independent acceptance. | October 10 ruling [S21]; maintained separation [S9] |
| Realization selection | At the selected operation/input form, zero eligible registrations yields its declared gap, one yields the selected call, and multiple yield implementation ambiguity. Cheapest, first, priority, installed-order and retry-until-success selection are prohibited. This is separate from mathematical ambiguity. An existing occurrence retains its chosen registration. The prescribed explicit-manifest comparison/replacement experiments and admitted fused realization remain available under their recorded rules. | Selection contract, revised November 3 [S41] |
| Retry and migration | A failed or consumed occurrence must not be automatically retried, replayed or migrated. An explicit user rerun is a fresh invocation/routing act; returning an existing committed binding or joining the same pending execution is not a new dispatch. A future resume/migration design requires an actual authorized policy change. | July adoption [S42]; November lifecycle contract [S43] |
| Default mathematical display | Results render mathematically and automatically, using LaTeX when available and a usable text fallback, without an extra display command. Emit once per event; do not stack a second plaintext display under the rendered result. Backend, routing and timing diagnostics are opt-in. Mathematical qualifications required by C15 remain with the result. MIME encoding, renderer architecture and later logging milestones retain their assigned implementation scope. | Rendering [S23]; one-emission ruling [S25]; opt-in diagnostics [S45] |
| Production-leaf sequencing | The recorded kernel-MVP readiness and independently selected frozen extension trials precede substantial production-leaf work in that development phase. Earlier diagnostic specimens remain limited to their assigned public interface checks; full required acceptance follows. This phase-specific order remains in its owning work plan, rather than becoming an all-time prerequisite for authorized construction or being silently repealed by omission. | Pre-migration phase policy [S36]; preserved exit trials [S44] |

Implementation-specific mechanisms mentioned in these sources do not acquire constitutional
status by being recorded alongside genuine requirements. Unresolved computational or
formalization work remains an obligation of its proper authority; its absence cannot authorize
changing the question or the completion standard.

## Governance

Contributors must read this constitution together with the applicable owning issue before
selecting an implementation. A plan or proposed replacement must be assessed against all
applicable articles, including actual later use and complete delivery, rather than only the
example it makes convenient. Existing review and acceptance evidence must establish the specific
claims made. This does not create a new approval board, checklist, controller or acceptance
ceremony.

A conflict with an implementation, roadmap, issue diagnosis or old source snapshot must be
resolved by correcting the subordinate artifact or by an explicitly authorized requirement
amendment. An agent's interpretation, CI success, registry entry or chronological recency cannot
supply that authorization. Authorship and permitted inputs remain separated as required by C1,
C9 and C10.

An amendment must:

1. Identify the exact article or policy being changed and the requirement-changing
   authority already granted for that change. Mathematical changes require
   independent mathematical justification; implementation convenience alone is
   insufficient.
2. State the old obligation, the new obligation and the reason, retaining the
   relevant primary-source or owner-decision reference. A correction of an
   erroneous encoding must preserve the intended mathematical question.
3. Update this canonical file, its version and amendment date in the same change.
   Keep stable article identifiers where their obligations continue; record
   replacements or removals explicitly rather than silently renumbering them.
4. Reconcile affected issue specifications and repository pointers so a stale
   duplicate does not become a competing constitution. Git history and the
   historical issue record retain the superseded text and its provenance.

Version changes are **major** for incompatible changes to an obligation or authority boundary,
**minor** for compatible additions or substantive elaboration, and **patch** for editorial
corrections that leave obligations unchanged. Editorial maintenance does not invent a new
approval requirement. Existing authorization remains effective.

Merges and migrations must retain the complete current constitution. Conflict resolution must
not silently select an older version or discard an article. Relocating or removing the canonical
file requires an explicit owner decision; routine document cleanup or an instruction to keep
ordinary repo documents as issue pointers does not authorize it.

The following authorship, extension-evidence and contributor obligations retain their normative
force and stable article identifiers. Their placement here distinguishes how contributors must
protect and deliver the product from the intrinsic properties of that product. Relocation does
not repeal, narrow or make optional any of these obligations.

### Independent authorship and permitted inputs (C1, C9, C10)

Independence concerns actual authorship and inputs. Mathematical work is assigned from
mathematical requirements and sources; acceptance is authored from accepted mathematics and the
public language; implementations work against the released computational contract. A downstream
diagnostic, generated goal or desired test outcome cannot be repackaged as the independent
mathematical assignment. Moving an implementation-shaped definition to another repository does
not make it independent.

Authors are separated by layer: kernel/contract construction, mathematical formalization,
acceptance assertions and computational leaves have separate authors. Each contributor must
remain within the assigned role and permitted inputs. A kernel or leaf worker may record a
missing accepted mathematical dependency against the existing obligation, but must not author,
commission or prescribe its upstream repair. A separate agent or repository cannot be used to
launder that downstream assignment into independent authority.

Formalization authors receive independently assigned mathematical requirements, sources and
upstream review; acceptance authors receive accepted mathematics, the approved public language
and independent mathematical sources. Leaf authors receive the released public contract,
accepted catalogue and backend resources, excluding kernel internals, the acceptance corpus and
expected answers. An exposed session cannot acquire independence by being told to forget. A
launcher may continue an already authorized independent assignment, but must not choose or
rewrite that assignment from downstream needs. These are authorship and input restrictions, not
a requirement to remove every credential capable of broader access.

These requirements implement the intrinsic separation of mathematical meaning, independent
assessment and computational realization. They are contribution obligations, not an additional
mathematical ontology or an execution architecture.

**Source basis:** [pre-migration author and repository boundaries][S36];
[maintained permitted-input rules][S9].

### Independent extension evidence (C12)

For the prescribed independent-extension trial, freeze the common baseline and existing
consumer. An independently supplied extension must work through the released public contract and
accepted mathematics without accommodation edits to the kernel, contract, old consumer or
expected answers. Independently authorized additive mathematics is distinguished from changing
the baseline to fit the implementation.

These trials exercise the interoperability and generic-growth requirements stated in C12;
the structural or compositional justification below remains required.

After the common baseline is fixed, independent contributors must choose the concrete extensions
themselves from the required scope, without orchestrator-supplied definitions or expected
outputs. Trials must exercise the distinct extension mechanisms claimed by the architecture. The
required structural or compositional argument must establish the generic property; a finite set
of successful specimens alone does not establish it.

An accommodation edit fails the frozen-baseline trial. Repairing the deficiency requires a new
candidate, a newly fixed baseline and repetition of the affected independent trials; it cannot
retroactively convert the old trial into success. Historical phase gates and concrete trial
inventories remain in their owning work orders, with their actual applicability and full
obligations preserved.

**Source basis:** [September growth requirement][S3]; [constructor-use clarification][S14];
[independence/additive-baseline requirement][S18]; [structural justification and independent
selection][S17]; [maintained extension-trial procedure][S38].

### C14. Construction remains replaceable; correctness remains fixed

Authorized construction may replace any implementation component, including a controller or
reviewer mechanism. A rule intended for an independently accepted finished system is not
automatically a prerequisite for constructing that system. The controller cannot make itself
irreplaceable or accept its own replacement.

Implementation freedom does not include changing the mathematical obligation, manufacturing
independent approval, narrowing completion or turning a downstream failure into an
implementation-shaped upstream theorem. An unavailable capability blocks the operation that
needs it; it does not invent a new mathematical requirement or invalidate already authorized
independent work.

**Source basis:** [October 1 archived review/construction directive][S20]; [October
means/outcomes distinction][S5]; [October 10 authority ruling][S21]; [later construction
supersession][S22]. The October 1 document presents owner text with preserved elisions and
survives on the archived `custodian/controller-b0` lineage, not as a main ancestor.

### C16. Preserve the assigned task through delegation, supporting work and completion

Research, decomposition, delegation, implementation, testing and reporting must preserve the
assigned outcome, domain, semantic distinctions, constraints and standard of evidence. A
contributor may revise the means and order of work, but must not replace the task with an easier
specimen, local proxy, supporting artifact or weaker acceptance condition. Preserving the task
also forbids inflating it with stronger capabilities or prerequisites that neither the
requirement nor a demonstrated dependency calls for.

A subtask is justified by its contribution to the parent obligation. The parent remains
responsible for composition, integration and the original required result. Successful
components, source checkpoints, accurate gap reports and handoffs do not discharge that
responsibility or require a fresh instruction to continue already authorized work. Delegation
must preserve the assigned authorship and input boundaries; it cannot transfer prohibited work
to another agent or disguise a downstream finding as an independent mathematical or acceptance
assignment.

A narrower subtask warrants only its own success claim. Choose subordinate work for the
necessary next use in the original workflow, and perform that next step when it is authorized
and feasible. Completing a supporting artifact and merely reporting that its consumer remains
unfinished does not discharge this duty.

Supporting research, tooling, infrastructure, documentation and validation must resolve an
actual dependency of the substantive task. Once the capability is sufficient for that
dependency, the contributor must use it and resume the substantive work. Finding or accurately
describing the remaining implementation is not completion of an implementation assignment. A
research assignment is judged by its own requested research outcome; it must not be silently
expanded into implementation either.

Work selection must follow actual input dependencies and the authorized priorities. A missing
input or capability blocks the operation that needs it; the contributor must identify that
operation and continue authorized work that does not depend on it. A review outage, publication
failure or absent optional infrastructure must not become a global stop or a reason to request
permission already granted. Existing role boundaries and genuinely required independent
acceptance remain binding.

When task substitution has occurred, the required correction is to restore the omitted
obligation, perform the missing integration or other substantive work, and complete the assigned
outcome. Another plan, checklist, disclaimer or description of partial progress is not that
correction.

**Source basis:** [November 2 contribution policies, opening and §§1,7][S33]; [maintained
actual-dependency and completion policies][S9].

### C17. Research required responsibilities before choosing implementation boundaries

Research and architectural comparison must start from the capabilities required by the user's
complete workflow. Existing modules, helper functions, representations and accumulated
responsibilities are candidates for replacement, not premises that every alternative must
preserve. A component is relevant when it solves the required responsibility; it need not
reproduce the incumbent's entire organization.

Before assigning a responsibility to bespoke code, contributors must inspect relevant
established capabilities and reference implementations and identify the concrete remaining gap.
The comparison must examine the complete required sequence of construction and subsequent use,
including the needed parameters, choices, dependencies and consumers. The costs of adaptation,
repeated reconstruction, downstream repair and verification belong in that comparison; the
smallest immediate diff is not a sufficient criterion.

This applies to every mathematical definition and proof obligation, including obligations
discovered inside a proof, within the independently assigned mathematical role. Search the
relevant formalization literature and corpus broadly under several appropriate mathematical and
identifier formulations; inspect source-appropriate libraries and reference implementations for
runtime representations, interpreters, codecs, caches and engine interfaces. Import, port or
adapt suitable existing work, and author only justified glue and unsupported residue. The
existing work record must identify the inspected source and revision, the responsibility it
supplies, the reuse or rejection decision and its compatibility and boundary reasons. Record the
searches, inspected hits and reasons each does or does not discharge the obligation with the
work, in its commit and owning issue. Every commit adding a definition or nontrivial proof under
this programme must cite a search record containing the queries and results needed for a
reviewer to rerun the searches and assess the reuse or residue claim. An unavailable index or
unsuccessful query is not evidence that no implementation exists. A software precedent supplies
neither mathematical authority nor acceptance.

Uncertainties that could invalidate the architecture must be resolved before substantial work is
invested in components that depend on them. Inspect the relevant source and run a meaningful
experiment when needed to resolve such uncertainty. Research must produce the evidence needed
for a decision and lead into the authorized substantive work. It does not require an exhaustive
survey, a predetermined rewrite, or a component that already implements the entire application.

Contributor assignments must identify the required outcome, constraints, permitted inputs and
acceptance obligation. An agent-selected procedure or proposed algorithm cannot acquire
requirement status merely by appearing in a plan or worker prompt. Reserved owner choices and
actual source-backed product contracts remain binding; delegated engineering choices remain the
implementer's responsibility. Internal architecture, representations and module boundaries are
delegated engineering decisions. A proposed change to what the user writes, sees or can compute
must identify the affected user requirement and the reserved decision; difficulty choosing an
internal mechanism is not such a decision. Material instruction corrections must reach all
affected active contributors without transmitting implementation details to authors whose
independence excludes those inputs.

**Source basis:** [November 2 contribution policies, §2 and requirement provenance][S33];
[general search-before-authoring requirement][S34]; [maintained implementation authority][S35].

### C18. Repair the responsible boundary and revise contradicted design assumptions

Before adding inference, retries, searches, duplicated state or consumer repairs, contributors
must determine whether the required information was already established earlier. If a
project-owned boundary lost information needed by a required consumer, the repair must restore
its preservation through that boundary and the affected consumers. Reconstructing a convenient
substitute at the point of failure does not establish preservation of the selected construction
or actual result.

A demonstrated shared failure mechanism must be corrected across its affected instances within
the required scope. One passing specimen or one reproduced failure does not bound a generic
obligation. Conversely, this requirement does not demand unrelated audits, preservation of
irrelevant information or support for unpromised consumers. Information may be abstracted away
when the promised behavior does not depend on it or it remains available through an adequate
explicit reference.

Architectures, plans, estimates and agent explanations are revisable hypotheses. Evidence
contradicting a premise required by the chosen design must reopen that premise and its dependent
decisions before more machinery is built around it. Validation must be able to establish that
the representation or architecture is unsuitable. A decision record is not proof of its
premises, and an evaluation of adequacy must not be converted into a standing commitment to
repair every failure inside the same design.

The response must match the evidence: repair a local defect locally; reconsider a representation
whose required consumers repeatedly lack the information it was supposed to retain. If a
responsibility is removed or transferred, the implementation must actually perform that change
rather than rename, centralize or retain the same responsibility behind a new interface.

**Source basis:** [November 2 contribution policies, §§3–4][S33]; [October 1 requirement to
correct affected instances][S20].

### C19. Verify consequential claims and exercise the property being claimed

Before an inherited statement determines scope, architecture, ownership, acceptance or omitted
work, contributors must inspect its primary evidence at the relevant source state using the
inputs permitted to their role. Agent reports, issue prose, reviews and handoffs remain claims.
Cross-references provide access to evidence; they do not create independent corroboration.
Previously verified evidence may be reused when its source state and assumptions still apply.

Falsifying a consequential claim requires reconsidering the decisions that depended on it, not
merely correcting its wording. This applies to assertions about behavior and completion as well
as dependency capabilities, API shapes, namespace ownership and mathematical conventions.
Requirement provenance must distinguish actual owner instructions from agent proposals; an
internal mechanism is not user-mandated merely because it is unusual, documented or already
implemented.

Validation must establish the property actually claimed. A test must not manually supply the
selected state, ownership, execution or lifecycle whose establishment it claims to verify.
Legitimate unrelated setup is allowed; providing the very missing capability in a fixture does
not test its implementation. When transferring a responsibility, establish both that the
receiving component performs it and that the superseded component no longer performs it for that
use. A successful helper call or a few matching outputs does not establish that transfer.

Ask whether the evidence could remain unchanged if the claimed capability were absent. For an
architectural claim, inspect the relevant source and responsibility path: final output alone
cannot establish removal of a prohibited path or transfer of the work it performed.

Source inspection, responsibility tracing and behavior tests must address the actual claim and
risk. These engineering checks do not replace independent mathematical acceptance. Validation
must be relevant to the change and culminate in the required integrated result; it must not
become an unrelated build, repeated experiment or self-created gate. Once decision-relevant
uncertainty is sufficiently resolved, use the evidence to perform the next authorized
substantive action.

Record work and requirement decisions in their owning issues and reconcile affected
documentation without creating competing work orders. Faithful documentation-only corrections
require relevant text, reference and consistency checks; they do not create a dedicated approval
transaction, full mathematics build or unrelated code task. Publishing that record is not a
prerequisite for already authorized independent implementation.

**Source basis:** [November 2 contribution policies, §§5–6][S33]; [pre-migration construction
and relevant-validation instructions][S36].

### C20. Review must be independent, informed, actionable and correctable

Independent review must receive the governing requirements, the complete relevant change and
enough unchanged context to assess the affected behavior. Independence does not justify
withholding a helper, explanation or source needed to understand the change. Candidate
explanations are claims to verify against independently obtained requirements and evidence; they
are neither authority nor automatically inadmissible.

The review must identify coherent base and candidate revisions and derive the relevant changes
from those same identities. It must not combine a file list from one comparison with patches
from another. The reviewer must be able to inspect relevant unchanged source. These inputs
remain subject to the assigned role: implementation review cannot become a route for sending
candidate-shaped questions or expected answers to independent mathematical or acceptance
authors.

A finding must distinguish a demonstrated implementation defect, missing evidence, failure of
the review operation, an erroneous earlier finding, and a proposed change to a reserved
requirement. Each finding must identify its governing obligation and supporting source, argument
or counterexample. Missing evidence can prevent acceptance until supplied, but does not
establish that the implementation is wrong. A failed or context-deficient review operation
supplies no substantive verdict.

Substantive implementation revision, new evidence, restored context or a demonstrated review
error permits reconsideration in the existing review discussion. Correcting a finding must not
require cosmetic code changes, repeated owner intervention or an additional appeals service.
Repeating an unchanged submission solely to obtain a different model answer is prohibited. A
signature identifies an author or decision; it does not make the judgment infallible.

Controls must prevent identified forbidden transitions while permitting required legitimate work
under the governing obligations. A control that blocks required work is defective even if it
also rejects prohibited actions. Allowing a previously rejected legitimate case does not itself
weaken a requirement. Review must examine the actual action, authority and data path; a
hypothetical concern without such a path cannot invent a new prerequisite. Authorized
replacement of a control must still be complete and must not confer self-approval.

An authorized objective delegates ordinary engineering decisions within its boundaries. Review
uncertainty, protected filenames, changed checks, implementation difficulty or the number of
affected files does not itself require a fresh owner decision. A reviewer must not transfer
delegated technical choices back to the owner or require ceremonial splitting of a coherent
integration. Escalation must identify the specific requirement or authority boundary that would
change or the actual unavailable operation. A review-only assignment remains review-only;
implementation authorization is not canceled merely by performing analysis or review, loading a
skill or revising an agent-authored plan.

**Source basis:** [October 1 recorded review and delegation directive][S20]; [maintained
construction and review policies][S9]; [coherent-review and assignment requirements on
main][S37]; [November 2 authorization policy][S33].

### Adoption record

| Version | Date | Change |
| --- | --- | --- |
| 1.0.0 | 2026-11-04 | Initial permanent repository constitution, formulated from the recovered requirements and committed at the owner's explicit request. Establishes C1–C15, obligation classes, scoped policies and amendment rules. No replacement execution architecture is selected by this adoption. |
| 1.1.0 | 2026-11-04 | Restore contribution and early-planning obligations omitted or only partially represented in 1.0.0: C16–C20 cover complete-task responsibility, source-appropriate research and reuse, correction of design assumptions, primary evidence, and informed revisable review. Clarify author separation, faithful mathematical projection, numeral/domain rules, independent extension trials, mathematical documentation and preservation of the complete public-language contract. These are source-backed restorations under the existing constitution-formulation assignment, not a new computational scope or selected architecture. |
| 1.1.1 | 2026-11-05 | Editorial conformance to the released [Spec Kit constitution workflow](https://github.com/github/spec-kit/blob/34a0d388eac671d656eb05b125ad3ed6056168ed/templates/commands/constitution.md): use the resolved scaffold, group C1–C20 under Core Principles, retain authority and policy sections, present Governance and the prescribed version/date footer, and wrap prose. All substantive obligations, article identifiers, formulas and source references are preserved. |
| 1.2.0 | 2026-11-05 | Make the intrinsic product explicit in C0: a growing categorical mathematical research language with first-class constructions, generic interface/composition growth, fixed mathematical meaning, actual computational workflows and mathematical interaction. Make the adopted mathematical roles of computations, classifiers, dependent families and higher coherence explicit in C1, C5 and C7. Elaborate C4, C11 and C12 positively; clarify the C8 and C15 titles; name lean-categories as the currently designated independent formal development. Relocate C14, C16–C20 and the detailed C1/C12 contributor procedures under Governance while preserving their obligations and identifiers. This restores the source-backed project definition and distinguishes it from contribution policy; it does not select a runtime architecture, reduce computational scope or amend the mathematical trust boundary. |

### Provenance

The source basis records why these obligations are present; the normative text above is the
maintained constitution. Historical sources establish requirements and corrections, not
implementation conformance. Edited comments and branch-only documents retain the qualifications
in the [constitutional archaeology][S31]. The [recovered issue formulation][S32] is the
preceding reconstruction; later architectural alternatives remain proposals.

The September citations use owner messages 4–7 in the [original recorded discussion][S3], dated
September 29 internally and committed September 30, preserved by PR #50 rather than main. The
file presents those messages as verbatim; the external conversation was not independently
authenticated and its internal timestamps state no timezone. The [redacted summary][S28] is
corroborating evidence, not a substitute for the original wording. Assistant responses in either
record do not create owner requirements.

The October 1 archived document and October 3 chapter are cited with their historical status,
not as proof that every later branch retained them. In particular, the October 9 omission of the
October 3 chapter motivates the explicit preservation requirement above; the omission is not
evidence of an authorized amendment.

[S1]: https://github.com/dzackgarza/lattice-research/blob/e97780e442e6c6dd4ef3c4b436c3c156929eb555/.agents/memories/category-spec-epistemic-foundation.md
[S2]: https://github.com/dzackgarza/lean-categories/issues/1#issuecomment-5053438230
[S3]: https://github.com/dzackgarza/lean-cas-dsl/blob/df43c82e939d3b5a54c9b1126abcaa2927c62e3f/specs/owner/intent-discussion.md#L612
[S4]: https://github.com/dzackgarza/lean-categories/blob/63e9f620f4f5722bc6d5e73249597deba8f23dd5/INTENT.md#current-api-ownership
[S5]: https://github.com/dzackgarza/lean-cas-dsl/blob/0c2f65239aa43e92e3ba122965d1afbc84b9a72f/specs/architecture.md
[S6]: https://github.com/dzackgarza/lattice-research/commit/b93befdcd453267cd29f6eb6d5b880064c9c0031
[S7]: https://github.com/dzackgarza/lean-cas-dsl/blob/eca90bead8a52ea452fa15398ff30124ee9dc5a0/DESIGN.md
[S8]: https://github.com/dzackgarza/lean-cas-dsl/issues/31#issuecomment-5139189973
[S9]: https://github.com/dzackgarza/lean-cas-dsl/issues/10#issuecomment-6574949858
[S10]: https://github.com/dzackgarza/lean-cas-dsl/issues/15#issuecomment-5126956290
[S11]: https://github.com/dzackgarza/lean-cas-dsl/issues/7
[S12]: https://github.com/dzackgarza/lean-categories/blob/c7f1bbcad513219b54d8b698aa28152daf3ff1d4/FOUNDATIONS.md
[S13]: https://github.com/dzackgarza/lean-cas-dsl/issues/82#issuecomment-6479380545
[S14]: https://github.com/dzackgarza/lean-cas-dsl/issues/69#issuecomment-6402662210
[S15]: https://lean-lang.org/doc/reference/latest/ValidatingProofs/
[S16]: https://github.com/dzackgarza/lean-cas-dsl/blob/73bfb1110eb319ff6a6689ac5b01e3b2b1ee049d/SPEC.md
[S17]: https://github.com/dzackgarza/lean-cas-dsl/blob/9396a930ec21abca6df1cc9c646ea0ab5e7cbff9/specs/owner/convergence-process.md
[S18]: https://github.com/dzackgarza/lean-cas-dsl/issues/24#issuecomment-6586827500
[S19]: https://github.com/dzackgarza/lean-cas-dsl/issues/69#issuecomment-6586826632
[S20]: https://github.com/dzackgarza/lean-cas-dsl/blob/5001089606236b35a3e7291ad9e3a7cdeb4e32cf/specs/owner/2026-10-01-review-and-delegation.md
[S21]: https://github.com/dzackgarza/lean-cas-dsl/commit/933c6636b5bd99464dbc2c8665907aa70e5b455a
[S22]: https://github.com/dzackgarza/lean-cas-dsl/blob/5a906241816733966a35e88ed4908b4f33841a80/specs/architecture.md
[S23]: https://github.com/dzackgarza/lean-cas-dsl/issues/16
[S24]: https://github.com/dzackgarza/lean-cas-dsl/issues/9
[S25]: https://github.com/dzackgarza/lean-cas-dsl/issues/35#issuecomment-5191634067
[S26]: https://github.com/dzackgarza/lean-cas-dsl/issues/13#issuecomment-5141559954
[S27]: https://github.com/dzackgarza/sage-categories/blob/f37647af4f59d8f3505e1b18b11dab30bf3edf84/specs/computational-generality.md

[S28]: https://github.com/dzackgarza/lean-cas-dsl/blob/42bf9ed874a373b7ac48df47540d28d1536aec99/custodian/owner-intent.md
[S29]: https://github.com/dzackgarza/lean-cas-dsl/blob/f34ce0debeada8d93cf23ecec1d78586199a3ac0/specs/computational-core.md
[S30]: https://github.com/dzackgarza/lean-cas-dsl/issues/19
[S31]: https://github.com/dzackgarza/lean-cas-dsl/issues/10#issuecomment-6614764539
[S32]: https://github.com/dzackgarza/lean-cas-dsl/issues/10#issuecomment-6630427911
[S33]: https://github.com/dzackgarza/lean-cas-dsl/blob/0cee529c343fbe1c5f7a5f1326d4b805cc8fed44/CONTRIBUTING.md
[S34]: https://github.com/dzackgarza/lean-cas-dsl/blob/22331a9fb7a0aa0f5046be70cc1ea56a224741f9/specs/computational-core.md#L226-L280
[S35]: https://github.com/dzackgarza/lean-cas-dsl/blob/22331a9fb7a0aa0f5046be70cc1ea56a224741f9/AGENTS.md#L118-L159
[S36]: https://github.com/dzackgarza/lean-cas-dsl/blob/22331a9fb7a0aa0f5046be70cc1ea56a224741f9/CONTRIBUTING.md
[S37]: https://github.com/dzackgarza/lean-cas-dsl/blob/22331a9fb7a0aa0f5046be70cc1ea56a224741f9/specs/architecture.md#L895-L974
[S38]: https://github.com/dzackgarza/lean-cas-dsl/blob/22331a9fb7a0aa0f5046be70cc1ea56a224741f9/specs/computational-core-plan.md#L218-L238
[S39]: https://github.com/dzackgarza/lean-cas-dsl/blob/ca9798cb285e2e696e3401aad27831b8353d6264/CONTRIBUTING.md
[S40]: https://github.com/dzackgarza/lean-cas-dsl/issues/10#issuecomment-6574948314
[S41]: https://github.com/dzackgarza/lean-cas-dsl/issues/22#issuecomment-6586847402
[S42]: https://github.com/dzackgarza/lean-cas-dsl/issues/5#issuecomment-5126214534
[S43]: https://github.com/dzackgarza/lean-cas-dsl/issues/68#issuecomment-6586827096
[S44]: https://github.com/dzackgarza/lean-cas-dsl/issues/24#issuecomment-6574949387
[S45]: https://github.com/dzackgarza/lean-cas-dsl/issues/8#issuecomment-5126214910

[S46]: https://github.com/dzackgarza/lean-cas-dsl/blob/a206552ca315726c5d8cca356cebc65f617d4d7a/README.md

**Version**: 1.2.0 | **Ratified**: 2026-11-04 | **Last Amended**: 2026-11-05
