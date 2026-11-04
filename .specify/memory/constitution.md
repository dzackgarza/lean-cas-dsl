# lean-cas-dsl Constitution

**Version:** 1.0.0

**Adopted:** 2026-11-04

**Last amended:** 2026-11-04

**Status:** normative project constitution

## Authority and scope

This file is the canonical, version-controlled constitution of lean-cas-dsl. It
states the requirements that every implementation, replacement architecture,
contribution and acceptance claim must satisfy. Its mandatory rules are expressed
by “must”, “must not”, and the quantified obligations below.

The owner explicitly requested a permanent repository constitution on 2026-11-04.
This is a specific exception to the earlier policy that repository documents
contain only issue pointers. The complete constitution must remain in the
repository. It must not be replaced by a pointer, omitted during a merge, or
removed as part of a documentation migration. Its preservation does not depend
on the architecture, programming language, process layout or planning tool.

The constitution governs engineering choices; it does not replace independent
mathematical authority. All mathematical definitions, categorical structures,
laws and abstract computational obligations must be independently formalized and
auditable, for example in lean-categories. A downstream implementation or this
document's notation cannot supply missing mathematics.

Implementation plans, work orders, diagnostics, completion evidence and
architectural proposals remain in their owning GitHub issues. Those records
specialize the requirements to an authorized task; neither an agent-authored
plan nor an existing implementation can amend this constitution. Applicable
owner instructions retain their authority. A change to a constitutional
requirement must be recorded explicitly under the amendment rules below.

The constitution specifies conformance obligations. It is not a declaration
that the existing implementation conforms, nor a substitute for the independent
formal definitions and proofs those obligations require.

## Obligation classes

The constitution contains three different kinds of obligation, whose quantifiers
must remain distinct:

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

Safety requirements govern every permitted operation. Conditional preservation
requirements govern the supported constructions and their composition. Delivery
requirements govern the claimed completed product; they are not an invented
prerequisite requiring the product to exist before authorized construction can
proceed. Each obligation retains its full scope.

Implementation-only changes must preserve these requirements across revisions.
An independently justified mathematical correction changes the accepted
specification explicitly; an implementation failure cannot make that correction
for it. “Permanent” does not make an erroneous historical mathematical definition
immutable.

The constitution fixes mathematical meaning, authority, required user
capabilities and completion. A plan chooses representations, algorithms,
languages, libraries, processes and deployment. Current owner-selected
engineering policies remain binding within their scope unless explicitly
changed; they are listed separately below rather than disguised as mathematical
necessities.

## Formal contract and notation

Let **M** denote an independently accepted, versioned categorical formalization, **P** the independently fixed public mathematical language contract, and **A** the independently authored accepted question/expectation corpus. Let **K** be a candidate interpreter/compiler/runtime and **L** its computational providers. These are roles, not a prescribed number of repositories or processes.

Write `Read(M,P,Γ,q)` for the mathematical readings of question `q` in the fixed mathematical context `Γ`. A reading is a complete selected judgment: context, typed operands, categories and parameters, selected structures, operation or composite, hypotheses, comparison/coherence data, result family and the requested relation or observation. “Complete” means all data on which that judgment depends, not a fixed record layout. Write `Req(M,J)` for the independently fixed computational obligation associated with judgment `J`; its content is supplied by the authoritative definitions and language contract, never by the provider under assessment. `Run(K,L,J)` is actual execution and is not identified with a proof of `Req(M,J)`.

The statements below are quantified specification obligations. Their formalization must instantiate the symbols using independently accepted definitions and establish the stated property of the actual interpretation or computational mechanism. Introducing an unconstrained `Correct` or `Realizes` parameter, or assuming the desired property as an axiom, does not discharge an obligation. The mathematical authority must fix the statement before the implementation is assessed. The formulas in this document are not themselves machine-checked proofs about the present code.

## C1. All mathematical authority is independently categorical

Every admitted public mathematical judgment must be derivable from the independently accepted definitions and construction rules in **M**, under its explicit context: `M; Γ ⊢ J`. Those rules fix its complete meaning, type and required categorical structure. Methods and predicates are expressed by the appropriate formal mathematical constructions, including the required higher morphisms where applicable. A backend name, Python class, implementation filter, registry label or successful computation cannot supply a missing mathematical rule.

A constructed object, parameter instance or local hypothetical object need not have its own pre-existing catalogue row. Its meaning comes from applying the accepted rules with the actual parameters and assumptions. Requiring an enumerated declaration for every instance would defeat the intended language and its infinite families.

There is one mathematical presentation: intrinsic objects, chosen presentations, families, classifiers, sections, computational operations and higher comparisons belong to that same independently owned mathematics. An implementation index is engineering data; a second presentation/capability ontology with independent mathematical standing is prohibited. Genuine basis and generator data are mathematical structures, not exceptions handed to a backend to define.

This constrains semantic authority, not the number of data structures. Compiler representations, indexes and derived views are permissible when their interpretation remains fixed by the same mathematical source and the required preservation is established.

For every provider or implementation-only change `u`,

$$
u(M,P,A)=(M,P,A).
$$

This is an authority restriction: these changes cannot redefine the mathematics, its intended public reading or the independent expected answers. It does not prohibit authorized implementation changes to the machinery that consumes them.

Independent formalization must be mathematically auditable against its stated sources and intended definitions. Typechecking a convenient but wrong definition does not establish that it is the intended mathematics. The historical requirement excludes `sorry` and project-created axioms used to assume the desired result; legitimate hypotheses belong in the statement.

The independently owned formal API must also specify the **abstract computational obligations**: what data and operations implement a construction, their dependent signatures, and how they compose. Backend independence does not restrict it to bare noncomputable definitions from which a downstream kernel must discover an execution model. Concrete invocation, encoding and provider selection are engineering responsibilities. Supplying those mechanisms must not become authority to redefine the abstract obligation.

Independence concerns actual authorship and inputs. Mathematical work is assigned from mathematical requirements and sources; acceptance is authored from accepted mathematics and the public language; implementations work against the released computational contract. A downstream diagnostic, generated goal or desired test outcome cannot be repackaged as the independent mathematical assignment. Moving an implementation-shaped definition to another repository does not make it independent.

**Source basis:** [May ownership record][S1]; [July one-diagram correction][S2]; [September owner record][S3]; [October computational-API correction][S4].

## C2. Implementations cannot choose the obligation they satisfy

The specification, permitted representation interpretation and correctness relation must be fixed independently of the candidate. A provider chooses private data structures and algorithms within the released computational contract. The mathematical meaning of their admissible public relationship to the requested construction is independently fixed. A need for a new mathematical interpretation is not permission for the provider or downstream interpreter to author it.

The quantifier order is:

$$
\text{independently fix }(M,J,\operatorname{Req}_{M,J});
\quad\text{then assess }I\text{ against }\operatorname{Req}_{M,J}.
$$

It is not `for each I, choose a relation that makes I correct`. The failure of the latter is elementary: for any total function `I`, define `R_I(x,y)` to mean `y = I(x)`. Then `R_I(x,I(x))` holds for every `x` by reflexivity, including when `I` gives the wrong answer to the intended problem. A proof of this statement supplies no relationship to that problem. The same defect occurs if a leaf defines its own denotation, checker, comparison or expected result and the system accepts that definition as authoritative.

This requirement does not silently replace the historical opaque-computation/independent-assessment evidence model with mandatory proof-carrying results. Any change to that evidence model must be stated separately. In either model, a supplier's self-authored proposition cannot become the standard against which that supplier is judged.

In particular, the laws in a formal definition do not automatically become proof-producing fields of every external reply. The independent API must distinguish mathematical laws from the computational data and operations an implementation supplies. Decoding a numeral produces that numeral; it does not prove it is the cardinality of the object asked about. Computational representations cannot be cast into law-bearing formal structures by assuming the missing proof.

**Source basis:** [September owner record][S3]; [October fundamental-model chapter, §§3–5][S5]. The logical counterexample above is proved directly.

## C3. Mathematical meaning is independent of computational availability

For fixed **M**, **P**, mathematical context `Γ` and question `q`, every choice of provider set, registration order, cache state and execution outcome must leave its mathematical readings unchanged:

$$
\operatorname{Read}_{M,P}^{L_1,c_1}(\Gamma,q)
=\operatorname{Read}_{M,P}^{L_2,c_2}(\Gamma,q)
=\operatorname{Read}_{M,P}(\Gamma,q).
$$

Removing all providers may make a meaningful operation unavailable for execution; it cannot remove that operation from the language, change its domain or select a different meaning. Installing a fast implementation cannot resolve a mathematical ambiguity. A backend failure cannot prove mathematical invalidity.

Ordinary mathematical expressions specify the mathematics, not a backend or algorithm. Implementation identity may be inspected through diagnostics; it is not something the user must insert into a mathematical expression to obtain its meaning.

The fixed-context qualification matters: different legitimate choices returned by a choice-producing operation can give later bindings different selected data. The law does not equate those different contexts. It prohibits computational availability or failure from choosing or rewriting the mathematical reading within the same context.

The formalization of the set of readings is distinct from an algorithm that computes it. This article does not assert decidability for arbitrary mathematical theories. Within the promised supported language, incomplete search or exhausted inspection must not be presented as a proof that there is no valid reading.

**Source basis:** [June feasibility reversal][S6]; [original July design][S7]; [September owner record][S3].

## C4. Generic structure determines the public interface

Mathematical applicability, structural propagation and inheritance must be determined by the accepted categorical constructions and their exact hypotheses. Per-leaf forwarding, class ancestry, a method-resolution order, a shortest path or the existence of a backend routine must not determine that mathematics. Generated classes and ordinary dispatch may execute already fixed rules without becoming their semantic authority.

For an accepted generic operation `o` and an object `X`,

$$
\operatorname{Applicable}_M(o,X)
\Longrightarrow
o\in\operatorname{PublicInterface}_{M,P}(X),
$$

independently of the quality or availability of the leaf implementation. Adding an applicable generic operation reaches existing objects through the common formal interface without editing each old provider. The owner's original examples include orthogonal groups, their subgroups and stabilizers: an implementation must not leave such an object without its mathematically entailed group or stabilizer interface.

Availability alone is insufficient. When an operation is the accepted composite of existing operations, generic composition must apply those operations to the actual selected data, transport arguments and results through the prescribed comparisons, and preserve the declared result interface and later uses. Correct realization is conditional on the supplied implementations fulfilling the independently fixed prerequisite obligations; registration alone does not establish fulfillment. The generic mechanism must not require new per-object forwarding or operation-specific cases. A genuinely missing algorithm remains missing execution, not a missing mathematical method; it remains owed wherever the accepted workload requires it.

This requires an adequate deterministic generic mechanism. It leaves open whether that mechanism is an interpreter, compiler or ordinary generated/library composition. Replacing it with hand-written CAS APIs for each domain would lose the requirement.

The prohibition concerns class ancestry or method order deciding mathematics. It does not forbid generated classes or ordinary library dispatch as execution machinery when the independent categorical interpretation has already fixed the meaning and required comparisons.

Conservative mathematical growth preserves existing fully selected meanings while adding applicable operations. It need not preserve the uniqueness of an underspecified surface expression when genuinely new mathematical routes create an ambiguity; selecting the old route by implementation priority would conceal that ambiguity.

**Source basis:** [July inherited-composition correction][S2]; [September owner examples][S3]; [October growth-mechanism chapter][S5].

## C5. Selected mathematical data cannot be erased

A judgment includes its selected category, parameters, structure, maps, comparisons and coherence. Sharing a carrier, object label, pair of endpoints or theorem name is insufficient to identify two judgments. Mathematical equality, isomorphism, presentation equivalence, occurrence identity and reference identity are different relations.

For every admissible translation `T` between representations of a judgment, the independent meaning must be preserved:

$$
\operatorname{Meaning}_{M,P}(T(J))
=\operatorname{Meaning}_{M,P}(J).
$$

The comparison establishing preservation must retain all selected data and the observation asked for. The equality here is a specification of preservation, not permission to erase distinctions by choosing a coarser quotient. A proof that two propositions are both true, or a matching Boolean result, does not identify the mathematical questions they express.

Generalized points retain their stage: a point `S → X` is not silently changed into an element obtained from an invented terminal object or underlying carrier. Parameter changes use the accepted variance, reindexing and comparison data. A noninvertible comparison cannot be used as an isomorphism.

An operation that asks for a choice, such as a generating family, returns a point of its independently specified choice fiber. Different valid choices need not be equal. Their actual chosen data must be retained for subsequent uses. This is distinct from a question that already prescribes a particular basis, comparison or lift: an implementation cannot replace that choice with a convenient one and call the question unchanged.

**Source basis:** [May object/presentation distinction][S1]; [July selected fibers and cells][S2]; [morphism/matrix correction][S8]; [preserved mathematical constraints][S9].

## C6. Domains and ambiguity are mathematical judgments

An operation is meaningful only on its independently declared domain, with its required structures and hypotheses established by the accepted mathematics. A surrounding desired operation does not authorize changing the reading of an argument to make the operation apply. A runtime exception, absent realization, timeout or malformed reply cannot establish that an input lies outside that domain.

Distinct unresolved mathematical readings remain distinct. Computational convenience cannot choose one. A negative semantic judgment requires the grounds prescribed by **M** and **P**; a failure to obtain such grounds remains a failure to establish the judgment.

An `unknown` computational outcome is an inability to establish the requested result, not a third mathematical truth value or permission to decide a predicate by convention. Session assumptions remain explicit hypotheses; introducing a hypothetical mathematical object is not an assertion of a new library theorem.

Exact and approximate requests have distinct meanings. A required tolerance and the associated independently specified error relation are part of an approximation request. An implementation cannot silently substitute a floating approximation for an exact answer, relax the tolerance, or declare the mathematical request invalid because its algorithm cannot meet that tolerance. Historical notation for an approximation is not permission to invent a literal mathematical quotient with no formal meaning.

This preserves the historical distinction between inversion on units and an invented inverse on a bare monoid, and between a selected structure and a convenient Lean instance on the same carrier. The general contract consumes independently supplied evidence; it does not authorize an interpreter to invent subject-mathematical lemmas.

**Source basis:** [July mathematical-role ruling][S2]; [procedural-unknown clarification][S10]; [approximation contract][S11]; [later domain requirements][S9].

## C7. Transport, lifts and higher coherence require their actual data

A functor supplies its declared action; it does not by itself supply a reverse lift, preservation of every limit, a selected representative or a chosen coherent extension. Every requested construction uses the accepted hypotheses and chosen data for that construction.

A result advertised as a universal construction must supply the required apex, defining maps and factorization operations in their specified relationship. If a later computation needs a chosen cell, comparison or lift, a mere existence proposition is insufficient for that use. No blanket strictification, quotient, truncation or “all cycles are identity” assumption may replace the required higher information.

The intended higher mathematical universe cannot be defined by the limits of an ordinary-category or strict two-dimensional execution model. Such a model is a scoped interpretation of the intended mathematics, with the required adequacy justification, not a license to remove higher objects, natural transformations, modifications or coherence from the public specification.

For a reduction `r`, the independent authority must provide the appropriate adequacy statement for every observation, action, composition, substitution and later continuation that the public contract promises after the reduction, including the uses required by C8. A reduction justified only for one observation remains confined to that use; it does not establish preservation of a richer interface. The implementation cannot infer adequacy from its need for a simpler representation. Symbolic or lazy retention is allowed when it preserves the entire required interface and selected information.

**Source basis:** [July higher-foundation correction][S2]; [first FOUNDATIONS][S12]; [later higher-scope correction][S13]; [October 29 reduction and subsequent-use requirements][S29].

## C8. Execution and later use refer to the same actual construction

Execution is directed at the already fixed complete judgment. The actual returned computational data and its maps, comparisons, parameters and dependencies remain associated through every required subsequent use. These are candidate computational views of the requested mathematics; associating them correctly does not prove that a wrong provider supplied the requested mathematical construction. Correct realization of the composition has the conditional meaning stated above, while the delivered system still owes the actual required successful computations.

A later use cannot substitute a separately reconstructed object merely because its formal expression or serialized label matches. An alternative evaluation or recomputation strategy is permissible only when it preserves the selected data, required identities and lifetime behavior, and dependent subsequent uses under the independently specified relation. This is a preservation requirement, not a universal prohibition on computing a value again.

For every permitted continuation `k`, the obligation is for the complete computation `k(J)`, using the actual result of `J`, with the selected transport where its presentation changes. Correctness of an isolated scalar observation does not discharge this requirement.

Where **M** independently fixes a representation interpretation, implementation correctness requires the corresponding action and observation equations for the whole declared interface. The representation interpretation is not a leaf-defined escape hatch. A valid wire shape or endpoint label proves neither those equations nor the universal property.

This article does not require foreign handles, one process per leaf, a particular intermediate language or runtime decoding. It applies equally to native values, CAS objects, generated programs and independently justified persistent artifacts.

Complete interfaces may be lazy, callable or symbolic. They must support the admitted infinite or nonenumerable objects and index families where those are part of the required specification; finite carrier, finite rank, finite support, finite presentation and finite diagram are distinct hypotheses and cannot be silently interchanged. Retaining a diagram and its public actions does not mean enumerating every element or cell. An approximation or finite replacement is a different mathematical construction unless the required comparison and adequacy are independently supplied.

**Source basis:** [October complete-interface chapter, §§6–8][S5]; [mathematical generality and infinite inputs][S27]; [public-constructor and later-use requirement][S14]; [preserved result boundary][S9].

## C9. Independent acceptance preserves the complete question

For every admitted assertion identity `a`, acceptance fixes its complete selected question `Q_a`, expected mathematical relation and required execution status independently of candidate behavior. An implementation-only revision must preserve these:

$$
(Q_a,E_a,\operatorname{Required}_a)_{\text{after}}
=(Q_a,E_a,\operatorname{Required}_a)_{\text{before}}.
$$

This does not freeze serialization, syntax spelling or an erroneous old reader record. Their correction must be justified independently against the unchanged mathematical question. A hash can reveal a change; it cannot establish mathematical equivalence or confer authority to admit the new record.

Expected answers must not be obtained from the implementation under assessment. Acceptance authors' actual inputs must preserve their required independence. Assigning another role label to an already exposed agent does not restore that independence.

**Source basis:** [September independent-assessment requirement][S3]; [October question-preservation chapter, §9][S5]; [preserved independent acceptance][S9].

## C10. Evidence has distinct obligations and cannot certify itself

Formal mathematical validity, correct interpretation, correct lowering, structural interface admission, actual dispatch, and mathematical correctness of a returned answer are different claims. A demonstration of one discharges another only through an independently justified implication with its hypotheses met.

In particular:

$$
\operatorname{WellTyped}(J)\not\Rightarrow\operatorname{Executed}(J),
\qquad
\operatorname{WellFormedReply}(r)\not\Rightarrow\operatorname{CorrectAnswer}_{M,J}(r).
$$

The first non-implication is witnessed by a well-typed question with no implementation. The second is witnessed by a well-shaped reply carrying the wrong scalar value. Passing a finite independent suite establishes the tested outcomes; it is not a proof of every possible computation. That limitation does not reduce the required suite or permit a missing positive result to count as success.

A candidate cannot install its own evaluator or accepted references as authority and then cite their approval. Separate source authorship, permitted inputs and authoritative advancement remain explicit. Packaging both components into one build is not by itself proof that the required independence survives.

Evidence binds the actual compatible mathematical, language, contract, implementation and assessment revisions used. Successes from incompatible revision combinations cannot be assembled into one acceptance claim. An unchanged declaration name or fingerprint does not establish that its definition or intended question is unchanged.

**Source basis:** [September owner evidence model][S3]; [October evidence distinctions, §§2,4–5,9,13][S5]; [Lean reference on proof validity and statement meaning][S15].

## C11. Required positive computation and full scope cannot be made vacuous

Let **W** be the independently fixed required workload, including the specified observations, later uses, extension cases and budgets. Completion requires the original obligations for every member:

$$
\operatorname{Complete}(K,L;M,P,A)
\Longrightarrow
\forall w\in W,\ \operatorname{RequiredOutcome}(w;K,L,M,P,A).
$$

The candidate does not choose **W** from the operations it happens to support. Missing, unreadable, unsupported, infrastructure-failed and not-reached cases remain in the denominator. A required successful computation is not discharged by a correct rejection.

A soundness-only condition would be inadequate: an implementation that never returns a result satisfies “every result it returns is correct” vacuously. The constitution therefore includes actual required positive computations, complete constructions and later uses, as well as semantic safety and protected negative cases.

A replacement must preserve the full already required product: mathematical language and discoverability, generic composition and extension, actual objects and maps, mixed-provider interoperability where required, notebook/research use and the independently fixed computational scope. A successful miniature example cannot redefine that scope.

**Source basis:** [original mathematical SPEC][S16]; [September convergence requirement][S17]; [October full-functioning-system obligation][S5]; [current fixed acceptance scope][S18].

## C12. Extension is assessed against a fixed common interface

For the prescribed independent-extension trial, freeze the common baseline and existing consumer. An independently supplied extension must work through the released public contract and accepted mathematics without accommodation edits to the kernel, contract, old consumer or expected answers. Independently authorized additive mathematics is distinguished from changing the baseline to fit the implementation.

The invariant is interoperability without private knowledge and generic growth without per-domain repair. It is not a requirement that implementations never share private code or a CAS session. Conversely, co-location does not excuse a producer that must modify every consumer or disclose its private representation to make the construction usable.

**Source basis:** [September growth requirement][S3]; [constructor-use clarification][S14]; [independence/additive-baseline requirement][S18].

## C13. Failure and lifecycle behavior cannot alter mathematics

Semantic invalidity, mathematical ambiguity, missing implementation, engine failure, malformed data, internal interpreter failure and a wrong answer remain different outcomes. No retry, fallback, restart or cache hit may change the selected question to conceal a failure.

Every object or computation exposed for later use must obey its declared identity and lifetime. Failure must not publish an incomplete successful construction, resurrect an invalid reference or silently substitute a fresh construction for the selected one. Implementations choose how to meet these requirements. The current ticket, snapshot and session machinery is not itself constitutional.

**Source basis:** [original notebook/pipeline contract][S7]; [actual-question and result-preservation requirements][S9]; [later declared lifecycle contract][S19].

## C14. Construction remains replaceable; correctness remains fixed

Authorized construction may replace any implementation component, including a controller or reviewer mechanism. A rule intended for an independently accepted finished system is not automatically a prerequisite for constructing that system. The controller cannot make itself irreplaceable or accept its own replacement.

Implementation freedom does not include changing the mathematical obligation, manufacturing independent approval, narrowing completion or turning a downstream failure into an implementation-shaped upstream theorem. An unavailable capability blocks the operation that needs it; it does not invent a new mathematical requirement or invalidate already authorized independent work.

**Source basis:** [October 1 archived review/construction directive][S20]; [October means/outcomes distinction][S5]; [October 10 authority ruling][S21]; [later construction supersession][S22]. The October 1 document presents owner text with preserved elisions and survives on the archived `custodian/controller-b0` lineage, not as a main ancestor.

## C15. The mathematical interface remains usable and its choices inspectable

Ordinary input and output expose the requested mathematics, with the promised mathematical rendering and a usable text form. A user must not need private backend vocabulary or source-code inspection to understand the result. The selected mathematical operation, assumptions, chosen presentations, provenance and computational limitations must be available through the prescribed inspection interface.

Formatting, tracing and inspection must preserve the selected mathematical question and respect the declared execution/lifecycle semantics; they cannot change its meaning or fabricate an execution outcome. A clearer diagnostic remains evidence of a gap when a positive computation is required. A synthetic demonstration or stale stored notebook output cannot establish a claim of actual researcher use or executed delivery.

This preserves the user-facing requirement without declaring a particular MIME bundle, notebook magic, Python client, logging option or renderer architecture eternal. Specific surface choices, including roots and multiplicities, exact approximation semantics, binders and differentials, remain part of the independently fixed mathematical language contract and its authorized revisions.

**Source basis:** [mathematical rendering requirement][S23]; [inspectable structural-map interface][S24]; [reported owner interface ruling][S25]; [actual research-use finding][S26].

## Implementation freedom and existing policies

The articles do not select an AST, interpreter rather than compiler, free-monad
encoding, native rather than foreign execution, number of processes, wire format,
cache or transaction implementation, physical repository layout, CAS
distribution, or code-size target. Every existing implementation component and
agent-selected plan remains a candidate for replacement. A replacement must
satisfy the complete obligations; changing the means does not change the task.

The following existing policies are distinct from the cross-architecture
articles. They remain applicable within their recorded scope. A proposal changing
one must identify the change explicitly and retain the constitutional
requirements; calling it an implementation detail does not silently repeal it.

| Current policy | Requirement and scope | Source |
| --- | --- | --- |
| Mathematical and leaf-code separation | New mathematics is formalized independently upstream. A computational leaf does not ship new Lean code. A native kernel does not by itself change that leaf rule; requiring providers to ship Lean modules does. | Original owner message 6 [S3] |
| Established computational implementations | Leaves use established engines and appropriate research implementations rather than needlessly reinventing mature algorithms. Their reuse supplies computation, not mathematical authority or proof of their answers. Independently justified new research algorithms are not prohibited. | Original owner message 6 [S3] |
| Computational evidence | Ordinary opaque results are assessed against independent mathematical expectations. Leaf-supplied claims, certificates, checkers, proofs, denotations, identifications and self-tests must not serve as semantic authority or correctness evidence; the independently authored permanent suite supplies correctness evidence about computed answers. Mandatory proof-producing replies are not current admission requirements. Changing this evidence boundary, including adopting a certificate-primary model, requires an explicit policy amendment; a leaf still cannot define its own correctness criterion. | Owner evidence distinction [S3]; maintained evidence policy [S9] |
| Delivery inputs | Own-organization delivery consumes the required latest-main dependencies and records the actual compatible revisions. Fixed diagnostic revision combinations remain valid for controlled comparisons; they do not become independent delivery targets. | Maintained delivery policy [S9] |
| Authorized computational scope | The complete currently assigned workload, including its connected computations, extension trials, observations and budgets, remains due. The V1 inventory and broader full-B0 obligation are distinct; neither historical counts nor proposed future algorithms silently change the assigned denominator. | V1 acceptance [S18]; full B0 [S30] |
| B0 authority during construction | The October 10 ruling makes role separation a conduct requirement: B0 acceptance does not wait on removing credentials capable of broader access. This removes that technical gate, not the restrictions on crossing roles or the requirement for independent acceptance. | October 10 ruling [S21]; maintained separation [S9] |

Implementation-specific mechanisms mentioned in these sources do not acquire
constitutional status by being recorded alongside genuine requirements.
Unresolved computational or formalization work remains an obligation of its
proper authority; its absence cannot authorize changing the question or the
completion standard.

## Application, preservation and amendments

Contributors must read this constitution together with the applicable owning
issue before selecting an implementation. A plan or proposed replacement must
be assessed against all applicable articles, including actual later use and
complete delivery, rather than only the example it makes convenient. Existing
review and acceptance evidence must establish the specific claims made.
This does not create a new approval board, checklist, controller or acceptance
ceremony.

A conflict with an implementation, roadmap, issue diagnosis or old source
snapshot must be resolved by correcting the subordinate artifact or by an
explicitly authorized requirement amendment. An agent's interpretation, CI
success, registry entry or chronological recency cannot supply that
authorization. Authorship and permitted inputs remain separated as required by
C1, C9 and C10.

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

Version changes are **major** for incompatible changes to an obligation or
authority boundary, **minor** for compatible additions or substantive
elaboration, and **patch** for editorial corrections that leave obligations
unchanged. Editorial maintenance does not invent a new approval requirement.
Existing authorization remains effective.

Merges and migrations must retain the complete current constitution. Conflict
resolution must not silently select an older version or discard an article.
Relocating or removing the canonical file requires an explicit owner decision;
routine document cleanup or an instruction to keep ordinary repo documents as
issue pointers does not authorize it.

### Adoption record

| Version | Date | Change |
| --- | --- | --- |
| 1.0.0 | 2026-11-04 | Initial permanent repository constitution, formulated from the recovered requirements and committed at the owner's explicit request. Establishes C1–C15, obligation classes, scoped policies and amendment rules. No replacement execution architecture is selected by this adoption. |

## Provenance

The source basis records why these obligations are present; the normative text
above is the maintained constitution. Historical sources establish requirements
and corrections, not implementation conformance. Edited comments and branch-only
documents retain the qualifications in the [constitutional archaeology][S31].
The [recovered issue formulation][S32] is the preceding reconstruction; later
architectural alternatives remain proposals.

The September citations use owner messages 4–7 in the [original recorded
discussion][S3], dated September 29 internally and committed September 30,
preserved by PR #50 rather than main. The file presents those messages as verbatim;
the external conversation was not independently authenticated and its internal
timestamps state no timezone. The [redacted summary][S28] is corroborating
evidence, not a substitute for the original wording. Assistant responses in
either record do not create owner requirements.

The October 1 archived document and October 3 chapter are cited with their
historical status, not as proof that every later branch retained them. In
particular, the October 9 omission of the October 3 chapter motivates the explicit
preservation requirement above; the omission is not evidence of an authorized
amendment.

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
