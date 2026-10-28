# Implementation and research landscape

Assessment date: 2026-10-28.

**The largest likely reinvention is a programming-language implementation: a typed intermediate representation, an evaluator, and a runtime for computations with retained results.** The wider architecture also has close predecessors in mathematical software interoperability and categorical computation. The strongest comparisons are compiler SSA, CAP/homalg, Math-in-the-Middle/MMT, and explicit mathematical models in Aldor and GATlab.

The evidence supports **uneven use of existing knowledge**, rather than a general absence of it. The development branch already has a [reuse assessment](https://github.com/dzackgarza/lean-cas-dsl/blob/362cb29f77525132519761046ae8ef14bb8bfa0b/specs/reuse/cross-repository-execution-prior-art.md) that discusses CAP, GATlab, Catlab, and predecessor implementations. Its derivation work applies some of those ideas. The remaining question is whether those designs govern the complete execution path, or whether each new consumer still needs another repair to retained context.

The comparison below uses the local documentation at `a712b3c` and the development implementation at `60829a1f7db040f6a8ae394777c0a10bc00d3946`, with its reuse assessment at `362cb29f77525132519761046ae8ef14bb8bfa0b`. These are explicit source snapshots. The judgments concern architecture and reuse; they do not assert a new execution result or an acceptance verdict.

| Local responsibility | Closest established work | Assessment |
| --- | --- | --- |
| Preserve selected operations, operands, producers, and results through execution | Typed compiler IR, SSA, abstract machines; Lean-MLIR | Strongest implementation-reuse opportunity |
| Compute universal constructions and derive operations from primitives | CAP, homalg, CompilerForCAP | Close operational match; already partly recognized |
| Give heterogeneous mathematical engines a common semantic language | Math-in-the-Middle, MMT/OMDoc, biform theories | Closest architectural predecessor |
| Keep mathematical structure separate from its carrier or native class | Axiom/Aldor; GATlab explicit models | Established design problem with direct examples |
| Resolve competing structural paths without accidental identification | Coercive subtyping, packed classes, hierarchy validation | Established coherence problem; the categorical scope here is broader |
| Retain additional structure and transport it along maps | Displayed categories and fibrations | Existing mathematical foundation, already present in reuse records |
| Exchange mathematical requests and retain remote values | OpenMath and SCSCP | Protocol reference designs; compatibility needs separate assessment |
| Judge untrusted computations against independent mathematics | Test-oracle research; separately verified checking systems | Established distinction between testing, checking, and trusting |

**Compiler construction is the most useful change of perspective.**

The kernel elaborates a mathematical expression, chooses its formal interpretation, prepares computational inputs, executes dependencies, and makes results available to later operations. Those are compiler and evaluator responsibilities. A formal expression, an instruction that computes it, and the result of a particular invocation need distinct identities.

The development source makes this overlap concrete. [`Trace`](https://github.com/dzackgarza/lean-cas-dsl/blob/60829a1f7db040f6a8ae394777c0a10bc00d3946/CasCatalogue/Trace.lean#L465-L560) uses an expression-keyed map, then adds occurrence wrappers to keep different producers apart. [`Harness`](https://github.com/dzackgarza/lean-cas-dsl/blob/60829a1f7db040f6a8ae394777c0a10bc00d3946/CasCatalogue/Realize.lean#L2189-L2227) retains expression results alongside action, service, derivation, and invocation records. [`Wire`](https://github.com/dzackgarza/lean-cas-dsl/blob/60829a1f7db040f6a8ae394777c0a10bc00d3946/CasCatalogue/Realize.lean#L214-L289) carries a form, payload, optional context, and completion-related flags. These are the local representations of problems that compiler IRs address directly.

In static single assignment, or SSA, a value identifies a particular definition. In MLIR, each value belongs to an operation result or a block argument; operations consume explicit values and may produce multiple results. This provides a reference for separating producer identity from equality of mathematical expressions. It also provides a model for retaining the distinct outputs of a structured computation. [MLIR language reference](https://mlir.llvm.org/docs/LangRef/).

For this repository, the useful consequence is specific: a later operation should refer to the retained result of the selected computation. Recovering that result from an equal formal expression can lose the supplier, presentation, endpoints, or selected maps. A pullback's apex and projections must remain associated with the same computed construction. SSA alone does not establish those dependent relationships; the IR's types or checked construction boundary must also retain them.

[Lean-MLIR](https://grosser.science/lean-mlir/) already develops SSA theory and verified compiler transformations in Lean. It deserves a direct suitability assessment before another execution representation is designed. Its published scope does not establish support for this project's dependent interfaces, external suppliers, or categorical lifts. It is a concrete candidate for reuse or adaptation, not evidence that the kernel can be replaced wholesale.

The evaluator also overlaps with work on deriving abstract machines from higher-order interpreters. Defunctionalization replaces continuation functions with explicit data and a transition function, making pending work and control flow inspectable. [Buszka and Biernacki](https://arxiv.org/abs/2108.07132) describe and implement this transformation. That literature is relevant to the transition from nested execution callbacks to explicit requests and retained results. It supplies a derivation method; it does not justify preserving several competing execution authorities.

**CAP is the closest source for the computational categorical interfaces.**

CAP specifies a kernel through its object, embedding, and universal lift. Its API includes operations that use a previously given kernel object. This directly addresses the problem of obtaining an object and then losing the maps or selected construction needed by later computations. [CAP universal objects](https://homalg-project.github.io/CAP_project/CAP/doc/chap6_mj.html).

CAP also records how one operation derives from other operations. Its derivations retain prerequisites, category applicability, implementation functions, and weights. The machinery computes available derivations and exposes their trees. Its documentation explicitly prevents the mathematical applicability filter from depending on current computational capability. [CAP derived methods](https://homalg-project.github.io/CAP_project/CAP/doc/chap8_mj.html).

These mechanisms match the repository's complete-result, generic-construction, and derivation-closure obligations unusually well. The [existing reuse assessment](https://github.com/dzackgarza/lean-cas-dsl/blob/362cb29f77525132519761046ae8ef14bb8bfa0b/specs/reuse/cross-repository-execution-prior-art.md) already connects CAP to the new computation-family plans. The assessment should therefore be whether that correspondence is complete at the public interface, rather than whether CAP has been mentioned.

CAP's operational designs can inform the kernel, and CAP computations can be exposed through ordinary leaves. Mathematical applicability and correctness still belong to the formal side here. In particular, an execution cost may select among implementations of one fixed operation; it cannot decide which mathematical route the user meant. A CAP implementation carries the same lack of authority as every other leaf.

**Math-in-the-Middle is the closest predecessor to the overall architecture.**

OpenDreamKit's Math-in-the-Middle approach places a central mathematical ontology between heterogeneous systems. System interfaces align with that shared vocabulary instead of relying only on pairwise translations. That is a close architectural comparison for a common mathematical language over Sage, GAP, Singular, and other engines. [Dehaye et al., Math-in-the-Middle](https://arxiv.org/abs/1603.06424).

MMT/OMDoc also has work on *biform theories*: specifications and computational implementations sharing formal module and typing information. Its Universal Machine evaluates expressions using implementations attached to the relevant operators. This is direct prior art for joining formal mathematical declarations with executable operations. [Kohlhase, Mance, and Rabe](https://arxiv.org/abs/1306.3198).

The local difference is material. This programme fixes Lean as its mathematical foundation, gives leaves no semantic authority, and assigns computational evidence to independent permanent assertions. The cited work does not establish that exact arrangement. Its value is in module interfaces, semantic alignment, and the separation of specification from computation. Importing a second authoritative ontology would conflict with the local goal; studying these representations need not do so.

The broader warning from this literature is that a common vocabulary does not finish interoperability. Each boundary still needs the exact parameters, presentations, morphisms, and supported operations. That is where this kernel's retained-context problems belong. Calling a value a module or a kernel leaves much of the computational interface unspecified.

**The distinction between a mathematical structure and its carrier is established language-design territory.**

Axiom/Aldor developed mathematical interfaces, parameterized domains, first-class types, and dependent typing for independently developed algebra libraries. These are close precedents for a language whose available operations follow mathematical structure. Aldor's use of “category” describes a programming interface; it is not by itself the categorical transport calculus required here. [Aldor guide](https://www.aldor.org/docs/HTML/chap1.html), [domains and categories](https://www.aldor.org/docs/HTML/chap7.html).

GATlab gives an especially direct modern example. Catlab's refactor explains why dispatch by native types cannot distinguish categories whose objects have the same Julia representation. It introduces an explicit model argument that selects the complete operation dictionary. This corresponds closely to the local need to retain the selected category, even when carriers or packets coincide. [GATlab explicit models](https://blog.algebraicjulia.org/post/2025/02/refactor1/index.html).

For example, a ring's additive and multiplicative structures can share a carrier while requiring different operations. A carrier type or raw value cannot select between them. The selected structure must travel with the operation and its arguments. The local `CategoryContext` work already follows this direction. The remaining burden is preserving that selection through every conversion and execution stage. GATlab's dictionaries are implementation mechanisms; their declarations would not become mathematical evidence in this programme.

**Coherence and transport have substantial existing research behind them.**

The repository's requirement to retain competing routes and justify their identification is related to coercive subtyping and mathematical hierarchy validation. [Sakaguchi's work on packed classes](https://arxiv.org/abs/2002.00620) identifies and checks hierarchy invariants that support predictable structure inference. [Wieser's study of Lean inheritance](https://arxiv.org/abs/2306.00617) explains how different paths through dependent structures can change the resulting types. These are precise precedents for failures otherwise easy to attribute only to Python inheritance.

The categorical requirement here goes further: parallel functors can be genuinely different, and a selected natural isomorphism may require computation. Ordinary subtype inference does not supply that action. The inspected [`resolveMethod`](https://github.com/dzackgarza/lean-cas-dsl/blob/60829a1f7db040f6a8ae394777c0a10bc00d3946/CasCatalogue/Resolve.lean#L409-L426) already rejects comparison ambiguity and requires a designated route. The research connection is useful for its invariants and algorithms, while the local operation must still preserve and execute the chosen categorical data.

Displayed categories provide another relevant representation: additional objects and morphisms are indexed over an existing category. Ahrens and Lumsdaine use them to organize categories of structured objects and fibrations in type theory. [Displayed Categories](https://arxiv.org/abs/1705.04296). The repository already cites UniMath and displayed-category sources in [`cc-lift-faithful`](../reuse/cc-lift-faithful.md). This is known mathematical infrastructure. It can guide the upstream formal representation, but the kernel must consume that representation rather than authoring a replacement.

**The port protocol and evidence model also have useful comparisons.**

OpenMath and SCSCP address mathematical data exchange and remote computational services. The GAP SCSCP implementation also documents remote object references and their lifetimes. These are relevant references for request framing, retaining external objects, and separating serialization from computation. [SCSCP specification and implementations](https://openmath.org/standard/scscp/), [GAP remote objects](https://gap-packages.github.io/scscp/doc/chap6_mj.html). They do not establish the complete dependent request/reply contract required here. Adopting a transport library would leave semantic validation with the kernel.

Independent expected answers address the established *test oracle problem*: how to decide whether observed output is correct. Specification-based and metamorphic testing are part of that literature. Here, formal laws can supply independently grounded families of assertions, while the permanent suite remains blind to implementations. Agreement between engines alone is weaker when they share algorithms or dependencies. [Barr et al., test-oracle survey](https://discovery.ucl.ac.uk/id/eprint/1471263/).

There is also a useful distinction between trusting a producer and checking its output. [SMTCoq](https://github.com/smtcoq/smtcoq/blob/main/README.md) uses a certified checker for witnesses from external solvers. The checker supplies the justification, rather than the solver's reputation or self-assessment. This programme deliberately uses an answer-only leaf contract and excludes that witness route. Its [scope statement](../computational-core.md#1-the-two-governing-invariants) already distinguishes protection of mathematical meaning from universal correctness of returned answers. The comparison clarifies that design choice; adding certificate traffic would change the evidence model.

**The useful next comparison is at interfaces, not project names.**

The immediate priority is to compare the selected computation/result boundary with typed SSA and abstract-machine designs. That comparison should account for dependent parameters, supplier identity, structured outputs, and subsequent use of the actual returned maps. It targets the concrete failure pattern documented in [the architecture-stall assessment](architecture-stalls-2026-10-28.md).

CAP is next: compare complete universal-construction interfaces and primitive-to-derived computation rules. MMT and biform theories then provide the broader check on the semantic/executable boundary. Aldor, GATlab, and hierarchy-validation work supply the model-selection and coherence constraints those interfaces must retain.

The residual work is a specific integration problem: preserve upstream mathematical meaning through a compositional execution language, keep external computations replaceable, and let independent assertions judge their answers. The inspected sources establish precedents for its major components. They do not establish a ready-made system satisfying this entire contract. The strongest recommendation is to reuse those components and their invariants at the boundaries where the implementation currently reconstructs lost information.
