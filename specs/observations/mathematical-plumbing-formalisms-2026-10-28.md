# Mathematical formalisms for kernel plumbing

Assessment date: 2026-10-28.

**Yes. The strongest fit is a dependently typed language of effectful computations, built from a signature and interpreted compositionally.** Its mathematical foundations are generalized algebraic theories, context comprehension, and algebraic effects. Freyd categories explain how its execution and wiring compose. These can replace repeated routing and bookkeeping code with a small set of constructors, generic interpreters, and structural laws.

The useful abstraction is concrete: declare an operation's dependent interface once; form larger computations by typed composition; interpret those computations through one kernel-controlled execution mechanism. Each new operation then supplies interface data and a primitive implementation, rather than another execution path.

This is an architectural assessment, not an implementation or an approved change of direction. It uses the source snapshots identified in the [landscape assessment](implementation-research-landscape-2026-10-28.md). The recommendations below are applications inferred from the cited research. None of the surveyed libraries has been built against this repository or shown to satisfy its full contract.

| Recurring obligation | Mathematical formalism | What can become generic |
| --- | --- | --- |
| Keep category, endpoints, and selected structure together | Dependent signatures; categories with families | Context extension, substitution, typed references |
| Compose primitive and derived operations | Free computations; algebraic effects and handlers | Sequencing, interpretation, propagation of execution failures |
| Retain a particular result and reuse its components | Typed SSA; Freyd categories | Binding, sharing, effect order |
| Reuse an interface through a mathematical translation | Generalized algebraic theories and theory morphisms | Translation of syntax; restriction of lawful formal models |
| Enforce valid transitions in a port or invocation | Parameterised monads; session types | Composition only across compatible states |
| Assemble independent components and their connections | Operads and string diagrams; structured cospans | Substitution of diagrams and boundary gluing |

**The essential distinction is between mathematical meaning and computational wiring.**

The repository's [intent](../../INTENT.md) assigns mathematical meaning to `lean-categories`, and its [evidence model](../architecture.md) allows a leaf to return wrong answers. Therefore a leaf cannot be assumed to be a model of the mathematical theory. A model must satisfy that theory's equations; an arbitrary implementation need not.

There are separate mathematical objects to describe here:

- The formal mathematical theory, including its equations and proved constructions.
- The syntax of requests, bindings, result references, and executions.

The kernel can prove structural facts about the second while consuming the first. It can prove that an instruction uses the selected input, that a reference has the declared form, or that interpreting a composite agrees with sequencing its instructions. None of these proves that an external answer is mathematically correct. That judgment remains with the permanent acceptance assertions.

In particular, a mathematical equality does not by itself license an execution rewrite. Two requests for mathematically equal expressions can involve different invocations, suppliers, or retained objects. Reusing an existing result and rerunning a computation are different operations.

**Dependent signatures and context comprehension address lost context.**

A signature describes sorts and operations. A *dependent* signature allows one sort to depend on an earlier value. For a category, this includes `Obj(C)` and `Hom(C, A, B)`. An arrow's endpoints are part of its type, so they need not be recovered later from a packet or a native class. Generalized algebraic theories, or GATs, add equations to such dependent signatures. GATlab provides implemented examples, syntax generation, and translations between theories. [Lynch et al., GATlab](https://arxiv.org/abs/2404.04837).

A category with families gives the context operations a mathematical interface. A context is a sequence of dependent declarations, such as

\[
\Gamma=(C:\mathrm{Cat},\ A:\mathrm{Obj}(C),\ B:\mathrm{Obj}(C),\ f:\mathrm{Hom}_C(A,B)).
\]

Types and terms live over contexts. A substitution \(\sigma:\Delta\to\Gamma\) supplies the declarations of \(\Gamma\) in context \(\Delta\). Reindexing must respect identity and composition:

\[
A[\mathrm{id}]=A,
\qquad
A[\sigma][\tau]=A[\sigma\circ\tau].
\]

Context extension adds a value together with its dependent type. This is the mathematical structure behind carrying a complete environment through a language. Categories with families and comprehension categories are established ways to express it. [Coraglia and Emmenegger, context comprehension](https://arxiv.org/abs/2403.03085).

**Proposed application:** make the selected formal context an index of each kernel instruction and result reference. Context extension and substitution then carry endpoints and selected structure through all instructions. The kernel would no longer need each execution branch to remember which optional fields to copy.

This targets a concrete representation boundary. In the inspected [`Wire`](https://github.com/dzackgarza/lean-cas-dsl/blob/60829a1f7db040f6a8ae394777c0a10bc00d3946/CasCatalogue/Realize.lean#L214-L289), form and payload sit beside optional category context, endpoints, construction inputs, and captured invocation data. A dependent representation could express which combinations are valid at construction time. External bytes would still need a checked decoder.

Lean already supplies dependent types and substitution. The recommendation is to use that structure for the finite supported catalogue interface, not implement another general type theory. Nor does context substitution supply an arbitrary mathematical transport: the action of a selected functor, and any comparison between routes, still comes from upstream mathematics.

**Free computations and handlers address repeated execution machinery.**

For a simple command interface, let \(Q\) be the type of requests and \(R(q)\) the type of replies to request \(q\). Its polynomial functor is

\[
F(X)=\sum_{q:Q}\bigl(R(q)\to X\bigr).
\]

A node selects a request and supplies a continuation for each possible reply. Well-founded computation trees with final results in \(A\) have constructors

\[
\mathrm{Pure}:A\to\mathrm{Prog}(A),
\qquad
\mathrm{Call}:\prod_{q:Q}(R(q)\to\mathrm{Prog}(A))\to\mathrm{Prog}(A).
\]

This is the free monad on the command functor. Given a lawful target monad \(M\), a handler

\[
h:\prod_{q:Q}M(R(q))
\]

extends to an interpreter of whole programs. Its definition is forced by `Pure` and `Call`: return final values, and sequence a handled request with the interpretation of its continuation. The free construction supplies compositionality once. This is the central algebraic-effects idea. [Plotkin and Pretnar, Handling Algebraic Effects](https://arxiv.org/abs/1312.1399), [Bauer, tutorial](https://arxiv.org/abs/1807.05923).

**Proposed application:** express primitive invocation, use of a retained result, and supported derivation instructions in a common typed computation language. A derived operation is a program over primitive requests. The kernel interpreter handles dispatch, sequencing, framing, and storage without a separate recursive evaluator for each mathematical family.

The handler belongs to the kernel. Leaves provide opaque computations behind it. Here \(R(q)\) describes the permitted reply form; membership is not a proof of the answer's mathematical specification. Raw output must pass framing and decoding before it becomes such a reply. `NoImplementation`, unavailability or a crash, and malformed output remain distinct execution outcomes. Mathematical invalidity belongs to semantic checking, while a well-formed wrong answer remains possible and is judged by the suite. Ambiguity and internal interpreter errors retain their separate classifications.

The displayed formula is the simple case. This kernel also needs context-indexed commands and dependent continuations. Combining dependency with effects requires explicit rules for when a later type may depend on an earlier result. Ahman's *Fibred Computational Effects* develops precisely that problem. It is a more relevant foundation than assuming an ordinary unindexed monad solves every dependency. [Ahman](https://arxiv.org/abs/1710.02594).

For potentially infinite execution traces, interaction trees extend the approach with coinductive computation trees and reusable handlers. [Xia et al., Interaction Trees](https://arxiv.org/abs/1906.00046). A finite kernel plan need not adopt coinduction merely because a primitive can block. Higher-order effects become relevant if an instruction takes or returns a computation, rather than just a value or an ordinary mathematical map.

**Freyd categories explain which wiring equations are valid.**

A Freyd-category presentation separates pure value manipulation from effectful computation. Pure maps have cartesian structure; computations have premonoidal structure, which retains sequencing without assuming arbitrary effects commute. Copying a value is therefore distinct from duplicating the computation that produced it.

Ghalayini and Krishnaswami give a type theory and categorical semantics for a variant of SSA, with soundness and completeness results. Their treatment includes effects and control flow, and a Lean mechanization. The artifact's README specifies that it formalizes the syntax, equations, and completeness proof, while the categorical semantics itself is otherwise unformalized. [Paper](https://arxiv.org/abs/2411.09347), [Lean artifact](https://github.com/imbrem/debruijn-ssa/tree/toplas-artifact).

**Proposed application:** let every execution result introduce a typed binding. Subsequent instructions consume that binding. Keep execution order explicit wherever effects may interact. This gives a mathematical specification for the producer-identity obligation currently handled by occurrence wrappers in [`Trace`](https://github.com/dzackgarza/lean-cas-dsl/blob/60829a1f7db040f6a8ae394777c0a10bc00d3946/CasCatalogue/Trace.lean#L465-L560).

For example, suppose the formal side fixes a pullback request for \(f:A\to C\) and \(g:B\to C\). The kernel binds the execution's structured reply as `p`. References to its apex and projections belong to that same binding:

```text
p := execute(selected_pullback_request)
u := execute(selected_operation_using(p.apex, p.left_projection))
```

A second invocation gets another binding, even if its request has the same mathematical expression. Its components cannot silently replace components of `p`. The reference types express this association; they do not assert that the returned components satisfy the pullback property. That property belongs to the formal specification and the independent assertions about answers.

This example identifies the intended saving: all structured results use the same binding, projection, and substitution machinery. A new construction need not invent its own path for recovering its producer or retaining its maps.

**Theory morphisms provide reuse across mathematical interfaces.**

A theory morphism \(\phi:T\to U\) translates the sorts and operations of \(T\) into \(U\), preserving equations. It sends syntax forward. By precomposition, it sends lawful models of \(U\) back to models of \(T\). GATlab implements theory maps and model migration, including an opposite-category example. It also states limits on automatic validation: preservation of arbitrary equations cannot be assumed decidable. [GATlab, theory morphisms](https://arxiv.org/html/2404.04837v1#S4).

**Proposed application:** upstream formal translations can support generic translation of operation expressions and dependent interfaces. This can reduce per-method forwarding code when several methods follow the same declared mathematical action. The mathematical translation must already exist upstream; the kernel instantiates it.

The same restriction applies at the implementation boundary. Restricting a lawful formal model along a theory map is justified mathematics. Calling an arbitrary leaf a lawful model would add an assumption the evidence model expressly rejects. Execution can interpret the free request syntax without inheriting the mathematical equations of its intended answers.

**Parameterised monads address lifecycle wiring.**

A parameterised monad records initial and final states in its type. In the simplest notation, \(M(i,j,A)\) describes a computation from state \(i\) to state \(j\) returning \(A\). Composition has the form

\[
M(i,j,A)\times(A\to M(j,k,B))\longrightarrow M(i,k,B).
\]

The middle states must agree. Atkey develops this structure for changing state types and communication protocols, including session-type examples. [Parameterised Notions of Computation](https://strathprints.strath.ac.uk/74442/).

**Proposed application:** encode distinctions such as a prepared invocation, a received packet, and a decoded reply, with failure exits represented explicitly. Where an external handle has a supplier or session owner, index its permitted uses by that owner. These types can exclude invalid local transitions; they cannot make an external process stay alive or make its answers true.

This should be part of the same indexed execution language where practical. Adding an unrelated lifecycle framework would preserve the duplication the abstraction is meant to remove.

**String diagrams and operads are useful when their laws match the effects.**

A wiring diagram specifies boxes, typed ports, and connections. Operadic substitution replaces a box by another diagram with the same boundary. An algebra of the operad interprets primitive boxes and extends to composite diagrams. Patterson, Spivak, and Vagner develop wiring diagrams as normal forms for symmetric monoidal computations and implement them in Catlab. [Wiring diagrams as normal forms](https://arxiv.org/abs/2101.12046).

For this project, diagrams could provide a common representation for composition, visualization, and execution planning. However, unrestricted symmetric monoidal rewiring assumes independence that shared external state may violate. An effect-order connection or an appropriate premonoidal presentation must retain that dependency. The SSA paper makes this distinction explicit. A diagram alone also does not express every dependent port relationship.

Structured cospans address a related assembly problem: compose open components by gluing matching boundaries through pushouts. Under suitable hypotheses, this yields a symmetric monoidal category and a double-category structure. [Baez and Courser, Structured Cospans](https://arxiv.org/abs/1911.04630). They are a strong option for network assembly. The inspected kernel's more immediate problem is typed dependence and retained execution identity, so they are a secondary fit here.

**The `sage-categories` formalism is reusable; its runtime realization is not.**

`sage-categories` at [`37ec164`](https://github.com/dzackgarza/sage-categories/blob/37ec1642fe19f24fb00f402fe45350341ebf6920/specs/functor.md#structure-functors-and-inherited-classes) contributed four mathematical devices. Each is a special case of a structure recommended above, so it needs no separate framework here.

| `sage-categories` device | Formalism it instantiates | Use in this kernel |
| --- | --- | --- |
| Selected structure functors; inheritance only along a selected faithful isofibration | Reindexing along a fibration. A category with families or a comprehension category is a fibration of types over contexts, and substitution is its cartesian lift. | Transport along an upstream-selected functor is one generic reindexing instruction. Its applicability is the upstream classification, never a class graph. |
| Axioms as property subcategories, pulled back along structure functors | Pullback of a classifier along a functor; inverse-image subcategories | Already owned by `lean-categories`. The kernel consumes the classification and keeps the retained inverse pair in the binding. |
| `Fun(C, D)` owns every functor `C → D`; `FunctorImageCache` retains actual images | Typed SSA binding of an execution result | A functor application is a binding. Its image, endpoints and supplier are components of that binding, not cache entries keyed by value. |
| CAP derived methods, consumed through the Catlab and CAP adapters | Free computations over primitive requests, with a handler | A derivation is a program over primitive requests. The kernel's one interpreter executes it. |

The failures of record come from the realization, not from these devices. The runtime compiled selected functors into Python classes with controlled C3 and declaration-order precedence. A shared class occurrence then stood for several distinct images ([#26](https://github.com/dzackgarza/sage-categories/issues/26)). A later refinement changed the class through which existing objects reached their operations ([#31](https://github.com/dzackgarza/sage-categories/issues/31), [#33](https://github.com/dzackgarza/sage-categories/issues/33)). In the formalism above these are binding errors: two applications of different functors share one producer identity, and a refinement rewrites an existing binding instead of extending the context. Typed bindings and context extension exclude both by construction.

Therefore reuse the mathematics of `sage-categories` through `lean-categories`, and reuse none of its supporting CAS machinery for plumbing: neither Sage's dynamic classes and C3, nor SymPy's assumption system. The CAS engines remain available behind leaves, where they compute and decide nothing about meaning.

**Existing code is relevant, but the library choice remains open.**

| Candidate | Established scope | Fit still to establish here |
| --- | --- | --- |
| [GATlab](https://algebraicjulia.github.io/GATlab.jl/stable/) | Dependent algebraic signatures, symbolic models, theory maps in Julia | Use as a design reference without introducing another semantic authority |
| [SSA Lean artifact](https://github.com/imbrem/debruijn-ssa/tree/toplas-artifact) | Mechanized SSA syntax, equations, and completeness development | Dependent request interfaces and this kernel's result ownership |
| [MIT PLV lean4-itree](https://github.com/mit-plv/lean4-itree) | Lean interaction trees using quotient polynomial functors | Required handlers, theorem surface, and toolchain compatibility |
| [HITrees](https://arxiv.org/abs/2510.14558) | Lean implementation of higher-order effects with execution and transition-system interpretations | Whether the kernel requires this additional expressive power |
| [Catlab](https://algebraicjulia.github.io/Catlab.jl/latest/) | Implemented categorical and wiring-diagram infrastructure | An appropriate dependent, effect-sensitive execution representation |

**The recommendation is one small computational calculus, with these structures supplying its laws.**

Use dependent contexts for interfaces and references; free effectful syntax for programs; and a kernel-owned interpreter for execution. Use the Freyd/SSA distinction to preserve sharing and effect order. Add state indices where protocol transitions require them. Theory morphisms and wiring diagrams then describe reuse and composition around that core.

The reduction in engineering comes from extending a signature instead of extending the evaluator. Within the supported interface language, adding an operation should add a declaration and a primitive registration. Substitution, result binding, sequencing, and decoding of already supported shapes should follow from existing machinery. Proofs about those structural operations can apply to every program formed from the signature.

There are real limits. A formal signature does not generate an effective codec for every Lean type. It does not choose an unspecified presentation, find an algorithm, invert a forgetful functor, or prove a leaf's answer. Lenses likewise require their own laws and retained data; they cannot manufacture a lift after information has been discarded. These obligations remain explicit at their existing owners.

The decisive architectural question is therefore whether the kernel can represent a new supported operation and its complete dependent result through existing constructors, without adding another case to execution or reconstructing context downstream. The cited formalisms supply precise ways to state that requirement and derive its implementation. They support a substantial reduction in bespoke wiring, while leaving the programme's semantic and evidence boundaries intact.
