# Contributing an operation — the wiring half

This documents how a computation gets **wired**: op signature, route,
executor, adapter. It is the half of the contributor contract that is
stable under the registry migration (issue #35).

Of the **mathematical half**, the structural part — declaring a category
and a membership — is deliberately not documented yet: its citation form is
owned by the upstream catalogue (lean-lattices#56) and lands with the
pinned consumer contract (lean-lattices#49). Until then, treat the
declarations in `CasDsl/Std.lean` as the examples of record. The worked
external-backend example (a numpy implementation of Vinberg's algorithm)
ships with that half. The DOCUMENTATION part of the mathematical half is
specified now — see §7, "Authoring the documentation fields."

## The path of a call

```
p.roots()
  → resolveMethod      semantic availability (category walk, Resolve.lean)
  → verifyResolution   Mathlib re-derives the membership (the tripwire)
  → routeFor           implementation selection (Route.lean)
  → execute            the (backend, opId) executor runs (this document)
```

Wiring only ever touches the last step plus the registration data the
selection reads. No wiring step may make a semantic claim: a route says
"this op can compute that method for this presentation", never "this
method exists".

## 1 · The adapter process (for an external backend)

An adapter is a child process speaking length-framed JSON on stdio
(`CasDsl/Port.lean`; `backends/sage_adapter.py` is the model). Each frame
is `<byte-length>\n<compact JSON>`; stderr is inherited (adapter logs land
on the kernel's stderr).

- **Handshake**: on start the adapter emits one unsolicited ready frame
  `{"op": "ready", "protocol": 1, "backend": …, "backend_version": …,
  "adapter_version": …, "capabilities": [opIds…]}`. A wrong protocol
  number kills the connection at handshake, loudly.
- **Requests**: `{"request_id": n, "op": opId, "args": {...}}`. Replies
  carry the same `request_id` and one of:
  - `{"status": "ok", "value": <codec frame>}`
  - `{"status": "error", "kind": …, "message": …}` — a structured backend
    refusal (e.g. `not_expressible`, `bad_request`); never invent a nearby
    answer to avoid one.
  - `{"status": "unsupported", "op": …}` for an op outside `capabilities`.
- **Values** cross the wire only as codec frames (`CasDsl/Codec.lean`;
  the Python side mirrors them in its `enc_*`/`dec_*` helpers). A new
  value shape means a new codec tag on BOTH sides plus a round-trip
  sample in `CasDslTests/Codec.lean` — never an ad-hoc encoding.
- **Discovery** is by environment variable with a checked default
  (`CASDSL_SAGE`, `CASDSL_ADAPTER`), relative to the project root.

Exactness is not negotiable: no floats on the wire, no silent
approximation, no dropped terms. What the backend cannot express exactly
is a structured error naming the ceiling.

## 2 · The Lean adapter module (`CasDsl/Backends/`)

One module per backend. Its jobs, in order (see `Sage.lean`):

- **Connection cache**: an `IO.Ref (Option PortConn)` holding the pipe.
  This is code wiring, exempt from the plugin state law (all *semantic*
  state lives in the `Environment`) — nothing a notebook can observe is
  stored here.
- **Encoders**: one per op, matching on the receiver `Obj` and producing
  the `args` JSON. A receiver outside the op's declared signature is
  `offSignature` — a `protocolError` blaming the registration, because
  routes are supposed to make it unreachable.
- **Argument validation**: receivers are shape-checked by routing;
  arguments are validated at execution. The executor is **default-deny**
  on arguments: an op takes its receiver alone unless it is explicitly
  listed as argument-taking.
- **`expectKind`**: the decoded reply must be the kind of value the op
  promises — a well-formed value of the wrong kind is an adapter defect,
  not a result. Where exact arithmetic on this side can check the answer
  against the receiver (a determinant, a charpoly's monicity, a companion
  matrix's trace/determinant, an approximation's certificate), check it.
  These checks are pure functions, `#guard`-tested in
  `CasDslTests/Core.lean` so deleting one fails the build.

## 3 · Op signatures (`OpSig`)

The executor's receiver match, restated as checked registration data:

```lean
{ backend := `sage, opId := "roots_poly_q",
  accepts := #[.elemOf (.polyOver (.exact .rat))],
  doc := …, docUrl := …, advisory := … }
```

- Registered with `registerOpSig!` in a `run_cmd`; a duplicate
  `(backend, opId)` is a build error, never a precedence question.
- `backendFn`, `conventions`, `doc` and `docUrl` are rendered by the
  diagnostics — see §7 for what belongs in each; an op naming no external
  docs falls back to the adapter source at registration.
- `advisory` is the provider's own disclosure of a choice the answer
  rides (Sage's fixed ℚ̄ ↪ ℂ embedding), appended IN NOTATION to every
  rendered result of the op — a qualifying phrase like "under a fixed
  embedding $\bar{\mathbb{Q}} \hookrightarrow \mathbb{C}$", written in
  the §7 register, never a standalone prose note. Registration data: no
  advisory text may live in `Eval.lean`.

## 4 · Executors

```lean
abbrev Executor := String → Obj → Array Obj → IO (Except ExecError Value)
initialize sageOpSigs.forM fun s => registerExecutor s.backend s.opId executor
```

Drive the executor table from the same array the signature registration
reads, so an op is executable exactly when it is declared. A pure-Lean
backend (`Native.lean`) is the same wiring with `Native.run` as a pure
function lifted into `IO` — keep it pure so every op is `#guard`-testable.

## 5 · Routes (`CasDsl/Std.lean`)

```lean
{ method := `roots, pattern := .elemOf (.polyOver (.exact .rat)),
  backend := `sage, opId := "roots_poly_q" }
```

- Registered with `registerRoute!`. `addRouteChecked` verifies at BUILD
  time that the route's pattern is implied by one of the op's declared
  `accepts` patterns — a route can never send an op a receiver shape it
  does not implement.
- Priorities break ties deterministically; a tie among applicable routes
  is an explicit ambiguity error at the call.
- A presentation with no matching route is a **structured capability
  gap** (`NoImplementation`) — the honest, auditable outcome. Do not
  widen a pattern to make a gap disappear.

## 6 · Proof obligations

Every wiring change carries its checks; the layered QC gates run them at
commit/push (`just test`, `just test-ci`):

- **Routing pins** — `expectRouted` / `expectGap` / `expectNotApplicable`
  in `CasDsl/Std.lean`'s `run_cmd` test block: which backend answers
  which presentation, and which presentations honestly gap.
- **Codec round-trip** — new value shapes join the samples in
  `CasDslTests/Codec.lean` (one of every constructor, including the
  degenerate cases).
- **Adapter round-trip** — `tests/roundtrip.py` drives the adapter
  process directly, pinning each op's wire behavior against live Sage,
  boundary cases included.
- **Product surface** — `tests/test_e2e.py` drives the installed
  kernelspec end to end; the committed notebooks are re-executed
  (`scripts/reexec_notebooks.py`) so their outputs are genuine kernel
  output — the demo as a runnable trail, boundaries with its live
  refusals.
- **Wording** — user-facing diagnostic text is pinned verbatim
  (`CasDslTests/Wording.lean`, `#guard_msgs`); a wording change is a
  reviewed product change.

## 7 · Authoring the documentation fields

Everything in these fields is **emitted text**: the diagnostics render it
verbatim to a research mathematician. The build enforces the mechanical
parts (the banned-vocabulary gate in `CasDslTests/Wording.lean` runs over
every field below), and `#explain_route`'s wording is pinned verbatim — a
field edit is a reviewed product change.

**The register.** Write LaTeX prose with inline math (`$…$`). Rendered
surfaces typeset it; plain-text surfaces show the source, which a
mathematician reads fluently — so the text must read acceptably both ways.
State mathematics in notation, never in prose paraphrase ("$x =
u\prod_i p_i^{e_i}$", not "a unit times prime powers"). No caps-as-emphasis,
no internal vocabulary, no project-management language; an unimplemented
case is a capability ceiling and must never be worded as mathematical
undefinedness.

**Placement — the generality rule.** Every sentence lives at the widest
level where it is true:

- `MethodDecl.doc` — the general mathematical statement of the operation,
  at the declaring category's generality. The worked example:

  ```
  for $x \in R$ a UFD: a factorization $x = u\prod_i p_i^{e_i}$
  with $u$ a unit, each $p_i$ irreducible and $e_i \geq 1$
  ```

  Nothing receiver-specific may appear here.
- `MethodDecl.conventions` — presentation choices true at the same
  generality ("stated up to units"). A convention chooses presentations,
  never the value of a well-defined predicate.
- `MethodDecl.advisory` — the template for an unexpected-but-true result,
  `{…}` placeholders filled by the method's own semantics.
- `OpSig.backendFn` — the REAL function the backend runs
  (`Integer.factor()`), which is what the diagnostics display; the wire
  `opId` is bookkeeping and never user-facing.
- `OpSig.conventions` — the receiver-specific presentation choices that
  motivated the op ("the unit is ±1, with all prime factors positive";
  "factors are monic; the unit carries the leading coefficient"). This is
  where per-ring normalization lives, never on the method.
- `OpSig.docUrl` — the EXTERNAL documentation of `backendFn` (the Sage
  reference page), verified to exist. Never a link back into this
  repository — the reader already knows the provider; an op naming no
  external docs falls back to the adapter source at registration.
- `Route.doc`/`Route.docUrl` — only for what the *binding* means beyond
  the op itself; usually empty.

**How it renders.** `#explain_route` shows: the availability path as an
arrow chain (`$360 \longrightarrow \mathbb{Z} \longrightarrow
\mathrm{EuclideanDomain} \longrightarrow \dots$` — arrows, because
availability is a path of functors, not subcategory containment), then
`method ≐ anchor: doc — conventions`, then `via backend, backendFn —
op conventions` with the docs link, then the result shape. The notebook
receives it as markdown (typeset math, clickable docs); plain contexts get
the same sentences as text.

**The anchor discipline (guideline).** Categories carry anchors as checked
registration data: a `CatDecl` names the category it means in Mathlib
(`ModuleCat`, `FintypeCat`), or the constant defining it where Mathlib
holds no name, and registration refuses the entry otherwise. For methods
the discipline is judgment: the anchor may not carry stronger
hypotheses than the declared generality of its home: `Polynomial.roots` is
the IsDomain *carrier* of an any-commutative-ring meaning, and citing
`EuclideanDomain.gcd` for a UFD-level declaration was an algorithm posing
as a meaning. This is judgment, not automation — though its mechanical
core (the anchor constant elaborates at the declared generality) is an
ordinary typecheck if a gate is ever wanted.
