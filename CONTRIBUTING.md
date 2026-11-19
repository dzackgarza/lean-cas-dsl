# Contribution references

- [Permanent constitution and independent-author/input boundaries](.specify/memory/constitution.md)
- [Current FR-012–FR-015: independent formalization and computation-only leaves](specs/001-categorical-research-language/spec.md)
- [Current source contract: actual cells, allowed choice data, mandatory errors and separate responsibilities](specs/001-categorical-research-language/contracts/mathematical-input.md)
- [Released computational-interface design and public-only handoff boundary](specs/001-categorical-research-language/contracts/computational-runtime.md)
- [Contribution policies and permitted inputs](https://github.com/dzackgarza/lean-cas-dsl/issues/85#issuecomment-6574924066)
- [Architecture, ownership and evidence](https://github.com/dzackgarza/lean-cas-dsl/issues/10#issuecomment-6574949858)

The linked policies determine which inputs each author may receive. The rules below apply to
implementation contributions; the released leaf contract retains its own owner.

The maintained [mathematical execution model](specs/architecture.md) reconstructs the *owner's* intended category-level software encapsulation, not merely a set of prohibitions. A category-aligned computational leaf may realize multiple accepted **constructors, common methods and immediate functor actions**, whereas one manifest `(operation, input form, backend)` is a **computational registration**, not the category itself. For the owner design statements in summary, see [#91 source A](https://github.com/dzackgarza/lean-cas-dsl/issues/91#issuecomment-6942015918), [formal contract B](https://github.com/dzackgarza/lean-cas-dsl/issues/91#issuecomment-6942060158), and [current implementation map C](https://github.com/dzackgarza/lean-cas-dsl/issues/91#issuecomment-6942116552). They are source input for the requirements, not a new acceptance process.

## Mathematical implementation rules

Read [the execution model](specs/architecture.md) before designing a fix. These rules apply C23;
they do not grant kernel or leaf authors authority to create missing mathematics.

| Rule | Required contribution | Defective substitute |
| --- | --- | --- |
| MATH001 | Name the source declaration, formal domain, selected data and consuming continuation. | Start from a backend class or serialized shape. |
| MATH002 | Compute functor targets through public object and morphism constructors; use the resulting target interface. | Add private cross-leaf conversions or per-source forwarding methods. |
| MATH003 | Derive inherited applicability from the accepted composite and its comparisons, including arrow actions. | Select the shortest or first registered route, or equate routes by endpoints. |
| MATH004 | Apply the declared classifier refinement using its evidence; retain any selected structure. | Infer mathematical membership from a list, or treat existence as a chosen basis. |
| MATH005 | Repair the boundary that lost a selected occurrence, endpoint or cone and update its consumers. | Recover a candidate by equal expressions, registry scans or apex recognition. |
| MATH006 | Prepare dependent inputs from their formal interface and route every public call through common preparation. | Add a named-construction runtime algorithm or a separate deferred-call interpreter. |
| MATH007 | Preserve the unchanged public mathematical workload and independent extension consumer. | Replace it with an opaque provider, helper assertion or dispatch count. |
| MATH008 | Consume new accepted declarations through the same generic kernel; run the prescribed extension trials against their frozen kernel, contract and old consumer. | Add a recognizer or repair an old leaf to accommodate the trial. |

Explain the required mathematical relationship and its retained computational association in the
change's rationale. Verification must distinguish structural transport checks from mathematical
correctness and independent acceptance. Documentation of a requirement does not establish its
implementation. An upstream formal gap is reported to its owner under the existing independent
input rules; a downstream repair cannot invent the missing theorem or definition.

## Focused development

Use the repository's selected toolchain and dependency tuple. Dependency refresh and SDK setup
are explicit actions; an ordinary source build does not change them.

| Command | Purpose |
| --- | --- |
| `just setup-sdk` | Provision the pinned contract SDK environment once before protocol tests. An explicit contract path may be supplied. |
| `just focus TARGET` | Build the changed Lean target once, streaming its diagnostics and preserving its exit status. |
| `just probe FILE` | Run a temporary Lean probe after Lake rebuilds its imports. |
| `just build-production` | Build the connected `CasRuntime.Session` production closure without compiler/runtime test modules. |
| `just test-compiler` / `just test-runtime` | Run the separate compiler/runtime test targets. |
| `just profile TARGET` | Request a separate diagnostic profile when that measurement is needed. |

After a focused change, rebuild its affected public consumer and exercise the same mathematical
input and continuation. Protocol peers check framing, dispatch, retained values and lifecycle;
the original mathematical workload still uses its independently supplied computations and
assertions. A cached elaboration is not a fresh external execution.

Keep checked source declarations below runtime state, specialized source rules below reader
assembly, and transport/lifecycle mechanisms below source lowering. Narrow public imports from
their actual exported types and executable dependencies; do not mechanically make every import
private or split a genuinely recursive mechanism merely to reduce file size. Test provisioning
belongs in the explicit setup command, never in `run_cmd` or a production import.

The ordinary build has no profiling prerequisite or automatic second profiling run. Functional
development may use the limits it needs under C21; the original final mathematical budgets are
unchanged. Any claim of a faster feedback loop must compare one actual functional edit at fixed
dependencies and inputs, including the affected rebuild and original public result. That
measurement does not replace the remaining functional work or its independent acceptance.

The runtime session imports the source-session API from `CasCompiler.ReadSession`.
Standalone `cas_source%` notation is exported by `CasCompiler.Read` and the `CasCompiler`
and `CasRuntime` aggregate modules; importing the narrow `CasRuntime.Session` module does
not export that notation elaborator or its executable import dependencies.
