# Contribution references

**Work priority:** required functionality has absolute priority over performance. Performance work is the last phase of this project and begins only when every required capability works through the public interface. A slow run, timeout, resource budget or red CI job does not select work and does not block functional work. [Full rule](https://github.com/dzackgarza/lean-cas-dsl/issues/10#work-priority).

- [Permanent constitution and independent-author/input boundaries](.specify/memory/constitution.md)
- [Current FR-012–FR-015: independent formalization and computation-only leaves](https://github.com/dzackgarza/lean-cas-dsl/issues/10#issuecomment-6660532064)
- [Current source contract: actual cells, allowed choice data, mandatory errors and separate responsibilities](https://github.com/dzackgarza/lean-cas-dsl/issues/66#issuecomment-6664276482)
- [Released computational-interface design and public-only handoff boundary](https://github.com/dzackgarza/lean-cas-dsl/issues/69#issuecomment-6664277464)
- [Contribution policies and permitted inputs](https://github.com/dzackgarza/lean-cas-dsl/issues/85#issuecomment-6574924066)
- [Architecture, ownership and evidence](https://github.com/dzackgarza/lean-cas-dsl/issues/10#issuecomment-6574949858)

The linked policies determine which inputs each author may receive. The rules below apply to
implementation contributions; the released leaf contract retains its own owner.

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

Explain the required mathematical relationship and its retained computational association in the
change's rationale. Verification must distinguish structural transport checks from mathematical
correctness and independent acceptance. Documentation of a requirement does not establish its
implementation. An upstream formal gap is reported to its owner under the existing independent
input rules; a downstream repair cannot invent the missing theorem or definition.
