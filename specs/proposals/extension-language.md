# PROPOSAL, not adopted: the permitted extension language (convergence process, step 2)

Status: proposed by the orchestrator on 2026-09-30. It is not in force. It takes effect only when
someone other than the orchestrator accepts it at the step 7 boundary (the custodian,
`custodian/containment`). Until then the current interfaces stand. This file changes no
obligation in `specs/owner/convergence-process.md`.

## Method

For each contributor, the input it receives, the only things it can submit, and for each form the
authority it carries. An authority that made a historical failure possible is removed from the
interface. A post-hoc check that rejects it is not enough.

## Leaf (current interface: `CasContract/Adapter.lean`, `LeafContribution`)

| Finding | Authority it grants | Proposed change |
| --- | --- | --- |
| `LeafContribution` has constructors for the forbidden moves: `category`, `method`, `property`, `subcategory`, `forgetfulRoute`, `identification`, `coercion`, `refineObject`, `resultClass`, `genericSemantics`, `naturalTransformation`. Each can be written and is then rejected by `LeafContract.check` | The interface expresses every historical bad move. Containment rests on a list of rejected constructors that the orchestrator maintains and can shorten | Delete the forbidden constructors. The leaf-facing type contains only realization forms, so the moves are unrepresentable rather than rejected. The negative probes become statements that the type has exactly the permitted constructors |
| `ImplementationEntry.trust` is declared by the leaf and checked against its evidence type (`validateImplementation`) | A self-declared epistemic label, consistent today only because a validator the orchestrator owns checks it | Remove the field. The status is a function of the evidence type (`TrustedImplementation` → trusted assertion, `CertifiedImplementation` → certificate-checked) |
| `RealizerEntry.category`: the leaf names the category it realizes | Bounded: the denotation must typecheck into that category | Keep. The category follows from the denotation's type, so the field could also be derived |
| `backendOperation` decodes an untrusted answer into the operation's semantic result type | Allowed computational failure (a wrong answer), not a semantic change | Keep |
| `presentation`: `Σ h, d.obj h ≅ X` | Before contract `9644884` a handle could be returned beside an iso that was not about it | Keep, with the dependent type checked (`core-presentation-dependent`, build pending) |
| Several realizations of one operation | Resolved by explicit `using` or reported ambiguous. The step 3 argument that installation order can never decide this is owed | Keep; the argument is owed |

## Formalization (lean-categories)

| Finding | Authority | Proposed change |
| --- | --- | --- |
| The registry validator (`LeanCategories/Catalogue/Registry/`) is written by the orchestrator | The consumer of the mathematics decides which mathematics is admissible | The validator is part of the trusted core (step 7). The orchestrator may propose changes; it cannot accept them |
| The formalization agent receives prompts written by the orchestrator | Implementation needs reach formalization (2026-09-30: kernel goal shapes sent upstream) | Formalization input is the mathematical requirement and its sources only (step 5). The orchestrator relays a requirement's location. It does not author its content |

## Kernel

| Finding | Authority | Proposed change |
| --- | --- | --- |
| `Semantic.lean` reads no realization rows (checked 2026-09-30 by search) | — | The step 3 property "replacing every leaf leaves meanings, types and operations unchanged" is owed as an argument from module boundaries: the semantic reading's imports and the registry fields it reads |
| Leaf rows and semantic rows live in one `RegistryState` | A future semantic path could read a realization row without any interface change | Split the state types so that the semantic reading cannot be passed realization rows |
| `establish` runs registered evidence (`1fbcd5c`); `CasGates.KernelPurity` is the orchestrator's | See `specs/architecture.md`, "The orchestrator is inside the threat model" | Part of the trusted core under step 7 |

## Acceptance

| Finding | Authority | Proposed change |
| --- | --- | --- |
| Permanence protects assertion text; the orchestrator owns the interpretation | Meaning changes silently with the kernel | `gov-meaning-permanence` |
| Acceptance subagent prompts are written by the orchestrator | The orchestrator can supply expected answers | Acceptance input is the accepted mathematics and the language specification only (step 5) |
