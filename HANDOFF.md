# B0: remaining work

## Ambient task

Complete the existing B0 proof of concept against the unchanged requirements in
[INTENT.md](INTENT.md), [architecture.md](specs/architecture.md), and the
[B0 acceptance table](specs/computational-core-plan.md). Establish the whole mathematical
language and its required computations at one coherent candidate, with complete question
preservation, independent extension trials, compositional arguments and independent acceptance.
Finish functional capability and integrated execution; latency optimization is not the objective.

The assignment is paused. Resume construction only on an owner instruction. Kernel/controller
source integration does not authorize its author to install an authoritative evaluator or accept B0.

## Completion condition

Every row below is mandatory. Verification must refer to the same candidate and recorded
latest-main dependency inputs. An isolated specimen, compilation, source review or fingerprint
comparison establishes only its own narrow result.

| Required item | Acceptance condition | Verified status at construction candidate `4bc36b6` |
| --- | --- | --- |
| Complete semantic inventory | Every identity in `CasAcceptance/Permanent/admitted.json` reads as its complete mathematical question. Retain failures and unreadable assertions in the denominator. | Not established; no complete current-candidate inventory report. |
| Composition, application, admission and binders | Complete generic mechanisms satisfy their full positive and protected-negative obligations, retaining dependent types, domain restrictions, supplied evidence and binder identity. | Full integrated acceptance remains unverified. |
| Parameters, selected structures and refinement | Retain complete parameters, chosen maps and structures, including distinct structures on one carrier. Refinement gains only a formally justified interface and keeps its original data. | Full integrated acceptance remains unverified. |
| Structured results and subsequent operations | Return complete structured objects and defining maps; execute every prescribed lift field and compose lifts; subsequent operations consume the actual retained result data. | Full integrated acceptance remains unverified. |
| Presentation and coherence transport | Use the prescribed nonidentity comparison and its actual maps. Preserve distinct routes and report unresolved ambiguity. Use admitted comparisons explicitly. | Incomplete; constructed coherence and the alternate-route transport argument remain unresolved. |
| Required registered computations | Every frozen ID listed below holds through the registered execution path. Proof discharge cannot replace required execution. | Not established at this candidate. |
| Required positive examples | Independently authored assertions establish the listed ranks, group kernels/properties, formed-module cardinality and F9 transport through required execution; retain their protected negatives. | Complete same-candidate outcomes remain unverified. |
| Failure interfaces | Preserve semantically invalid, NoImplementation, unavailable/crashed, malformed and wrong-answer outcomes. Ambiguity and internal interpreter errors remain distinct; timeouts are not invalidity. | Complete same-candidate verification remains outstanding. |
| Complete question preservation | Independently assess every admitted question, including parameters, selected structures, maps, relations, logical forms, routes, binders and proof proposition types. Assess meaning-preserving proof/encoding changes independently. | Incomplete; existing bounded assessments are not a full accepted migration. |
| Independent extension trials | Satisfy every mechanism listed below at a frozen kernel, contract and old leaves. Contributors choose the concrete extensions. A needed kernel or old-leaf change fails that trial and requires repair, re-freezing and repetition. | Not established. |
| Compositional arguments | Establish the required general arguments as well as examples. Account for route-enumeration completeness, constructor-induced cells and nonidentity transport. | Incomplete; source boundaries are recorded in `custodian/FINDINGS.md`. |
| Build, boundaries and protected judgment | Meet gates A/B/C and same-candidate protected negatives; enforce the formal/leaf firewall and independently protected authoritative transitions. | Complete candidate acceptance remains outstanding. |
| Final independent acceptance and release | Obtain protected independent B0 acceptance and reconcile the published source, resolved inputs and hosted checks at the actual revision. | Outstanding. |

**Frozen registered-execution IDs:** `sets.card.z4_cubed`, `sets.card.z7`,
`sets.card.z5_empty_power`, `sets.card.fin2_times_z3`, `sets.card.integers`,
`sets.finite.integers`, `sets.finite.fin2_times_z3`, `sets.implemented.card_fin`,
`sets.card.fin2_sqcup_fin3`, `sets.eq.rev_rev`, `sets.limit.pullback.card`,
`finite_sets.limit.pullback.card`, `lattices.discriminant.a1`,
`lattices.discriminant.a2`, `lattices.discriminant.a3`.

**Required positive scope:** rank of A2 and E8; kernels of the sign map, trivial map and
identity of S3; C3 abelian and S3 nonabelian; finite-product refinement; formed-module cardinality; F9 transport.
The acceptance author owns their assertions and admission. Preserve the current independently
authored proposal and its sources in `tests/acceptance/b0-required-positives.cas.proposed`.

**Independent trial scope:** new structured object; new generic operation reaching old objects;
generic group-valued construction; classifier/refinement; competing structural routes;
parameter/base transport; nonidentity presentation change; structured-result lifting;
generic application/admission/binder; leaf replacement with missing, wrong, malformed and
unavailable implementations. Both directions of extension are required. Leaf replacement must
leave mathematical meaning, types and operation availability unchanged.

**Permitted gaps and exclusions:** `NoImplementation` is allowed only outside the required
computational subset. Every admitted assertion still requires valid semantic interpretation and
complete question assessment. A missing lift computation may be reported as a named gap where
the trial permits it; it cannot satisfy a required positive computation. Engine absence is an
execution dependency, not a permitted stub. Notebook reconstruction is deferred; new mathematical
coverage, production leaves and notebook features remain outside B0 under their existing dispositions.

The semantic authority is `lean-categories`; the kernel consumes it and authors no mathematics.
Leaves provide opaque computations, ship no mathematics or Lean, and supply no correctness evidence.
Permanent leaf-blind acceptance assertions are the correctness evidence. Keep formalization,
acceptance and leaf authors in their assigned roles and permitted inputs. The kernel author neither
writes upstream mathematics nor commissions it from downstream failures. Candidate output cannot
regenerate authoritative expectations or approve its own interpretation/evaluator changes.

## Ranked next work

### 1. Establish the complete current-candidate outcomes

Verify the source before believing any status above. The construction code is at
`4bc36b61e15ac2bd0abab2a48317d1423ee1b0fe` on
`b0/poc-independent-role-integration`. Use
`/home/dzack/gitclones/lean-cas-dsl-functional-repair` for its compiled cache, or
`/home/dzack/gitclones/lean-cas-dsl-poc-independent` for the integration branch.
Check each checkout's revision, dirty state and code differences against that candidate;
documentation checkpoints do not identify a different verified runtime.

Preserve the unrelated `CasCatalogue/Language.lean` changes in the original
`/home/dzack/gitclones/lean-cas-dsl` checkout. Compare them with
`/tmp/b0-poc-32c3897/original-language-restored.patch` before any operation affecting that file.

Inspect `/tmp/b0-poc-4bc36b6/source-inputs-before-native.json` and
`loaded-artifact-hashes-before-native.json` for the exact input/artifact references.
`/tmp/b0-poc-4bc36b6/harness.json` is empty and supplies no inventory outcomes.
Verify those facts from disk. Refresh own-organisation dependencies to latest main before the
next build/run, record the actual revisions, and keep source/dependencies/artifacts fixed during
execution. Historical revisions are references, not pins.

Run the complete unchanged admitted inventory through the actual installed registrations with
proof discharge disabled. Use a fresh report path and retain every result:

```bash
just track-main
lake build cas-harness
CAS_SAGE_PYTHON=/home/dzack/.local/bin/sage-docker-python \
CAS_GAP_PYTHON=/home/dzack/gitclones/lean-cas-dsl/.venv/bin/python \
lake exe cas-harness --computation-only \
  --report /tmp/b0-poc-4bc36b6/resumed-inventory.json \
  > /tmp/b0-poc-4bc36b6/resumed-inventory.log 2>&1
```

Check every admitted identity, its full question/proposition and outcome, plus the required
computations' actual dispatches. Then run the unchanged required-positive proposal through
production `#cas_tests ... computing`, with all its original bindings and a separate report.
The proposal's entire required scope must be assessed, not only its F9 or product specimens.

### 2. Repair the generic mechanisms that prevent those outcomes

Use actual per-assertion failures and the full completion table to select work. Retain each
original failing assertion and its same-candidate protected negatives. Reuse existing mechanisms;
keep expected answers, mathematical requirements and assertion inventory fixed.

Resolve the compositional bounds in `custodian/FINDINGS.md` and the governing plan:

- Kernel calls currently inherit public `SemanticState.routes` fuel 32. Establish complete
  enumeration for the admitted route semantics; increasing a constant is not a completeness argument.
- `Resolve.comparisonsFrom` handles exact route segments. The inspected constructor interface
  supplies action on functors but no general constructor-induced cell action. Keep its dependent
  consumer open until the required accepted input/mechanism exists; continue independent work.
- Distinguish explicit `CellSyntax` component application from ordinary execution along a selected
  route. Establish the required alternate-route/nonidentity transport path rather than infer a
  runtime defect solely from discarded comparison IDs.

A source-level proposal is not an implemented or accepted correction. A missing accepted input
blocks only its consumers. Follow the repository's focused-build/profile rules for necessary
checks; do not raise heartbeats, weaken assertions or select a new hotspot because a slow check passes.

### 3. Establish full preservation and candidate validation

Give the acceptance author opaque complete questions and their independently fixed sources,
without leaf code or runtime outcomes. Cover every admitted identity. Reuse existing assessments
only when their exact inputs and scope apply. Assess changed meanings separately from proof noise;
never replace authoritative records with candidate-generated baselines.

At a meaningful committed candidate, run the full required integration gate and protected
negatives. Evaluate the completion table against actual behavior, not compilation or stable hashes.
Keep any unresolved mathematical input, semantic ambiguity, interpreter error and realization
failure separate.

### 4. Freeze and obtain independent B0 acceptance

After the generic mechanisms meet their obligations, freeze the kernel, contract and old leaves.
Run all independently chosen trials above and establish the compositional arguments. Repair and
repeat failed trials at a newly frozen candidate. Obtain independent protected judgment under
`custodian/SETUP.md`, then verify the final release against its exact hosted revision.

**Retired lanes:** reader/encoder latency optimization as the next objective; proposed subsecond
budgets as B0 gates; staged dependency pins or re-pin sequences; specimen-specific kernel behavior;
assertion/expectation changes to fit an implementation; source integration treated as evaluator
activation or B0 acceptance. The next obligation is the complete POC, not another local optimization.
