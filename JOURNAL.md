# Journal

Process narration lives here, not in chat: what was done, what was found, what is pending and on
whom. Chat carries only what needs the owner's action or decision. Newest entry first; one entry
per working session; terse. Not an authority: rules live in their owning documents (AGENTS.md).

## 2026-10-01 (orchestrator, session_01SKJ21csPEAnJmemqQztSVD)

State: integration branch `b0/construction` (head after this commit) carries #59 (stage A
kernel), #60 (B0 documents), the gate correction (`partial def` ratchet, kernel-totality gate
withdrawn) and the construction mandate. #59 and #60 are superseded vehicles; their branches are
kept.

Done:
- Stage A source: registry reader in the kernel; one outcome model; suite out of compilation;
  `scripts/check_acceptance_regression.py` (new failing assertion fails; missing report fails);
  export checked as a faithful projection of the registry state and against upstream's catalogue
  root (`LeanCategories.Catalogue`). No Lean change since `da209f5`; CI full build and
  acceptance-vs-base passed at `7dc2d7c`.
- Controller: construction-aware `prompt.md`; `review.py` phase from base `custodian/phase.json`,
  typed outcomes, outage ≠ rejection, mandate + context + explanation inputs, batches,
  reconsideration; `verify.py --construction`; workflows; authorship gate maps `custodian/` to the
  orchestrator in construction. `test_review.py`: 49/49 on a scratch copy.
- Documents: construction mandate (architecture.md), AGENTS.md "Current task: construct B0",
  CONTRIBUTING "Documentation and construction work", plan stage A. "You have no memory" deleted
  on a retracted instruction, then restored (`ce0ad81`).

Pending:
- Ruleset `ecustodian-main` (id 24252144): drop `pull_request`, `required_status_checks`; keep
  `deletion`, `non_fast_forward` (custodian/SETUP.md). Needs repository administration; refused to
  this session ("Write access to this GitHub API path is not permitted through this proxy").
  Then fast-forward `b0/construction` onto `main`.
- #59 "Build and audit": semgrep's exception lookup for the known `pull_request_target` finding hit
  GitHub's rate limit (403); one re-run queued (run 36893318437).
- Next construction work: stage B (`b0-typed-application`) once stage A is on `main`.
