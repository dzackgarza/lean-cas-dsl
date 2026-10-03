# Observed connected polynomial computation

An independent root rerun of the ordinary DSL assertion in `polynomial-reuse.lean`
returned `ExecutionOutcome.holds`. The full dispatch capture retains actual requests,
responses, connection identity, and input owners. Factorization returns token1; product
consumes that token and returns token2; degree consumes token2; equality observes the
returned degree. Native Sage performs these computations.

This is one connected assertion, not acceptance of B0, the original suite, or the
strengthened shipping workflows. The returned-factor binder and structured-result
integration remain unfinished. No original assertion or acceptance inventory changed.

`polynomial-reuse-context.json` identifies source and compiled artifacts, exact consumed
mathematical and contract revisions, and the leaf revision. Producer sources were frozen
but not yet committed at the time of the run; the recorded hashes are after-run evidence,
not a claim of a paired immutable snapshot. The runner uses the existing cloud activation
and leaves manifest. It writes raw observations under `/tmp` and creates a fresh harness.
These observations do not add a completion gate or certify other backend answers.
