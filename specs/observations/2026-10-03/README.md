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

The cached polynomial runner records the same ordinary assertion twice on one
live harness. Both observations hold. Its five actual request/reply records
contain four calls for the first observation and one fresh equality call for the
second; cached computational values do not fabricate dispatch evidence. The
runner used math 01b44cd and contract bcd4721 with native leaf 4f4ad334. This is a
focused execution capture, not an immutable full-baseline snapshot.
