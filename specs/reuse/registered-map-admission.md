# Registered admission of complete map parameters

`DeclaredAdmission` consumes an existing `ObjectEntry.admission` and its registered
evidence procedure. The complete demanded type determines the declaration's full
dependent arguments. The planner compares every applicable registered domain;
registry order supplies no preference, and an unresolved data argument supplies
no candidate.

## Selected endpoints and dependent parameters

A map expression retains its original source and target objects while its body
is read on their declared carriers. When the registry supplies admission into
their exact Hom type, the reader uses that admission and checks its independent
proof obligations. The source category bundle includes its actual dictionary,
so equal underlying carriers cannot select a different scalar action or category.

An ordinary function or map of sets used as a declaration parameter is read at
its given signature directly. Adding a constrained-function domain to the
registry cannot introduce a new condition on that ordinary parameter.

A structured parameter may use the same registered admission when its demanded
type is a data projection of the admitted value. The projection path is limited
to fixed, nonrecursive records with one data field and proposition-valued
remaining fields. All dependent parameters must close from the demanded type.
The actual projection expression must have that exact type. A record with two
data fields supplies no implicit projection.

For example, the independently registered module-morphism domain has the actual
type `M ⟶ N`. A declaration requiring its underlying `LinearMap` consumes the
existing single data field of `ModuleCat.Hom`. This is a check on the full declared
record and its projection; the reader contains no module-specific constructor,
linearity procedure, or field-selection rule.

Destructured inputs similarly use declared component maps. The given complete
domain may determine all parameters of a registered component family even when
the domain has no separate named object row. The reader checks its arity and
every projection's exact source. It retains the original domain rather than
giving it the component family's object name.

## Explicit proofs

For `value in Domain using (proof(...))`, a named registered domain uses its own
admission interface. Each independent proof is elaborated against the actual
obligation after the original data and dependent parameters are fixed. The
proof must be closed and accepted by Lean; extra proofs are rejected. A missing
explicit proof uses only the domain's registered evidence procedure.

The existing unnamed constrained-record constructor path remains available for
complete targets without a named admission. A named admitted family is not
reinterpreted as an anonymous record because its implementation unfolds to one.

## Computational reuse

The original map remains attached to the admitted point through the existing
`admittedPoint`, `element`, and `point` data frames. The public structural codec
already omits proposition fields and unwraps records with one data field. A
checked projection through those wrappers therefore retains the same actual
computational data and its owning session. It does not reconstruct a proof from
the backend's value or replace that value with a formal representative.

Observing a complete callable follows this retained point to its original map.
The existing complete operation request materializes that map, and the result is
cached before rebuilding admitted wrappers and later declared actions. A later
computation consequently consumes the returned callable, including any opaque
session-owned data.

## Engineering checks

`CasAcceptance/Kernel/RegisteredMapAdmissionProbes.lean` checks full Hom planning,
ordinary function parameters without extra conditions, exact category retention,
typed destructured parameters, rejection of arbitrary multi-field projections,
and reuse of the actual cached opaque point through a projected parameter.

`WholeOperationObservationProbes.lean` exercises the actual process interface for
complete operation materialization. `FixedQuestionExecutionControls.lean` uses
the unchanged independently specified reindexed question for the six execution
outcomes and live, foreign, expired, and newly established session observations.
These engineering checks do not alter the mathematical assertions or supply
their expected answers.
