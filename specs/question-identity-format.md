# Reading exported semantic questions

This document describes the existing public `question` field emitted by the
interpretation exporter and execution report. It does not introduce a second
question representation or an acceptance baseline. The interpretation exporter
does not load computational registrations, evaluate answers, or accept a
mathematical reading.

## Envelope and source provenance

Each exported reading has `file`, `id`, `sourceLine`, `question`, and
`proposition` fields. `sourceLine` is the original one-based line, or zero for
an inventory-only record without an identified source item.
The `question` string contains two complete JSON term tables:

```text
<claim kind>:<claim table JSON>:operations:<operation table JSON>
```

Claim kinds are `literal`, `homs`, `implemented`, `decision:true`,
`decision:false`, `judged:true`, and `judged:false`. Parse each JSON value as
JSON; do not split strings that occur inside it. Each table is an object with
`roots` and `terms`. A term reference is a zero-based index into that table's
`terms` array. The two tables have separate index spaces. They contain the
actual descriptions, not cryptographic digests.

There is no independent numeric schema-version field in this existing format.
The producing source revision identifies its representation. An assessment
must retain the actual kernel, contract, mathematical source revisions and
trees, toolchain, ordered imports, package selection, and resolved module
artifacts. The export failure report records imports and module paths. Those
paths and the historical dependency label in an interpreted request do not
authenticate the sources used to build an artifact; record that provenance
separately.

`proposition` is a human-readable display. It can omit implicit arguments or
use notation. All typed arguments needed for a structural comparison are in
the complete `question` payload; display equality alone is insufficient.

Every required inventory ID receives a reading. An unsuccessful interpretation
has empty question/display strings and a separate diagnostic with `file`,
`id`, `sourceLine`, `source`, `stage`, `kind`, `detail`, and completed-stage
observations. A failed
unnamed binding is identified in the diagnostics by its original source file
and binding name. A missing complete reading is an open obligation, not an
accepted migration or an omitted denominator.

## Typed term tables

Each term node is an array. Except for literal data described below, numeric
children are term references in the same table.

| Tag | Remaining fields, in order |
| --- | --- |
| `sort` | Universe-level syntax |
| `const` | Complete Lean declaration name, ordered universe-level arguments |
| `app` | Function, argument |
| `lam` | Domain type, body, binder information |
| `forall` | Domain type, body, binder information |
| `let` | Type, value, body, nondependent-let flag |
| `bvar` | De Bruijn index, as an integer rather than a term reference |
| `proj` | Structure declaration name, field index, structure value |
| `literal` | Lean literal representation |
| `proof` | Complete proposition type of the proof |

Universe levels have tags `zero`, `succ`, `max`, `imax`, and `param`, with
their corresponding ordered level children or parameter name. A completed
question has no unresolved term or universe metavariables, free local
variables, or escaping bound variables.

Metadata and binder spelling are omitted. Proof implementations are represented
by their exact proposition types. Selected computational data occurring in
those propositions remain present. No reduction by truth, provability,
logical equivalence, equal carriers, or coincident endpoints is part of this
representation.

For the first five claim kinds, `roots` is `[term, type]`. For `judged` claims,
it is a recursively structured question:

| Root tag | Remaining fields |
| --- | --- |
| `proposition` | Proposition term reference |
| `judgement` | Relation name, ordered operand references, ordered route, ordered declaration names, ordered operand-type references |
| `and` | Left question, right question |
| `not` | Negated question |

The expected truth orientation remains in the `decision` or `judged` prefix.
An expected equality operand remains an operand of the original typed claim;
it is not replaced by the observed runtime answer.

## Retained operation table

The operation table's `roots` is an array of `[term, operation]` pairs.
`term` identifies the complete formal result whose operation is retained.
Multiplicity is preserved. This outer collection has a canonical comparison
order; it is not an execution schedule. Order inside parameter arrays, routes,
constructor paths, comparison stages, operands, and lift lists is meaningful.
Dependencies refer to complete formal terms in this same table, allowing a
reviewer to follow the actual previously selected maps and results.

In the following table, names such as source, target, receiver, proof, or body
denote typed term references; IDs, route labels, flags, and field selectors are
literal metadata. A category context is `[category expression, bundle]`, with
the bundle a complete typed term. An ordered parameter list contains typed
term references.

| Operation tag | Remaining fields, in order |
| --- | --- |
| `object` | Object ID, parameters |
| `parameterTransport`, `structureTransport` | Source ID/category, source category when applicable, target category, route, receiver |
| `proofRefinement` | Classifier ID, source category, target category, source, action, identity |
| `parameterEquivalence` | Expected parameter, representative, complete presentation records |
| `retainedRoute` | Source category, target category, route, applications, receiver |
| `namedMorphism`, `namedCallable` | ID/address, category for callable, parameters |
| `admittedPoint` | Object ID, category, parameters, original point, original category, source, target |
| `constrainedPoint` | Constructor, category, original domain, source, target, original point |
| `powerObjectMap`, `objectField` | Object ID, field, category for object field, parameters |
| `namedInclusion` | Object ID, category, parameters, source, target |
| `callableRecipe` | Category, domain, target, body |
| `presentation` | Presentation ID, parameters, inverse flag |
| `generator` | Object ID, parameters |
| `elementNumeral` | Numeral data, target, selected element |
| `elementValue` | Original point, target, selected element |
| `productMediator` | Category, product presentation, domain, left map, right map |
| `morphismComposition` | Category, first map, second map, source, middle, target |
| `morphismIdentity` | Category, object |
| `contextualRoute` | Source context, target context, route, applications, receiver, morphism flag |
| `contextualComposition` | Context, first map, second map, source, middle, target |
| `contextualIdentity` | Context, object |
| `contextualArrow` | Context, actual morphism, source, target |
| `arrowProjection` | Receiver |
| `limitProjection` | Receiver, index term |
| `structuredProjection` | Receiver, field selector, component index |
| `pointView` | Source, target, route, applications, argument |
| `operationPoint` | Operation ID, parameters, comparison, operation, target, selected element |
| `operationApply` | Operation ID, parameters, operands, target, selected element |
| `presentationApply` | Presentation ID, parameters, inverse flag, source, target, argument |
| `morphismTransport` | Source category, target category, route, receiver |
| `functor` | Functor ID, parameters, receiver |
| `categoryParameter`, `functorParameter` | ID, parameters |
| `cartesian` | Functor ID, parameters, base morphism, receiver, field |
| `construction` | Construction ID, parameters, receiver |
| `constructionMap` | Construction ID, parameters, source, target, actual morphism |
| `coreObject` | Category context, object |
| `coreIso` | Category context, source, target, forward map, backward map |
| `selectedLift` | Lift ID, parameters, source, actual inclusion, monicity proposition |
| `liftProjection` | Receiver, field |
| `liftFactor` | Receiver, actual base map, original cone, compatibility proposition |
| `cellComponent` | Cell ID, parameters, constructor path, inverse flag, receiver |
| `cellEndpoint` | Cell ID, parameters, constructor path, inverse flag, right-endpoint flag, receiver |
| `binder` | Binder ID, parameters, original domain, entire body, admitted family |
| `arrow` | Category, actual morphism, source, target |
| `literal` | Form ID, literal term |
| `method`, `property` | ID, route, receiver |
| `methodWithLifts` | Method ID, route, ordered lift IDs, receiver |
| `limit` | Limit ID, complete diagram, optional lift ID |

Each parameter-presentation record contains source ID, source category,
target category, parameters, route, applications, carrier route,
identification declaration names, original object, image, and identity, in
that order. These are complete records, including distinct records that
share the same initial source/route/parameter key.

## Independent comparison

An independent reader may renumber table indices and reorder JSON object
members while preserving the entire referenced DAG and every meaningful
array order. It must compare the original mathematical question against its
independent specification, including previously unreadable questions. A
revision label, equal display, successful execution, stable serialization,
or equal truth value supplies no such judgment.

Computational ownership, process IDs, returned values, and execution failure
conditions are separate observations. Changing a computational manifest does
not change the interpreted question. Removing a mathematical comparison cell
does change the available interpretation environment: both unresolved route
candidates must survive a semantic ambiguity, rather than acquiring a
fabricated completed question.
