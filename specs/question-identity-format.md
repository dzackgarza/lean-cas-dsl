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
`decision:false`, and `judged:<expected>`. The latter retains Lean's existing
`Option Bool` display: `(some true)`, `(some false)`, or `none`, rather than
flattening an optional expectation to a Boolean. Parse each JSON value as
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
the complete root is an object with `question`, `proposition`, and `type` fields.
The latter two are references to the exact execution proposition and its type
in this same term table. They are retained even when the proposition is `True`
or `False`; a change to what execution consumes must not be hidden by an
unchanged displayed judgement. The `question` field is recursively structured:

| Root tag | Remaining fields |
| --- | --- |
| `proposition` | Proposition term reference |
| `judgement` | Relation name, ordered operand references, ordered route, ordered declaration names, ordered operand-type references |
| `and` | Left question, right question |
| `not` | Negated question |

The expected truth orientation, including an absent optional expectation,
remains in the `decision` or `judged` prefix.

Earlier producers emitted only the recursive question as a judged root. Their
source revision identifies that historical representation; it must not be
silently relabelled as including the execution proposition. The new field does
not replace the complete original judgement with a truth value and changes no
protected assertion or historical baseline.
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
| `operationEquivalence` | Representative result term, chosen candidate index, complete candidate records, complete family-comparison records |
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
| `method`, `property` | ID, route, receiver, retained comparison records |
| `methodWithLifts` | Method ID, route, ordered lift IDs, receiver, retained comparison records |
| `limit` | Limit ID, complete diagram, optional lift ID |

Each parameter-presentation record contains source ID, source category,
target category, parameters, route, applications, carrier route,
identification declaration names, original object, image, and identity, in
that order. These are complete records, including distinct records that
share the same initial source/route/parameter key.

### Complete method and property comparison records

At producer `841091d` and subsequent sources retaining this field, each method,
lifted-method and property record ends with the ordered array of comparisons
validated for that resolution. Each element is `[context, term]`, where `term`
is a reference in the same enclosing operation table. It retains the complete
typed comparison value under the term-table rules above; it is not a digest,
display string or reference into a separate table.

`context` has exactly `[cellID, constructors, before, after]`. The cell ID and
ordered constructor IDs are literal strings. `before` and `after` are ordered
edge representation strings retaining the full whiskering context, using the
same route-comparison encoding described for operation-source records below.
No field is inferred from the selected route or omitted when several comparisons
participate. The receiver remains the record's original complete typed receiver.
Retaining a comparison does not replace the separately recorded selected route
or choose that cell's source as the method receiver.

Earlier producer formats end at the receiver and do not contain this field.
Their existing payloads and independent assessments are not relabelled. A schema
description supplies decoding information only; it does not authorize a meaning
migration or accept a changed interpretation.

### Complete operation-equivalence records

An `operationEquivalence` node has the exact array shape
`["operationEquivalence", representative, chosen, candidates, comparisons]`.
`representative` is a term reference in this operation table. `chosen` is a
zero-based index into `candidates`, not a term reference. It identifies a
serialization representative of the retained checked class. It does not establish
agreement, remove alternative sources, or give an operation priority over another.

Every candidate has the following ordered fields:

| Position | Field | Representation |
| --- | --- | --- |
| 0 | Operation | Registered operation ID string |
| 1 | Complete declaration application | Term reference, before its supplied operands |
| 2 | Result | Term reference |
| 3 | Sources | Array of complete source records, in retained order |

Every source record has these ordered fields:

| Position | Field | Representation |
| --- | --- | --- |
| 0 | Selected category context | `[categoryExpression, bundle]`; expression is a literal representation string and bundle is a term reference |
| 1 | Receiver | Term reference |
| 2 | Structural route | Ordered array of literal edge representation strings |
| 3 | Complete action applications | Ordered array of term references |
| 4 | Route comparisons | Array of `[cellID, constructors, before, after]` records |
| 5 | Comparison witnesses | Ordered array of term references |

In a route-comparison record, `cellID` is its registered string ID,
`constructors` is the ordered array of constructor ID strings, and `before` and
`after` are the ordered arrays of edge representation strings recording its
whiskering context. These four fields are literal metadata, not term references.
The separate typed witnesses remain in field 5 of the enclosing source record.

Every family-comparison record has these ordered fields:

| Position | Field | Representation |
| --- | --- | --- |
| 0, 1 | Left and right candidate | Zero-based indices into the enclosing candidate array |
| 2, 3 | Left and right source | Zero-based indices into those candidates' source arrays |
| 4 | Actual dependent parameters | Ordered array of term references |
| 5, 6 | Left and right universal family | Term references |
| 7, 8 | Complete left and right family type | Term references |
| 9 | Universal identity | Term reference; a proof retains its complete proposition |

The parameter list instantiates the shared dependent context of the universal
identity. Comparing only its result at one supplied operand would omit the
retained universal statement. Candidate/source indices must be interpreted in
their enclosing arrays; renumbering term-table nodes does not renumber these
indices. Array order is retained throughout these records.

### Transparent binding marker in term graphs

The term tables can contain the generic administrative constant
`CasCatalogue.Trace.operationResult`. Its complete definition is:

```lean
def CasCatalogue.Trace.operationResult (_binding : String)
    {α : Sort u} (value : α) : α := value
```

Consequently `Trace.operationResult binding (α := A) value` reduces to the
same `value` of the same complete type `A`. Its three application arguments are,
in order, the binding string, implicit type, and value. The string retains an
operation ID or named callable address so separate registered bindings can have
separate trace keys even when they use the same declaration. It is not a
mathematical operation, proof, returned computational answer, or new selected
structure. The binding marker and the complete associated operation records
remain in the serialized question. Its transparent value equation alone does
not justify discarding a route, changing a declaration binding, or equating two
different operation records during semantic review.

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
