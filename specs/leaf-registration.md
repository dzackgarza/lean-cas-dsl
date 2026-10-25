# Leaf registration and the realized reading

This specification states how the kernel runs leaves under the evidence model
([architecture.md](architecture.md), "The evidence model: nothing from a leaf is trusted"). It is
the design that plan node `gov-leaf-authority` implements. It refines CC-ADAPTER, CC-DECODE and
CC-ROUTE ([computational-core.md](computational-core.md)).

## The firewall in code

| Side | What it holds | Who writes it |
| --- | --- | --- |
| Formal | operations, their input and result forms, what each form denotes | `lean-categories` (formalization author) |
| Formal | resolution, encoding, decoding, comparison, Lean discharge | the kernel (`lean-cas-dsl`) |
| Formal | the acceptance suite | `lean-cas-dsl` (acceptance author) |
| Leaf | registrations and backend programs | a leaf package, e.g. `lean-cas-dsl-leaves` (leaf author) |

Only data crosses the firewall. Going out, it is the encoding of an input; coming back, it is JSON
that the kernel decodes or rejects. No Lean crosses it, in either direction.

## Forms are formal

Every registered operation has a declared dependent signature. Its input and result forms are
derived from the upstream rows and their mathematical definitions. Literal forms supply a data
type `T` and its denotation `denote : T → …`; named objects, arrows, selected elements and
canonical constructions retain their registered identity and complete parameters. Examples:
a finite set of integers as a list, a cardinal as a natural number or `ℵ₀`, a matrix as rows, a
morphism of finite sets as its graph. Which forms exist, and what they denote, is mathematics. A
leaf never declares a form.

The kernel owns each form's wire encoding, and it is generic: a structural codec over the
inductive type `T`, derived from `T`'s definition. It has no per-type code, whether from the
kernel or from a leaf:
- a natural number or an integer is a JSON number;
- a list is an array;
- a constructor application is `{"ctor": name, "args": […]}`;
- a record (one constructor, no indices) is the array of its data fields, or the field itself
  when it has one: a point of `Fin n` is its number, a pair is `[x, y]`, and a map of finite sets
  is its graph `[[0,0],[1,1],[2,1]]`;
- a quotient is sent as a representative: a `Finset` is the list of its elements;
- a proof field is never on the wire. Direct literal decoding establishes the declared data
  type's constraints by decision, or rejects the literal. Structured computational packets
  remain data; decoding them does not manufacture a proved mathematical construction.

Decoding is total: direct literals are closed values of their declared data type; structured
answers are complete computational packets in the declared form. Ill-formed outputs are
rejected as malformed. Formal construction proofs remain independent of both.

**Diagrams and universal answers.** The input form of a limit or colimit is the diagrams of its
category, and its form id is the category's id (`cat.sets`). A diagram is sent as the standard
diagram's name with its explicit arguments in their forms, e.g.
`{"ctor": "cospan", "args": [f, g]}`. The answer is the complete universal datum,
`{"ctor": "cone" | "cocone", "args": [apex, leg₁, …]}`. The kernel decodes it against the
data fields of the standard cone constructor of the shape:
- the apex is a named object or a literal of the category;
- each leg uses the declared map interface at its complete endpoints, including a finite
  graph or an owned callable when that interface admits one;
- formal commutation proofs remain with the independent mathematical construction.

A missing leg or a leg that is not a map at the declared endpoints makes the answer
malformed (CC-DECODE). Commutation of the returned data is a correctness question for
acceptance. Returned presentation maps are computational data at declared endpoints.
They do not establish an isomorphism or universality. The formal construction and its universal
property remain those of the accepted mathematics, independently of this answer.

A subobject reply retains its apex, fixed ambient object and defining monomorphism. For a
requested construction, the formal functor and input independently fix its meaning and selected
structure. The answer retains all computational fields without becoming a proved identification
with that construction. Optional `presentation` maps retain their declared directions and full
endpoints as computational data. Inverse equations and inclusion squares are correctness
questions for acceptance, not prerequisites for promoting the answer to a formal subobject.
Prescribed formal lifts determine the semantic construction; computational lifting preserves
the returned inclusion and complete representation. A well-formed wrong structured answer,
like a well-typed wrong numeral, reaches acceptance as a wrong answer.

For each prescribed subobject-lift step, the kernel instantiates all four public fields of
`LiftEntry.computation` (`MonoLiftComputation.obj`, `hom`, `forward`, and `backward`) at the
complete selected action, source receiver and formal base. The corresponding concrete field
addresses and input packet are specified in `CasContract/Port.lean`. It executes the route
in reverse order, supplying preceding actual outputs to subsequent field requests and using
the actual object and inclusion as the next step's base. A completed packet retains all four
outputs of every step. A packet containing only a base reply, source and lift ids is incomplete.
Map framing uses actual computational endpoints and `Unit` validators; it does not prove
monicity, inverse equations, factorization, universality or agreement with a canonical answer.
Opaque callables on infinite carriers retain their owning session and are never enumerated.

Subsequent computations retain the complete requested functor action and returned subobject
response together. The first is fixed by the formal trace; the second is computational data.
An `objectPresentation` envelope does not establish an isomorphism between them or determine
available operations. Functor actions and defining-map projections preserve this separation.

The complete wire grammar is maintained in `cas_leaf_contracts`' `CasContract/Port.lean`.
It includes registered named morphisms, functor actions, structured arrows and subobjects,
finite function graphs, and canonical limit apex/leg descriptors. Selected element data is a
closed numeral/generator/arithmetic grammar at an exact independently selected object.
Its computational form retains that object's complete presentation, including a structural
image; element encoding never replaces such an image by a named object with the same carrier.
The element envelope preserves the selected descriptor and its computational ownership.
Presentation applications retain their registered comparison, parameters and direction; their
returned points never choose the endpoint by carrier equality.

A returned construction's defining leg retains the complete returned cone or cocone, its
registered diagram and actual typed index. Computational projection uses the returned leg;
formal projection uses the authoritative construction's defining map. Neither is substituted
for the other because apex cardinalities agree. A forward point view similarly retains the full
selected source element, registered object action, target and original generalized-point
domain. It applies only the declared carrier identification. Nonidentity point maps keep their
actual morphism transport and composition; no carrier is used to invent a source structure.

A created-cone envelope additionally retains the registered creation lift, complete source
diagram and complete returned target cone. Formal creation derives the source construction
from accepted mathematics; computational data does not need a proof of the target's universal
property and does not choose a named source object. A nullary operation point retains the operation's full
declaration parameters and actual registered singleton-to-terminal comparison, plus its original
generalized domain and complete selected target. Unsupported computation is a computational
gap; a wire tag cannot supply a terminal bridge, structure or proof.

These encodings compose with the declared dependent forms and complete output fields retained.
Formal proof fields belong to the authoritative construction, not a proof reconstructed from
backend data. Object identities and selected structural maps remain in the semantic trace. A wire
constructor cannot register an operation, change a category, or manufacture a comparison.
Adding a new upstream object therefore uses the same recursive typed codec, while adding a
registered comparison uses its accepted formal maps while computational responses remain data.

An anonymous structural image's registration form is
`image:<compact JSON [target-category-id, edge-descriptor]>`. The edge descriptor is
`{"functor":"id"}`, `{"classifierForget":"id"}`, or
`{"constructorMap":["id", inner-edge-descriptor]}`. This names the complete registered
edge and target schema; its actual ordered declaration parameters remain in the typed value
and wire data. A short classifier or constructor identifier resolves only when the registry
contains exactly one matching edge and target. Competing edges require the complete image key.

## Executable registered actions

A `FunctorEntry` already supplies a complete mathematical functor. Its existing
identifier names the object action; `<id>#map` names its morphism action and
`<id>#input` names the complete request form. These are projections of that row,
not additional mathematical operations. Existing object-action registrations at
source forms remain peers of the complete request form. An ambiguous choice of
admitted implementations remains ambiguous.

One executor demands object images and whole morphism images from these ports.
An object request contains the actual source and all ordered explicit action
parameters. A whole-map request uses the existing `apply` frame, with
`map(action, typedMap(X_actual, Y_actual, f_actual))` as its arrow. Its source and
target are the already executed `F(X)` and `F(Y)` packets. Its generalized domain
is that actual image source and its argument is the identity on that domain.
Returned `typedMap` endpoints must equal those exact supplied image packets.
An unframed whole callable is retained inside that same `typedMap` frame, with
its original returned data unchanged. Later actions read the occurrence's actual
endpoint fields even when its two formal endpoints are the same expression.
This validates the interface; it neither proves the functor laws nor checks the
mathematical answer by substituting a canonical result.

Composites execute their selected primitive applications in order. The cache
retains the full action, actual original data and owners, complete parameters,
and both actual image endpoints for a map. Carrier equality, coincidence at one
object, and a definitionally equal cached name do not choose a different source
or action. A registered comparison's component reuses the images of its already
checked left and right routes even when its Hom type reduces their expressions.
Existing dependent constructions use this same object/map boundary at their
published construction addresses.

Production execution demands these actions before an unrelated target operation
consumes their result; interpretation may retain deferred recipes. The action
receipt preserves the source, complete action and parameter owners internally.
A complete returned packet with no nested opaque token is portable. A token
anywhere in a returned packet keeps the supplying process and session, including
when it is nested in a typed map. A cached owned result cannot cross an expired
session. A target-only consumer receives the actual target packet; the internal
action receipt does not require it to decode source routes or source data.

Checked projections from actual complete Arrow/subobject fields and restoration
of a retained proof-refinement source remain intrinsic. Other classifier-forget
and constructor-induced actions use the same executor through a canonical
derived address. Write `E` for the existing structured edge identity:

```text
E = {"functor": id}
  | {"classifierForget": id}
  | {"constructorMap": [constructorId, E]}
```

For a non-functor root, the object address is `action:` followed by the canonical
compact JSON spelling of `E`; its map and input projections append `#map` and
`#input`. Every referenced row must exist, and every constructor must publish its
action on functors. A bare functor root retains its existing public identifier;
alternate JSON spellings are not aliases. The recursive family includes nested
registered constructors and therefore is not a finite list of new operations.

Both requests carry the existing complete action descriptor as their single
framing parameter. It retains the ordered actual parameters inside every nested
action. The object request retains its actual receiver. The map request uses
that same descriptor in `map(action, typedMap(X_actual, Y_actual, f_actual))`
and retains the actual image endpoints fixed before dispatch. An implementation
at one derived input cannot supply a different edge's action. The kernel checks
the whole selected formal action separately from these framing checks.

The existing `coreObject(original)` data form is checked through the independently
selected `Core.of` field and its original complete object interface. Missing or
unrelated data cannot select that field. An absent admitted primitive action
reports a computational gap; an unavailable representation bridge between live
processes remains distinct. Neither is filled by changing a target consumer's
decoder.

## A registration is data

A leaf package is a manifest, `leaves.json` at the root of the package, plus the programs it
names:

```json
{
  "backends": [
    {"name": "sage", "command": "python3", "args": ["sage/leaf.py"]}
  ],
  "registrations": [
    {"operation": "<catalogue operation id>", "input": "<input form id>", "backend": "sage"}
  ]
}
```

A registration has no other field. The kernel admits a registration only when:
- its operation is a catalogue operation;
- its input form is a declared input form of that operation;
- its backend is named in the manifest.

Otherwise the registration is not admitted, and the harness reports it. A leaf ships no Lean, and
the kernel imports nothing from any leaf package. The kernel reads the manifest of the leaf
package named by `CAS_LEAVES` (its directory or its `leaves.json`) at run time; any package with
a conforming manifest is a leaf package.

The port protocol is unchanged: length-prefixed JSON frames, a `ready` announcement, and requests
`{request_id, op, args}` with replies `{request_id, status, value}`. `op` is the registration's
operation id and `args` is the encoded input.

## The realized reading

A statement's semantic reading elaborates it from the catalogue alone
([architecture.md](architecture.md), "Acceptance"), into a Lean term built from catalogue
operations and literal denotations. The realized reading evaluates that same term; there is no
second traversal of the statement. It evaluates bottom-up:
1. **Literals.** A subterm `denote t` of a registered literal form is the value `t` of that form,
   encoded by the kernel. The extent of a finite-subset literal is the literal itself.
2. **Transport.** Before a registration is selected, the receiver of a method or property is sent
   along the route the semantic reading resolved, as far as the catalogue's refinement rows relate
   it to a base object at the same parameters. For example, `Fin(3) in FiniteSets` goes to
   `Fin(3)` in `Sets`. Only catalogue rows move an object. A registration on a form the catalogue
   sends elsewhere along the operation's route could never be selected, so it is not admitted.
3. **Operations.** For an operation applied to evaluated arguments, the kernel picks the admitted
   registration of that operation for the arguments' form, sends the encoded input, and decodes
   the answer in the operation's result form. The outcomes:
   - no admitted registration: a gap;
   - two admitted registrations for the same operation and form: a gap, reported as ambiguous;
   - a backend that cannot start: unavailable;
   - a rejected answer: malformed.
4. **Composites.** The decoded value is the input of the next operation along the resolved route.
   Universal constructions come back as their complete data (apex and legs, kernel and inclusion)
   in the result form, and a decode missing a defining arrow is malformed (CC-DECODE).

## Comparison

`assert X = L` holds when the decoded value of `X` equals the literal `L` in the form's type, by
decidable equality on `T` computed by the kernel. `assert P` compares a decoded three-valued
decision with the expected one. No proof about a leaf's value is formed, and nothing a leaf
returned is used as evidence of anything except its own answer.

## What Lean discharges

Before any leaf is called, the kernel tries to decide the statement's semantic proposition in
Lean, generically: `decide` within a fixed budget, and the catalogue's registered evidence
(LC-18).
- If Lean proves it, the statement holds as proved, and no leaf is consulted.
- If Lean refutes the well-typed comparison, its outcome is `wrong`; reading validity is
  unchanged. No leaf was consulted in that discharge.
- Otherwise the realized reading decides it.

## Running a fixed question with selected implementations

The public harness selects an implementation environment independently of the mathematical
statement. Given an already built kernel, an independently supplied assertion file and its
inventory, run:

```sh
lake env .lake/build/bin/cas-harness \
  --suite /absolute/path/to/questions.cas \
  --inventory /absolute/path/to/inventory.json \
  --manifest /absolute/path/to/leaves.json \
  --report /absolute/path/to/report.json \
  --computation-only
```

The `--suite` argument also accepts a directory. `--computation-only` requests actual
computational execution of the same interpreted question instead of first discharging it in
Lean. It changes neither the assertion nor its expected answer. To compare implementations,
keep the question file, inventory and selected mathematical source fixed and supply a different
manifest and report path. A manifest contains only the public backend declarations and
operation/input registrations above; it carries no interpretation or expected answer.

For independently supplied mathematical extensions, repeat `--import Fully.Qualified.Module`
to load their already compiled catalogue modules alongside the standard catalogue. The selected
module list is part of the mathematical environment and stays fixed when comparing computational
implementations. This uses the same built harness and kernel; adding a mathematical module does
not require editing their source. A leaf still ships no Lean and cannot choose these imports.

The JSON report retains `id`, `question`, `proposition`, `kind`, `detail`, `fails` and the actual
`dispatches` for each assertion. `question` includes the complete typed claim and its operation
trace; `proposition` is a readable display. A comparison of environments must retain the same
question, rather than treating equal displays or equal answers as proof of unchanged meaning.
The report's dispatch records are engineering observations, not mathematical evidence.

For a fixed well-formed true assertion, independent environment specimens exercise the
following outcomes:

| Environment behavior | Reported outcome |
| --- | --- |
| Declared computations supply the independently expected answer | `holds` |
| No matching registration, or a conforming `unsupported` reply for the dispatched operation | `gap` with the missing implementation reason |
| Several matching registrations | `gap` with the realization ambiguity reason |
| A backend cannot start, exits during a request, or reports an engine failure | `unavailable` |
| A response has an invalid frame, wrong request ID, missing required field or incompatible endpoint | `malformed` |
| A response has the required form but contradicts the independent assertion | `wrong` |
| The kernel violates an internal invariant or raises an unclassified exception | `internal` |

The last row is exercised by a kernel engineering fault fixture, not by granting a leaf an
`internal` or `invalid` verdict. A leaf's error reply remains an execution failure. Semantic
invalidity or ambiguity is determined before implementation selection. Conflicting nested
failure tags cannot turn an internal failure into an invalid mathematical question or a gap.

Owned data and callable tokens remain attached to the live connection that created them.
Subsequent operations in that session must retain their owners, including every owner carried
by transported maps and complete structured results. A fresh harness invocation opens its own
sessions; it does not import tokens from an earlier report. Ownership checks and deliberate
foreign-session fixtures are engineering tests of this boundary, separate from the unchanged
mathematical assertion. No backend identifier or wire token belongs in the assertion text.

The normal path avoids backend calls after successful Lean discharge. A leaf supplies values
and never supplies a proof.

Where the fixed B0 requirements additionally demand registered execution, a separate
`cas-harness --computation-only` run evaluates the same interpreted questions without proof
discharge. Its per-assertion dispatch records identify the actual registered requests made by
the runner. A required computational observation needs both its independent assertion to hold
and an actual backend request; a proof-only hold does not establish that observation. Dispatch
records are execution observations, not mathematical evidence about an implementation.

## What is removed

These go, in the code and in every document that describes them:
- **From the contract:**
  - realizers and denotation functors, and realized actions with their squares (`Action.lean`);
  - handle isomorphisms, presentations with identifications, and observations with proofs;
  - deciders and equalities with evidence (`Decide.lean`), and re-typing by decisions
    (`Refine.lean`);
  - limit realizations identified by a backend (`Limits.lean`);
  - the `Trust` enum and trusted and certified implementations (`Trust.lean`);
  - `register_leaf` and leaf-supplied decoders;
  - the leaf import rule (`Leaf.lean`), since a leaf imports nothing.
- **In the leaves:** every Lean module. Each becomes a registration in the manifest, and its
  program keeps only the engine call.
- **In the acceptance suite:**
  - the probe modules that test the realization machinery;
  - proofs of admitted assertions formed from a leaf's definitions.

  The admitted propositions stay, and are checked by the realized reading.

## Acceptance of the replacement

- A leaf package contains no `.lean` file, and nothing in `lean-cas-dsl` imports one.
- The contract's registration type has exactly the three fields above.
- A deliberately wrong leaf answer, for example cardinality always `7`, turns the affected
  assertions `wrong` and changes nothing else: no meaning, no type, no available operation, and no
  other assertion's outcome.
- A leaf answer that is not a value of the result form is `malformed`.
- A statement Lean decides holds with no leaf installed.
- The existing `.cas` suite runs through the new reading. What no registration computes is
  reported as a gap, never hidden.
