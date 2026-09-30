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
| Leaf | registrations and backend programs | `lean-cas-dsl-leaves` (leaf author) |

Only data crosses the firewall. Going out, it is the encoding of an input; coming back, it is JSON
that the kernel decodes or rejects. No Lean crosses it, in either direction.

## Forms are formal

Every registered operation has declared input and result forms, and each form is a registered
literal form of `lean-categories`: a data type `T` and its denotation `denote : T → …`. Examples:
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
- a proof field is never on the wire. On decoding, the kernel establishes it by decision, or it
  rejects the value.

Decoding is total: an answer is a closed value of `T`, read at the type the kernel asked for, or
it is rejected as malformed.

**Diagrams and universal answers.** The input form of a limit or colimit is the diagrams of its
category, and its form id is the category's id (`cat.sets`). A diagram is sent as the standard
diagram's name with its explicit arguments in their forms, e.g.
`{"ctor": "cospan", "args": [f, g]}`. The answer is the complete universal datum,
`{"ctor": "cone" | "cocone", "args": [apex, leg₁, …]}`. The kernel decodes it against the
standard cone constructor of the shape:
- the apex is a named object or a literal of the category;
- each leg is a graph literal;
- the commutation conditions are decided by the kernel.

A missing leg, a leg that is not a map, or a commutation that does not hold makes the answer
malformed (CC-DECODE).

## A registration is data

A leaf is a manifest, `leaves.json` at the root of `lean-cas-dsl-leaves`, plus the programs it
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
the kernel imports nothing from the leaves' package.

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
- If Lean refutes it, the statement is false mathematics. It is invalid and is reported against
  the suite, never against a leaf.
- Otherwise the realized reading decides it.

A leaf is never asked for what Lean can discharge, and it never supplies a proof.

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

- The leaves' package contains no `.lean` file, and nothing in `lean-cas-dsl` imports it.
- The contract's registration type has exactly the three fields above.
- A deliberately wrong leaf answer, for example cardinality always `7`, turns the affected
  assertions `wrong` and changes nothing else: no meaning, no type, no available operation, and no
  other assertion's outcome.
- A leaf answer that is not a value of the result form is `malformed`.
- A statement Lean decides holds with no leaf installed.
- The existing `.cas` suite runs through the new reading. What no registration computes is
  reported as a gap, never hidden.
