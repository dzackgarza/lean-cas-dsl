# Product and component-schema recovery, 2026-10-28

This is a new recovery report, **not** the byte-exact original integration review.
No Lean run or live integration occurred during recovery. All files here are external
recovery artifacts; repository source remains untouched by this agent.

## Exact files recovered and checked

| File | Bytes | SHA256 |
| --- | ---: | --- |
| DeclaredProduct.lean | 13273 | 51fd331b3c04a1777a7c22dc0d086a7c8a74bfd89785267e4eef30d7a0cac831 |
| ComponentFieldSchemaEngineering.lean | 7717 | 6f27974de4d722c5547c264cb4d74723fff4c72b56d730a2e13bc015ecf5c2b5 |
| declared-product-contract-export.patch | 2559 | 9d545cae5aac48064dc32a02bfd7318dd26a9420cccb8f980465919ea1c25ace |
| declared-product-realize.patch | 18690 | 73c8f1b4bf4bb5e99f50a2ae20d75f891a4ec098039044832715012bdc39a8c1 |

The hashes above match the final pre-reset records. The Realize patch includes the
last descriptor-only diagram constructor guard, not its earlier 18,361-byte draft.

## Files whose exact final bytes remain missing

| Original file | Bytes if known | Recorded final SHA256 |
| --- | ---: | --- |
| component-field-schema.patch | 45366 | f0e2ad4790eda9c57668fc58289cf91c358b2da423f711caf113ec20b3de7b22 |
| declared-product-language.patch | 22255 | 345cb4109175c86257241dbf115ea721826fbef8fde3478eb0c54fee6cbc0e44 |
| declared-product-registry.patch | 1122 | ba7ece51b69cff2237142f1310407e5b941e802bd341b3cc41a2932839d15f79 |
| declared-product-patch-simulation.json | unknown | 62503331b3e641efc68b44956144e8ccd2940501956443cbe847dc81a0aefa20 |
| declared-product-integration-review.md | unknown | 5bcfff2b27154f22ae741e779bfcbca288f10f8abdbfbe4d8a2fdb235f5182e9 |

The complete schema source additions are retained in
`component-interface-recovered.lean`. `reconstruct-schema.py` preserves the
retained source transformations and doc wording. It is a **reconstructed helper**,
not a recovered original script. Some old-text anchors were reconstructed from
the retained descriptions and may need spelling/indentation repair against the
exact baseline. It fails closed on unmatched or ambiguous anchors and never
writes live source. Use `--only object|data|realize|docs`; `--emit` prints a patch.

The ObjectPresentation source produced by this helper **does** match the recorded
full final-source SHA256 exactly:
`0679bed629bb03ed2c91088f5a3388401e44cde6fe326498223f8d200834ef3b`.
That result was checked during recovery from the restored repository plus its
missing component selector line. Its enclosing patch is not independently
byte-verified without the rest of the schema patch.

The original schema patch used a hand-authored ObjectPresentation fragment, then
Python difflib with three lines of context for ComputationalData (36 hunks),
Realize (six hunks), contract Port (two hunks), README (one hunk), and wire examples
(one hunk). It stripped numbered hunk headers to plain `@@` and wrapped all
fragments in apply_patch `*** Begin Patch` / `*** End Patch` syntax. The
reconstructed helper preserves that format and ordering.

## Exact baseline source hashes needed to reconstruct patches

Kernel root was `/workspace/scratch/4e9256f8ceed/lean-cas-dsl-kernel`.

| File | SHA256 |
| --- | --- |
| CasCatalogue/Language.lean | 095ce98f9e3e7889e83ea42d8b0656ba249c59496b22ba458b9185ffd7115a19 |
| CasCatalogue/ObjectPresentation.lean | f17f58e6402dbe25bc218da85651f2dded00a33b9c235f296860092d41e550d7 |
| CasCatalogue/ComputationalData.lean | 88b953ccee0d89ce034121a34ddc31618b655b0ee64ce5c81fa6457d82a76d8b |
| CasCatalogue/Realize.lean | 345c54dbe134ea73bcdbe60efd549d401dc5f72320c22033ca1f500e8513731a |
| CasCatalogue/Registry.lean | fcfb0035038d2d8ac5007543410c6ce144d73877a074567cbb8d21b00f314c73 |
| CasGates/KernelPurity.lean | 18839ab1e97992fafb8bcb73c4a039c571c6ca67ae561c99ce18b17baf487bbb |

The restored `3a4b` source already matches Registry and KernelPurity. Its
ObjectPresentation becomes the exact baseline by adding the following line after
the `constants` selector:

```lean
  | "component" => entry.components.map (·.projection)
```

Contract root was `/workspace/scratch/4e9256f8ceed/lean-cas-dsl-leaf-contracts-lift`.

| File | SHA256 |
| --- | --- |
| CasContract/Port.lean | 544ea087f6d8ed684c4940949f1b2d36ab32f54c2985bbed627d0085595729ec |
| python/cas_port.py | 5fedf13b0528927a0d5aed0c75b6dc049cfc43442d3c03166cdc514a45769154 |
| api/README.md | 2eecbf158e4a8b8491c3a73221b2ecf756ec8155d17f535f2ca08b68aa73d7f9 |
| api/wire-examples.md | 3cffaa0338647dcb9653cec02d9049ef7075f6a238e167ea37467a8fd143ecd9 |
| tools/export_declared_ports.lean | 6becbd7cbe3f8ef8965995b2a02ea71468c7a3b7fb9a817f61919d76e8043f2a |

The live component-selector addition in contract commits after `6b216b5` is not
fully retained as literal patch bytes here. Required behavior: retain all prior
objectField selectors, accept `component`, require its parameter list to be an
array, preserve ordinary full public parameter data including wrapped/owned Fin
indices, and leave exact count/dependent Fin bounds to declaration validation.
Python framing must not narrow the index to an unwrapped JSON integer. The tests
run before reset checked framing only, including wrapped-index positives and
missing/nonarray/unknown-selector negatives; no mathematical correctness claim.

## Language integration source retained

The full final Language patch is missing. The following source changes and
snippets survive and define its intended reconstruction. The exact baseline had
later reader fixes; do not blindly apply context from the restored older source.

Imports: add `ObjectPresentation` after `DirectConstruction`; add
`DeclaredProduct` after `DeclaredAdmission`.

The comment on `declaredEndpointObject` became:

```lean
/-- An object endpoint supplied by a checked declaration. A literal product keeps that exact
endpoint and its ordered factor context. Its registered component fan checks the interface;
it does not turn the declared endpoint into a separately selected universal construction. -/
```

After the existing ordered factor discovery and same-factor sharing shortcut,
the literal-product branch became:

```lean
  let context ← CategoryContext.ofNamed category endpoint
  let selected ← DeclaredProduct.selectBinary context left right
  unless ← withoutModifyingState (withTransparency .all <|
      isDefEq selected.endpoint endpoint) do
    throwStratum .invalid "the checked coordinate interface changed its declared product endpoint"
  -- This is the declaration's original object occurrence. The component witness
  -- supplies maps when needed; neither its row application nor a cone apex replaces it.
  let source := Value.object endpoint category none none none
  return retainObjectContext
    (.object endpoint category none none (some (#[first, second], source, #[], #[], #[]))) known
```

The following comment replaced the old limit/fallback explanation:

```lean
  -- An explicit product already fixes its ordered fields. There is no unknown
  -- whole structure to discover by repeatedly trying every component carrier.
```

`applyTo` changes, whose full exact body is not retained:

- Take the full target `CategoryContext`; check every factor against it.
- Recover each point's domain with `CategoryContext.morphismDomain`, require
  common domains, and use full context `hom` types throughout.
- For two operands, use `DeclaredProduct.selectBinary` and
  `DeclaredProduct.binaryPresentation`; the source is `selected.endpoint`.
- Form the fan/lift using that witness. Retain `.productMediator` trace with
  original operands and their domains, without substituting unrelated packets.
- Elaborate the supplied map with `elabTermEnsuringType` at the full context Hom,
  then `synthesizeSyntheticMVarsNoPostponing`, `mkExpectedTypeHint` and Trace alias.
- Compose with the selected complete `CategoryStruct` dictionary and explicit
  carrier/object arguments. Use the same full context Hom for the result.
- Do not select a global product row and do not tag this literal endpoint as
  `.limit` or `.constructionApexView`. User-selected actual cones remain separate.

`directComponentPresentation?` changes:

- Bind `(application, base, _)` rather than `(application, base, components)`.
- Replace elaboration of `components.arity` and `.projection` from visible
  parameters with `ObjectPresentation.componentsAt base parameters presentedCarrier`.
- Retain each owning `ObjectEntry`, require its exact ID to equal the initial
  owner's ID; equal carriers/maps do not deduplicate distinct owners.
- Following the owner-ID comparison, insert the final exact occurrence guard:

```lean
    let originalArguments := firstFamily.getAppArgs
    let candidateArguments := family.getAppArgs
    unless originalArguments.size == candidateArguments.size do
      throwSemanticAmbiguity "the component presentations retain different owner telescopes"
    for (original, candidate) in originalArguments.zip candidateArguments do
      if ← isProof original then continue
      unless original == candidate do
        throwSemanticAmbiguity "the component presentations retain distinct original owner arguments"
```

- Keep existing complete type/parameter/family comparisons, including formal
  proof parameters. The exact-occurrence guard supplements those checks.
- Replace the coalescence comment with:

```lean
  -- Equivalent views of this same component owner retain every checked full
  -- presentation. A distinct owning interface was rejected above, independently
  -- of equality of its maps or carriers. The actual source remains a child.
```

Immediately before `componentElements`, add:

```lean
/-- Retain an exact component-field application at its accepted owner. Local
parameters remain in the current interpretation scope; no unresolved data or
second morphism registration is needed to name this already declared map. -/
partial def retainComponentMorphism (entry : ObjectEntry) (value : Expr) : M Expr := do
  let value ← instantiateMVars value
  let parameters ← ObjectPresentation.componentParameters entry value
  Trace.recordProduced (← read).trace value
    (.objectField entry.id "component" entry.category parameters)

/-- Read components through their complete declared presentation. The owning
object publishes each callable field directly. A refinement may supply that
presentation only after its entire structured object matches. -/
```

`componentElements` changes:

- Use `objectContext X` and check full context of each accepted component map.
- Named owner branch checks `entry.components.isSome`, owner category, then uses
  `componentsAt entry parameters objectHandle`. No duplicate MorphismEntry is
  required; retain the exact accepted callable with `retainComponentMorphism`.
- Anonymous discovery carries ObjectEntry, applies complete original owner
  arguments with `componentsAtArguments entry application.arguments`, retains
  distinct owners as ambiguous, and requires a unique candidate.
- Remove only the fresh arbitrary-global-product fallback; preserve actual
  `Cone.pt` / user-selected universal construction paths.

KernelPurity import hunk was exactly:

```diff
*** Update File: /workspace/scratch/4e9256f8ceed/lean-cas-dsl-kernel/CasGates/KernelPurity.lean
@@
 import all CasCatalogue.DirectConstruction
 import all CasCatalogue.DeclaredAdmission
+import all CasCatalogue.DeclaredProduct
 import all CasCatalogue.SelectedLift
```

## Registry manifest missing hunk

The current manifest omits ObjectComponents entirely. The final draft added an
optional `components` object on `RegistryManifestObject`, carrying String names
for `arity`, `projection`, and optional `isLimit`, and mapped all three directly
from each accepted ObjectEntry. Exact original struct/comment/whitespace bytes
are missing; use the recorded final hash to establish exact recovery.

Contract export does **not** consume this manifest. It independently projects
accepted registry declarations; its exact recovered patch adds the optional
isLimit relation and canonical component type there too.

## Design review retained

The selected coordinate family is fixed before any computational descriptor
choice. It matches complete object/category dictionaries and ordered literal
Prod projections using independent rigid factor locals. This is consumption of
the declaration's literal product interface, not a claim that a specialized
X×X construction is mathematically invalid. Distinct matching coordinate
families report ambiguity, never declaration-order precedence.

The generic Fin-two to binary-fan adapter reindexes through existing
WalkingPair/Bool/Fin equivalences and existing fan/isLimit equivalences, then
checks the whole cone and both coordinate maps. It authors no new mathematics.

The Realize public OperationProductLegs API still exposes a genuine
`LimitCone (pair first second)`. For compatibility, an already registered limit
row may furnish the `limitLeg` descriptor only after the independent declared
selection and exact closed diagram/cone/ordered-map comparison. Its actual
published diagram constructor must match the transmitted syntax. Exactly one
match uses legacy descriptors; zero or multiple matches use objectField
component descriptors. This does not select another mathematical witness.
Row type inapplicability is separate from malformed accepted interfaces or
internal errors; only interpretation-invalid nonapplicability is skipped.

The component canonical interface follows the **object's** complete telescope,
then a mandatory explicit typed Fin index. Projection binder visibility cannot
remove or reorder public parameters or the index. Formal proof parameters
remain in traces; public wire filtering omits proof parameters deliberately.
Full original applications retain their exact original hidden arguments after
type checking, rather than closing a freshly reconstructed instance with
definitionally equal but differently owned values. Scoped local fvars are valid
during interpretation; unresolved metavariables are not. Runtime public fields
must still be closed. No post-index `whnf.isForall` check may reject a Hom just
because its concrete representation reduces to a function.

The schema adapter must be used by all ComputationalData objectField branches
(formerly near lines1435,1790,2348), generic declaration validation, interface
reconstruction, Realize decoding, replay/capture, and Language component lookup.
The recovered transformation script records those changes. Wrapped valueData
and owned opaque parameters remain valid public forms. Exact dependent Fin
type and bounds are enforced by generic declaration validation.

No leaf source or mathematical expected answer was used. The control is an
ordinary kernel engineering probe; it registers no mathematical row and is not
acceptance evidence. It was uncompiled before reset.

## Verification state and future targets

Before reset, all final draft hunks were simulated sequentially in memory:
schema, Language, Realize-product, registry, contract export. Every old hunk
matched uniquely and there was no added trailing whitespace. This was a patch
applicability check, not a Lean compile. The original receipt itself remains
missing, so its historical success is not a new recovery-time execution.

Known final virtual source hashes:

| File | SHA256 |
| --- | --- |
| ObjectPresentation | 0679bed629bb03ed2c91088f5a3388401e44cde6fe326498223f8d200834ef3b |
| ComputationalData | 9ed968f35a1dc54e8d75539c7fc278c232d98fbc40006f44d4a5d4520e618672 |
| Port | 44699a2aff37f8429fb20d96d6dba6e2c999fbb2b94a8493aa3473b8c78d9aed |
| README | f3b47a5ce53db0b26a1a4c4df5fc0b50f4a13d53bf26748a259521da76e41e0b |
| wire examples | 1c7db678f8a613fea9fee32c9f27d2e490e0e62f7cb6df47f40b967a204a2f61 |
| KernelPurity | a893c3179f36ea67a5eb5c76f0c2a974706e13bd052fc064ebbc369933d73ef2 |
| Registry | 4f525a215ad10fa1e4f2363c6bacf8240ed16fd82dc259cdfdde9d0eae0f45d8 |
| contract exporter | d7ef3e3063cb17ccce6b68213f7ff541938b453837fa2fa246c0f56f07ae0826 |

The last Language and Realize virtual hashes were not printed in retained
outputs after their final guards; earlier hashes must not be substituted.

Runtime still selected old mathematics3bd4 before reset. Parent must explicitly
select independently authored mathematics3d3848fce69720e0bc734e54dbeb2b80324a44f1
before compiling this consumer. No selection or build is authorized by recovery.

After source restoration and parent go, runtime's smallest useful compile order:

1. Contract Port; Registry; DirectConstruction/CategoryContext; ObjectPresentation;
   DeclaredProduct.
2. Language; ComputationalData; Realize.
3. External ComponentFieldSchemaEngineering, then unchanged product comparison,
   declared endpoint/parameter, product point, callable coordinate, computed
   point, whole function, contextual Hom and binder probes.
4. KernelPurity and both exports.

Concrete open risks: implicit argument inference in the generic binary fan
adapter; complete cone/mediator definitional agreement; original endpoint and
equal-factor source provenance; complete-family validator/decoder consistency;
and unchanged fixed descriptor/API controls. None was resolved by a compile
before the reset.

Reuse search performed before reset: `object components projection telescope`
and `forallTelescope mkLambdaFVars binder info` both failed reaching
https://formalization-corpus.dzackgarza.com/api/openapi.json with
`<urlopen error [Errno 1] Operation not permitted>`. The design instead inspected
accepted Semantic.validateObject/applyObjectParameters and existing Lean
mkLambdaFVars, mkAppN, forallTelescope. That failure was a search limitation,
not a reason to author new mathematical declarations.
