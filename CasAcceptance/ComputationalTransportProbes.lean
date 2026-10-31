/- Copyright (c) 2026 Dzack Garza. Released under Apache 2.0 license. -/
module

import CasCatalogue.Realize
import LeanCategories.Catalogue.Semantics
meta import CasCatalogue.Realize
meta import LeanCategories.Catalogue.Semantics

open Lean Meta Elab Term CasCatalogue

/-! Engineering regressions for retained computational dependencies and structural projections.
The returned fields below exercise framing and data flow. They establish no mathematical
correctness, construction law, or acceptance answer. No backend process is started. -/

-- A complete cone may expose its actual apex, but an intervening action must survive intact.
run_elab do
  let state ← registryState
  let some row := state.limits.find? (·.id.raw == "lim.sets.product")
    | throwError "the existing product declaration is unavailable"
  let some action := state.functors.find? (·.id.raw == "fun.sets.list")
    | throwError "the existing nonidentity list action is unavailable"
  let trace ← Trace.new
  let left ← elabTermAndSynthesize (← `(CasCatalogue.Foundation.Objects.fin 2)) none
  let right ← elabTermAndSynthesize (← `(CasCatalogue.Foundation.Objects.fin 3)) none
  let diagram ← mkAppM ``CategoryTheory.Limits.pair #[left, right]
  let presentation ← Semantic.limitPresentation row diagram
  let cone ← mkAppM ``CategoryTheory.Limits.LimitCone.cone #[presentation]
  let apex ← mkAppM ``CategoryTheory.Limits.Cone.pt #[cone]
  let functor ← instantiateFresh action.declaration
  let image ← Semantic.objOf functor apex
  let node (tag : String) (args : Array Json) :=
    Json.mkObj [("ctor", toJson tag), ("args", Json.arr args)]
  let keys := (Array.range 6).map toJson
  let actualApex := node "finiteData" #[node "obj.sets.fin" #[toJson (6 : Nat)], Json.arr keys]
  let leftLeg := node "finiteGraph" #[Json.arr keys,
    Json.arr ((Array.range 6).map fun n => Json.arr #[toJson n, toJson (n / 3)])]
  let rightLeg := node "finiteGraph" #[Json.arr keys,
    Json.arr ((Array.range 6).map fun n => Json.arr #[toJson n, toJson (n % 3)])]
  let objects := #[node "obj.sets.fin" #[toJson (2 : Nat)],
    node "obj.sets.fin" #[toJson (3 : Nat)]]
  let packet := node "cone" #[actualApex, leftLeg, rightLeg]
  let .ok plan ← StructuredResult.dataPlan row diagram presentation
    | throwError "the existing product has no complete computational schema"
  let external := fun binder => Id.run do
    let some binding := plan.binders[binder]? | return none
    for role in binding.inputRoles do
      if let .argument index := role then return objects[index]?
    return none
  if let .error message ← StructuredResult.validatePlannedData plan packet
      (fun port seen data => ComputationalData.validatePlannedPort plan port seen data external
        ComputationalData.endpointKeys) then
    throwError "the transport fixture is not complete computational cone data: {message}"
  let construction := node "constructionApex" #[toJson row.id.raw,
    node "pair" objects, packet]
  let direct : Realize.Wire := {
    form := .limitApex row
    payload := .computed apex (.owned "transport-probe" 7 construction) }
  let selected ← Realize.computationalApexReceiver trace direct
  unless selected.form.id == "obj.sets.fin" && selected.json == actualApex &&
      selected.value == direct.value && selected.owner?.isNone &&
      (selected.payload matches .computed _ (.inline _)) do
    throwError "a complete portable apex lost its actual data, formal value or computational origin"
  let accepted ← Realize.edgeDescriptor trace (.functor action.id) functor
  -- The unknown descriptor is a preservation control, not a new mathematical registration.
  for descriptor in #[accepted, node "unregistered.transport.probe" #[]] do
    let mapped := node "functorAction" #[descriptor, construction]
    let input : Realize.Wire := {
      form := .functorImage action CategoryId.sets
      payload := .computed image (.owned "transport-probe" 7 mapped) }
    let retained ← Realize.computationalApexReceiver trace input
    unless retained.form.id == input.form.id && retained.form.category == input.form.category &&
        retained.json == input.json && retained.value == input.value &&
        retained.owner? == input.owner? do
      throwError "apex selection discarded a residual action or changed its complete context"

-- A full Arrow subcategory can be an atomic registered category. Its defining projections
-- reuse the actual complete packet through the public method path, with no projection leaf.
run_elab do
  let state ← registryState
  let ring ← elabTermAndSynthesize (← `(RingCat.of ℤ)) none
  let object ← elabTermAndSynthesize (← `(ModuleCat.of ℤ ℤ)) none
  let identity ← mkAppM ``CategoryTheory.CategoryStruct.id #[object]
  let arrow ← mkAppM ``CategoryTheory.Arrow.mk #[identity]
  let some cokernel := state.functors.find? (·.id.raw == "fun.arrows_modules.cokernel")
    | throwError "the existing complete cokernel action is unavailable"
  let fixed ← Semantic.objOf (← mkAppM cokernel.declaration #[ring]) arrow
  let sourceCategory ← Semantic.namedCategoryFor state cokernel.target
  let node (tag : String) (args : Array Json) :=
    Json.mkObj [("ctor", toJson tag), ("args", Json.arr args)]
  let opaqueData (token : String) := node "opaqueData" #[toJson token]
  let fields := #[opaqueData "actual source", opaqueData "actual quotient",
    opaqueData "actual quotient map"]
  for spelling in #["arrow", "subobject"] do
    let complete := node spelling fields
    if let .error message ← ComputationalData.validatePort fixed (← inferType fixed) complete then
      throwError "a complete typed quotient packet was rejected: {message}"
    let trace ← Trace.new
    let harness ← Realize.Harness.empty
    let input : Realize.Wire := {
      form := .functorImage cokernel sourceCategory.id
      payload := .computed fixed (.owned "transport-probe" 11 complete) }
    harness.results.modify (·.insert fixed input)
    for (name, expected) in #[("projection", node "arrow" fields), ("codomain", fields[1]!)] do
      let (value, _) ← Semantic.method name fixed sourceCategory (some trace)
      let actual ← Realize.realize harness trace "a complete quotient's defining projection" value
      unless actual.json == expected && actual.value == value &&
          actual.owner? == input.owner? do
        throwError "the quotient method changed actual defining data, formal value or owner"
      if name == "projection" then
        let hom ← mkAppM ``CategoryTheory.Arrow.hom #[value]
        Trace.record (some trace) hom (.arrowProjection value)
        let projected ← Realize.realize harness trace "the returned quotient's actual map" hom
        unless projected.json == fields[2]! && projected.value == hom &&
            projected.owner? == input.owner? do
          throwError "successive quotient projection lost its actual callable or owner"

-- Composition consumes two opaque callables as data and retains their common session.
run_elab do
  let state ← registryState
  let trace ← Trace.new
  let harness ← Realize.Harness.empty
  let some sets := state.categories.find? (·.id == CategoryId.sets)
    | throwError "the existing set category is unavailable"
  let object ← elabTermAndSynthesize (← `(Bool)) none
  let first ← elabTermAndSynthesize (← `(TypeCat.ofHom Bool.not)) none
  let second ← mkAppM ``CategoryTheory.CategoryStruct.id #[object]
  let value ← mkAppM ``CategoryTheory.CategoryStruct.comp #[first, second]
  let cached (formal : Expr) (token : String) : Realize.Wire := {
    form := .canonicalMorphism sets
    payload := .computed formal (.opaque "transport-probe" 13 token) }
  let firstWire := cached first "first opaque callable"
  let secondWire := cached second "second opaque callable"
  harness.results.modify (fun entries =>
    (entries.insert first firstWire).insert second secondWire)
  Trace.record (some trace) value (.morphismComposition sets.id first second object object object)
  let actual ← Realize.realize harness trace "the composed opaque callables" value
  let expected := Json.mkObj [("ctor", toJson "compose"),
    ("args", Json.arr #[firstWire.json, secondWire.json])]
  unless actual.json == expected && actual.value == value &&
      actual.owner? == firstWire.owner? do
    throwError "composition changed an opaque callable, formal value or owner"

-- A selected family parameter travels with the actual map action, including on opaque data.
run_elab do
  let state ← registryState
  let trace ← Trace.new
  let harness ← Realize.Harness.empty
  let some sourceCategory := state.categories.find? (·.id == CategoryId.modulesR)
    | throwError "the existing module fibre is unavailable"
  let some entry := state.functors.find? (·.id == FunctorId.modulesFibreInclusion)
    | throwError "the existing fibre inclusion is unavailable"
  let targetCategory ← Semantic.namedCategoryFor state entry.target
  let source ← elabTermAndSynthesize
    (← `(ModuleCat.of (RingCat.of (ZMod 4)) (ZMod 4))) none
  let identity ← mkAppM ``CategoryTheory.CategoryStruct.id #[source]
  let edge := EdgeRef.functor entry.id
  let action ← Semantic.edgeFunctor state edge
  let image ← Semantic.mapOf action identity
  let action ← instantiateMVars action
  unless !action.hasMVar && !action.hasLevelMVar && !image.hasMVar && !image.hasLevelMVar do
    throwError "the exact selected map action left a category parameter unresolved"
  let input : Realize.Wire := {
    form := .canonicalMorphism sourceCategory
    payload := .computed identity (.opaque "transport-probe" 21 "selected callable") }
  harness.results.modify (·.insert identity input)
  Trace.record (some trace) image
    (.morphismTransport sourceCategory.id targetCategory.id #[edge] identity)
  let actual ← Realize.realize harness trace "the selected opaque map action" image
  let .ok #[descriptor, retained] := (actual.json.getObjVal? "args").bind (·.getArr?)
    | throwError "the mapped callable lost its action or original data"
  let node (tag : String) (args : Array Json) :=
    Json.mkObj [("ctor", toJson tag), ("args", Json.arr args)]
  let expected := node entry.id.raw #[node "obj.rings.integers_mod" #[toJson (4 : Nat)]]
  unless descriptor == expected && retained == input.json && actual.value == image &&
      actual.owner? == input.owner? do
    throwError "map transport changed its complete selected parameters, callable or owner"

-- Endpoint descriptors are request dependencies even when both compared points are portable.
-- Two admitted backends distinguish owner selection from the ordinary ambiguity control;
-- absent sessions then stop the request before any process can be started.
run_elab do
  let state ← registryState
  let trace ← Trace.new
  let some sets := state.categories.find? (·.id == CategoryId.sets)
    | throwError "the existing set category is unavailable"
  let some fin := state.objects.find? (·.id.raw == "obj.sets.fin")
    | throwError "the existing finite object form is unavailable"
  let operation := "mor.sets.equality"
  let manifest : Manifest := {
    backends := #[{ name := "transport-probe", command := "/not-executed" },
      { name := "foreign-probe", command := "/not-executed" }]
    registrations := #[{ operation, input := operation, backend := "transport-probe" },
      { operation, input := operation, backend := "foreign-probe" }] }
  let harness ← Realize.Harness.ofManifest "." manifest
  unless harness.admitted.size == 2 do
    throwError "the ownership control requires both independently admitted equality rows"
  let domain ← Realize.closedElementDomain state
  let target ← elabTermAndSynthesize (← `(CasCatalogue.Foundation.Objects.fin 2)) none
  let first ← elabTermAndSynthesize
    (← `(TypeCat.ofHom (fun _ : CasCatalogue.Foundation.Objects.fin 1 => (0 : Fin 2)))) none
  let second ← elabTermAndSynthesize
    (← `(TypeCat.ofHom (fun _ : CasCatalogue.Foundation.Objects.fin 1 => (1 : Fin 2)))) none
  let portable (formal : Expr) (datum : Nat) : Realize.Wire := {
    form := .canonicalMorphism sets
    payload := .computed formal (.inline (toJson datum)) }
  let observe := do
    try
      discard <| Realize.observeEquality harness trace
        (portable first 0) (portable second 1) domain target
      pure none
    catch error => pure (CasCatalogue.Exception.stratum? error)
  unless (← observe) == some .ambiguousRealization do
    throwError "the unowned equality request lost its genuine backend ambiguity"
  let ownedTarget : Realize.Wire := {
    form := .object fin
    payload := .computed target (.opaque "transport-probe" 51 "actual selected carrier") }
  harness.results.modify (·.insert target ownedTarget)
  unless (← observe) == some .unavailable do
    throwError "equality dropped its selected carrier's owner before backend selection"

-- Bare graphs acquire both exact structured endpoints before composition. In particular
-- the intermediate group and ownership carried only by endpoint descriptors are retained.
run_elab do
  let state ← registryState
  let trace ← Trace.new
  let harness ← Realize.Harness.empty
  let some groups := state.categories.find? (·.id == CategoryId.groups)
    | throwError "the existing group category is unavailable"
  let some units := state.objects.find? (·.id.raw == "obj.groups.units")
    | throwError "the existing structured group form is unavailable"
  let source ← elabTermAndSynthesize
    (← `(CasCatalogue.Algebra.Units.groupUnits (MonCat.of (ZMod 3)))) none
  let middle ← elabTermAndSynthesize
    (← `(CasCatalogue.Algebra.Units.groupUnits (MonCat.of (ZMod 4)))) none
  let target ← elabTermAndSynthesize
    (← `(CasCatalogue.Algebra.Units.groupUnits (MonCat.of (ZMod 5)))) none
  let first ← elabTermAndSynthesize
    (← `(GrpCat.ofHom (1 : $(← exprToSyntax source) →* $(← exprToSyntax middle)))) none
  let second ← elabTermAndSynthesize
    (← `(GrpCat.ofHom (1 : $(← exprToSyntax middle) →* $(← exprToSyntax target)))) none
  let composite ← mkAppM ``CategoryTheory.CategoryStruct.comp #[first, second]
  let node (tag : String) (args : Array Json) :=
    Json.mkObj [("ctor", toJson tag), ("args", Json.arr args)]
  let mut endpoints := #[]
  for (object, label) in #[(source, "source monoid"), (middle, "intermediate monoid"),
      (target, "target monoid")] do
    let descriptor := node units.id.raw #[node "opaqueData" #[toJson label]]
    if let .error message ← ComputationalData.validatePort object (← inferType object) descriptor then
      throwError "the endpoint is not a complete typed group descriptor: {message}"
    let endpoint : Realize.Wire := {
      form := .object units
      payload := .computed object (.owned "transport-probe" 61 descriptor) }
    harness.results.modify (·.insert object endpoint)
    endpoints := endpoints.push endpoint
  -- Arbitrary graph entries test framing only, not group-map correctness.
  let firstGraph := Json.arr #[Json.arr #[toJson (0 : Nat), toJson (1 : Nat)]]
  let secondGraph := Json.arr #[Json.arr #[toJson (1 : Nat), toJson (2 : Nat)]]
  for (formal, data) in #[(first, firstGraph), (second, secondGraph)] do
    harness.results.modify (·.insert formal {
      form := .canonicalMorphism groups, payload := .computed formal (.inline data) })
  Trace.record (some trace) composite
    (.morphismComposition groups.id first second source middle target)
  let actual ← Realize.realize harness trace "the graphs at complete structured endpoints" composite
  let #[sourceEndpoint, middleEndpoint, targetEndpoint] := endpoints
    | throwError "the framing probe lost an endpoint"
  let expected := node "compose" #[
    node "typedMap" #[sourceEndpoint.json, middleEndpoint.json, firstGraph],
    node "typedMap" #[middleEndpoint.json, targetEndpoint.json, secondGraph]]
  unless actual.json == expected && actual.value == composite &&
      actual.owner? == middleEndpoint.owner? do
    throwError "graph composition lost an exact structured endpoint or its owning session"

-- A named arrow used by a later invocation remains a descriptor even when its own-form
-- registration is installed. Only explicit whole-arrow observation selects that registration.
-- Two admitted rows make premature dispatch visible without starting a backend process.
run_elab do
  let state ← registryState
  let trace ← Trace.new
  let some empty := state.morphisms.find? (·.id.raw == "mor.sets.tuple_empty")
    | throwError "the existing empty tuple map is unavailable"
  let some cons := state.morphisms.find? (·.id.raw == "mor.sets.tuple_cons")
    | throwError "the existing tuple constructor is unavailable"
  let some sets := state.categories.find? (·.id == CategoryId.sets)
    | throwError "the existing set category is unavailable"
  let manifest : Manifest := {
    backends := #[{ name := "deferred-one", command := "/not-executed" },
      { name := "deferred-two", command := "/not-executed" }]
    registrations := #[{ operation := empty.id.raw, input := empty.id.raw, backend := "deferred-one" },
      { operation := empty.id.raw, input := empty.id.raw, backend := "deferred-two" }] }
  let harness := { (← Realize.Harness.ofManifest "." manifest) with computationOnly := true }
  unless harness.admitted.size == 2 do throwError "the descriptor-demand control lost its two admitted rows"
  let object ← elabTermAndSynthesize (← `(CasCatalogue.Foundation.Objects.fin 2)) none
  let emptyValue ← mkAppM empty.declaration #[object]
  Semantic.namedMorphism empty emptyValue (some trace)
  let descriptor ← Realize.realize harness trace "the unapplied empty-tuple descriptor" emptyValue
  unless (descriptor.json.getObjValAs? String "ctor").toOption == some empty.id.raw &&
      (← harness.connections.get).isEmpty do
    throwError "forming a named arrow eagerly executed its standalone registration"
  let observed ← try
      discard <| Realize.realizeArrowObservation harness trace descriptor
      pure none
    catch error => pure (CasCatalogue.Exception.stratum? error)
  unless observed == some .ambiguousRealization do
    throwError "whole-arrow observation did not select the named operation's actual registrations"
  let domain ← Realize.closedElementDomain state
  let first ← elabTermAndSynthesize
    (← `(TypeCat.ofHom (fun _ : CasCatalogue.Foundation.Objects.fin 1 => (0 : Fin 2)))) none
  Trace.record (some trace) first (.elementNumeral 0 object object)
  let some (_, emptyTarget) := Language.homEnds? (← inferType emptyValue)
    | throwError "the empty tuple has no full endpoints"
  let some product := state.limits.find? (·.id.raw == "lim.sets.product")
    | throwError "the existing product interface is unavailable"
  let diagram ← mkAppM ``CategoryTheory.Limits.pair #[object, emptyTarget]
  let presentation ← Semantic.limitPresentation product diagram
  let firstFunction ← Language.functionOf first
  let emptyFunction ← Language.functionOf emptyValue
  let pairFunction ← withLocalDeclD `point domain fun point => do
    mkLambdaFVars #[point] (← mkAppM ``Prod.mk #[mkApp firstFunction point, mkApp emptyFunction point])
  let paired ← mkAppM ``TypeCat.ofHom #[pairFunction]
  Trace.record (some trace) paired (.productMediator sets.id presentation domain first emptyValue)
  let constructor ← mkAppM cons.declaration #[object, mkNatLit 0]
  Semantic.namedMorphism cons constructor (some trace)
  let some (middle, target) := Language.homEnds? (← inferType constructor)
    | throwError "the tuple constructor has no full endpoints"
  discard <| Semantic.recordNamedObject object (some trace)
  discard <| Semantic.recordNamedObject emptyTarget (some trace)
  let invocation ← mkAppM ``CategoryTheory.CategoryStruct.comp #[paired, constructor]
  Trace.record (some trace) invocation
    (.morphismComposition sets.id paired constructor domain middle target)
  let attempted ← try
      discard <| Realize.realize harness trace "the invocation containing a named point" invocation
      pure none
    catch error => pure (some (CasCatalogue.Exception.stratum? error, ← error.toMessageData.toString))
  let some (stratum, message) := attempted
    | throwError "the absent outer operation unexpectedly executed"
  unless stratum == some .noImplementation && message.contains cons.id.raw &&
      (← harness.connections.get).isEmpty do
    throwError "a nested named point was dispatched before its enclosing complete invocation: {message}"

-- Computation-only whole-arrow comparison requires actual named-arrow data even when the
-- retained formal expressions are equal. A complete but wrong cached graph remains wrong.
run_elab do
  let state ← registryState
  let trace ← Trace.new
  let emptyHarness ← Realize.Harness.empty
  let harness := { emptyHarness with computationOnly := true }
  let some sets := state.categories.find? (·.id == CategoryId.sets)
    | throwError "the existing set category is unavailable"
  let some entry := state.morphisms.find? (·.id.raw == "mor.sets.fin_rev")
    | throwError "the existing named finite map is unavailable"
  let reversal ← mkAppM entry.declaration #[mkNatLit 3]
  Semantic.namedMorphism entry reversal (some trace)
  let proposition ← mkEq reversal reversal
  let reflexive : Language.Claim := .homs reversal reversal sets proposition "the named arrow" "itself"
  let demanded ← try
      discard <| Realize.realizeClaim harness trace reflexive
      pure none
    catch error => pure (CasCatalogue.Exception.stratum? error)
  unless demanded == some .noImplementation do
    throwError "computation-only comparison evaluated an uncomputed named expression in Lean"
  let some (object, _) := Language.homEnds? (← inferType reversal)
    | throwError "the named finite map lost its endpoints"
  let identity ← mkAppM ``CategoryTheory.CategoryStruct.id #[object]
  Trace.record (some trace) identity (.morphismIdentity sets.id object)
  let composite ← mkAppM ``CategoryTheory.CategoryStruct.comp #[reversal, reversal]
  Trace.record (some trace) composite
    (.morphismComposition sets.id reversal reversal object object object)
  let graph := Json.mkObj [("ctor", toJson "finiteGraph"), ("args", Json.arr #[
    toJson (#[0, 1, 2] : Array Nat),
    Json.arr ((Array.range 3).map fun n => Json.arr #[toJson n, toJson (0 : Nat)])])]
  if let .error message ← ComputationalData.validatePort reversal (← inferType reversal) graph then
    throwError "the adversarial callable is not complete finite graph data: {message}"
  harness.results.modify (·.insert reversal {
    form := .namedMorphism entry, payload := .computed reversal (.inline graph) })
  let claim : Language.Claim := .homs composite identity sets (← mkEq composite identity)
    "the computed composite" "the explicit identity"
  match ← Realize.realizeClaim harness trace claim with
  | .wrong _ => pure ()
  | _ => throwError "whole-arrow observation replaced the actual wrong graph with its formal expression"

-- Equality observation consumes the unique applicable registered declaration. These
-- immutable registry snapshots exercise selection only; they install no mathematical row.
run_elab do
  let state ← registryState
  let #[published] := state.morphisms.filter fun entry =>
      entry.name == "=" && entry.category == CategoryId.sets
    | throwError "the control requires one published equality declaration"
  let renamed : MorphismEntry := { published with id := ⟨"probe.observation.renamed"⟩ }
  let duplicate : MorphismEntry := { published with id := ⟨"probe.observation.duplicate"⟩ }
  let otherSurface : MorphismEntry := {
    published with id := ⟨"probe.observation.other_surface"⟩, name := "another predicate" }
  let otherPredicate : MorphismEntry := {
    published with
    id := ⟨"probe.observation.membership"⟩
    declaration := `CasCatalogue.Foundation.PowerSets.member }
  let otherCategory : MorphismEntry := {
    published with id := ⟨"probe.observation.other_category"⟩, category := CategoryId.groups }
  let unrelated := state.morphisms.filter fun entry => entry.id != published.id
  let target ← elabTermAndSynthesize (← `(CasCatalogue.Foundation.Objects.fin 5)) none
  let (selected, arrow, parameters, source, truth) ← Realize.equalityObservation state target
  unless selected.id == published.id && parameters.size == 1 &&
      (← withTransparency .all <| isDefEq parameters[0]! target) &&
      !arrow.hasMVar && !arrow.hasLevelMVar do
    throwError "the equality observation changed its declared row or complete typed parameter"
  let expectedSource ← mkAppM ``Prod #[target, target]
  unless ← withTransparency .all <| isDefEq source expectedSource do
    throwError "the equality observation lost its independently selected product source"
  let power ← Language.powerObjectIn state CategoryId.sets
  let truthMap ← instantiateFresh power.truth
  let some (_, expectedTruth) := Language.homEnds? (← inferType truthMap)
    | throwError "the registered truth map lost its endpoint"
  unless ← withTransparency .all <| isDefEq truth expectedTruth do
    throwError "the observation selected truth values independently of the power-object interface"
  for rows in #[unrelated.push renamed, #[renamed] ++ unrelated.reverse,
      #[otherSurface, otherPredicate, otherCategory, renamed],
      #[renamed, otherCategory, otherPredicate, otherSurface]] do
    let (entry, actual, data, input, output) ← Realize.equalityObservation
      { state with morphisms := rows } target
    unless entry.id == renamed.id && data.size == parameters.size &&
        (← withTransparency .all <| isDefEq actual arrow) &&
        (← withTransparency .all <| isDefEq input source) &&
        (← withTransparency .all <| isDefEq output truth) do
      throwError "renaming or reordering registry rows changed the selected equality meaning"
  let failure (rows : Array MorphismEntry) := do
    try
      discard <| Realize.equalityObservation { state with morphisms := rows } target
      pure none
    catch error => pure (CasCatalogue.Exception.stratum? error)
  for rows in #[unrelated, #[otherSurface], #[otherPredicate], #[otherCategory]] do
    unless (← failure rows) == some .noImplementation do
      throwError "an absent or inapplicable equality row supplied an observation"
  for rows in #[#[renamed, duplicate], #[duplicate, renamed]] do
    unless (← failure rows) == some .ambiguousRealization do
      throwError "competing applicable equality declarations were selected by insertion order"

-- An ordinary numeral transported through a declared inclusion can be observed as
-- plain data. A computed point with the same retained formal value must still expose
-- a well-formed wrong answer; the formal equality does not replace its returned data.
run_elab do
  let state ← registryState
  let trace ← Trace.new
  let harness := { (← Realize.Harness.empty) with computationOnly := true }
  let some sets := state.categories.find? (·.id == CategoryId.sets)
    | throwError "the existing set category is unavailable"
  let some entry := state.inclusions.find? (·.id.raw == "incl.sets.naturals_degrees")
    | throwError "the existing plain-data inclusion is unavailable"
  let inclusion ← instantiateFresh entry.declaration
  let some (source, target) := Language.homEnds? (← inferType inclusion)
    | throwError "the inclusion lost its exact selected endpoints"
  Trace.record (some trace) inclusion (.namedInclusion entry.id sets.id #[] source target)
  let domain ← Realize.closedElementDomain state
  let numeral ← elabTermAndSynthesize
    (← `(TypeCat.ofHom (fun _ : CasCatalogue.Foundation.Objects.fin 1 => (3 : Nat)))) none
  Trace.record (some trace) numeral (.elementNumeral 3 source source)
  let expected ← mkAppM ``CategoryTheory.CategoryStruct.comp #[numeral, inclusion]
  Trace.record (some trace) expected
    (.morphismComposition sets.id numeral inclusion domain source target)
  let described ← Realize.realize harness trace "the independently included numeral" expected
  let .ok (decoded, _) ← Realize.decodeValue trace sets (← inferType expected) described.json
    | throwError "the included numeral's complete public descriptor did not reconstruct: {described.json}"
  unless ← withTransparency .all <| isDefEq decoded expected do
    throwError "the included numeral's descriptor changed its complete fixed meaning"
  let computed ← elabTermAndSynthesize
    (← `(TypeCat.ofHom (fun _ : CasCatalogue.Foundation.Objects.fin 1 =>
      ((3 : Nat) : WithBot Nat)))) none
  unless computed != expected && (← withTransparency .all <| isDefEq computed expected) do
    throwError "the point control needs two distinct presentations of the same fixed formal value"
  let claim : Language.Claim := .homs computed expected sets (← mkEq computed expected)
    "the computed plain point" "the independently included numeral"
  for (answer, correct) in #[(3, true), (4, false)] do
    let data := Json.mkObj [("ctor", toJson "some"), ("args", Json.arr #[toJson answer])]
    if let .error message ← Codec.decode target data then
      throwError "the adversarial point is not complete plain data: {message}"
    harness.results.modify (·.insert computed {
      form := .canonicalMorphism sets, payload := .computed computed (.inline data) })
    let actual ← Realize.realizeClaim harness trace claim
    unless (match actual with | .holds => correct | .wrong _ => !correct | _ => false) do
      throwError "plain-point observation did not compare the returned data with the declared inclusion"
  unless (← harness.connections.get).isEmpty do
    throwError "plain-point observation unnecessarily started a computational session"
