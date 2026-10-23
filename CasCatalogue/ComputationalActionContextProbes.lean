module

import CasCatalogue.LiftedSubobjectData
import LeanCategories.Catalogue.Semantics
meta import CasCatalogue.LiftedSubobjectData
meta import LeanCategories.Catalogue.Semantics

open Lean Meta Elab Term CasCatalogue

/-! Engineering checks of action framing at fixed public projection contexts.
No returned computational data establishes a mathematical object or its laws. -/

run_elab do
  let state ← registryState
  let some kernel := state.functors.find? (·.id.raw == "fun.arrows_groups.kernel")
    | throwError "missing public kernel action"
  let some domain := state.functors.find? (·.id.raw == "fun.subobjects_groups.domain")
    | throwError "missing public subobject-domain action"
  let sign ← elabTermAndSynthesize (← `(CasCatalogue.Algebra.FiniteGroups.sign 3)) none
  let arrow ← mkAppM ``CategoryTheory.Arrow.mk #[sign]
  let fixed ← Semantic.objOf (← instantiateFresh kernel.declaration) arrow
  let inclusion ← mkAppM ``CategoryTheory.ObjectProperty.FullSubcategory.obj #[fixed]
  let projected ← mkAppM ``CategoryTheory.Arrow.left #[inclusion]
  let direct ← Semantic.objOf (← instantiateFresh domain.declaration) fixed
  let wire := fun (tag : String) (args : Array Json) =>
    Json.mkObj [("ctor", toJson tag), ("args", Json.arr args)]
  let source := wire "obj.subgroups.kernel" #[
    wire "obj.groups.symmetric" #[toJson (3 : Nat)],
    wire "obj.groups.cyclic" #[toJson (2 : Nat)],
    wire "mor.groups.sign" #[toJson (3 : Nat)]]
  let edge := wire domain.id.raw #[]
  let action := wire "functorAction" #[edge, source]
  for context in #[projected, direct] do
    match ← ComputationalData.validatePort context (← inferType context) action with
    | .ok () => pure ()
    | .error message => throwError "complete public action context rejected: {message}"
  for changed in #[
      wire "functorAction" #[wire "fun.subobjects_groups.inclusion" #[], source],
      wire "functorAction" #[edge, wire "obj.groups.symmetric" #[toJson (3 : Nat)]],
      wire "functorAction" #[edge, wire "obj.subgroups.kernel" #[
        wire "obj.groups.symmetric" #[toJson (3 : Nat)],
        wire "obj.groups.cyclic" #[toJson (2 : Nat)],
        wire "mor.groups.sign" #[toJson "not-a-numeral"]]]] do
    let .error _ ← ComputationalData.validatePort projected (← inferType projected) changed
      | throwError "changed action, receiver category or dependent field framing was accepted"
  -- Deliberately invented computational carriers test framing, not the actual
  -- kernel or group laws. The public question and all formal maps stay fixed.
  let graph := fun (pairs : Array (Nat × Nat)) => Json.arr (pairs.map fun (x, y) =>
    Json.arr #[toJson (x : Nat), toJson (y : Nat)])
  let identity := graph #[(0, 0), (1, 1), (2, 2)]
  let forward := graph #[(0, 1), (1, 2), (2, 0)]
  let backward := graph #[(0, 2), (1, 0), (2, 1)]
  let point := Json.arr #[forward, backward]
  let other := Json.arr #[identity, identity]
  let points := #[point, other]
  let finite := fun descriptor points => wire "finiteData" #[descriptor, Json.arr points]
  let target := wire "obj.groups.symmetric" #[toJson (3 : Nat)]
  let callable := Json.arr (points.map fun p => Json.arr #[p, p])
  let packet := fun apex ambient definingMap => wire "subobject" #[apex, ambient, definingMap]
  let apex := finite action points
  let ambient := finite target points
  let check := fun data => do ComputationalData.validatePort fixed (← inferType fixed) data
  if let .error message ← check (packet apex ambient callable) then
    throwError "complete finite computational fields rejected: {message}"
  -- A false inverse law is not a framing failure or a proof produced here.
  let unproved := Json.arr #[identity, backward]
  let wrongApex := finite action #[unproved]
  let wrongAmbient := finite target #[unproved]
  if let .error message ← check
      (packet wrongApex wrongAmbient (Json.arr #[Json.arr #[unproved, unproved]])) then
    throwError "well-framed unproved computational data rejected: {message}"
  let incompletePoint := Json.arr #[graph #[(0, 1), (1, 2)], backward]
  let missingSlot := Json.arr #[forward]
  for changed in #[
      packet action ambient callable,
      packet (finite action #[point, point]) ambient callable,
      packet apex ambient (Json.arr #[Json.arr #[point, point]]),
      packet apex ambient (Json.arr #[Json.arr #[point, point], Json.arr #[point, other]]),
      packet (finite action #[incompletePoint]) ambient callable,
      packet (finite action #[missingSlot]) ambient callable,
      packet apex (finite target #[point]) callable] do
    let .error _ ← check changed
      | throwError "missing inventory, incomplete graph or malformed computational fields accepted"

  let formalMap ← mkAppM ``CategoryTheory.Arrow.hom #[inclusion]
  let typed := fun domain codomain definingMap => wire "typedMap" #[domain, codomain, definingMap]
  if let .error message ← LiftedSubobjectData.validateMap formalMap action target
      (typed apex ambient callable) then
    throwError "exact symbolic endpoints rejected their explicit inventories: {message}"
  for (expectedSource, expectedTarget, actual) in #[
      (apex, ambient, typed (finite action #[point]) ambient
        (Json.arr #[Json.arr #[point, point]])),
      (action, target, typed (finite target points) ambient callable),
      (action, target, typed
        (wire "finiteData" #[action, toJson "not-an-inventory"]) ambient callable),
      (action, target, typed apex ambient (Json.arr #[Json.arr #[point, point]]))] do
    let .error _ ← LiftedSubobjectData.validateMap formalMap expectedSource expectedTarget actual
      | throwError "lift endpoint replacement, malformed inventory or incomplete map accepted"

run_elab do
  -- A deliberately wrong four-point apex for the formal six-point product
  -- must retain its own released scalar codec and both defining-map roles.
  let state ← registryState
  let some row := state.limits.find? (·.id.raw == "lim.sets.product")
    | throwError "missing released product"
  let left ← elabTermAndSynthesize (← `(CasCatalogue.Foundation.Objects.fin 2)) none
  let right ← elabTermAndSynthesize (← `(CasCatalogue.Foundation.Objects.integersMod 3)) none
  let formal ← mkAppM row.declaration #[left, right]
  let cone ← mkAppM ``CategoryTheory.Limits.LimitCone.cone #[formal]
  let diagram := (← whnfR (← inferType cone)).getAppArgs.back!
  let .ok plan ← StructuredResult.dataPlan row diagram formal
    | throwError "the public product has no complete data plan"
  let wire := fun tag args => Json.mkObj [("ctor", toJson (tag : String)), ("args", Json.arr args)]
  let named := fun tag n => wire tag #[toJson (n : Nat)]
  let input := #[named "obj.sets.fin" 2, named "obj.sets.integers_mod" 3]
  let keys := (Array.range 4).map toJson
  let apex := wire "finiteData" #[named "obj.sets.fin" 4, Json.arr keys]
  let pairs := keys.map fun x => Json.arr #[x, toJson (0 : Nat)]
  let graph := fun inventory pairs => wire "finiteGraph" #[Json.arr inventory, Json.arr pairs]
  let leg := graph keys pairs
  let packet := fun object first second => wire "cone" #[object, first, second]
  let external := fun binder => Id.run do
    let some binding := plan.binders[binder]? | return none
    for role in binding.inputRoles do
      if let .argument index := role then return input[index]?
    return none
  let check := fun answer => StructuredResult.validatePlannedData plan answer
    fun port seen data => ComputationalData.validatePlannedPort plan port seen data external
      ComputationalData.endpointKeys
  if let .error message ← check (packet apex leg leg) then
    throwError "noncanonical scalar apex or its complete defining maps rejected: {message}"
  let wrongFin := graph keys (pairs.set! 0 (Json.arr #[toJson (0 : Nat), toJson (2 : Nat)]))
  let wrongMod := graph keys (pairs.set! 0 (Json.arr #[toJson (0 : Nat), toJson (3 : Nat)]))
  for changed in #[
      packet (wire "finiteData" #[named "obj.sets.fin" 4, Json.arr (keys.extract 0 3)]) leg leg,
      packet apex (graph keys (pairs.extract 0 3)) leg,
      packet apex (graph (keys.extract 0 3) (pairs.extract 0 3)) leg,
      packet apex wrongFin leg,
      packet apex leg wrongMod] do
    let .error _ ← check changed
      | throwError "actual primitive codec bounds, inventory or complete graph checks were bypassed"
