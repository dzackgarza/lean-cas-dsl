module

public import LeanCategories.Catalogue.Semantics.Limits.Registration
public import LeanCategories.Catalogue.Semantics.Limits.Lifts
public meta import LeanCategories.Catalogue.Semantics.Limits.Lifts
public import LeanCategories.Catalogue.Semantics.Foundation.Objects
public meta import CasCatalogue.StructuredResult
public meta import CasCatalogue.ComputationalData
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Mono

/-! Engineering checks of the semantic/computational boundary and constructor-role
provenance. Wrong computational claims remain data and never supply universal laws. -/

open Lean Meta Elab Term Command CategoryTheory Limits CasCatalogue

namespace CasAcceptance.StructuredComparisonProbes

run_elab do
  let state ← registryState
  let some row := state.limits.find? (·.id.raw == "lim.sets.pullback")
    | throwError "missing registered set pullback"
  -- The formal apex and both input objects deliberately coincide. Their constructor
  -- roles must still differ when the computational apex is a wrong Fin 3.
  let presentation ← elabTermAndSynthesize (← `(({
    cone := PullbackCone.mk (𝟙 (Fin 2)) (𝟙 (Fin 2)) (by rfl)
    isLimit := PullbackCone.isLimitMkIdId (𝟙 (Fin 2)) } :
    LimitCone (cospan (𝟙 (Fin 2)) (𝟙 (Fin 2)))))) none
  let presentationType ← whnfR (← inferType presentation)
  let diagram := presentationType.getAppArgs.back!
  let plan ← match ← StructuredResult.dataPlan row diagram presentation with
    | .ok plan => pure plan
    | .error message => throwError "formal construction data plan failed: {message}"
  let #[apexPort, leftPort, rightPort] := plan.ports
    | throwError "the public pullback constructor lost its apex or defining legs"
  let some leftDomain := leftPort.domainBinder
    | throwError "the left defining leg lost its source role"
  let some rightDomain := rightPort.domainBinder
    | throwError "the right defining leg lost its source role"
  unless leftDomain == apexPort.constructorBinder && rightDomain == leftDomain do
    throwError "defining legs do not depend on the actual returned apex slot"
  let some leftTarget := leftPort.codomainBinder
    | throwError "the left defining leg lost its target role"
  let some rightTarget := rightPort.codomainBinder
    | throwError "the right defining leg lost its target role"
  unless leftTarget != leftDomain && rightTarget != rightDomain do
    throwError "formal equality merged returned-apex and input-diagram roles"
  let apexField := apexPort.formalField
  let some leftBinding := plan.binders[leftTarget]?
    | throwError "the retained diagram role disappeared"
  let some leftValue := leftBinding.formalValue
    | throwError "the input-diagram role lacks its independent formal context"
  unless ← withTransparency .all <| isDefEq apexField leftValue do
    throwError "fixture does not exercise coincident formal objects"
  let fin (n : Nat) := Json.mkObj [("ctor", toJson "obj.sets.fin"),
    ("args", Json.arr #[toJson n])]
  let fin2 := fin 2
  let fin3 := fin 3
  let graph (values : Array Nat) := Json.arr <| values.mapIdx fun index value =>
    Json.arr #[toJson index, toJson value]
  let leftGraph := graph #[0, 1, 0]
  let rightGraph := graph #[1, 0, 1]
  let answer := Json.mkObj [("ctor", toJson "cone"),
    ("args", Json.arr #[fin3, leftGraph, rightGraph])]
  let endpointKeys (descriptor : Json) : TermElabM (Except String (Option (Array Json))) := do
    let .ok ("obj.sets.fin", #[size]) := ComputationalData.envelope descriptor
      | return .error "endpoint has no complete published finite descriptor"
    let .ok size := fromJson? (α := Nat) size
      | return .error "finite endpoint cardinal is not a natural"
    return .ok (some ((List.range size).toArray.map toJson))
  let inputArrow := Json.mkObj [("ctor", toJson "arrow"),
    ("args", Json.arr #[fin2, fin2, graph #[0, 1]])]
  let inputArrows := #[inputArrow, inputArrow]
  let resolveRole (role : StructuredResult.InputRole) : Option Json := do
    let position := match role with
      | .argument position | .source position | .target position => position
    let arrow ← inputArrows[position]?
    match role with
    | .argument _ => return arrow
    | .source _ =>
        let args ← ((arrow.getObjVal? "args").bind (·.getArr?)).toOption
        args[0]?
    | .target _ =>
        let args ← ((arrow.getObjVal? "args").bind (·.getArr?)).toOption
        args[1]?
  let externalDescriptor := fun binder => do
    let binding ← plan.binders[binder]?
    let role ← binding.inputRoles[0]?
    let descriptor ← resolveRole role
    if binding.inputRoles.all (fun other => resolveRole other == some descriptor) then
      some descriptor
    else none
  unless externalDescriptor leftTarget == some fin2 &&
      externalDescriptor rightTarget == some fin2 do
    throwError "the input endpoint roles did not resolve through the retained input arrows"
  unless (externalDescriptor leftDomain).isNone do
    throwError "the returned apex acquired an input-diagram role"
  let validate (data : Json) := StructuredResult.validatePlannedData plan data
    fun port seen value => do
      match ← ComputationalData.validatePlannedPort plan port seen value
          externalDescriptor endpointKeys with
      | .ok () => return .ok ()
      | .error message =>
          let field ← ppExpr port.formalField
          let type ← ppExpr port.expectedType
          return .error s!"port {port.index}: {message}; formalField={field}; expectedType={type}"
  match ← validate answer with
  | .ok () => pure ()
  | .error message => throwError "wrong-apex packet framing failed: {message}"
  unless plan.actualData? leftDomain #[fin3] == some fin3 do
    throwError "the returned apex role did not resolve to actual Fin 3 data"
  unless (plan.actualData? leftTarget #[fin3]).isNone do
    throwError "the diagram role was incorrectly filled from the equal formal apex"
  let diagramData := Json.mkObj [("ctor", toJson "cospan"),
    ("args", Json.arr inputArrows)]
  let .ok result ← StructuredResult.complete row diagram diagramData (.direct answer)
      presentation validate
    | throwError "opaque answer failed to attach to the independent formal construction"
  unless result.answer == answer && result.diagramJson == diagramData do
    throwError "the original computational packet or input context was replaced"
  unless ← withTransparency .all <| isDefEq result.apex apexField do
    throwError "a wrong computational apex changed formal meaning"
  unless ← withTransparency .all <| isDefEq result.presentation presentation do
    throwError "a backend packet replaced the formal universal construction"
  let leftIndex ← elabTermAndSynthesize (← `(WalkingCospan.left)) none
  let rightIndex ← elabTermAndSynthesize (← `(WalkingCospan.right)) none
  for (index, actual) in #[(leftIndex, leftGraph), (rightIndex, rightGraph)] do
    let .ok projected ← StructuredResult.projectData row diagram answer index
      | throwError "a required defining leg could not consume its returned data"
    unless projected == actual do
      throwError "a defining leg was replaced by its canonical formal map"
    let formalLeg ← result.leg index
    discard <| StructuredResult.checkReconstruction formalLeg
  let malformedGraph := graph #[0, 1]
  let outOfRangeGraph := graph #[0, 1, 2]
  let packet (fields : Array Json) := Json.mkObj [("ctor", toJson "cone"),
    ("args", Json.arr fields)]
  for malformed in #[packet #[fin3, malformedGraph, rightGraph],
      packet #[fin3, outOfRangeGraph, rightGraph], packet #[fin3, leftGraph],
      packet #[fin3, leftGraph, rightGraph, fin2]] do
    if (← validate malformed).isOk then
      throwError "incomplete graph, wrong actual endpoint or incomplete packet accepted"
  let duplicateGraph := Json.arr #[Json.arr #[toJson (0 : Nat), toJson (0 : Nat)],
    Json.arr #[toJson (0 : Nat), toJson (1 : Nat)],
    Json.arr #[toJson (2 : Nat), toJson (0 : Nat)]]
  if (← validate (packet #[fin3, duplicateGraph, rightGraph])).isOk then
    throwError "a repeated graph-domain key was accepted"
  let sourceDiagram := Json.mkObj [("originalSourceDiagram", diagramData)]
  let createdPacket := StructuredResult.ComputationPacket.created
    LiftId.finiteSetsPullbacks.raw sourceDiagram answer
  let .ok created ← StructuredResult.complete row diagram diagramData createdPacket
      presentation validate
    | throwError "complete creation provenance was discarded"
  let expectedJson := Json.mkObj [("ctor", toJson "createdCone"),
    ("args", Json.arr #[toJson LiftId.finiteSetsPullbacks.raw, sourceDiagram, answer])]
  unless created.json == expectedJson && created.answer == answer do
    throwError "creation provenance or opaque answer was reconstructed or copied"
  unless ← withTransparency .all <| isDefEq created.apex result.apex do
    throwError "creation provenance changed independently fixed formal meaning"
  logInfo "PASS: coincident formal objects retain distinct data roles; wrong Fin 3 apex accepted; actual graph endpoints, opaque defining legs and creation provenance retained"

end CasAcceptance.StructuredComparisonProbes
