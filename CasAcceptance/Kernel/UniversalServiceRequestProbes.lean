module
import CasCatalogue.UniversalServiceRequest
meta import CasCatalogue.UniversalServiceRequest
import LeanCategories.Catalogue.Semantics.Independent.ScalarAndFormExtensions
meta import LeanCategories.Catalogue.Semantics.Independent.ScalarAndFormExtensions

open Lean Meta Elab Term CategoryTheory CasCatalogue
open CasCatalogue.ServiceRequest
open CasCatalogue.SimpleServiceRequest (node)

/- These controls supply typed operand handles from accepted formal fixtures.
They execute no backend, manufacture no mathematical law and make no live owner claim. -/

private def opaqueField (name : String) : Json := node "opaqueData" #[toJson name]
private def ref (index : Nat) : Json := node "resultRef" #[toJson index]
private def typed (source target : Json) (name : String) : Json :=
  node "typedMap" #[source, target, opaqueField name]

private def refuses (fragment : String) (work : TermElabM α) : TermElabM Unit := do
  let rejected ← withoutModifyingState do
    try
      discard <| work
      return false
    catch error =>
      let message ← error.toMessageData.toString
      unless (message.splitOn fragment).length > 1 do throw error
      return true
  unless rejected do throwError "control unexpectedly accepted: {fragment}"

private def decoder (operands : Array Operand)
    (endpoints : Array (Nat × Nat × Nat) := #[])
    (projections : Array (Nat × String × Nat) := #[])
    (conditions : Array Expr := #[]) : Decoder := Id.run do
  let lookup := fun data => do
    let operand ← if let .ok ("resultRef", #[index]) := ComputationalData.envelope data then
      let .ok index := index.getNat? | throwStratum .malformed "bad control reference"
      let some operand := operands[index]? | throwStratum .malformed "unknown control reference"
      pure operand
    else
      let some operand := operands.find? (·.data == data)
        | throwStratum .malformed "no retained control operand for packet"
      pure operand
    return operand
  return {
    argument := fun expected data => do
      let operand ← lookup data
      unless ← withTransparency .all <| isDefEq (← inferType operand.value) expected do
        throwStratum .malformed "control operand has wrong complete type"
      return operand
    object := lookup
    arrow := fun data => do
      let operand ← lookup data
      unless (Language.homEnds? (← inferType operand.value)).isSome do
        throwStratum .malformed "control operand is not a complete Hom"
      return operand
    endpoint := fun operand sourceSide => do
      let some (_, source, destination) := endpoints.find? (·.1 == operand.handle)
        | throwStratum .malformed "control map has no retained endpoints"
      let some result := operands[if sourceSide then source else destination]?
        | throwError "bad endpoint control fixture"
      return result
    project := fun operand field index => do
      unless index.isNone do throwError "unexpected indexed projection in control"
      let some (_, _, selected) := projections.find? (fun row => row.1 == operand.handle && row.2.1 == field)
        | throwStratum .malformed "control object has no retained field"
      let some result := operands[selected]? | throwError "bad projection control fixture"
      return result
    condition := fun expected => do
      for condition in conditions do
        if !condition.hasSorry && (← Decide.kernelAccepts expected condition) then return condition
      throwStratum .noImplementation "no independent formal condition in control"
    declaration := fun name data => do
      let operands ← data.mapM lookup
      let application ← DirectConstruction.instantiate name (← operands.mapM fun operand => exprToSyntax operand.value)
      let required ← DirectConstruction.dataArguments application.explicit
      unless required.size == data.size do
        throwStratum .malformed "control declaration omitted a selected data parameter"
      return { application, operands } }

private def limitControl (colimit : Bool) : TermElabM Unit := do
  let state ← registryState
  let id := if colimit then "colim.sets.coproduct" else "lim.sets.product"
  let some row := state.limits.find? (·.id.raw == id) | throwError "published row missing"
  let some category := state.categories.find? (·.id == row.category) | throwError "category missing"
  let first ← elabTermAndSynthesize (← `(ULift.{0} (Fin 2))) none
  let second ← elabTermAndSynthesize (← `(ULift.{0} (Fin 3))) none
  let operands : Array Operand := #[
    {value := first, data := opaqueField "first actual input", handle := 0},
    {value := second, data := opaqueField "second actual input", handle := 1}]
  let some constructor ← Semantic.diagramConstructor row | throwError "diagram constructor missing"
  let template := node (Codec.label constructor) #[ref 0, ref 1]
  let some prepared ← UniversalServiceRequest.prepare? (decoder operands) (.limit row) (.diagrams category) template
    | throwError "universal family was not handled"
  unless prepared.request == node (Codec.label constructor) (operands.map (·.data)) do
    throwError "the universal request replaced actual input packets"
  unless prepared.dependencies.map (·.handle) == #[0, 1] && prepared.constructionInputs.isSome do
    throwError "the universal request lost typed dependencies or constructor-slot roles"
  let presentation ← Semantic.limitPresentation row (← mkAppM constructor #[first, second])
  let .ok plan ← StructuredResult.dataPlan row (← mkAppM constructor #[first, second]) presentation
    | throwError "published data plan missing"
  let answer := node (if colimit then "cocone" else "cone")
    (plan.ports.map fun port => opaqueField s!"untrusted output {port.index}")
  let .ok (some complete) ← prepared.complete answer
    | throwError "well-framed untrusted universal outputs did not complete"
  unless complete.answer == answer do throwError "universal answer data were replaced"
  let some validate := prepared.validateTemplate | throwError "typed template traversal missing"
  let seen ← IO.mkRef (#[] : Array Expr)
  validate (fun formal _ => seen.modify (·.push formal)) answer
  unless (← seen.get) == plan.ports.map (·.formalField) do
    throwError "template reference checks did not follow declared constructor slots"
  let wrong := node (if colimit then "cone" else "cocone") #[]
  if (← prepared.complete wrong).isOk then throwError "wrong universal direction was accepted"
  if (← prepared.complete (node (if colimit then "cocone" else "cone") #[])).isOk then
    throwError "missing complete universal fields were accepted"
  refuses "changes its registered diagram constructor" <|
    UniversalServiceRequest.prepare? (decoder operands) (.limit row) (.diagrams category)
      (node "wrongDiagram" #[ref 0, ref 1])

run_elab limitControl false
run_elab limitControl true

private def liftFixture (withCondition : Bool := true) :
    TermElabM (LiftEntry × Form × Decoder × Json × Array Json × Array Operand) := do
  let state ← registryState
  let some row := state.lifts.find? (·.id.raw == "lift.bilin_module.restrict")
    | throwError "published lift missing"
  let some form := state.liftInputForm? row.inputAddress | throwError "published lift input missing"
  let source ← elabTermAndSynthesize (← `(CasCatalogue.Modules.Bilinear.Valued.DegeneratePlaneLifts.source)) none
  let inclusion ← elabTermAndSynthesize (← `(CasCatalogue.Modules.Bilinear.Valued.DegeneratePlaneLifts.kernelInclusion)) none
  let evidence ← elabTermAndSynthesize (← `(CasCatalogue.Modules.Bilinear.Valued.DegeneratePlaneLifts.firstLift)) none
  let monic ← synthInstance (← mkAppM ``CategoryTheory.Mono #[inclusion])
  let plan ← SelectedLift.fromEvidence row evidence source inclusion monic
  let arrow ← mkAppM ``CategoryTheory.Arrow.mk #[inclusion]
  let baseType ← LiftedSubobjectData.subobjectType (← inferType arrow)
  let base ← elabTermAndSynthesize
    (← `(⟨$(← exprToSyntax arrow), $(← exprToSyntax monic)⟩)) (some baseType)
  let some (baseObject, ambient) := Language.homEnds? (← inferType inclusion) | unreachable!
  let cone ← elabTermAndSynthesize (← `(CasCatalogue.Modules.Bilinear.Valued.DegeneratePlaneFactorization.cone)) none
  let baseMap ← elabTermAndSynthesize (← `(CasCatalogue.Modules.Bilinear.Valued.DegeneratePlaneFactorization.baseMediator)) none
  let proof ← elabTermAndSynthesize (← `(CasCatalogue.Modules.Bilinear.Valued.DegeneratePlaneFactorization.cone_base_factorization)) none
  let some (domain, _) := Language.homEnds? (← inferType cone) | unreachable!
  let imageDomain ← Semantic.objOf plan.action domain
  let parameters ← DirectConstruction.dataArguments plan.parameters
  let parameterData := parameters.mapIdx fun index _ => opaqueField s!"actual ordered parameter {index}"
  let .functor functor ← SelectedLift.innerEdge state row | throwError "fixture action changed"
  let action := node functor.raw parameterData
  let sourceData := opaqueField "actual source"
  let baseObjectData := opaqueField "actual base object"
  let ambientData := opaqueField "actual image ambient"
  let inclusionData := typed baseObjectData ambientData "original inclusion"
  let baseData := node "subobject" #[baseObjectData, ambientData, inclusionData]
  let objectData := opaqueField "actual lift object"
  let imageData := node "functorAction" #[action, objectData]
  let outputs := #[objectData, typed objectData sourceData "defining map",
    typed imageData baseObjectData "forward", typed baseObjectData imageData "backward"]
  let domainData := opaqueField "original factor domain"
  let imageDomainData := node "functorAction" #[action, domainData]
  let coneData := typed domainData sourceData "cone"
  let baseMapData := typed imageDomainData baseObjectData "base factor"
  let p := parameters.size
  let fixed := #[source, base, baseObject, inclusion, ambient] ++ plan.ports ++
    #[cone, baseMap, domain, imageDomain, ← Semantic.objOf plan.action plan.ports[0]!]
  let actual := #[sourceData, baseData, baseObjectData, inclusionData, ambientData] ++ outputs ++
    #[coneData, baseMapData, domainData, imageDomainData, imageData]
  let operands := ((parameters.zip parameterData) ++ (fixed.zip actual)).mapIdx fun index pair =>
    ({ value := pair.1, data := pair.2, handle := index } : Operand)
  let endpoints := #[(p+3,p+2,p+4),(p+6,p+5,p),(p+7,p+13,p+2),(p+8,p+2,p+13),
    (p+9,p+11,p),(p+10,p+12,p+2)]
  let projections := #[(p+1,"obj",p+2),(p+1,"hom",p+3)]
  let decode := decoder operands endpoints projections (if withCondition then #[proof] else #[])
  let actionTemplate := node functor.raw ((List.range p).toArray.map ref)
  return (row, form, decode, actionTemplate, outputs, operands)

private def liftControl (field : LiftField) : TermElabM Unit := do
  let (row, form, decode, action, outputs, operands) ← liftFixture
  let p := operands.size - 14
  let some index := LiftField.all.findIdx? (· == field) | unreachable!
  let earlier := ((List.range index).toArray.map fun i => ref (p+5+i))
  let request := Json.mkObj [("ctor", "monoLiftInput"),
    ("parameters", Json.arr ((List.range p).toArray.map ref)),
    ("args", Json.arr #[toJson row.id.raw, action, ref p, ref (p+1), Json.arr earlier])]
  let some prepared ← UniversalServiceRequest.prepare? decode (.liftField row field) form request
    | throwError "lift family was not handled"
  let .ok invocation := Backend.LiftInput.decode prepared.request (row.fieldAddress field)
    | throwError "prepared lift framing failed"
  unless invocation.parameters == (operands.extract 0 p).map (·.data) &&
      invocation.outputs == outputs.extract 0 index &&
      invocation.source == (operands.map (·.data))[p]! && invocation.base == (operands.map (·.data))[p+1]! do
    throwError "lift request replaced ordered parameters or actual retained packets"
  for i in [:p] do
    unless (prepared.dependencies.map (·.handle)).contains i do throwError "lift parameter handle lost"
  unless (← prepared.complete outputs[index]!).isOk do throwError "complete selected lift field rejected"
  if field != .obj then
    if (← prepared.complete (typed (opaqueField "wrong endpoint") (opaqueField "wrong endpoint") "wrong")).isOk then
      throwError "changed lift endpoints accepted"
  let missing := Json.mkObj [("ctor", "monoLiftInput"),
    ("args", Json.arr #[toJson row.id.raw, action, ref p, ref (p+1), Json.arr earlier])]
  refuses "omitted its selected evidence parameters" <|
    UniversalServiceRequest.prepare? decode (.liftField row field) form missing
  if index > 0 then
    let wrongEarlier := earlier.set! 0 (ref p)
    let wrong := Json.mkObj [("ctor", "monoLiftInput"),
      ("parameters", Json.arr ((List.range p).toArray.map ref)),
      ("args", Json.arr #[toJson row.id.raw, action, ref p, ref (p+1), Json.arr wrongEarlier])]
    refuses "preceding lift output" <|
      UniversalServiceRequest.prepare? decode (.liftField row field) form wrong

run_elab liftControl .obj
run_elab liftControl .hom
run_elab liftControl .forward
run_elab liftControl .backward

run_elab do
  let (row, form, decode, action, outputs, operands) ← liftFixture
  let p := operands.size - 14
  let some source := operands[p]? | throwError "original source control missing"
  let originalHom ← elabTermAndSynthesize
    (← `(CasCatalogue.Modules.Bilinear.Valued.DegeneratePlaneLifts.formedMap)) none
  let original ← mkAppM ``CategoryTheory.Arrow.mk #[originalHom]
  let originalData := node "arrow" #[source.data, opaqueField "original target", opaqueField "original arrow"]
  let exact : Operand := { value := original, data := originalData, handle := 1000 }
  let decode := { decode with
    argument := fun expected data => do
      if data == ref 1000 then
        unless ← withTransparency .all <| isDefEq (← inferType exact.value) expected do
          throwError "original Arrow control has wrong type"
        return exact
      decode.argument expected data
    project := fun operand field index => do
      if operand.handle == 1000 && field == "source" && index.isNone then return source
      decode.project operand field index }
  let request := Json.mkObj [("ctor", "liftInput"),
    ("parameters", Json.arr ((List.range p).toArray.map ref)),
    ("args", Json.arr #[toJson row.id.raw, action, ref 1000, ref (p+1), Json.arr #[]])]
  let some prepared ← UniversalServiceRequest.prepare? decode (.liftField row .obj) form request
    | throwError "original Arrow lift family was not handled"
  let .ok invocation := Backend.LiftInput.decode prepared.request (row.fieldAddress .obj)
    | throwError "original Arrow request framing failed"
  unless invocation.originalArrow && invocation.source == originalData &&
      (prepared.dependencies.map (·.handle)).contains 1000 do
    throwError "original Arrow request dropped its complete retained source handle or packet"
  unless (← prepared.complete outputs[0]!).isOk do
    throwError "original Arrow lift object output failed"

run_elab do
  let (row, form, decode, action, outputs, operands) ← liftFixture
  let p := operands.size - 14
  let request := Json.mkObj [("ctor", "liftFactorInput"),
    ("parameters", Json.arr ((List.range p).toArray.map ref)),
    ("args", Json.arr #[toJson row.id.raw, action, ref p, ref (p+1),
      Json.arr ((List.range 4).toArray.map fun i => ref (p+5+i)), ref (p+10), ref (p+9)])]
  let some prepared ← UniversalServiceRequest.prepare? decode (.liftFactor row) form request
    | throwError "factor family was not handled"
  let .ok invocation := Backend.LiftFactorInput.decode prepared.request row.factorAddress
    | throwError "prepared factor framing failed"
  unless invocation.outputs == outputs && invocation.parameters == (operands.extract 0 p).map (·.data) do
    throwError "factor lost ordered parameters or actual existing outputs"
  unless (← prepared.complete (typed (operands.map (·.data))[p+11]! outputs[0]! "factor result")).isOk do
    throwError "well-framed factor result rejected"
  if (← prepared.complete (typed outputs[0]! (operands.map (·.data))[p+11]! "reversed factor")).isOk then
    throwError "reversed factor endpoints accepted"
  let (_, _, unproved, _, _, _) ← liftFixture false
  refuses "no independent formal condition" <|
    UniversalServiceRequest.prepare? unproved (.liftFactor row) form request
  let fakeProof := Json.mkObj [("ctor", "liftFactorInput"),
    ("parameters", Json.arr ((List.range p).toArray.map ref)),
    ("args", (request.getObjVal? "args").toOption.get!), ("proof", toJson true)]
  refuses "no independent formal condition" <|
    UniversalServiceRequest.prepare? unproved (.liftFactor row) form fakeProof
  logInfo "Universal service framing, typed dependencies and independent formal-condition controls passed."
