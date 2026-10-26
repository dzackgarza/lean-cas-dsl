module

import CasCatalogue.Realize
import Mathlib.CategoryTheory.SingleObj
meta import CasCatalogue.Realize

open Lean Meta Elab Command Term CategoryTheory
open CasCatalogue CasCatalogue.Language CasCatalogue.Realize

/- External engineering controls only. Existing mathematical declarations fix
all types. These checks inspect framing, inventory authority and ownership;
they do not assert a computed mathematical answer or author a leaf. -/

meta section

private def packet (tag : String) (args : Array Json) : Json :=
  Json.mkObj [("ctor", toJson tag), ("args", Json.arr args)]

private def valid (label : String) (expected : Expr) (data : Json)
    (objects : ComputationalData.InterfaceObjects := #[]) : TermElabM Unit := do
  if let .error message ← ComputationalData.validateCallableAt objects expected data then
    throwError "{label}: {message}"

private def invalid (label : String) (expected : Expr) (data : Json)
    (objects : ComputationalData.InterfaceObjects := #[]) : TermElabM Unit := do
  let .error _ ← ComputationalData.validateCallableAt objects expected data
    | throwError "{label}: an incompatible complete interface was accepted"

private partial def containsPacket (whole wanted : Json) : Bool :=
  whole == wanted || match whole with
    | .arr fields => fields.any (containsPacket · wanted)
    | .obj fields => fields.any fun _ value => containsPacket value wanted
    | _ => false

run_elab do
  let fin := fun n => packet "obj.sets.fin" #[toJson (n : Nat)]
  let naturals := packet "obj.sets.naturals" #[]
  let integers := packet "obj.sets.integers" #[]
  let terminal := packet "obj.sets.terminal" #[]
  let maps := packet "obj.sets.maps" #[naturals, integers]
  let target ← elabTermAndSynthesize (← `(CasCatalogue.Foundation.Maps.maps ℕ ℤ)) none
  let one ← globalPointSource.run {}
  let expected ← mkAppM ``Quiver.Hom #[one, target]
  let opaqueValue := packet "opaqueData" #["the exact original infinite callable"]
  let inner := packet "typedMap" #[naturals, integers, opaqueValue]
  let admitted : Backend.AdmittedPoint := {
    object := "obj.sets.maps", parameters := #[naturals, integers]
    domain := fin 1, source := maps, target := maps, argument := inner }
  valid "whole function as one selected global point" expected admitted.encode
  invalid "internal domain changed" expected
    { admitted with argument := packet "typedMap" #[fin 2, integers, opaqueValue] }.encode
  invalid "internal target changed" expected
    { admitted with argument := packet "typedMap" #[naturals, fin 2, opaqueValue] }.encode
  invalid "internal domain substituted for outer point domain" expected
    { admitted with domain := naturals }.encode
  let graph := fun keys rows => packet "finiteGraph" #[Json.arr keys, Json.arr rows]
  let row := fun key value => Json.arr #[key, value]
  let framed := fun value => packet "typedMap" #[fin 1, maps, value]
  let complete := framed (graph #[toJson (0 : Nat)] #[row (toJson (0 : Nat)) inner])
  valid "complete function-valued point graph" expected complete
  invalid "outer graph missing its actual input" expected
    (framed (graph #[toJson (0 : Nat)] #[]))
  invalid "outer graph duplicates an actual input" expected
    (framed (graph #[toJson (0 : Nat)]
      #[row (toJson (0 : Nat)) inner, row (toJson (0 : Nat)) inner]))
  invalid "explicit inventory changed despite known actual keys" expected
    (framed (graph #[toJson (0 : Nat), toJson (1 : Nat)] #[row (toJson (0 : Nat)) inner]))
  invalid "nested function changes its full source" expected
    (framed (graph #[toJson (0 : Nat)]
      #[row (toJson (0 : Nat)) (packet "typedMap" #[fin 2, integers, opaqueValue])]))
  let actualValue := packet "opaqueData" #["one independently listed function value"]
  let finiteTarget := packet "finiteData" #[maps, Json.arr #[actualValue]]
  valid "known actual function codomain inventory" expected
    (packet "typedMap" #[fin 1, finiteTarget,
      graph #[toJson (0 : Nat)] #[row (toJson (0 : Nat)) actualValue]])
  valid "known inventory still checks a complete nested callable" expected
    (packet "typedMap" #[fin 1, packet "finiteData" #[maps, Json.arr #[inner]],
      graph #[toJson (0 : Nat)] #[row (toJson (0 : Nat)) inner]])
  let badInner := packet "typedMap" #[fin 2, integers, opaqueValue]
  invalid "inventory membership cannot authorize a different inner Hom" expected
    (packet "typedMap" #[fin 1, packet "finiteData" #[maps, Json.arr #[badInner]],
      graph #[toJson (0 : Nat)] #[row (toJson (0 : Nat)) badInner]])
  let badTarget := packet "typedMap" #[naturals, fin 2, opaqueValue]
  invalid "inventory membership cannot authorize a different inner target" expected
    (packet "typedMap" #[fin 1, packet "finiteData" #[maps, Json.arr #[badTarget]],
      graph #[toJson (0 : Nat)] #[row (toJson (0 : Nat)) badTarget]])
  invalid "function-shaped value escapes actual codomain inventory" expected
    (packet "typedMap" #[fin 1, finiteTarget,
      graph #[toJson (0 : Nat)] #[row (toJson (0 : Nat)) inner]])
  let punit ← elabTermAndSynthesize (← `(PUnit.{1})) none
  let punitType ← mkAppM ``Quiver.Hom #[punit, target]
  let inverse := packet "presentation" #["cmp.sets.singleton_terminal", Json.arr #[], toJson true]
  let restaged := packet "typedMap" #[terminal, maps, packet "compose" #[inverse, complete]]
  valid "PUnit point retains its complete comparison and callable" punitType restaged
  invalid "PUnit is not the scalar convention" punitType inner
  invalid "PUnit has no invented formal singleton inventory" punitType
    (packet "typedMap" #[terminal, maps, Json.arr #[row (Json.arr #[]) inner]])
  let natType ← elabTermAndSynthesize (← `(ℕ)) none
  let intType ← elabTermAndSynthesize (← `(ℤ)) none
  let directHom ← mkAppM ``Quiver.Hom #[natType, intType]
  for declared in #[directHom, target] do
    let some retained ← ComputationalData.declaredCallableType? declared
      | throwError "the complete direct or definition-aliased callable type was lost"
    unless ← withTransparency .all <| isDefEq retained directHom do
      throwError "the callable classification changed its independently declared complete type"
    valid "strict direct/alias complete callable" retained inner
    invalid "strict direct/alias source" retained badInner
    invalid "strict direct/alias target" retained badTarget
  -- An interface association may retain a definitionally equal expression,
  -- but it cannot replace the admission's independently declared scalar input
  -- by a Hom-shaped expression and thereby choose the map-data validator.
  let scalarHom ← elabTermAndSynthesize
    (← `((SingleObj.star ℕ) ⟶ (SingleObj.star ℕ))) none
  unless ← withTransparency .all <| isDefEq scalarHom natType do
    throwError "the scalar alias control has no common underlying type"
  let star ← elabTermAndSynthesize (← `(SingleObj.star ℕ)) none
  let sourceToken := packet "opaqueData" #["the retained single-object source"]
  let targetToken := packet "opaqueData" #["the retained single-object target"]
  let positive := packet "obj.sets.positive_naturals" #[]
  let positiveType ← elabTermAndSynthesize
    (← `(CasCatalogue.Algebra.Semirings.positiveNaturals)) none
  let positiveExpected ← mkAppM ``Quiver.Hom #[one, positiveType]
  let scalarAdmission : Backend.AdmittedPoint := {
    object := "obj.sets.positive_naturals", parameters := #[]
    domain := fin 1, source := naturals, target := positive, argument := toJson (0 : Nat) }
  let scalarObjects : ComputationalData.InterfaceObjects :=
    #[(naturals, scalarHom), (sourceToken, star), (targetToken, star)]
  valid "declared scalar input survives a retained definition alias" positiveExpected
    scalarAdmission.encode scalarObjects
  invalid "a retained scalar alias cannot select the callable validator" positiveExpected
    { scalarAdmission with argument := packet "typedMap" #[sourceToken, targetToken, opaqueValue] }.encode
    scalarObjects
  logInfo "PASS: full callable types, actual inventories and declared scalar input authority"

run_elab do
  let state ← registryState
  let some rings := state.categories.find? (·.id == CategoryId.rings)
    | throwError "the published ring category is absent"
  let some sets := state.categories.find? (·.id == CategoryId.sets)
    | throwError "the published set category is absent"
  let trace ← Trace.new
  let ringValue ← (object state "ℤ" #[] (some rings)).run { trace := some trace }
  let ring ← (semanticObject ringValue).run {}
  let some moduleCategory := state.categories.find? (·.id == CategoryId.modulesR)
    | throwError "the published module category is absent"
  let moduleValue ← (object state "RegularModule" #[ringValue] (some moduleCategory)).run
    { trace := some trace }
  let module ← (semanticObject moduleValue).run {}
  let context ← CategoryContext.ofNamed moduleCategory module
  let identity ← mkAppM ``CategoryTheory.CategoryStruct.id #[module]
  Trace.record (some trace) identity (.contextualIdentity context module)
  discard <| Semantic.recordNamedObject module (some trace)
  let owner ← wholeCallableObject identity module module context
  unless ← withTransparency .all <| isDefEq owner.application.value (← inferType identity) do
    throwError "the complete module Hom owner was erased to a carrier function"
  let some innerHom ← ComputationalData.declaredCallableType? owner.application.value
    | throwError "the complete named Hom type was not retained through its declaration"
  unless ← withTransparency .all <| isDefEq innerHom (← inferType identity) do
    throwError "the callable-value validator changed the full module Hom type"
  let token := packet "opaqueData" #["the actual full module morphism"]
  let original : Wire := {
    form := .canonicalMorphism moduleCategory
    payload := .computed identity (.owned "whole-function-probe-owner" 23 token)
    categoryContext := some context }
  let harness ← Harness.empty
  let one ← globalPointSource.run {}
  let point ← wholeCallablePoint harness trace original module module one context owner
  unless point.owner? == original.owner? && containsPacket point.json token &&
      point.pointDataInterface.isSome && !point.serviceHandles.isEmpty do
    throwError "the whole-Hom point lost actual opaque data, its owner or original service operands"
  let some (pointDomain, pointTarget) := homEnds? (← inferType point.value)
    | throwError "the whole-Hom point lost its complete outer signature"
  unless ← withTransparency .all <| isDefEq pointDomain one <&&>
      isDefEq pointTarget owner.application.value do
    throwError "the whole-Hom point changed its independent selected owner"
  let otherModule ← elabTermAndSynthesize (← `(ModuleCat.of ℚ ℚ)) none
  let otherIdentity ← mkAppM ``CategoryTheory.CategoryStruct.id #[otherModule]
  let otherContext ← CategoryContext.ofNamed moduleCategory otherModule
  let wrong : Wire := { original with
    payload := forwardPayload original otherIdentity token
    categoryContext := some otherContext }
  let rejected ← try
    discard <| wholeCallablePoint harness trace wrong otherModule otherModule one otherContext owner
    pure false
  catch error =>
    if Exception.stratum? error == some .noImplementation then pure true else throw error
  unless rejected do throwError "a different selected scalar/module Hom borrowed the original owner"
  -- The independently declared admission source is PUnit, while its input is
  -- the original complete function on the selected module carrier.
  let admission ← mkConstWithFreshMVarLevels (owner.entry.admission.get!)
  let (arguments, infos, result) ← forallMetaTelescopeReducing (← inferType admission)
  let some (declaredDomain, declaredTarget) := homEnds? result
    | throwError "the original admission has no complete point interface"
  unless ← withTransparency .all <| isDefEq declaredTarget owner.application.value do
    throwError "the original admission has another complete Hom owner"
  let explicit := (List.range arguments.size).toArray.filter (infos[·]!.isExplicit)
  let some inputIndex := explicit.find? fun index =>
      (result.findMVar? (· == arguments[index]!.mvarId!)).isNone
    | throwError "the declared admission input is absent"
  let input ← instantiateMVars (← inferType arguments[inputIndex]!)
  let declaredDomain ← instantiateMVars declaredDomain
  if ← withTransparency .all <| isDefEq declaredDomain one then
    throwError "the PUnit admission control collapsed to Fin 1"
  let some inputOwner ← callableObjectPlan? input
    | throwError "the complete original function input has no registered owner"
  let .forallE _ inputSource inputTarget _ ← withTransparency .all <| whnf input
    | throwError "the declared module admission did not retain its function input"
  unless ← withTransparency .all <| isDefEq inputSource inputTarget do
    throwError "the selected identity control changed its internal endpoints"
  let raw ← mkAppM ``CategoryTheory.CategoryStruct.id #[inputSource]
  Trace.record (some trace) raw (.morphismIdentity sets.id inputSource)
  let rawContext ← CategoryContext.ofNamed sets inputSource
  let rawToken := packet "opaqueData" #["the original whole admission function"]
  let rawWire : Wire := {
    form := .canonicalMorphism sets
    payload := .computed raw (.owned "whole-function-probe-owner" 23 rawToken)
    categoryContext := some rawContext }
  let inputPoint ← wholeCallablePoint harness trace rawWire inputSource inputTarget
    declaredDomain rawContext inputOwner
  unless inputPoint.owner? == rawWire.owner? && containsPacket inputPoint.json rawToken &&
      inputPoint.pointDataInterface.isNone do
    throwError "the PUnit admission changed the original data owner or used scalar point metadata"
  let params ← DirectConstruction.dataArguments owner.application.explicit
  let (parameterData, _) ← realizedParameterData harness trace params
  let domainData ← realizeEndpoint harness trace "the actual admission domain" declaredDomain
  let sourceData ← realizeEndpoint harness trace "the whole-function input object" inputOwner.application.value
  let targetData ← realizeEndpoint harness trace "the selected full Hom owner" owner.application.value
  let admitted : Backend.AdmittedPoint := {
    object := owner.entry.id.raw, parameters := parameterData.map (·.json)
    domain := domainData.json, source := sourceData.json, target := targetData.json
    argument := inputPoint.json }
  let expected ← mkAppM ``Quiver.Hom #[declaredDomain, owner.application.value]
  let rawSourceEndpoint ← realizeCallableEndpoint harness trace rawWire inputSource true (some rawContext)
  let rawTargetEndpoint ← realizeCallableEndpoint harness trace rawWire inputTarget false (some rawContext)
  let retained : ComputationalData.InterfaceObjects :=
    ((parameterData.zip params).map fun (data, formal) => (data.json, formal)) ++
      #[(rawSourceEndpoint.json, inputSource), (rawTargetEndpoint.json, inputTarget)]
  valid "actual PUnit admission with complete original function point" expected admitted.encode retained
  invalid "PUnit admission cannot reuse an inner callable as an outer point" expected
    { admitted with argument := packet "typedMap" #[
      (← realizeCallableEndpoint harness trace rawWire inputSource true (some rawContext)).json,
      (← realizeCallableEndpoint harness trace rawWire inputTarget false (some rawContext)).json,
      rawToken] }.encode retained
  let oneData ← realizeEndpoint harness trace "the independent Fin 1 domain" one
  invalid "PUnit admission cannot claim Fin 1 as its original point domain" expected
    { admitted with domain := oneData.json }.encode retained
  -- Exercise an actual nonidentity endpoint action using the already
  -- registered Fin 1 / PUnit comparison. This changes data representation,
  -- while the complete outer admission signature remains PUnit -> input.
  let some comparisonRow := state.presentations.find?
      (·.id.raw == "cmp.sets.singleton_terminal")
    | throwError "the original point-domain comparison is absent"
  let comparison ← ObjectPresentation.applyParameters comparisonRow.declaration #[]
  let reverse ← mkAppM ``CategoryTheory.Iso.symm #[comparison]
  let presentation := fun inverse => packet "presentation"
    #[comparisonRow.id.raw, Json.arr #[], toJson (inverse : Bool)]
  let presentedDomain : Wire := { domainData with
    payload := (← combinedPayload declaredDomain oneData.fragment #[domainData, oneData])
    endpointPresentation := some {
      comparison := reverse, forward := presentation true, backward := presentation false } }
  harness.results.modify (·.insert declaredDomain presentedDomain)
  let restaged ← wholeCallablePoint harness trace rawWire inputSource inputTarget
    declaredDomain rawContext inputOwner
  unless restaged.morphismFramed && containsPacket restaged.json (presentation false) &&
      containsPacket restaged.json (presentation true) do
    throwError "the restaged producer did not retain its actual nonidentity endpoint action"
  let outerContext ← CategoryContext.ofNamed sets declaredDomain
  let (reused, _) ← completeCallableFragment harness trace declaredDomain inputOwner.application.value
    restaged outerContext
  unless reused == restaged.fragment && restaged.owner? == rawWire.owner? do
    throwError "same-endpoint reuse applied a presentation twice or changed the original owner"
  let serviceOperands ← harness.serviceOperands.get
  unless restaged.serviceHandles.any (fun handle =>
      (serviceOperands[handle]?).any fun candidate =>
        candidate.value == rawWire.value && candidate.fragment == rawWire.fragment) do
    throwError "restaging lost its exact original whole-function service operand"
  let changedDomain := { presentedDomain with
    payload := .computed declaredDomain (.inline
      (packet "finiteData" #[oneData.json, Json.arr #[toJson (1 : Nat)]])) }
  harness.results.modify (·.insert declaredDomain changedDomain)
  let changedInventory ← try
    discard <| completeCallableFragment harness trace declaredDomain inputOwner.application.value
      restaged outerContext
    pure false
  catch error =>
    if Exception.stratum? error == some .ambiguousRealization then pure true else throw error
  unless changedInventory do throwError "a reused typedMap changed its actual endpoint inventory"
  harness.results.modify (·.insert declaredDomain presentedDomain)
  let endpointToken := packet "opaqueData" #["the exact actual function-space endpoint"]
  let selectedInput := inputOwner.application.value
  let selectedEndpoint : Wire := {
    form := .diagrams sets
    payload := .computed selectedInput (.owned "whole-function-endpoint-owner" 71 endpointToken)
    categoryContext := some outerContext }
  harness.results.modify (·.insert selectedInput selectedEndpoint)
  let scopedPoint ← wholeCallablePoint harness trace rawWire inputSource inputTarget
    declaredDomain rawContext inputOwner
  let (sameScoped, _) ← completeCallableFragment harness trace declaredDomain selectedInput
    scopedPoint outerContext
  unless sameScoped == scopedPoint.fragment do
    throwError "the complete actual scoped endpoint was not reusable"
  harness.results.modify (·.insert selectedInput
    { selectedEndpoint with
      payload := .computed selectedInput (.owned "different-endpoint-owner" 72 endpointToken) })
  let changedOwner ← try
    discard <| completeCallableFragment harness trace declaredDomain selectedInput
      scopedPoint outerContext
    pure false
  catch error =>
    if Exception.stratum? error == some .ambiguousRealization then pure true else throw error
  unless changedOwner do throwError "equal endpoint bytes selected a different actual owner"
  logInfo "PASS: full module owner, actual PUnit admission, exact composition framing and ownership"
  discard (pure ring)

run_elab do
  let state ← registryState
  let some modules := state.categories.find? (·.id == CategoryId.modulesR)
    | throwError "the selected module category is absent"
  let integerModule ← elabTermAndSynthesize (← `(ModuleCat.of ℤ PUnit.{1})) none
  let rationalModule ← elabTermAndSynthesize (← `(ModuleCat.of ℚ PUnit.{1})) none
  let firstContext ← CategoryContext.ofNamed modules integerModule
  let secondContext ← CategoryContext.ofNamed modules rationalModule
  let first ← mkAppM ``CategoryTheory.CategoryStruct.id #[integerModule]
  let second ← mkAppM ``CategoryTheory.CategoryStruct.id #[rationalModule]
  let owner ← wholeCallableObject first integerModule integerModule firstContext
  let wrong : Wire := {
    form := .canonicalMorphism modules
    payload := .computed second (.opaque "same-carrier-owner" 83 "whole map")
    categoryContext := some secondContext }
  let rejected ← try
    discard <| wholeCallablePoint (← Harness.empty) (← Trace.new) wrong rationalModule rationalModule
      (← globalPointSource.run {}) secondContext owner
    pure false
  catch error =>
    if Exception.stratum? error == some .noImplementation then pure true else throw error
  unless rejected do throwError "same PUnit carriers erased the selected module scalar context"
  let some groups := state.categories.find? (·.id == CategoryId.groups)
    | throwError "the selected group category is absent"
  let group ← elabTermAndSynthesize (← `(GrpCat.of (Multiplicative ℤ))) none
  let groupContext ← CategoryContext.ofNamed groups group
  let identity ← mkAppM ``CategoryTheory.CategoryStruct.id #[group]
  let groupOwner ← wholeCallableObject identity group group groupContext
  unless ← withTransparency .all <| isDefEq groupOwner.application.value (← inferType identity) do
    throwError "the full group Hom owner was replaced by an erased function type"
  -- Existing SingleObj instances have coincident object and Hom types but
  -- distinct complete category dictionaries; no semantic row is registered.
  let some sets := state.categories.find? (·.id == CategoryId.sets)
    | throwError "the contextual framing form metadata is absent"
  let multiplicative ← elabTermAndSynthesize (← `(Cat.of (SingleObj ℕ))) none
  let additive ← elabTermAndSynthesize
    (← `(Cat.of (SingleObj (Multiplicative ℕ)))) none
  let endpoint ← elabTermAndSynthesize (← `(SingleObj.star ℕ)) none
  let retained : CategoryContext := { expression := sets.expression, bundle := multiplicative }
  let changed : CategoryContext := { retained with bundle := additive }
  let input : Wire := {
    form := .canonicalMorphism sets
    payload := .computed (mkNatLit 2) (.opaque "complete-context-owner" 84 "actual map")
    categoryContext := some retained }
  CategoryContext.checkMorphism retained input.value endpoint endpoint
  CategoryContext.checkMorphism changed input.value endpoint endpoint
  let rejectedContext ← try
    discard <| completeCallableFragment (← Harness.empty) (← Trace.new)
      endpoint endpoint input changed
    pure false
  catch error =>
    if Exception.interpretationKind error == .invalid then pure true else throw error
  unless rejectedContext do throwError "complete callable framing replaced a full category dictionary"
  logInfo "PASS: full group/module ownership and coincident-Hom category-context rejection"

end
