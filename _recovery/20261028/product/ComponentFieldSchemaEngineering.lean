/- Copyright (c) 2026 Dzack Garza. Released under Apache 2.0 license. -/
module

import CasCatalogue.Realize
import CasCatalogue.DeclaredProduct
import CasCatalogue.ObjectPresentation
meta import CasCatalogue.Realize
meta import CasCatalogue.DeclaredProduct
meta import CasCatalogue.ObjectPresentation

open Lean Meta Elab Term CasCatalogue

/-! Kernel engineering controls for the schema's parameter telescope. The only
mathematical family is the independently accepted component interface. Eta
expansion below changes binder visibility, never its mathematical body. The
distinct parameter labels are positioned test inputs, not backend answers. -/

private def node (tag : String) (args : Array Json) : Json :=
  Json.mkObj [("ctor", toJson tag), ("args", Json.arr args)]

private partial def binderVisibility (value : Expr) (info : BinderInfo) : Expr :=
  match value with
  | .lam name type body _ => .lam name type (binderVisibility body info) info
  | value => value

private def projectionVariant (projection : Expr) (info : BinderInfo) : TermElabM Expr :=
  forallTelescopeReducing (← inferType projection) fun parameters _ => do
    return binderVisibility (← mkLambdaFVars parameters (mkAppN projection parameters)) info

run_elab do
  let state ← registryState
  let some category := state.categories.find? (·.id == CategoryId.sets)
    | throwError "the accepted set category is unavailable"
  let trace ← Trace.new
  let factor ← mkAppM ``Fin #[mkNatLit 2]
  let context ← CategoryContext.ofNamed category factor
  let selected ← DeclaredProduct.selectBinary context factor factor
  let some components := selected.entry.components
    | throwError "the accepted selection lost its component metadata"
  let object ← mkConstWithFreshMVarLevels selected.entry.declaration
  let arity ← mkConstWithFreshMVarLevels components.arity
  let projection ← mkConstWithFreshMVarLevels components.projection
  let ownerInfos ← forallTelescopeReducing (← inferType object) fun parameters _ =>
    parameters.mapM (·.fvarId!.getBinderInfo)
  let formalParameters ← DirectConstruction.dataArguments selected.parameters
  let parameterData ← formalParameters.mapIdxM fun index parameter => do
    match ← Codec.encode parameter with
    | .ok data => pure data
    | .error _ => pure (toJson (toString index))
  let objects : ComputationalData.InterfaceObjects := parameterData.zip formalParameters
  let decodeArgument (expected : Expr) (data : Json) :
      TermElabM (Except String (Expr × Option Form)) := do
    if let .ok label := data.getStr? then
      let some position := label.toNat? | return .error "the test parameter label is malformed"
      let some value := formalParameters[position]?
        | return .error "the test parameter position is outside its original input array"
      unless ← withTransparency .all <| isDefEq (← inferType value) expected do
        return .error "the positioned test parameter has a different complete type"
      return .ok (value, none)
    Realize.decodeValue trace category expected data
  for visibility in #[BinderInfo.default, BinderInfo.implicit] do
    let variant ← projectionVariant projection visibility
    let family ← ObjectPresentation.componentInterface object arity variant
    let infos ← forallTelescopeReducing (← inferType family) fun parameters _ =>
      parameters.mapM (·.fvarId!.getBinderInfo)
    unless infos == ownerInfos.push .default do
      throwError "projection visibility changed the owner's public telescope or omitted its index"
    let mut recoveredIndices : Array Expr := #[]
    for ordinal in [:2] do
      let formal := selected.coordinates[ordinal]!
      let expected ← inferType formal
      for indexData in #[toJson ordinal, node "valueData" #[toJson ordinal]] do
        let data := parameterData.push indexData
        let .ok () ← ComputationalData.validateDeclaredData components.projection data (some family)
          | throwError "canonical public framing rejected complete component parameters"
        let .ok () ← ComputationalData.declarationPorts components.projection formal expected
            data objects none (some family)
          | throwError "typed component ports rejected an exact coordinate or its wrapped index"
        let .ok _ ← ComputationalData.interfaceDeclaration objects components.projection expected
            data none none (some family)
          | throwError "the callable interface lost canonical component parameters"
        let .ok (decoded, _) ← Realize.decodeDeclaration components.projection expected data
            decodeArgument (some family)
          | throwError "the component decoder omitted or inferred a mandatory supplied slot"
        unless ← withTransparency .all <|
            isDefEq (← inferType decoded) expected <&&> isDefEq decoded formal do
          throwError "the component decoder changed the accepted original coordinate map"
        let parameters ← ObjectPresentation.componentParameters selected.entry decoded
        let some index := parameters.back? | throwError "the decoded coordinate omitted its public index"
        unless ← withTransparency .all <| isDefEq index selected.indices[ordinal]! do
          throwError "the decoded coordinate changed its ordered index at equal factors"
        if indexData == toJson ordinal then recoveredIndices := recoveredIndices.push index
        let descriptor := node "objectField"
          #[toJson selected.entry.id.raw, toJson "component", Json.arr data]
        let .ok () ← ComputationalData.validatePublicData descriptor
          | throwError "the public objectField framing omitted its schema-derived signature"
        let .ok () ← ComputationalData.validatePort formal expected descriptor objects
          | throwError "the public component port omitted its schema-derived signature"
        let .ok () ← ComputationalData.validateCallableAt objects expected descriptor
          | throwError "the public callable component omitted its schema-derived signature"
      for malformed in #[parameterData, parameterData ++ #[toJson ordinal, toJson ordinal],
          parameterData.push (toJson (2 : Nat)), parameterData.push (node "valueData" #[])] do
        if (← ComputationalData.declarationPorts components.projection formal expected
            malformed objects none (some family)).isOk then
          throwError "typed component ports accepted a missing, extra, unbounded or malformed index"
        if (← Realize.decodeDeclaration components.projection expected malformed
            decodeArgument (some family)).isOk then
          throwError "component decoding accepted a missing, extra, unbounded or malformed index"
    unless recoveredIndices.size == 2 do throwError "the two original coordinate occurrences were lost"
    if ← withoutModifyingState (isDefEq recoveredIndices[0]! recoveredIndices[1]!) then
      throwError "equal factor types collapsed the two mandatory coordinate indices"
  withLocalDeclD `localFactor (← inferType factor) fun localFactor => do
    let local ← DeclaredProduct.selectBinary context localFactor localFactor
    let (_, family) ← ObjectPresentation.componentsAt local.entry local.parameters local.object
    let projection := mkApp family local.indices[0]!
    let parameters ← ObjectPresentation.componentParameters local.entry projection
    unless projection.hasFVar && parameters.any (·.hasFVar) do
      throwError "component interpretation discarded its scoped original object parameters"
  logInfo "component schema controls: explicit and implicit projection binders, equal-factor indices, wrappers, malformed indices, and scoped locals passed"
