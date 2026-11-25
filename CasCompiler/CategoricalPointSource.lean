module

public import CasCompiler.CategoricalPointFamily
public import CasCompiler.PublishedPorts

public section

namespace CasCompiler

open Lean Meta CasCatalogue

/-- Resolve the retained point owner through the shared exact public address boundary.
The native source family itself stays independent of runtime/program admission. -/
def CategoricalPointFamily.fromMark (data : MData) : MetaM CategoricalPointFamily := do
  unless data.getName `CasCompiler.source.kind == ``CategoricalPointFamily do
    throwError "the source generalized point lost its complete owner"
  let state ← semanticState
  let address := data.getString `CasCompiler.source.id
  let kind := data.getName `CasCompiler.source.point.owner
  let inverse := data.getBool `CasCompiler.source.point.inverse
  unless kind == ``CategoricalPointOwner.component || !inverse do
    throwError "only the original cell component can retain an inverse orientation"
  let owner : CategoricalPointOwner ← if kind == ``CategoricalPointOwner.named then do
      let morphisms := state.morphisms.filter (·.id.raw == address)
      let applications := state.objects.filter (fun entry =>
        entry.application.isSome && entry.applicationAddress == address)
      match morphisms, applications with
      | #[entry], #[] => pure (.named (.morphism entry))
      | #[], #[entry] => pure (.named (.application entry))
      | _, _ => throwError "the generalized point lost its exact original named owner"
    else if kind == ``CategoricalPointOwner.component then do
      let .ok (some (entry, constructors)) := PublishedPorts.component? state address
        | throwError "the generalized point lost its original component owner"
      pure (.component entry constructors inverse)
    else if kind == ``CategoricalPointOwner.cartesian then do
      let .ok (some entry) := PublishedPorts.cartesian? state address
        | throwError "the generalized point lost its original cartesian owner"
      pure (.cartesian entry)
    else if kind == ``CategoricalPointOwner.binder then do
      let #[entry] := state.binders.filter (·.id.raw == address)
        | throwError "the generalized point lost its original binder owner"
      pure (.binder entry)
    else if kind == ``CategoricalPointOwner.action then do
      if let .ok (some (edge, true)) := PublishedPorts.edge? state address then
        pure (.action edge)
      else
        let #[entry] := state.functors.filter (fun entry => entry.id.raw ++ "#map" == address)
          | throwError "the generalized point lost its original map action owner"
        pure (.action (.functor entry.id))
    else throwError "the generalized point lost its original owner kind"
  if data.getBool `CasCompiler.source.point.reference &&
      !data.getBool `CasCompiler.source.point.whole then
    throwError "an original arrow reference cannot change into a generalized invocation"
  let family ← CategoricalPointFamily.forOwner owner
  let family ← if data.getBool `CasCompiler.source.point.whole then family.asWhole else pure family
  let family ← if data.getBool `CasCompiler.source.point.reference then family.asReference else pure family
  unless data.getName `CasCompiler.source.declaration == family.declaration &&
      data.getName `CasCompiler.source.application == family.declaration do
    throwError "the source generalized point changed its declaration witness"
  return family

/-- Consume only an original native cell/cartesian/binder envelope. The resulting family
and argument positions are checked against that exact selected arrow before lowering. -/
def CategoricalPointFamily.native? (expression : Expr) :
    MetaM (Option (CategoricalPointFamily × List Level × Array Expr)) := do
  if expression.isFVar then return none
  if let .mdata data _ := expression then
    if data.contains `CasCompiler.lower.value ||
        data.getName `CasCompiler.source.kind == ``CategoricalPointFamily then return none
  let selected ← if let some original ← sourceCellComponent? expression then
      pure (some (CategoricalPointOwner.component original.cell.entry
        original.cell.constructors original.cell.inverse,
        original.cell.application, #[original.receiver]))
    else if let some original ← sourceCartesian? expression then
      pure (some (.cartesian original.entry, original.application, #[original.receiver]))
    else if let .mdata data body := expression then do
      if data.getName `CasCompiler.source.kind == ``BinderEntry then do
        let #[entry] := (← semanticState).binders.filter
          (·.id.raw == data.getString `CasCompiler.source.id)
          | throwError "the native binder lost its original registered owner"
        unless data.getName `CasCompiler.source.declaration == entry.operation do
          throwError "the native binder changed its original declaration"
        pure (some (.binder entry, body, #[]))
      else if data.getBool `CasCompiler.source.derived &&
          body.isAppOfArity ``CategoryTheory.Functor.map 8 then do
        let kind := data.getName `CasCompiler.source.kind
        let id := data.getString `CasCompiler.source.id
        let edge ← if kind == ``EdgeRef.functor then pure (some (EdgeRef.functor ⟨id⟩))
          else if kind == ``EdgeRef.classifierForget then pure (some (.classifierForget ⟨id⟩))
          else pure none
        let some edge := edge | return none
        let application ← routedActionApplication edge body.getAppArgs[4]!
        unless application.consumeMData.getAppFn.constName? ==
            some (data.getName `CasCompiler.source.declaration) do
          throwError "the native map action changed its selected declaration"
        pure (some (.action edge, application, body.getAppArgs.extract 5 8))
      else pure none
    else pure none
  let some (owner, application, extra) := selected | return none
  let family ← CategoricalPointFamily.forOwner owner
  let application := application.consumeMData
  let .const declaration levels := application.getAppFn
    | throwError "the native point owner lost its complete declaration application"
  unless declaration == family.declaration do
    throwError "the native point owner changed its original declaration"
  if application.getAppNumArgs < family.declarationParameterCount then return none
  let parameters := application.getAppArgs ++ extra
  let (arrow, _) ← family.arrowAt levels parameters
  unless ← isDefEq arrow expression do
    throwError "the native point family changed its original selected arrow"
  return some (family, levels, parameters)

/-- Form the common source request from an actual selected native arrow, or from the actual
composition ending in it. The whole-arrow case preserves the arrow itself; generalized
postcomposition retains the original preceding map and its full native domain. -/
def categoricalPointSource? (expression : Expr) : MetaM (Option Expr) := do
  if expression.isFVar then return none
  if let .mdata data _ := expression then
    if data.contains `CasCompiler.lower.value then return none
  let value := expression.consumeMData
  if value.isAppOfArity ``CategoryTheory.CategoryStruct.comp 7 then
    let inputs := value.getAppArgs
    if let some (family, levels, parameters) ← CategoricalPointFamily.native? inputs[6]! then
      let point := inputs[5]!
      let (domain, _) ← categoricalPointEndpoints point
      let marked ← family.mark levels parameters domain point
      unless ← isDefEq marked expression do
        throwError "the generalized point changed its actual native composition"
      return some marked
  let some (family, levels, parameters) ← CategoricalPointFamily.native? expression | return none
  let (arrow, bundle) ← family.arrowAt levels parameters
  let (source, _) ← categoricalPointEndpoints arrow
  let identity ← categoricalPointIdentity bundle source
  let selected ← if (← family.carrierFamily?).isSome then family.asReference else family.asWhole
  return some (← selected.mark levels parameters source identity)

/-- Resolve only the exact retained canonical object-action address and its native witness. -/
def SourceActionFamily.fromMark (data : MData) : MetaM SourceActionFamily := do
  unless data.getName `CasCompiler.source.kind == ``SourceActionFamily do
    throwError "the object action lost its original source owner"
  let address := data.getString `CasCompiler.source.id
  let state ← semanticState
  let edge ← if let .ok (some (edge, false)) := PublishedPorts.edge? state address then
      pure edge
    else
      let #[entry] := state.functors.filter (·.id.raw == address)
        | throwError "the object action lost its original canonical edge"
      pure (.functor entry.id)
  let family ← SourceActionFamily.forEdge edge
  unless data.getName `CasCompiler.source.declaration == family.declaration &&
      data.getName `CasCompiler.source.application == family.declaration do
    throwError "the object action changed its original native declaration"
  return family

/-- Keep the actual source-selected native object action as a complete published request.
Only the original action wrapper and its own functor application select this boundary. -/
def SourceActionFamily.native? (expression : Expr) : MetaM (Option Expr) := do
  let .mdata data body := expression | return none
  if data.contains `CasCompiler.lower.value || !data.getBool `CasCompiler.source.derived then
    return none
  unless body.isAppOfArity ``CategoryTheory.Functor.obj 6 do return none
  let kind := data.getName `CasCompiler.source.kind
  let id := data.getString `CasCompiler.source.id
  let edge ← if kind == ``EdgeRef.functor then pure (some (EdgeRef.functor ⟨id⟩))
    else if kind == ``EdgeRef.classifierForget then pure (some (.classifierForget ⟨id⟩))
    else pure none
  let some edge := edge | return none
  let family ← SourceActionFamily.forEdge edge
  unless data.getName `CasCompiler.source.declaration == family.declaration do
    throwError "the native object action changed its original selected declaration"
  let application := (← routedActionApplication edge body.getAppArgs[4]!).consumeMData
  let .const declaration levels := application.getAppFn
    | throwError "the native object action lost its declaration application"
  unless declaration == family.declaration do
    throwError "the native object action replaced its original selected application"
  let result ← family.mark levels application.getAppArgs body.getAppArgs[5]!
  unless ← isDefEq result expression do
    throwError "the source object action changed its original native value"
  return some result

end CasCompiler
