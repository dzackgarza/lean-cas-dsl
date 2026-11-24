module

public import CasCompiler.SourceCarrier
public import CasCompiler.SourceObjectAlias
public import CasCompiler.SourcePointOrigin
public import CasCompiler.Layout

@[expose] public section

namespace CasCompiler

open Lean Meta CasCatalogue

/-- The two released owners of the common named point interface. Object application is an
existing field of its exact selected object row, not a new ComputationRef or registry row. -/
inductive PointFamilyOwner
  | morphism (entry : MorphismEntry)
  | application (entry : ObjectEntry)

def PointFamilyOwner.operation : PointFamilyOwner → String
  | .morphism entry => entry.id.raw
  | .application entry => entry.id.raw ++ "#application"

def PointFamilyOwner.category : PointFamilyOwner → CategoryId
  | .morphism entry => entry.category
  | .application entry => entry.category

/-- A released callable and the checked carrier-function path of its complete native family.
The actual arrow, its parameters and its applied point remain independent inputs. -/
structure PointFamily where
  private mk ::
  owner : PointFamilyOwner
  declaration : Name
  category : NamedCategoryEntry
  family : Expr
  familyType : Expr
  universeParams : List Name
  path : Array Name

def PointFamily.operation (family : PointFamily) : String := family.owner.operation

/-- Retain the actual selected owner on its unchanged complete native declaration application. -/
def PointFamily.mark (family : PointFamily) (arrow : Expr) : Expr :=
  match family.owner with
  | .morphism entry => sourceReference ``MorphismEntry entry.id.raw family.declaration arrow
  | .application entry => sourceReference ``ObjectEntry.application entry.id.raw family.declaration arrow

private def pointCategory (category : NamedCategoryEntry) (arrow : Expr) :
    MetaM NativeSourceCategory := do
  let declaration ← checkedDeclaration category.declaration
  let levels ← declaration.levelParams.mapM fun _ => mkFreshLevelMVar
  let family := mkConst category.declaration levels
  let (parameters, _, _) ← forallMetaTelescopeReducing (← inferType family)
  let bundle := mkAppN family parameters
  let identity ← categoryIdentity bundle
  -- mkAppM checks at a new metavariable depth. Constrain the selected category's
  -- original parameters here from the complete native arrow type before that check.
  let mapFunction ← mkAppM ``CategoryTheory.Functor.map #[identity]
  let (arguments, binders, _) ← forallMetaTelescope (← inferType mapFunction)
  let some index := binders.findIdx? (·.isExplicit)
    | throwError "the native identity map lost its original arrow argument"
  unless index + 1 == arguments.size do
    throwError "the native identity map changed its complete arrow telescope"
  let some argument := arguments[index]?
    | throwError "the native identity map lost its complete arrow type"
  unless ← withAtLeastTransparency .default
      (isDefEq (← inferType argument) (← inferType arrow)) do
    throwError "the named point arrow is outside its complete registered category"
  let bundle ← instantiateMVars bundle
  let identity ← instantiateMVars identity
  discard <| mkAppM ``CategoryTheory.Functor.map #[identity, arrow]
  if bundle.hasMVar || bundle.hasLevelMVar then
    throwError "the named point action requires its complete selected category"
  return ⟨.morphism, category.expression, bundle, none, none⟩

private def unchangedPoint (argument : InputArgumentRef) (arrow : BindingId) : MetaM Bool := do
  match argument with
  | .slot index => return index == 0
  | .expression source =>
    match ← source.inputProjectionThrough #[] #[] #[arrow] with
    | some (.projection route) =>
      match route.target with
      | .argument index => return index == 0 && route.path.isEmpty
      | .context _ => return false
    | _ => return false

/-- Reuse the registered declaration checks and the existing native carrier action under
the complete rigid parameter telescope. No field suffix or actual scalar selects a port. -/
private def pointFamily (owner : PointFamilyOwner) (declarationName : Name) :
    MetaM PointFamily := withLCtx {} #[] do
  let state ← semanticState
  let #[category] := state.categories.filter (·.id == owner.category)
    | throwError "the named callable requires its original registered category"
  let declaration ← checkedDeclaration declarationName
  let family := mkConst declarationName (declaration.levelParams.map Level.param)
  let path ← forallTelescopeReducing declaration.type fun parameters result => do
    let result ← whnfR result
    unless result.isAppOfArity ``Quiver.Hom 4 do
      throwError "the named point action requires a complete native morphism family"
    withLocalDeclD `arrow result fun arrow => do
      let bindings := (parameters.push arrow).mapIdx fun index expression =>
        { id := { session := "point-action-path", serial := index },
          role := BindingRole.parameter, expression : LocalBinding }
      let context ← ContextTelescope.capture bindings
      let arrowId := bindings.back!.id
      let function ← sourceFunction ⟨arrow, some (← pointCategory category arrow)⟩
      let source ← SourceLayout.ofTerm (← context.close function)
      let (_, application) ← ApplicationLayout.ofSource source context #[]
      let some (.callable route steps) ←
          application.inputProjectionThrough #[(#[], 1)] #[] #[arrowId]
        | throwUnsupportedSource "the named morphism has no native input-function path"
      let .context original := route.target
        | throwError "the named carrier function changed its original arrow"
      unless original == arrowId do
        throwError "the named carrier function lost its actual arrow input"
      let #[step] := steps
        | throwUnsupportedSource "the named carrier requires another source action"
      let #[argument] := step.arguments
        | throwUnsupportedSource "the named carrier changed its complete point argument"
      unless step.selection.isEmpty && (← unchangedPoint argument arrowId) do
        throwUnsupportedSource "the named carrier does not apply its unchanged original point"
      return route.path
  return ⟨owner, declarationName, category, family, declaration.type, declaration.levelParams, path⟩

opaque PointFamily.forEntry (entry : MorphismEntry) : MetaM PointFamily :=
  pointFamily (.morphism entry) entry.declaration

/-- Prepare only the original published application field of the selected object row. -/
opaque PointFamily.forApplication (entry : ObjectEntry) : MetaM PointFamily := do
  let #[original] := (← semanticState).objects.filter (·.id == entry.id)
    | throwError "the object application requires its exact registered owner"
  let some declaration := original.application
    | throwError "the selected object has no published application"
  unless original.declaration == entry.declaration && original.category == entry.category &&
      entry.application == some declaration do
    throwError "the object application changed its original selected owner"
  pointFamily (.application original) declaration

/-- Name only whole authored endpoint families. A native product retains its actual typed
constructor and ordered components; the released objectProduct codec uses that exact pair. -/
private def pointEndpoint (category : CategoryId) (value : Expr) : MetaM Expr := do
  if value.isAppOfArity ``Prod 2 then
    let first ← sourceNamedObjectAlias category value.getAppArgs[0]!
    let second ← sourceNamedObjectAlias category value.getAppArgs[1]!
    return mkAppN value.getAppFn #[first, second]
  sourceNamedObjectAlias category value

/-- Complete authored endpoints at the unchanged original declaration parameters. Only
whole-family native aliases can supply a registered name for an unbound raw declaration. -/
opaque PointFamily.endpoints (family : PointFamily) (arrow : Expr) : MetaM (Expr × Expr) := do
  unless arrow.consumeMData.getAppFn.constName? == some family.declaration do
    throwError "the named point action changed its released morphism family"
  let type ← whnfR (← inferType arrow)
  unless type.isAppOfArity ``Quiver.Hom 4 do
    throwError "the named point action requires its complete declaration parameters"
  let source ← declaredEndpoint type.getAppArgs[2]!
  let target ← declaredEndpoint type.getAppArgs[3]!
  return (← pointEndpoint family.owner.category source,
    ← pointEndpoint family.owner.category target)

/-- The checked native carrier action of the actual original arrow. -/
opaque PointFamily.function (family : PointFamily) (arrow : Expr) : MetaM Expr := do
  sourceFunction ⟨arrow, some (← pointCategory family.category arrow)⟩

/-- Explicit source inputs of one named provider-requested point action. This provenance is
local to the application; it is not a property inferred from a later point value. -/
structure NativePointRequest where
  private mk ::
  arrow : Expr
  domain : Expr
  source : Expr
  target : Expr
  point : Expr

/-- Retain the caller's complete typed input positions beside its unchanged original point.
The domain comes from that point's existing native map; explicit endpoints are validated,
not selected by equality. Native reduction still sees exactly the original point value. -/
def PointFamily.withRequest (family : PointFamily) (arrow domain source target point : Expr) :
    MetaM Expr := do
  let (expectedSource, expectedTarget) ← family.endpoints arrow
  let some original ← sourcePointOrigin? point
    | throwError "a named point request requires its original source point map"
  checkRegisteredDomains domain original.domain
  checkRegisteredDomains source expectedSource
  checkRegisteredDomains target expectedTarget
  unless ← isDefEq domain original.domain <&&>
      isDefEq source expectedSource <&&> isDefEq target expectedTarget do
    throwError "the named point request changed its complete native domain or endpoints"
  let mut body := point
  for input in #[arrow, domain, source, target] do
    body ← mkAppM ``Function.const #[← inferType input, body, input]
  return .mdata (KVMap.empty.setString `CasCompiler.source.pointRequest family.operation) body

/-- Recover only the invocation-local wrapper produced above. Source aliases are not searched:
an earlier action's explicit endpoint packet cannot become a later action's input authority. -/
private partial def pointRequest (family : PointFamily) (point : Expr) :
    MetaM (Option NativePointRequest) := do
  let .mdata data body := point | return none
  let address := data.getString `CasCompiler.source.pointRequest
  if address.isEmpty then return ← pointRequest family body
  unless address == family.operation do
    throwError "the point request names a different released callable family"
  let mut body := body
  let mut supplied := #[]
  for _ in [:4] do
    unless body.isAppOfArity ``Function.const 4 do
      throwError "the named point request lost a complete typed input position"
    supplied := supplied.push body.getAppArgs[3]!
    body := body.getAppArgs[2]!
  let #[target, source, domain, arrow] := supplied
    | throwError "the named point request has an incomplete native input layout"
  discard <| family.withRequest arrow domain source target body
  return some ⟨arrow, domain, source, target, body⟩

/-- Read the original invocation-local wrapper without exposing its private constructor. -/
opaque PointFamily.request? (family : PointFamily) (point : Expr) :
    MetaM (Option NativePointRequest) :=
  pointRequest family point

end CasCompiler
