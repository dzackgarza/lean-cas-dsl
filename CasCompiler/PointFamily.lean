module

public import CasCompiler.SelectionData
import all CasCompiler.SelectionData

public import CasCompiler.SourceCarrier
public import CasCompiler.SourceObjectAlias
public import CasCompiler.SourcePointOrigin
public import CasCompiler.Layout

@[expose] public section

namespace CasCompiler

open Lean Meta CasCatalogue


def PointFamilyOwner.operation : PointFamilyOwner → String
  | .morphism entry => entry.id.raw
  | .application entry => entry.id.raw ++ "#application"

def PointFamilyOwner.category : PointFamilyOwner → CategoryId
  | .morphism entry => entry.category
  | .application entry => entry.category


def PointFamily.operation (family : PointFamily) : String := family.owner.operation


def PointFamily.selected (family : PointFamily) (levels : List Level)
    (parameters : Array Expr) (arrow : Expr) : MetaM (SourceSelection Expr) := do
  unless levels.length == family.universeParams.length do
    throwError "the named point action changed its original universe arguments"
  let expected := mkAppN (mkConst family.declaration levels) parameters
  check expected
  unless ← isDefEq arrow expected do
    throwError "the named point action changed its complete original declaration application"
  match family.owner with
  | .morphism entry =>
      return {
        value := arrow
        reference := some (.named (.registered (.inr entry) family.category))
        originalApplication := some expected }
  | .application _ =>
      return {
        value := arrow
        originalApplication := some expected
        application := some {
          family := .application family, universes := levels, parameters } }

private def pointCategory (category : NamedCategoryEntry) (arrow : Expr) :
    MetaM NativeSourceCategory := do
  let declaration ← checkedDeclaration category.declaration
  let levels ← declaration.levelParams.mapM fun _ => mkFreshLevelMVar
  let family := mkConst category.declaration levels
  let (parameters, _, _) ← forallMetaTelescopeReducing (← inferType family)
  let bundle := mkAppN family parameters
  let identity ← categoryIdentity bundle


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



private def pointFamily? (owner : PointFamilyOwner) (declarationName : Name) :
    MetaM (Option PointFamily) := withLCtx {} #[] do
  let state ← semanticState
  let #[category] := state.categories.filter (·.id == owner.category)
    | throwError "the named callable requires its original registered category"
  let declaration ← checkedDeclaration declarationName
  let family := mkConst declarationName (declaration.levelParams.map Level.param)
  let path? ← forallTelescopeReducing declaration.type fun parameters result => do
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
        | return none
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
      return some route.path
  let some path := path? | return none
  return some ⟨owner, declarationName, category, family, declaration.type, declaration.levelParams, path⟩

private def pointFamily (owner : PointFamilyOwner) (declarationName : Name) :
    MetaM PointFamily := do
  let some family ← pointFamily? owner declarationName
    | throwUnsupportedSource "the named morphism has no native input-function path"
  return family



opaque PointFamily.forEntry? (entry : MorphismEntry) : MetaM (Option PointFamily) :=
  pointFamily? (.morphism entry) entry.declaration

opaque PointFamily.forEntry (entry : MorphismEntry) : MetaM PointFamily :=
  pointFamily (.morphism entry) entry.declaration


opaque PointFamily.forApplication (entry : ObjectEntry) : MetaM PointFamily := do
  let #[original] := (← semanticState).objects.filter (·.id == entry.id)
    | throwError "the object application requires its exact registered owner"
  let some declaration := original.application
    | throwError "the selected object has no published application"
  unless original.declaration == entry.declaration && original.category == entry.category &&
      entry.application == some declaration do
    throwError "the object application changed its original selected owner"
  pointFamily (.application original) declaration


opaque PointFamily.endpoints (family : PointFamily) (arrow : Expr) : MetaM (Expr × Expr) := do
  unless arrow.consumeMData.getAppFn.constName? == some family.declaration do
    throwError "the named point action changed its released morphism family"
  let type ← whnfR (← inferType arrow)
  unless type.isAppOfArity ``Quiver.Hom 4 do
    throwError "the named point action requires its complete declaration parameters"
  return (← declaredEndpoint type.getAppArgs[2]!, ← declaredEndpoint type.getAppArgs[3]!)



private def pointEndpoint [Monad m] [MonadLiftT MetaM m]
    (category : CategoryId) (value : Expr) (select : SourceSelection Expr → m Expr) : m Expr := do
  if value.isAppOfArity ``Prod 2 then
    let first ← select (← liftM (m := MetaM) <|
      sourceNamedObjectAlias category { value := value.getAppArgs[0]! })
    let second ← select (← liftM (m := MetaM) <|
      sourceNamedObjectAlias category { value := value.getAppArgs[1]! })
    return ← select { value := mkAppN value.getAppFn #[first, second] }
  select (← liftM (m := MetaM) <| sourceNamedObjectAlias category { value })


opaque PointFamily.withEndpoints [Monad m] [MonadLiftT MetaM m] (family : PointFamily)
    (arrow : Expr) (select : SourceSelection Expr → m Expr) : m (Expr × Expr) := do
  let (source, target) ← liftM (m := MetaM) <| family.endpoints arrow
  return (← pointEndpoint family.owner.category source select,
    ← pointEndpoint family.owner.category target select)


opaque PointFamily.function (family : PointFamily) (arrow : Expr) : MetaM Expr := do
  sourceFunction ⟨arrow, some (← pointCategory family.category arrow)⟩



def PointFamily.checkRequest (family : PointFamily) (arrow domain source target originalDomain : Expr)
    (context : Option OpenContext := none) : MetaM Unit := do
  let inputs := #[arrow, domain, source, target, originalDomain]
  let check : Array Expr → MetaM Unit := fun inputs => do
    let (expectedSource, expectedTarget) ← family.endpoints inputs[0]!
    checkRegisteredDomains inputs[1]! inputs[4]!
    checkRegisteredDomains inputs[2]! expectedSource
    checkRegisteredDomains inputs[3]! expectedTarget
    unless ← isDefEq inputs[1]! inputs[4]! <&&>
        isDefEq inputs[2]! expectedSource <&&> isDefEq inputs[3]! expectedTarget do
      throwError "the named point request changed its complete native domain or endpoints"
  match context with
  | some context => context.withOriginalSources inputs check
  | none => check inputs



opaque PointFamily.withRequest (family : PointFamily) (arrow domain source target : Expr)
    (point : SourceSelection Expr) (context : Option OpenContext := none) :
    MetaM (SourceSelection Expr) := do
  let some original := point.pointOrigin
    | throwError "a named point request requires its original source point map"
  family.checkRequest arrow domain source target original.domain context
  let request : NativePointRequest := ⟨arrow, domain, source, target, point.value⟩
  return { point with pointRequest := some (.named family request) }

end CasCompiler
