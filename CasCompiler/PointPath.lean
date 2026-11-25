module

public import CasCompiler.SourceCarrier
public import CasCompiler.Layout

public section

namespace CasCompiler

open Lean Meta CasCatalogue

/-- A native carrier-function path checked for an entire rigid source family. -/
structure NativePointFamily where
  private mk ::
  family : Expr
  universeParams : List Name
  path : Array Name

/-- The same checked path at one exact complete source result layout. -/
structure NativePointPath (source : SourceLayout) where
  private mk ::
  path : Array Name

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

/-- Check the same unchanged point action in its complete original native context. -/
private def nativePointPath (bindings : Array LocalBinding) (result : Expr)
    (category : Expr → MetaM NativeSourceCategory) : MetaM (Array Name) := do
  let result ← if result.isAppOfArity ``Quiver.Hom 4 then pure result else whnfR result
  unless result.isAppOfArity ``Quiver.Hom 4 do
    throwUnsupportedSource "the point action requires a complete native morphism family"
  withLocalDeclD `arrow result fun arrow => do
    let session := (← mkFreshUserName `nativePointPath).toString
    let arrowId : BindingId := ⟨session, 0⟩
    let bindings := bindings.push
      { id := arrowId, role := BindingRole.parameter, expression := arrow }
    let context ← ContextTelescope.capture bindings
    let function ← sourceFunction ⟨arrow, some (← category arrow)⟩
    let source ← SourceLayout.ofTerm (← context.close function)
    let (_, application) ← ApplicationLayout.ofSource source context #[]
    let some (.callable route steps) ←
        application.inputProjectionThrough #[(#[], 1)] #[] #[arrowId]
      | throwUnsupportedSource "the morphism has no native input-function path"
    let .context original := route.target
      | throwError "the carrier function changed its original arrow"
    unless original == arrowId do throwError "the carrier function lost its actual arrow input"
    let #[step] := steps
      | throwUnsupportedSource "the carrier requires another source action"
    let #[argument] := step.arguments
      | throwUnsupportedSource "the carrier changed its complete point argument"
    unless step.selection.isEmpty && (← unchangedPoint argument arrowId) do
      throwUnsupportedSource "the carrier does not apply its unchanged original point"
    return route.path

private def requirePointPath (source : SourceLayout) (path : Array Name) : MetaM Unit := do
  let mut selected := source
  for projection in path do
    let #[field] := selected.fields.filter (·.projection == projection)
      | throwError "the native carrier path lost its exact result projection"
    unless field.wireIndex.isSome do
      throwError "the native carrier path selected a proof-only field"
    selected ← field.toLayout
  unless selected.kind == .function do
    throwError "the native carrier path does not end at its original function"

/-- Reuse PointFamily's native input-function check under the whole rigid parameter
telescope. The selected complete category is supplied by the original source owner. -/
opaque NativePointFamily.prepare (family : Expr) (universes : List Name)
    (category : Array Expr → Expr → MetaM NativeSourceCategory) :
    MetaM NativePointFamily := withLCtx {} #[] do
  let path ← forallTelescopeReducing (← inferType family) fun parameters result => do
    let bindings := parameters.mapIdx fun index expression =>
      { id := { session := "point-action-path", serial := index },
        role := BindingRole.parameter, expression : LocalBinding }
    nativePointPath bindings result (category parameters)
  return ⟨family, universes, path⟩

/-- Prepare a carrier path for this exact source result, using its independently retained
complete category and bundle. All source binders, selected instances and rigid universes stay
in the original context; no whole-family claim or matching-field search is introduced. -/
opaque NativePointPath.prepare (source : SourceLayout) (category : CategoryExpr)
    (bundle : ClosedTerm) : MetaM (NativePointPath source) := do
  let path ← source.source.withOpen fun bindings expression => do
    let context ← ContextTelescope.capture bindings
    let bundle ← bundle.inContext context
    nativePointPath bindings (← inferType expression) fun _ =>
      pure { role := .morphism, expression := category, bundle }
  requirePointPath source path
  return ⟨path⟩

/-- Specialize only that original already checked family and path. Native conversion checks
the caller's fixed application; it never searches another family or a matching output field. -/
opaque NativePointFamily.specialize (family : NativePointFamily) (source : SourceLayout)
    (levels : List Level) (arguments : Array ClosedTerm) : MetaM (NativePointPath source) := do
  unless levels.length == family.universeParams.length do
    throwError "the native carrier path lost its complete universe substitution"
  source.source.withOpen fun bindings expression => do
    let context ← ContextTelescope.capture bindings
    let actual ← arguments.mapM (·.inContext context)
    let expected := mkAppN
      (family.family.instantiateLevelParams family.universeParams levels) actual
    unless ← isDefEq expression expected do
      throwError "the native carrier path changed its complete original source application"
  requirePointPath source family.path
  return ⟨family.path⟩

end CasCompiler
