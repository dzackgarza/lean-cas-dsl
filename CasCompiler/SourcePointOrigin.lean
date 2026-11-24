module

public import CasCompiler.Surface

public section

namespace CasCompiler

open Lean Meta CasCatalogue

/-- The already selected native generalized point whose value the reader retained.
Its original source object supplies the point domain; the value's carrier does not. -/
structure NativeSourcePointOrigin where
  private mk ::
  point : Expr
  domain : Expr
  target : Expr

private def nativePointOrigin (point value : Expr) : MetaM NativeSourcePointOrigin := do
  let point ← instantiateMVars point
  let type ← whnfR (← inferType point)
  unless type.isAppOfArity ``Quiver.Hom 4 do
    throwError "a retained source point requires its complete native map"
  let domain ← declaredEndpoint type.getAppArgs[2]!
  let target ← declaredEndpoint type.getAppArgs[3]!
  discard <| getLevel domain
  discard <| getLevel target
  unless ← isDefEq (← inferType value) target do
    throwError "the retained source point has a different native value target"
  if point.hasMVar || point.hasLevelMVar then
    throwError "the retained source point has undetermined native parameters"
  return ⟨point, domain, target⟩

/-- Preserve the actual point map after the reader's supplied carrier comparisons.
The typed Function.const wrapper leaves the native value unchanged. Its own metadata key
does not introduce a published computation boundary or obstruct native input projections. -/
def retainSourcePoint (point value : Expr) : MetaM Expr := do
  discard <| nativePointOrigin point value
  let body ← mkAppM ``Function.const #[← inferType point, value, point]
  return .mdata (KVMap.empty.setName `CasCompiler.source.pointOrigin
    ``NativeSourcePointOrigin) body

/-- Read only an explicitly retained point origin through its native source alias, typed
identity wrappers and exact constructor fields. No domain is guessed from the value's type,
a terminal convention or a matching registry object. The caller retains the complete
original value source and occurrence separately for input admission. -/
partial def sourcePointOrigin? (expression : Expr) : MetaM (Option NativeSourcePointOrigin) := do
  let expression ← instantiateMVars expression
  match expression with
  | .mdata data body =>
    if data.getName `CasCompiler.source.pointOrigin == ``NativeSourcePointOrigin then
      unless body.isAppOfArity ``Function.const 4 do
        throwError "the source point lost its typed provenance wrapper"
      return some (← nativePointOrigin body.getAppArgs[3]! body.getAppArgs[2]!)
    sourcePointOrigin? body
  | .fvar id =>
    match (← id.getDecl).value? with
    | some value => sourcePointOrigin? value
    | none => pure none
  | .letE _ _ value body _ => sourcePointOrigin? (body.instantiate1 value)
  | _ =>
    if let some projection ← SourceProjection.ofExpr? expression then
      let parent := projection.parent.consumeMData
      unless parent.getAppFn.constName? == some projection.info.ctorName do return none
      -- projectCore? selects the declared constructor argument without whnf, delta
      -- reduction or looking for another component with the same native value.
      let some selected ← projectCore? parent projection.info.i | return none
      return ← sourcePointOrigin? selected
    if expression.isAppOfArity ``id 2 then
      return ← sourcePointOrigin? expression.getAppArgs[1]!
    if expression.isAppOfArity ``Function.const 4 then
      return ← sourcePointOrigin? expression.getAppArgs[2]!
    let reduced := expression.headBeta
    if reduced == expression then return none
    sourcePointOrigin? reduced

end CasCompiler
