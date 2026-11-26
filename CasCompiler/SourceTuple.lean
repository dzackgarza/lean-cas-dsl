module

public import CasCompiler.Surface
public import Mathlib.Data.Fin.VecNotation

public section

namespace CasCompiler

open Lean Meta Elab Term



partial def nativeTypeView (source : Expr) : SourceReadM Expr := do
  if let some selected ← SourceReadM.selection? source then
    unless selected.value.equal source do
      return ← nativeTypeView selected.value
  let value ← whnf source
  unless value.equal source do return ← nativeTypeView value
  if let some projection ← SourceProjection.ofExpr? value then
    let parent ← nativeTypeView projection.parent
    unless parent.equal projection.parent do
      let constructor ← liftM (m := MetaM) <| getConstInfoCtor projection.info.ctorName
      return ← nativeTypeView (mkProj constructor.induct projection.info.i parent)
  if let .app function argument := value then
    let nativeFunction ← nativeTypeView function
    unless nativeFunction.equal function do
      return ← nativeTypeView (mkApp nativeFunction argument)
  return value



private def retainTuple (value expected : Expr) : SourceReadM Expr := do
  let native := value.consumeMData
  let environment ← liftM (m := CoreM) getEnv
  if let .const declaration _ := native.getAppFn then
    if let some (.ctorInfo constructor) := environment.find? declaration then
      if (getStructureInfo? environment constructor.induct).isSome then
        return ← retainSourceConstructor value (some expected)
  if (← inferType value).equal expected then return value
  let selected := (← SourceReadM.selection? value).getD { value }
  SourceReadM.select { selected with value } (some expected)




private def constructTuple (declaration : Name) (expected : Expr)
    (arguments : Array (Expr → ExceptT MessageData SourceReadM Expr)) :
    ExceptT MessageData SourceReadM Expr := do
  let nativeExpected ← liftM <| nativeTypeView expected
  let result ← liftM <| elabSourceApplicationApplicableScoped
    (← mkConstWithFreshMVarLevels declaration)
    (Array.replicate arguments.size Syntax.missing) (some nativeExpected)
    (fun index type => (arguments[index]! type).run)
  match result with
  | .ok (value, _) =>
    liftM <| retainTuple value expected
  | .error message => throwThe MessageData message




private partial def finiteTuple (components : Array (Expr → ExceptT MessageData SourceReadM Expr))
    (expected : Expr) : ExceptT MessageData SourceReadM Expr := do
  let nativeExpected ← liftM <| nativeTypeView expected
  let .forallE name domain codomain info := nativeExpected
    | liftM (m := TermElabM) <| throwError "the source finite tuple requires its declared indexed domain"
  let index ← whnf domain
  unless index.isAppOfArity ``Fin 1 do
    liftM (m := TermElabM) <| throwError "the source finite tuple requires its declared finite index"
  unless ← isDefEq index.getAppArgs[0]! (mkNatLit components.size) do
    throwThe MessageData m!"the source tuple has a different declared finite arity"
  let homogeneous ← if codomain.hasLooseBVars then pure false
    else pure ((← getLevel codomain).dec.isSome)
  if components.isEmpty then
    if homogeneous then return ← constructTuple ``Matrix.vecEmpty expected #[]
    let value ← liftM <| SourceReadM.withLambda name domain info fun argument =>
      mkAppOptM ``Fin.elim0 #[some (codomain.instantiate1 argument), some argument]
    return ← liftM <| retainTuple value expected
  let some first := components[0]?
    | liftM (m := TermElabM) <| throwError "a nonempty source finite tuple requires its first component"
  let constructor := if homogeneous then ``Matrix.vecCons else ``Fin.cases
  constructTuple constructor expected #[first,
    fun type => finiteTuple (components.drop 1) type]




def sourceMatrix (rows : Array (Array (TSyntax `cas_term))) (expected : Expr)
    (readComponent : TSyntax `cas_term → Expr → SourceReadM Expr) : SourceReadM Expr := do
  if let some first := rows[0]? then
    unless rows.all (·.size == first.size) do
      liftM (m := TermElabM) <| throwError "source matrix rows have different finite arities"
  let result ← (finiteTuple (rows.map fun row type =>
    finiteTuple (row.map fun component type => liftM (readComponent component type)) type) expected).run
  match result with
  | .ok value => pure value
  | .error message => liftM (m := TermElabM) <| throwError message





private partial def sourceTupleCore (components : Array (TSyntax `cas_term)) (expected : Expr)
    (readComponent : TSyntax `cas_term → Expr → ExceptT MessageData SourceReadM Expr) :
    ExceptT MessageData SourceReadM Expr := do
  let type ← liftM <| nativeTypeView expected
  if let .forallE _ domain _ _ := type then
    let index ← whnf domain
    if index.isAppOfArity ``Fin 1 then
      return ← finiteTuple (components.map fun component type =>
        readComponent component type) expected
  let constructor ←
    if type.isAppOfArity ``Prod 2 then pure ``Prod.mk
    else if type.isAppOfArity ``Sigma 2 then pure ``Sigma.mk
    else if type.isAppOfArity ``PSigma 2 then pure ``PSigma.mk
    else
      liftM (m := TermElabM) <| CasCatalogue.throwUnsupportedSource
        "source tuple construction is not implemented for this declared domain"
  unless components.size >= 2 do
    throwThe MessageData m!"a source pair requires both native components"
  let some first := components[0]?
    | liftM (m := TermElabM) <| throwError "a source pair requires its first component"
  let tail := components.drop 1
  constructTuple constructor expected #[
    fun type => readComponent first type,
    fun type => do
      if let #[last] := tail then readComponent last type
      else sourceTupleCore tail type readComponent]




def sourceTupleApplicable (components : Array (TSyntax `cas_term)) (expected : Expr)
    (readComponent : TSyntax `cas_term → Expr → SourceReadM (Except MessageData Expr)) :
    SourceReadM (Except MessageData Expr) :=
  (sourceTupleCore components expected fun component type =>
    ExceptT.mk (readComponent component type)).run


def sourceTuple (components : Array (TSyntax `cas_term)) (expected : Expr)
    (readComponent : TSyntax `cas_term → Expr → SourceReadM Expr) : SourceReadM Expr := do
  let result ← sourceTupleApplicable components expected fun component type => do
    return .ok (← readComponent component type)
  match result with
  | .ok value => pure value
  | .error message => liftM (m := TermElabM) <| throwError message

end CasCompiler
