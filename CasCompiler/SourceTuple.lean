module

public import CasCompiler.Surface
public import Mathlib.Data.Fin.VecNotation

public section

namespace CasCompiler

open Lean Meta Elab Term

-- As in ReadExpression's native application, infer the complete dependent argument
-- types first, then retain each actual source expression in the final application.
-- Reuse: Lean.Elab.App.elabAppArgs and native constructor declarations.
private def constructTuple (declaration : Name) (expected : Expr)
    (arguments : Array (Expr → ExceptT MessageData TermElabM Expr)) :
    ExceptT MessageData TermElabM Expr := do
  let function ← mkConstWithFreshMVarLevels declaration
  let holes ← arguments.mapM fun _ => mkFreshExprMVar none
  discard <| elabAppArgs function #[] (holes.map Arg.expr) (some expected) false false
  let mut actual := #[]
  for argument in arguments, hole in holes do
    let value ← argument (← instantiateMVars (← inferType hole))
    unless ← isDefEq hole value do
      throwThe MessageData m!"the source tuple component has a different dependent native type"
    actual := actual.push (Arg.expr value)
  let value ← elabAppArgs function #[] actual (some expected) false false
  mkExpectedTypeHint value expected

-- Nondependent finite data use Mathlib's native vector notation constructors.
-- Dependent or Sort-polymorphic families retain Fin.cases/Fin.elim0. Every component
-- receives its actual declared type before its original source is read.
private partial def finiteTuple (components : Array (Expr → ExceptT MessageData TermElabM Expr))
    (expected : Expr) : ExceptT MessageData TermElabM Expr := do
  let .forallE name domain codomain info ← whnf expected
    | throwError "the source finite tuple requires its declared indexed domain"
  let index ← whnf domain
  unless index.isAppOfArity ``Fin 1 do
    throwError "the source finite tuple requires its declared finite index"
  unless ← isDefEq index.getAppArgs[0]! (mkNatLit components.size) do
    throwThe MessageData m!"the source tuple has a different declared finite arity"
  let homogeneous ← if codomain.hasLooseBVars then pure false
    else pure ((← getLevel codomain).dec.isSome)
  if components.isEmpty then
    if homogeneous then return ← constructTuple ``Matrix.vecEmpty expected #[]
    return ← withLocalDecl name info domain fun argument => do
      let value ← mkAppOptM ``Fin.elim0
        #[some (codomain.instantiate1 argument), some argument]
      mkLambdaFVars #[argument] value
  let some first := components[0]?
    | throwError "a nonempty source finite tuple requires its first component"
  let constructor := if homogeneous then ``Matrix.vecCons else ``Fin.cases
  constructTuple constructor expected #[first,
    fun type => finiteTuple (components.drop 1) type]

/-- Construct finite rows at the complete supplied native matrix domain.
Reuse: the same native finite tuple constructors as sourceTuple. Row and column arities
come from the actual function type; original cells are read once in order. -/
def sourceMatrix (rows : Array (Array (TSyntax `cas_term))) (expected : Expr)
    (readComponent : TSyntax `cas_term → Expr → TermElabM Expr) : TermElabM Expr := do
  if let some first := rows[0]? then
    unless rows.all (·.size == first.size) do
      throwError "source matrix rows have different finite arities"
  let result ← (finiteTuple (rows.map fun row type =>
    finiteTuple (row.map fun component type => liftM (readComponent component type)) type) expected).run
  match result with
  | .ok value => pure value
  | .error message => throwError message

/-- Construct a tuple at its actual declared native domain.
Reuse: Prod/Sigma/PSigma, native Matrix.vecCons/vecEmpty for homogeneous finite data,
and Fin.cases/Fin.elim0 for dependent families. Original components are read once at their
actual dependent types; the complete declared domain is never replaced. -/
private partial def sourceTupleCore (components : Array (TSyntax `cas_term)) (expected : Expr)
    (readComponent : TSyntax `cas_term → Expr → ExceptT MessageData TermElabM Expr) :
    ExceptT MessageData TermElabM Expr := do
  let type ← whnf expected
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
      CasCatalogue.throwUnsupportedSource
        "source tuple construction is not implemented for this declared domain"
  unless components.size >= 2 do
    throwThe MessageData m!"a source pair requires both native components"
  let some first := components[0]?
    | throwError "a source pair requires its first component"
  let tail := components.drop 1
  constructTuple constructor expected #[
    fun type => readComponent first type,
    fun type => do
      if let #[last] := tail then readComponent last type
      else sourceTupleCore tail type readComponent]

/-- The existing tuple construction with explicit component applicability. Only a component's
own result or a false native component/arity comparison returns an error. Exceptions from
its reader, declaration inference or the selected constructor remain native exceptions. -/
def sourceTupleApplicable (components : Array (TSyntax `cas_term)) (expected : Expr)
    (readComponent : TSyntax `cas_term → Expr → TermElabM (Except MessageData Expr)) :
    TermElabM (Except MessageData Expr) :=
  (sourceTupleCore components expected fun component type =>
    ExceptT.mk (readComponent component type)).run

/-- Required tuple reading retains the original public callback and diagnostics. -/
def sourceTuple (components : Array (TSyntax `cas_term)) (expected : Expr)
    (readComponent : TSyntax `cas_term → Expr → TermElabM Expr) : TermElabM Expr := do
  let result ← sourceTupleApplicable components expected fun component type => do
    return .ok (← readComponent component type)
  match result with
  | .ok value => pure value
  | .error message => throwError message

end CasCompiler
