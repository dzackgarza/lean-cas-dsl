module

public import CasCompiler.Surface

public section

namespace CasCompiler

open Lean Meta Elab Term

-- As in ReadExpression's native application, infer the complete dependent argument
-- types first, then retain each actual source expression in the final application.
-- Reuse: Lean.Elab.App.elabAppArgs and native constructor declarations.
private def constructTuple (declaration : Name) (expected : Expr)
    (arguments : Array (Expr → TermElabM Expr)) : TermElabM Expr := do
  let function ← mkConstWithFreshMVarLevels declaration
  let holes ← arguments.mapM fun _ => mkFreshExprMVar none
  discard <| elabAppArgs function #[] (holes.map Arg.expr) (some expected) false false
  let mut actual := #[]
  for argument in arguments, hole in holes do
    let value ← argument (← instantiateMVars (← inferType hole))
    unless ← isDefEq hole value do
      throwError "the source tuple component has a different dependent native type"
    actual := actual.push (Arg.expr value)
  let value ← elabAppArgs function #[] actual (some expected) false false
  mkExpectedTypeHint value expected

-- Reuse Fin.cases/Fin.elim0, the native construction underlying Fin.cons.
-- Each component receives its actual dependent type before its source is read.
private partial def finiteTuple (components : Array (Expr → TermElabM Expr))
    (expected : Expr) : TermElabM Expr := do
  let .forallE name domain codomain info ← whnf expected
    | throwError "the source finite tuple requires its declared indexed domain"
  let index ← whnf domain
  unless index.isAppOfArity ``Fin 1 do
    throwError "the source finite tuple requires its declared finite index"
  unless ← isDefEq index.getAppArgs[0]! (mkNatLit components.size) do
    throwError "the source tuple has a different declared finite arity"
  if components.isEmpty then
    return ← withLocalDecl name info domain fun argument => do
      let value ← mkAppOptM ``Fin.elim0
        #[some (codomain.instantiate1 argument), some argument]
      mkLambdaFVars #[argument] value
  let some first := components[0]?
    | throwError "a nonempty source finite tuple requires its first component"
  constructTuple ``Fin.cases expected #[first,
    fun type => finiteTuple (components.drop 1) type]

/-- Construct finite rows at the complete supplied native matrix domain.
Reuse: the same Fin.cases constructor as sourceTuple. Row and column arities come
from the actual dependent function type; original cells are read once in order. -/
def sourceMatrix (rows : Array (Array (TSyntax `cas_term))) (expected : Expr)
    (readComponent : TSyntax `cas_term → Expr → TermElabM Expr) : TermElabM Expr := do
  if let some first := rows[0]? then
    unless rows.all (·.size == first.size) do
      throwError "source matrix rows have different finite arities"
  finiteTuple (rows.map fun row type =>
    finiteTuple (row.map fun component type => readComponent component type) type) expected

/-- Construct a tuple at its actual declared native domain.
Reuse: Prod/Sigma/PSigma constructors and Fin.cases, the dependent constructor underlying
Mathlib.Data.Fin.Tuple.Basic's Fin.cons. Empty tails use native Fin.elim0. Original
components are read once at their actual dependent types; the domain is never replaced. -/
partial def sourceTuple (components : Array (TSyntax `cas_term)) (expected : Expr)
    (readComponent : TSyntax `cas_term → Expr → TermElabM Expr) : TermElabM Expr := do
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
    throwError "a source pair requires both native components"
  let some first := components[0]?
    | throwError "a source pair requires its first component"
  let tail := components.drop 1
  constructTuple constructor expected #[
    fun type => readComponent first type,
    fun type => do
      if let #[last] := tail then readComponent last type
      else sourceTuple tail type readComponent]

end CasCompiler
