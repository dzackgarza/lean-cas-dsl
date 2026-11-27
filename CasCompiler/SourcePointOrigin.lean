module

public import CasCompiler.SelectionData
import all CasCompiler.SelectionData
public import CasCompiler.Surface

public section

namespace CasCompiler

open Lean Meta CasCatalogue


opaque NativeSourcePointOrigin.ofPoint (point value : Expr) :
    MetaM NativeSourcePointOrigin := do
  let point ← instantiateMVars point
  let type ← inferType point
  let type ← if type.isAppOfArity ``Quiver.Hom 4 then pure type else whnfR type
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


def retainSourcePoint (point : Expr) (source : SourceSelection Expr) :
    MetaM (SourceSelection Expr) := do
  return { source with pointOrigin := some (← NativeSourcePointOrigin.ofPoint point source.value) }

private def globalPointDomain : Elab.Term.TermElabM (SourceSelection Expr) := do
  let (entry, category) ← selectObject "Fin" (some "Sets")
  discard <| checkedDeclaration entry.declaration
  let domain ← mkAppM entry.declaration #[mkNatLit 1]
  let categoryFamily ← mkConstWithFreshMVarLevels category.declaration
  let (parameters, _, _) ← forallMetaTelescopeReducing (← inferType categoryFamily)
  let bundle := mkAppN categoryFamily parameters
  let carrier ← mkAppM ``CategoryTheory.Bundled.α #[bundle]
  unless ← isDefEq (← inferType domain) carrier do
    throwError "the global point domain is outside its original registered category"
  let bundle ← instantiateMVars bundle
  if bundle.hasMVar || bundle.hasLevelMVar then
    throwError "the global point domain lost its complete registered category"
  return {
    value := domain
    reference := some (.named (.registered (.inl entry) category))
    originalApplication := some domain
    category := some ⟨.object, category.expression, bundle, none, none⟩ }

private def globalPointAt (domain : Expr) (source : SourceSelection Expr) :
    MetaM (SourceSelection Expr) := do
  let point ← withLocalDeclD `globalPoint domain fun input => do
    let function ← mkLambdaFVars #[input] source.value
      (usedOnly := false) (usedLetOnly := false)
    mkAppM ``TypeCat.ofHom #[function]
  retainSourcePoint point source



def retainGlobalSourcePoint [Monad m] [MonadLiftT Elab.Term.TermElabM m]
    (select : SourceSelection Expr → m Expr) (source : SourceSelection Expr) :
    m (SourceSelection Expr) := do
  if source.pointOrigin.isSome then return source
  let selected ← liftM (m := Elab.Term.TermElabM) globalPointDomain
  let domain ← select selected
  liftM (m := Elab.Term.TermElabM) <| globalPointAt domain source



def sourcePairPoint [Monad m] [MonadLiftT Elab.Term.TermElabM m]
    (select : SourceSelection Expr → m Expr) (first second : SourceSelection Expr) :
    m (SourceSelection Expr) := do
  let sources : SourceSelection Expr × SourceSelection Expr ←
    if first.pointOrigin.isNone && second.pointOrigin.isNone then do
      let selected ← liftM (m := Elab.Term.TermElabM) globalPointDomain
      let domain ← select selected
      let left ← liftM (m := Elab.Term.TermElabM) <| globalPointAt domain first
      let right ← liftM (m := Elab.Term.TermElabM) <| globalPointAt domain second
      pure (left, right)
    else do
      let left ← retainGlobalSourcePoint select first
      let right ← retainGlobalSourcePoint select second
      pure (left, right)
  let (firstSource, secondSource) := sources
  liftM (m := Elab.Term.TermElabM) do
    let some left := firstSource.pointOrigin
      | throwError "the first application operand lost its original source point"
    let some right := secondSource.pointOrigin
      | throwError "the second application operand lost its original source point"
    checkRegisteredDomains left.domain right.domain
    unless left.domain.equal right.domain do
      throwError "application operands require the same original generalized-point domain"
    let value ← mkAppM ``Prod.mk #[first.value, second.value]
    let point ← withLocalDeclD `applicationPoint left.domain fun input => do
      let first ← sourceSetFunction left.point
      let second ← sourceSetFunction right.point
      let pair ← mkAppM ``Prod.mk #[mkApp first input, mkApp second input]
      let function ← mkLambdaFVars #[input] pair (usedOnly := false) (usedLetOnly := false)
      mkAppM ``TypeCat.ofHom #[function]
    retainSourcePoint point { value }

end CasCompiler
