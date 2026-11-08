module

public import CasCompiler.SourceCarrier
public import LeanCategories.Catalogue.Lift

public section

namespace CasCompiler

open CategoryTheory

universe u₁ u₂ v₁ v₂

/-- Native storage for a selected application of the independent lift interface.
This records its original inputs; all resulting operations are the upstream projections.
Source: MonoLift and the mathematical-input contract, existing lift and universal data. -/
structure SourceLiftApplication {C : Type u₁} {D : Type u₂}
    [Category.{v₁} C] [Category.{v₂} D] (U : C ⥤ D) where
  selected : CasCatalogue.MonoLift U
  object : C
  domain : D
  inclusion : domain ⟶ U.obj object
  monicity : Mono inclusion

open Lean Meta Elab Term CasCatalogue

-- Reuse structuralEdges/edgesFrom's unary constructor action, preserving the exact edge.
private partial def liftEdgeBoundary (state : SemanticState) (ref : EdgeRef) :
    MetaM (CategoryExpr × CategoryExpr) := do
  match ref with
  | .constructMap id inner =>
    let (source, target) ← liftEdgeBoundary state inner
    return (.construct id #[.category source], .construct id #[.category target])
  | _ =>
    let some edge := state.structuralEdge? ref
      | throwError "the selected lift edge is not a declared structural action"
    return (edge.source, edge.target)

private def liftBoundary (state : SemanticState) (row : LiftEntry) :
    MetaM (CategoryExpr × CategoryExpr) := do
  let .subobjects := row.kind
    | throwUnsupportedSource "selected limit lifting requires its declared diagram"
  let (source, target) ← liftEdgeBoundary state row.edge
  -- validateLift checks the complete edge against the actual functor's mapArrow.
  -- Its declared unary boundaries retain the source and target category expressions.
  let .construct _ #[.category source] := source
    | throwError "the selected lift has no declared arrow source category"
  let .construct _ #[.category target] := target
    | throwError "the selected lift has no declared arrow target category"
  return (source, target)

/-- Check the selected whole family before applying original source arguments.
Reuse: Registry.validateLift checks the complete callable family against MonoLift.computation.
The supplied proof selects an actual inclusion; its carrier must equal the written input. -/
def sourceSelectedLift (row : LiftEntry) (receiver input : NativeSourceJudgement)
    (selected monicity : Expr) : TermElabM NativeSourceJudgement := do
  let state ← semanticState
  let (source, target) ← liftBoundary state row
  let some category := receiver.category
    | throwError "a selected lift requires its complete source category"
  unless category.role == .object && category.expression.syntacticEq source do
    throwError "the selected lift has a different complete source category"
  let type ← whnfR (← inferType selected)
  unless type.isAppOfArity ``MonoLift 5 do
    throwError "the selected lift declaration has a different native interface"
  let functor := type.getAppArgs[4]!
  let (domain, codomain) ← functorCategoryBundles functor
  unless ← isDefEq domain category.bundle do
    throwError "the selected lift has different native category parameters"
  let proofType ← whnfR (← inferType monicity)
  unless proofType.isAppOfArity ``CategoryTheory.Mono 5 do
    throwError "the selected lift requires its explicit monicity evidence"
  let inclusion := proofType.getAppArgs.back!
  let arrow : NativeSourceJudgement :=
    ⟨inclusion, some ⟨.morphism, target, codomain, none⟩⟩
  let actual ← if input.category.any (fun selected =>
      selected.role == .morphism && selected.expression.syntacticEq target) then
    pure arrow
  else sourceCarrier arrow
  unless ← isDefEq (← inferType actual.value) (← inferType input.value) <&&>
      isDefEq actual.value input.value do
    throwError "the supplied monicity evidence has a different original inclusion"
  let agreement ← mkExpectedTypeHint (← mkEqRefl actual.value)
    (← mkEq actual.value input.value)
  checkWithKernel agreement
  let domainObject := proofType.getAppArgs[2]!
  let value ← mkAppM ``SourceLiftApplication.mk
    #[selected, receiver.value, domainObject, inclusion, monicity]
  let value ← withLetDecl (← mkFreshUserName `liftInputAgreement)
      (← inferType agreement) agreement fun binding =>
    mkLetFVars #[binding] value (usedLetOnly := false) (generalizeNondepLet := false)
  return ⟨sourceReference ``LiftEntry row.id.raw row.evidence value, none⟩

private partial def liftReference (value : Expr) : MetaM (Option LiftEntry) := do
  match value with
  | .fvar id =>
    match (← id.getDecl).value? with
    | some value => liftReference value
    | none => pure none
  | .mdata data body =>
    if data.getName `CasCompiler.source.kind != ``LiftEntry then return ← liftReference body
    let #[row] := (← semanticState).lifts.filter
      (·.id.raw == data.getString `CasCompiler.source.id)
      | throwError "the selected native lift reference is not unique"
    unless row.evidence == data.getName `CasCompiler.source.declaration do
      throwError "the selected native lift changed its source declaration"
    return some row
  | _ => pure none

/-- Project the actual independent callable data at the retained original application.
Reuse: MonoLift.computation and its four existing field projections. No result is rebuilt. -/
def sourceLiftMember? (receiver : NativeSourceJudgement) (name : String) :
    TermElabM (Option NativeSourceJudgement) := do
  let type ← whnfR (← inferType receiver.value)
  unless type.isAppOf ``SourceLiftApplication do return none
  let some row ← liftReference receiver.value
    | throwError "the native lift application has no selected source reference"
  let (source, target) ← liftBoundary (← semanticState) row
  let functor := type.getAppArgs.back!
  let (sourceBundle, targetBundle) ← functorCategoryBundles functor
  let selected ← mkAppM ``SourceLiftApplication.selected #[receiver.value]
  let object ← mkAppM ``SourceLiftApplication.object #[receiver.value]
  let domainObject ← mkAppM ``SourceLiftApplication.domain #[receiver.value]
  let inclusion ← mkAppM ``SourceLiftApplication.inclusion #[receiver.value]
  let monicity ← mkAppM ``SourceLiftApplication.monicity #[receiver.value]
  let computation ← mkAppM ``MonoLift.computation #[selected]
  let declaration ← match name with
    | "obj" => pure ``MonoLiftComputation.obj
    | "hom" => pure ``MonoLiftComputation.hom
    | "forward" => pure ``MonoLiftComputation.forward
    | "backward" => pure ``MonoLiftComputation.backward
    | _ => throwError "the selected lift has no declared member {name}"
  let function ← mkAppM declaration #[computation]
  -- The actual input and proof are supplied explicitly; local instances cannot replace them.
  let value := mkAppN function #[object, domainObject, inclusion, monicity]
  check value
  let category := if name == "forward" || name == "backward" then target else source
  let bundle := if name == "forward" || name == "backward" then targetBundle else sourceBundle
  let role := if name == "obj" then SourceCategoryRole.object else .morphism
  return some ⟨value, some ⟨role, category, bundle, none⟩⟩

end CasCompiler
