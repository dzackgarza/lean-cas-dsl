module

public import CasCompiler.SourceCarrier
public import LeanCategories.Catalogue.Lift
public import CasCompiler.LiftFamily
public import CasCompiler.SelectedField

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

-- Reuse registered boundaries and edgesFrom's unary constructor action.
-- An explicitly selected lift keeps the registered action's actual role.
private partial def liftEdgeBoundary (state : SemanticState) (ref : EdgeRef) :
    MetaM (CategoryExpr × CategoryExpr) := do
  match ref with
  | .constructMap id inner =>
    let (source, target) ← liftEdgeBoundary state inner
    return (.construct id #[.category source], .construct id #[.category target])
  | .functor id =>
    let some entry := state.functor? id
      | throwError "the selected lift functor is not registered"
    return (entry.source, entry.target)
  | .classifierForget id =>
    let some entry := state.classifier? id
      | throwError "the selected lift classifier is not registered"
    return (.classifierTotal id, entry.host)

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
  unless (← sourceDomain selected).getAppFn.constName? == some row.evidence do
    throwError "the selected lift changed its independent source declaration"
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
  let selection ← mkFreshUserName `selectedLift
  let value := .mdata (KVMap.empty.setName `CasCompiler.selection selection) value
  return ⟨sourceReference ``LiftEntry row.id.raw row.evidence value, none⟩

private partial def liftSelection (value : Expr) : MetaM Name := do
  match value with
  | .fvar id =>
    let some value := (← id.getDecl).value?
      | throwError "the selected lift has no retained source identity"
    liftSelection value
  | .mdata data body =>
    let selection := data.getName `CasCompiler.selection
    if selection.isAnonymous then liftSelection body else pure selection
  | _ => throwError "the selected lift lost its source identity"

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

/-- The original inputs of a selected lift application (`SourceLiftApplication.mk`): the
evidence, the object, the base, the inclusion and its monicity, read through the definitions of
the source bindings that name it. -/
private partial def liftInputs (value : Expr) : MetaM (Expr × Expr × Expr × Expr × Expr) := do
  match value with
  | .fvar id =>
    let some value := (← id.getDecl).value?
      | throwError "the selected lift application has no definition"
    liftInputs value
  | .mdata _ body => liftInputs body
  | .letE _ _ bound body _ => liftInputs (body.instantiate1 bound)
  | _ =>
    let some name := value.getAppFn.constName?
      | throwError "the selected lift application is not formed by its constructor"
    unless name == ``SourceLiftApplication.mk do
      throwError "the selected lift application is not formed by its constructor"
    let constructor ← getConstInfoCtor name
    let #[evidence, object, domain, inclusion, monicity] :=
        value.getAppArgs.extract constructor.numParams value.getAppNumArgs
      | throwError "the selected lift application has a different constructor"
    return (evidence, object, domain, inclusion, monicity)

/-- Project the actual independent callable data at the retained original application.
Reuse: LiftEntry.computation and the four field projections of MonoLiftComputation, applied to
the application's own inputs. The lift's computation is marked for its ports (LiftFamily); no
result is rebuilt and the computation is not unfolded. -/
def sourceLiftMember? (receiver : NativeSourceJudgement) (name : String) :
    TermElabM (Option NativeSourceJudgement) := do
  let type ← whnfR (← inferType receiver.value)
  unless type.isAppOf ``SourceLiftApplication do return none
  let some row ← liftReference receiver.value
    | throwError "the native lift application has no selected source reference"
  let (source, target) ← liftBoundary (← semanticState) row
  let functor := type.getAppArgs.back!
  let (sourceBundle, targetBundle) ← functorCategoryBundles functor
  let (evidence, object, domainObject, inclusion, monicity) ← liftInputs receiver.value
  let computation ← LiftFamily.atEvidence row .computation evidence
  let selection ← liftSelection receiver.value
  let computation ← selectRecordActions selection computation
  let declaration ← match name with
    | "obj" => pure ``MonoLiftComputation.obj
    | "hom" => pure ``MonoLiftComputation.hom
    | "forward" => pure ``MonoLiftComputation.forward
    | "backward" => pure ``MonoLiftComputation.backward
    | _ => throwError "the selected lift has no declared member {name}"
  let function ← mkAppM declaration #[computation]
  -- The actual input and proof are supplied explicitly; local instances cannot replace them.
  let value := selectedField selection declaration
    (mkAppN function #[object, domainObject, inclusion, monicity])
  check value
  let category := if name == "forward" || name == "backward" then target else source
  let bundle := if name == "forward" || name == "backward" then targetBundle else sourceBundle
  let role := if name == "obj" then SourceCategoryRole.object else .morphism
  return some ⟨value, some ⟨role, category, bundle, none⟩⟩

/-- The universal factor through a selected lift (`factor(g) through L with f using proof(p)`):
for the base arrow `g : U Y ⟶ K`, the source arrow `f : Y ⟶ X` and the formal equation
`p : U.map f = g ≫ i`, the arrow `Y ⟶ L.obj X i` of the lift's upstream factor computation at
the lift's actual object and inclusion. Reuse: MonoLift.factorComputation and
MonoLiftFactorComputation.factor; the factor laws stay upstream and are not data. -/
def sourceLiftFactor (receiver : NativeSourceJudgement) (base source proof : Expr) :
    TermElabM NativeSourceJudgement := do
  let type ← whnfR (← inferType receiver.value)
  unless type.isAppOf ``SourceLiftApplication do
    throwError "a source factor requires a selected lift application"
  let some row ← liftReference receiver.value
    | throwError "the native lift application has no selected source reference"
  let (category, _) ← liftBoundary (← semanticState) row
  let (bundle, _) ← functorCategoryBundles type.getAppArgs.back!
  let (evidence, object, domainObject, inclusion, monicity) ← liftInputs receiver.value
  let computation ← LiftFamily.atEvidence row .factor evidence
  let function ← mkAppM ``MonoLiftFactorComputation.factor #[computation]
  let sourceType ← whnfR (← inferType source)
  unless sourceType.isAppOfArity ``Quiver.Hom 4 do
    throwError "the factor's source arrow is not a morphism"
  let apex := sourceType.getAppArgs[2]!
  -- The actual input, proof and source object are supplied explicitly; no instance is searched.
  let value := mkAppN function #[object, domainObject, inclusion, monicity, apex, base, source, proof]
  let selection ← liftSelection receiver.value
  let selected ← selectRecordActions selection
    (← LiftFamily.atEvidence row .computation evidence)
  let target := mkAppN (← mkAppM ``MonoLiftComputation.obj #[selected])
    #[object, domainObject, inclusion, monicity]
  let resultType ← whnfR (← inferType value)
  unless resultType.isAppOfArity ``Quiver.Hom 4 do
    throwError "the selected factor has no declared morphism endpoints"
  let value ← mkExpectedTypeHint value
    (mkAppN resultType.getAppFn (resultType.getAppArgs.set! 3 target))
  check value
  return ⟨value, some ⟨.morphism, category, bundle, none⟩⟩

end CasCompiler
