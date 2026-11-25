module

public import LeanCategories.Catalogue.Registry.Computation
public import CasCompiler.Layout
public import CasCompiler.Declaration
public import CasCompiler.LiftFamily
public import CasCompiler.PresentationFamily
public import CasCompiler.RoutedMethodFamily
public import CasCompiler.PropertyFamily
public import CasCompiler.PointFamily
public import CasCompiler.CategoricalPointFamily
public import CasCompiler.LimitFamily
public import CasCompiler.LimitUniversalFamily
public import CasCompiler.PreparedCreationFamily
public import CasCompiler.SourceReference

@[expose] public section

namespace CasCompiler

open Lean Meta CasCatalogue

/-- The accepted whole-family source, before specialization or executable selection. -/
structure SourceProgram where
  private mk ::
  source : CheckedComputationDerivation

/-- One formal callable slot. Its ordinal and published reference are independent of its type. -/
structure PrerequisiteSlot where
  index : Nat
  source : CheckedComputationPrerequisite
  expression : Expr

/-- The checked slot supplies its exact address before any substitution or native projection.
Metadata retains the original whole family and its rigid universe application. -/
private def selectedComputationFamily (source : CheckedComputationPrerequisite) : Expr :=
  let (kind, id) := match source.reference with
    | .operation id => (``OperationEntry, id.raw)
    | .functor id => (``EdgeRef.functor, id.raw)
    | .method id => (``MethodEntry, id.raw)
    | .construction id => (``ConstructionEntry, id.raw)
    | .morphism id => (``MorphismEntry, id.raw)
  sourceReference kind id source.declaration source.family

/-- Read every published alternative through the upstream safety and axiom checks.
The upstream checked packet is retained intact, including rigid universes and equality.
Source: LeanCategories/Catalogue/Registry/Computation.lean at
8c35703b104aca1700b9fb40d1af4164ca31a55d. -/
opaque SourceProgram.forTarget (target : ComputationRef) : MetaM (Array SourceProgram) := do
  return (← checkedComputationDerivations target).map fun source => ⟨source⟩

/-- Open only the prerequisite prefix with fresh locals; keep the entire target family.
Lean's telescope and application operations retain dependent binder types and slot order. -/
def SourceProgram.withPrerequisites (program : SourceProgram)
    (action : Array PrerequisiteSlot → Expr → MetaM α) : MetaM α := do
  let source := program.source
  forallBoundedTelescope (← inferType source.template) (some source.prerequisites.size)
      fun locals _ => do
    unless locals.size == source.prerequisites.size do
      throwError "checked source program has an incomplete prerequisite telescope"
    let slots := source.prerequisites.mapIdx fun index prerequisite =>
      { index, source := prerequisite, expression := locals[index]! : PrerequisiteSlot }
    action slots (mkAppN source.template locals).headBeta

/-- Instantiate the accepted template with its original ordered primitive families.
Only the independently checked template supplies composition; each prerequisite keeps its
own public reference. No declaration search or source equality selects a primitive. -/
opaque SourceProgram.instantiate (program : SourceProgram) (universes : List Level) : MetaM Expr := do
  unless universes.length == program.source.universeParams.length do
    throwError "the source program lost its complete universe substitution"
  let family ← program.withPrerequisites fun slots body => do
    return body.replaceFVars (slots.map (·.expression))
      (slots.map (selectedComputationFamily ∘ PrerequisiteSlot.source))
  return family.instantiateLevelParams program.source.universeParams universes

/-- A directly registered family, checked before any specialization or provider selection. -/
structure SourceFamily where
  private mk ::
  source : CheckedComputationPrerequisite
  universeParams : List Name

/-- Resolve the exact public address and retain the entire rigid family.
Reuse: ComputationRef.declaration, the release AxiomAudit.permitted budget and native context closure. -/
opaque SourceFamily.forReference (reference : ComputationRef) : MetaM SourceFamily := do
  let declaration ← reference.declaration (← semanticState)
  let info ← checkedDeclaration declaration
  let family ← withLCtx {} #[] do
    let context ← ContextTelescope.capture #[]
    context.close (mkConst declaration (info.levelParams.map Level.param))
  let source : CheckedComputationPrerequisite :=
    { reference, declaration, family := family.expression, familyType := family.type }
  return ⟨{ source with family := selectedComputationFamily source }, info.levelParams⟩

/-- Apply the exact selected family while retaining its original marked source roles.
Only native input routing receives the separate whole-family body. A nullary family keeps
the same zero-argument application frame so later native projections retain this authority. -/
opaque SourceFamily.applyIn (family : SourceFamily) (universes : List Level)
    (context : OpenContext) (arguments : Array ClosedTerm) :
    MetaM (SourceLayout × ApplicationLayout) := do
  unless universes.length == family.universeParams.length do
    throwError "the selected family lost its complete universe substitution"
  let (original, native) ← withLCtx {} #[] do
    let empty ← ContextTelescope.capture #[]
    let original := family.source.family.instantiateLevelParams family.universeParams universes
    let .mdata _ native := original
      | throwError "the selected family lost its original source address"
    return (← empty.close original, ← empty.close native)
  ApplicationLayout.ofSource (← SourceLayout.ofTerm original) context arguments (some native)

/-- A complete accepted source interface: a registered family, checked derivation target,
ordered primitive slot, selected lift/presentation/method, or native property observation. -/
inductive ProgramBoundary
  | registered (family : SourceFamily)
  | target (program : SourceProgram)
  | prerequisite (program : SourceProgram) (index : Fin program.source.prerequisites.size)
  | lift (family : LiftFamily)
  | presentation (family : PresentationFamily)
  | routedMethod (family : RoutedMethodFamily)
  | property (family : PropertyFamily)
  | application (family : PointFamily)
  | point (family : CategoricalPointFamily)
  | objectAction (family : SourceActionFamily)
  | limit (family : LimitFamily) (owner : ClosedTerm)
  | limitUniversal (family : LimitUniversalFamily) (owner : ClosedTerm)
  | creation (family : PreparedCreationFamily)

/-- A published computation-family address, when this boundary has one. Other accepted
source interfaces retain their own exact registered address in the boundary witness. -/
def ProgramBoundary.reference : ProgramBoundary → Option ComputationRef
  | .registered family => some family.source.reference
  | .target program => some program.source.entry.target
  | .prerequisite program index => some program.source.prerequisites[index.val].reference
  | .lift _ | .presentation _ | .routedMethod _ | .property _ | .application _
  | .point _ | .objectAction _ | .limit _ _ | .limitUniversal _ _ | .creation _ => none

def ProgramBoundary.universeParams : ProgramBoundary → List Name
  | .registered family => family.universeParams
  | .target program | .prerequisite program _ => program.source.universeParams
  | .lift family => family.universeParams
  | .presentation family => family.universeParams
  | .routedMethod family => family.universeParams
  | .property family => family.universeParams
  | .application family => family.universeParams
  | .point family => family.universeParams
  | .objectAction family => family.universeParams
  | .limit family _ => family.universeParams
  | .limitUniversal family _ => family.universeParams
  | .creation family => family.family.universeParams

/-- Open the accepted family in the caller's original complete source context. Global
declarations retain their rigid universe substitution; a fixed creation request reopens its
already captured native context and is never reinterpreted in an empty local context. -/
def ProgramBoundary.familyIn (boundary : ProgramBoundary) (universes : List Level)
    (context : OpenContext) : MetaM Expr := do
  unless universes.length == boundary.universeParams.length do
    throwError "the source boundary changed its complete universe telescope"
  let instantiate : Expr → MetaM Expr := fun source =>
    pure (source.instantiateLevelParams boundary.universeParams universes)
  match boundary with
  | .registered family => instantiate family.source.family
  | .target program => instantiate program.source.target
  | .prerequisite program index => instantiate program.source.prerequisites[index.val].family
  | .lift family => instantiate family.family
  | .presentation family => instantiate family.family
  | .routedMethod family => instantiate family.family
  | .property family => instantiate family.family
  | .application family => instantiate family.family
  | .point family => instantiate family.family
  | .objectAction family => instantiate family.family
  | .limit family _ => instantiate family.family
  | .limitUniversal family _ => instantiate family.family
  | .creation family => do
    unless universes == family.universes do
      throwError "the fixed creation changed its original evidence universe arguments"
    family.familyIn context

end CasCompiler
