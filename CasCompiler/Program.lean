module

public import CasCompiler.SelectionData
import all CasCompiler.SelectionData

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



structure PrerequisiteSlot where
  index : Nat
  source : CheckedComputationPrerequisite
  expression : Expr





opaque SourceProgram.forTarget (target : ComputationRef) : MetaM (Array SourceProgram) := do
  let targetReference ← SelectedSourceReference.forComputation target
  (← checkedComputationDerivations target).mapM fun source => do
    let prerequisites ← source.prerequisites.mapM fun prerequisite =>
      SelectedSourceReference.forComputation prerequisite.reference
    return ⟨source, targetReference, prerequisites⟩



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




opaque SourceProgram.instantiate [Monad m] [MonadLiftT MetaM m] [MonadControlT MetaM m]
    (program : SourceProgram) (universes : List Level) (identities : CasRuntime.IdentitySupply)
    (context : OpenContext) (selections : SourceSelectionScope Expr)
    (action : OpenContext → SourceSelectionScope Expr → Expr → m α) : m α := do
  unless universes.length == program.source.universeParams.length do
    liftM (m := MetaM) <| throwError "the source program lost its complete universe substitution"
  let template := program.source.template.instantiateLevelParams
    program.source.universeParams universes
  let rec visit (remaining : List (Fin program.source.prerequisites.size))
      (context : OpenContext) (selections : SourceSelectionScope Expr)
      (arguments : Array Expr) : m α := do
    match remaining with
    | [] =>
      let value := (mkAppN template arguments).headBeta
      liftM (m := MetaM) <| check value
      action context selections value
    | index :: remaining =>
      let source := program.source.prerequisites[index.val]
      let value := source.family.instantiateLevelParams program.source.universeParams universes
      let some reference := program.prerequisiteReferences[index.val]?
        | liftM (m := MetaM) <| throwError "the accepted program lost an original full prerequisite row"
      let selected : SourceSelection Expr := { value, reference := some reference, application := some {
        family := .prerequisite program index, universes, parameters := #[] } }
      SourceSelectionScope.withBinding identities selections context selected
        fun context selections value => visit remaining context selections (arguments.push value)
  visit (List.finRange program.source.prerequisites.size) context selections #[]




opaque SourceFamily.forReference (reference : ComputationRef) : MetaM SourceFamily := do
  let selectedReference ← SelectedSourceReference.forComputation reference
  let some declaration := selectedReference.declaration
    | throwError "the accepted source family lost its original declaration"
  let info ← checkedDeclaration declaration
  let family ← withLCtx {} #[] do
    let context ← ContextTelescope.capture #[]
    context.close (mkConst declaration (info.levelParams.map Level.param))
  let source : CheckedComputationPrerequisite :=
    { reference, declaration, family := family.expression, familyType := family.type }
  let pointFamily ← match selectedReference with
    | .named (.registered (.inr entry) _) => PointFamily.forEntry? entry
    | _ => pure none
  return ⟨source, info.levelParams, selectedReference, pointFamily⟩



opaque SourceFamily.applyIn (family : SourceFamily) (universes : List Level)
    (context : OpenContext) (arguments : Array ClosedTerm) :
    MetaM (SourceLayout × ApplicationLayout) := do
  unless universes.length == family.universeParams.length do
    throwError "the selected family lost its complete universe substitution"
  let original ← withLCtx {} #[] do
    let empty ← ContextTelescope.capture #[]
    let original := family.source.family.instantiateLevelParams family.universeParams universes
    empty.close original
  ApplicationLayout.ofSource (← SourceLayout.ofTerm original) context arguments (some original)



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
  | limit (family : LimitFamily) (owner : SelectedLimitOwner ClosedTerm)
  | limitUniversal (family : LimitUniversalFamily) (owner : SelectedLimitOwner ClosedTerm)
  | creation (family : PreparedCreationFamily)



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
