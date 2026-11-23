module

public import LeanCategories.Catalogue.Registry.Computation
public import CasCompiler.Layout
public import CasCompiler.Declaration
public import CasCompiler.LiftFamily
public import CasCompiler.PresentationFamily

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
  return ⟨{ reference, declaration, family := family.expression, familyType := family.type },
    info.levelParams⟩

/-- Exact registered family, checked derivation target, ordered primitive slot, or a published
computation of a selected lift. -/
inductive ProgramBoundary
  | registered (family : SourceFamily)
  | target (program : SourceProgram)
  | prerequisite (program : SourceProgram) (index : Fin program.source.prerequisites.size)
  | lift (family : LiftFamily)
  | presentation (family : PresentationFamily)

/-- The published computation family, whose public address is a `ComputationRef`. A lift's
computation is addressed by its lift row instead (`ProgramBoundary.lift`). -/
def ProgramBoundary.reference : ProgramBoundary → Option ComputationRef
  | .registered family => some family.source.reference
  | .target program => some program.source.entry.target
  | .prerequisite program index => some program.source.prerequisites[index.val].reference
  | .lift _ | .presentation _ => none

def ProgramBoundary.family : ProgramBoundary → Expr
  | .registered family => family.source.family
  | .target program => program.source.target
  | .prerequisite program index => program.source.prerequisites[index.val].family
  | .lift family => family.family
  | .presentation family => family.family

def ProgramBoundary.universeParams : ProgramBoundary → List Name
  | .registered family => family.universeParams
  | .target program | .prerequisite program _ => program.source.universeParams
  | .lift family => family.universeParams
  | .presentation family => family.universeParams

end CasCompiler
