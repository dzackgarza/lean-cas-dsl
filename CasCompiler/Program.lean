module

public import LeanCategories.Catalogue.Registry.Computation

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

end CasCompiler
