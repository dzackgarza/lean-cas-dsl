module

public import CasCompiler.SourceRing
import CasCompiler.SourceCarrier

public section

namespace CasCompiler

open Lean Meta Elab Term CasCatalogue

/-- The distinguished point registered on the actual selected source object.
Reuse: registeredDomain follows original source aliases, applyObjectParameters retains the
declaration's complete actual parameters, and sourcePointValue applies its native point map.
No generator is selected by a coincident carrier or an inferred algebraic structure. -/
def sourceObjectGenerator (object : NativeSourceJudgement) : TermElabM Expr := do
  let some category := object.category
    | throwError "an explicit generator requires its selected source object"
  unless category.role == .object do
    throwError "an explicit generator requires an object"
  let (declared, entries) ← registeredDomain object.value
  if entries.isEmpty then
    throwUnsupportedSource "an explicit generator requires a registered source object"
  let #[entry] := entries
    | throwSemanticAmbiguity "an explicit generator requires one registered source object"
  unless declared.getAppFn.constName? == some entry.declaration do
    throwError "the generator's source object lost its original declaration parameters"
  let some generator := entry.generator
    | throwUnsupportedSource "the selected object has no registered generator"
  discard <| checkedDeclaration entry.declaration
  discard <| checkedDeclaration generator
  let point ← applyObjectParameters s!"generator of {entry.id.raw}" generator declared.getAppArgs
  let pointType ← whnfR (← inferType point)
  unless pointType.isAppOfArity ``Quiver.Hom 4 do
    throwUnsupportedSource "the selected generator requires its remaining declared parameters"
  let carrier ← sourceCarrierFamilyObject category category.bundle object.value
  checkRegisteredDomains pointType.getAppArgs[3]! carrier
  unless ← isDefEq pointType.getAppArgs[3]! carrier do
    throwError "the registered generator has a different complete selected carrier"
  let value ← sourcePointValue point (some carrier)
  -- A named set's original binder is already its exact element type. Keeping that binder
  -- lets later operation selection use its declared named refinement. Structured objects
  -- keep the same complete carrier provenance used by the ordinary carrier reader.
  let type ← if category.expression.syntacticEq (.atom CategoryId.sets) then
      pure object.value
    else annotateSourceType category object.value carrier
  let value ← mkAppOptM ``id #[some type, some value]
  return sourceReference ``ObjectEntry.generator entry.id.raw generator value

end CasCompiler
