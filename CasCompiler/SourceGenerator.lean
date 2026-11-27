module

public import CasCompiler.SourceRing
import CasCompiler.SourceCarrier

public section

namespace CasCompiler

open Lean Meta Elab Term CasCatalogue





def sourceObjectGenerator (object : NativeSourceJudgement) : SourceReadM Expr := do
  let some category := object.category
    | liftM (m := TermElabM) <| throwError "an explicit generator requires its selected source object"
  unless category.role == .object do
    liftM (m := TermElabM) <| throwError "an explicit generator requires an object"
  let (declared, entries) ← registeredSourceDomain object.value
  if entries.isEmpty then
    liftM (m := TermElabM) <| throwUnsupportedSource "an explicit generator requires a registered source object"
  let #[entry] := entries
    | liftM (m := TermElabM) <| throwSemanticAmbiguity "an explicit generator requires one registered source object"
  unless declared.getAppFn.constName? == some entry.declaration do
    liftM (m := TermElabM) <| throwError "the generator's source object lost its original declaration parameters"
  let some generator := entry.generator
    | liftM (m := TermElabM) <| throwUnsupportedSource "the selected object has no registered generator"
  discard <| checkedDeclaration entry.declaration
  discard <| checkedDeclaration generator
  let point ← applyObjectParameters s!"generator of {entry.id.raw}" generator declared.getAppArgs
  let pointType ← whnfR (← inferType point)
  unless pointType.isAppOfArity ``Quiver.Hom 4 do
    liftM (m := TermElabM) <| throwUnsupportedSource "the selected generator requires its remaining declared parameters"
  let carrier ← sourceCarrierFamilyObject category category.bundle object.value
  checkRegisteredSourceDomains pointType.getAppArgs[3]! carrier
  unless ← (← get).context.withOriginalSources #[pointType.getAppArgs[3]!, carrier]
      (fun values => isDefEq values[0]! values[1]!) do
    liftM (m := TermElabM) <| throwError "the registered generator has a different complete selected carrier"
  let value ← sourcePointValue point (some carrier)



  let type ← if category.expression.syntacticEq (.atom CategoryId.sets) then
      pure object.value
    else annotateSourceType category object.value carrier
  let selected := (← SourceReadM.selection? value).getD { value }
  let selected ← retainSourceApplication { selected with
    value := value
    reference := some (.generator entry) } point
  SourceReadM.select selected (some type)

end CasCompiler
