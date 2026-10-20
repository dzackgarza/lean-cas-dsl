module

public import CasCatalogue.EvidencePresentation

@[expose] public section

open Lean Meta Elab Term

namespace CasCatalogue.ProofRefinement

/-- The actual total object and its checked full forgetful image. No computational answer
participates in constructing this proof-only refinement. -/
structure Result where
  value : Expr
  action : Expr
  identity : Expr

/-- Elaborate the public constructor of an actual classifier total under its full forgetful
image constraint. Remaining fields must be propositions established by existing class or
Decidable instances; this never chooses missing structure from its carrier. -/
def construct (state : RegistryState) (classifier : ClassifierId)
    (target : NamedCategoryEntry) (source : Expr) : TermElabM Result := do
  unless !source.hasMVar && !source.hasLevelMVar && !source.hasFVar &&
      !source.hasLooseBVars && (← isTypeCorrect source) do
    throwStratum .invalid "a proof refinement requires a complete supplied object"
  unless target.expression.syntacticEq (.classifierTotal classifier) do
    throwStratum .invalid "the requested category is not this classifier's total"
  let total ← mkAppHere ``CategoryTheory.Bundled.α #[← instantiateFresh target.declaration]
  let reduced ← withTransparency .all <| whnf total
  let some head := reduced.getAppFn.constName?
    | throwStratum .invalid "the classifier total has no supplied data constructor"
  let .inductInfo info ← getConstInfo head
    | throwStratum .invalid "the classifier total has no supplied data constructor"
  let [ctor] := info.ctors
    | throwStratum .invalid "the classifier total does not determine one data constructor"
  let constructor ← mkConstWithFreshMVarLevels ctor
  let (args, _, type) ← forallMetaTelescopeReducing (← inferType constructor)
  unless ← withTransparency .all <| isDefEq type total do
    throwStratum .invalid "the public constructor does not inhabit this classifier total"
  let candidate := mkAppN constructor args
  let action ← Semantic.asFunctor (← Semantic.edgeFunctor state (.classifierForget classifier))
  let pref ← mkAppHere ``CategoryTheory.Functor.toPrefunctor #[action]
  let image ← withTransparency .all <| mkAppHere ``Prefunctor.obj #[pref, candidate]
  unless ← withTransparency .all <| isDefEq image source do
    throwStratum .invalid "the classifier's full forgetful image is not the supplied object"
  for arg in args do
    let arg ← instantiateMVars arg
    unless arg.isMVar do continue
    let obligation ← instantiateMVars (← inferType arg)
    unless ← isProp obligation do
      throwStratum .invalid m!"the classifier requires additional chosen data: {obligation}"
    let presented ← Language.evidencePresentation state obligation
    let proof? ← match ← isClass? presented with
      | some _ => synthInstance? presented
      | none => Decide.decisionProof presented
    let some proof := proof?
      | throwStratum .invalid m!"the published instances do not establish {obligation}"
    unless ← Decide.kernelAccepts obligation proof do
      throwStratum .invalid "the refinement obligation has no accepted proof"
    unless ← isDefEq arg proof do
      throwStratum .invalid "the refinement proof changed its complete obligation"
  let value ← instantiateMVars candidate
  let action ← instantiateMVars action
  let image ← instantiateMVars image
  unless !value.hasMVar && !value.hasLevelMVar && !value.hasSorry &&
      !action.hasMVar && !action.hasLevelMVar && (← isTypeCorrect value) &&
      (← withTransparency .all <| isDefEq (← inferType value) total) &&
      (← withTransparency .all <| isDefEq image source) do
    throwStratum .invalid "the proof refinement did not retain its complete supplied data"
  let identity ← mkEqRefl image
  unless ← Decide.kernelAccepts (← mkEq image source) identity do
    throwStratum .invalid "the full forgetful image identification is not accepted"
  return { value, action, identity }

end CasCatalogue.ProofRefinement
