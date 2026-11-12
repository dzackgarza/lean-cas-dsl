module

public import CasCompiler.SourceRing
public import CasCatalogue.Evaluation
public import CasContract.Failure

public section

namespace CasCompiler

open Lean Meta Elab Term CasCatalogue

/-- The explicit arguments of an application, in order. -/
def sourceExplicitArguments (expression : Expr) : MetaM (Array Expr) := do
  let arguments := expression.getAppArgs
  let info ← getFunInfoNArgs expression.getAppFn arguments.size
  return (arguments.zip (info.paramInfo.map (·.isExplicit))).filterMap fun (argument, explicit) =>
    if explicit then some argument else none

/-- The registered object with an admission whose object family, at the parameters that
reducible unification determines, is the native type `type` (`ℙ` for `Nat.Primes`). -/
def sourceAdmissionDomain? (type : Expr) : MetaM (Option ObjectEntry) := do
  let state ← semanticState
  let mut found := #[]
  for entry in state.objects do
    unless entry.admission.isSome do continue
    discard <| checkedDeclaration entry.declaration
    let family ← mkConstWithFreshMVarLevels entry.declaration
    let (parameters, _, _) ← forallMetaTelescopeReducing (← inferType family)
    let applicable ← withoutModifyingState <| withReducible <|
      isDefEq (mkAppN family parameters) type
    if applicable then found := found.push entry
  match found with
  | #[] => return none
  | #[entry] => return some entry
  | _ => throwSemanticAmbiguity "several admitted subobjects have this carrier"

/-- Establish the hypothesis `obligation` of an admission by the domain's registered evidence and
nothing else, at the closed value it is about. The result is the term the procedure built.
Source: ObjectEntry.evidence (LC-18) and `Evaluation.runProcedure`, the one procedure runner. -/
private def establish (entry : ObjectEntry) (obligation : Expr) : TermElabM Expr := do
  let some evidence := entry.evidence
    | throwStratum .invalid m!"{entry.name} registers no evidence for its admission"
  let closed ← zetaReduce (← instantiateMVars obligation)
  if closed.hasFVar || closed.hasMVar then
    throwStratum .invalid
      m!"the hypothesis {closed} of {entry.name} is about a value that is not closed"
  let goal ← mkFreshExprMVar closed .syntheticOpaque
  match ← Evaluation.runProcedure evidence goal.mvarId! with
  | .error message =>
    throwStratum .invalid m!"{closed} is not established by the evidence of {entry.name}: {message}"
  | .ok remaining =>
    unless remaining.isEmpty do
      throwStratum .invalid m!"the evidence of {entry.name} leaves {closed} unestablished"
    let term ← instantiateMVars goal
    if term.hasMVar || term.hasSorry then
      throwStratum .invalid m!"the evidence of {entry.name} built no closed term for {closed}"
    return term

/-- The element `v` of the subobject `D` (the object whose carrier is `target`), by its registered
admission `∀ params (x : B) (h : P x), 1 ⟶ D params`: `x` is read in `B` by `read`, each
hypothesis is established by the domain's evidence, and the admitted point is read at its point.
The element is the first explicit binder that the admission's target does not depend on; the
explicit binders after it are its hypotheses. Source: ObjectEntry.admission and the original
reader's `admit`. A value that is not established to lie in `D` is not an element of it. -/
def sourceAdmission (entry : ObjectEntry) (target : Expr) (read : Expr → TermElabM Expr) :
    TermElabM Expr := do
  let some admission := entry.admission
    | throwStratum .invalid m!"{entry.name} registers no admission"
  discard <| checkedDeclaration admission
  let constant ← mkConstWithFreshMVarLevels admission
  let (arguments, infos, type) ← forallMetaTelescopeReducing (← inferType constant)
  let type ← whnfR type
  unless type.isAppOfArity ``Quiver.Hom 4 do
    throwError "the admission of {entry.name} is not a point map"
  unless ← withReducible (isDefEq type.getAppArgs[3]! target) do
    throwStratum .invalid m!"the admission of {entry.name} does not land in the selected domain"
  let explicit := (List.range arguments.size).toArray.filter (infos[·]!.isExplicit)
  let some element := explicit.find? fun index =>
      (type.findMVar? (· == arguments[index]!.mvarId!)).isNone
    | throwError "the admission of {entry.name} takes no value"
  let value ← read (← instantiateMVars (← inferType arguments[element]!))
  unless ← isDefEq arguments[element]! value do
    throwStratum .invalid m!"the value is not in the set that {entry.name} is included in"
  for argument in arguments, info in infos do
    if info.isInstImplicit && (← instantiateMVars argument).isMVar then
      let some instanceValue ← synthInstance? (← inferType argument)
        | throwError "the admission of {entry.name} lacks its declared instance"
      discard <| isDefEq argument instanceValue
  for index in explicit.filter (element < ·) do
    let proof ← establish entry (← inferType arguments[index]!)
    unless ← isDefEq arguments[index]! proof do
      throwStratum .invalid m!"the evidence of {entry.name} does not apply"
  let admitted ← instantiateMVars (mkAppN constant arguments)
  if admitted.hasMVar || admitted.hasLevelMVar then
    throwStratum .invalid m!"the parameters or evidence of {entry.name} are not determined"
  sourcePointValue admitted (some target)

end CasCompiler
