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

/-- The unique registered object family application that is the native type `type` by reducible
unification (`polynomials ℤ` for `Polynomial ℤ`), or `type` itself when there is none or several. -/
def sourceRegisteredForm (type : Expr) : MetaM Expr := do
  let mut found := #[]
  for entry in (← semanticState).objects do
    discard <| checkedDeclaration entry.declaration
    let family ← mkConstWithFreshMVarLevels entry.declaration
    let (parameters, _, _) ← forallMetaTelescopeReducing (← inferType family)
    let object := mkAppN family parameters
    let applicable ← withoutModifyingState do
      unless ← withReducible (isDefEq object type) do return false
      return !(← instantiateMVars object).hasMVar
    if applicable then
      discard <| withReducible (isDefEq object type)
      let object ← instantiateMVars object
      unless found.contains object do found := found.push object
  match found with
  | #[object] => return object
  | _ => return type

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
  -- The procedure is stated of the value's mathematics, not the reader's categorical plumbing.
  let presented ← Evaluation.evidencePresentation (← semanticState) closed
  let goal ← mkFreshExprMVar presented .syntheticOpaque
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
  -- A closed value is admitted at its plumbing-free normal form, which is definitionally it.
  let value ← if (← zetaReduce value).hasFVar then pure value
    else Evaluation.normalizedValue (← zetaReduce (← instantiateMVars value))
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

/-- A binding operator `token` (`∫_{a}^{b} e dt`, `lim_{t → a} e`, `∑_{t ∈ A} e`) through its
registered rows (Registry.Entry.BinderEntry). The notation's arguments are the operation's last
explicit parameters, each a point `1 ⟶ X` (read as an element of `X`) or an object; the bound
variable ranges over the row's domain at the same parameters; the map `t ↦ e` is admitted into
the operation's source object with that object's evidence; the operation is applied to it.
`readArgument` reads an argument at a type, `readBody` the body with the bound variable. Every
parameter must be fixed by the arguments and the body; one row must read the statement. -/
def sourceBinder (token : String) (arguments : Array (Expr → TermElabM Expr))
    (bound : Name) (readBody : Expr → TermElabM Expr) : TermElabM Expr := do
  let state ← semanticState
  let rows := state.binders.filter (·.token == token)
  let attempt := fun (row : BinderEntry) => do
    discard <| checkedDeclaration row.operation
    discard <| checkedDeclaration row.domain
    let operation ← mkConstWithFreshMVarLevels row.operation
    let (parameters, infos, arrow) ← forallMetaTelescopeReducing (← inferType operation)
    let explicit := (parameters.zip infos).filter (·.2.isExplicit) |>.map (·.1)
    unless arguments.size ≤ explicit.size do throwError "the binder takes fewer arguments"
    for parameter in explicit.extract (explicit.size - arguments.size) explicit.size,
        read in arguments do
      let type ← whnfR (← instantiateMVars (← inferType parameter))
      let value ← if type.isAppOfArity ``Quiver.Hom 4 then do
          let element ← read (← instantiateMVars type.getAppArgs[3]!)
          let constant ← withLocalDeclD `point type.getAppArgs[2]! fun point =>
            mkLambdaFVars #[point] element
          elabAppArgs (← mkConstWithFreshMVarLevels ``TypeCat.ofHom) #[] #[Arg.expr constant]
            (some type) false false
        else read type
      unless ← isDefEq parameter value do throwError "the binder argument has another type"
    let domainConstant ← mkConstWithFreshMVarLevels row.domain
    -- The bound variable lies in the registered form of the domain (`ℝ` for `∫_{a}^{b}`).
    let domain ← sourceRegisteredForm (← instantiateMVars (mkAppN domainConstant parameters))
    let arrow ← whnfR arrow
    unless arrow.isAppOfArity ``Quiver.Hom 4 do throwError "the binder operation is not a map"
    let some entry ← sourceAdmissionDomain? (← instantiateMVars arrow.getAppArgs[2]!)
      | throwError "the binder operation does not act on an admitted object of maps"
    let point ← sourceAdmission entry (← instantiateMVars arrow.getAppArgs[2]!) fun base => do
      withLocalDeclD bound domain fun parameter => do
        let body ← readBody parameter
        let function ← mkLambdaFVars #[parameter] body
        unless ← isDefEq (← inferType function) base do
          throwError "the binder body is not a map of the operation's source"
        return function
    let applied ← instantiateMVars (mkAppN operation parameters)
    if applied.hasMVar || applied.hasLevelMVar then
      throwUnsupportedSource m!"the binder {token} has parameters its arguments do not determine"
    let function ← sourceSetFunction (sourceReference ``BinderEntry row.id.raw row.operation applied)
    elabAppArgs function #[] #[Arg.expr point] none false false
  let mut readings := #[]
  for row in rows do
    let reading ← withoutModifyingState do
      try pure (some (← attempt row)) catch _ => pure none
    if reading.isSome then readings := readings.push row
  match readings with
  | #[row] => attempt row
  | #[] =>
    match rows with
    | #[row] => attempt row
    | _ => throwStratum .invalid m!"no registered binder {token} reads these arguments and body"
  | _ => throwSemanticAmbiguity m!"several registered binders {token} read this statement"


/-- The registered object whose family, at parameters that reducible unification determines, is
the native type `type`, with that application. -/
private def registeredObjectAt? (type : Expr) : MetaM (Option (ObjectEntry × Expr)) := do
  let mut found := #[]
  for entry in (← semanticState).objects do
    if entry.refines.isSome then continue
    discard <| checkedDeclaration entry.declaration
    let family ← mkConstWithFreshMVarLevels entry.declaration
    let (parameters, _, _) ← forallMetaTelescopeReducing (← inferType family)
    let object := mkAppN family parameters
    let applicable ← withoutModifyingState do
      unless ← withReducible (isDefEq object type) do return false
      return !(← instantiateMVars object).hasMVar
    if applicable then
      discard <| withReducible (isDefEq object type)
      found := found.push (entry, ← instantiateMVars object)
  match found with
  | #[unique] => return some unique
  | _ => return none

/-- A registered map out of the set `source`: a declaration whose arrow, at parameters that
reducible unification with `source` determines, leaves `source`. -/
private def mapFrom? (declaration : Name) (source : Expr) : MetaM (Option (Expr × Expr)) := do
  discard <| checkedDeclaration declaration
  let constant ← mkConstWithFreshMVarLevels declaration
  let (parameters, _, arrow) ← forallMetaTelescopeReducing (← inferType constant)
  let arrow ← whnfR arrow
  unless arrow.isAppOfArity ``Quiver.Hom 4 do return none
  let applicable ← withoutModifyingState do
    unless ← withReducible (isDefEq arrow.getAppArgs[2]! source) do return false
    return !(← instantiateMVars (mkAppN constant parameters)).hasMVar
  unless applicable do return none
  discard <| withReducible (isDefEq arrow.getAppArgs[2]! source)
  return some (← instantiateMVars (mkAppN constant parameters),
    ← instantiateMVars arrow.getAppArgs[3]!)

/-- A registered map into the set `target`, at the parameters that reducible unification of its
target with `target` determines, with its source set. -/
private def mapInto? (declaration : Name) (target : Expr) : MetaM (Option (Expr × Expr)) := do
  discard <| checkedDeclaration declaration
  let constant ← mkConstWithFreshMVarLevels declaration
  let (parameters, _, arrow) ← forallMetaTelescopeReducing (← inferType constant)
  let arrow ← whnfR arrow
  unless arrow.isAppOfArity ``Quiver.Hom 4 do return none
  let applicable ← withoutModifyingState do
    unless ← withReducible (isDefEq arrow.getAppArgs[3]! target) do return false
    return !(← instantiateMVars (mkAppN constant parameters)).hasMVar
  unless applicable do return none
  discard <| withReducible (isDefEq arrow.getAppArgs[3]! target)
  return some (← instantiateMVars (mkAppN constant parameters),
    ← instantiateMVars arrow.getAppArgs[2]!)

/-- Every chain of registered inclusions out of the set `current`, as the maps along it with the
set it ends in. A visited object is not entered again, so each chain is a simple path. -/
private partial def inclusionChains (state : SemanticState) (current : Expr)
    (visited : List String) : TermElabM (Array (Array Expr × Expr)) := do
  let mut found := #[(#[], current)]
  let some (entry, _) ← registeredObjectAt? (← sourceRegisteredForm current) | return found
  if visited.contains entry.id.raw then return found
  for inclusion in state.inclusions do
    unless inclusion.sub == entry.id do continue
    let some (arrow, next) ← mapFrom? inclusion.declaration current | continue
    for (maps, last) in ← inclusionChains state next (entry.id.raw :: visited) do
      found := found.push (#[arrow] ++ maps, last)
  return found

/-- The element `value` of a named set read in the named set `target`, through the registered
inclusions (`ℕ ⊆ ℤ`) and the target's registered constants (`R ↪ R[x]`): `none` when no chain
of these maps leads there. Several chains are a competing reading. Source: InclusionEntry,
ObjectEntry.constants and the original reader's rule for elements of related sets. -/
def sourceCoercion? (value target : Expr) : TermElabM (Option Expr) := do
  let state ← semanticState
  let source ← instantiateMVars (← inferType value)
  let some _ ← registeredObjectAt? (← sourceRegisteredForm source) | return none
  let some (goal, _) ← registeredObjectAt? (← sourceRegisteredForm target) | return none
  let chains ← inclusionChains state source []
  let mut readings := #[]
  for (maps, last) in chains do
    if maps.isEmpty then continue
    if ← withoutModifyingState (isDefEq last target) then readings := readings.push maps
  if let some constants := goal.constants then
    if let some (arrow, coefficients) ← mapInto? constants (← sourceRegisteredForm target) then
      for (maps, last) in chains do
        if ← withoutModifyingState (isDefEq last coefficients) then
          readings := readings.push (maps.push arrow)
  match readings with
  | #[] => return none
  | #[maps] =>
    let mut result := value
    for arrow in maps do
      let function ← sourceSetFunction arrow
      result ← elabAppArgs function #[] #[Arg.expr result] none false false
    return some (← mkExpectedTypeHint result target)
  | _ => throwSemanticAmbiguity "several registered maps read this element in the expected set"

end CasCompiler
