module

public import CasCompiler.SourceRing
public import CasCompiler.SourceTypeOrigin
public import CasCompiler.SourceProof
public import CasCatalogue.Evaluation
public import CasContract.Failure

public section

namespace CasCompiler

open Lean Meta Elab Term CasCatalogue


def sourceExplicitArguments (expression : Expr) : MetaM (Array Expr) := do
  let arguments := expression.getAppArgs
  let info ← getFunInfoNArgs expression.getAppFn arguments.size
  return (arguments.zip (info.paramInfo.map (·.isExplicit))).filterMap fun (argument, explicit) =>
    if explicit then some argument else none



def sourceRegisteredForm (type : Expr) : SourceReadM Expr := do
  if (← SourceReadM.selection? type).isSome then return type
  let mut found : Array (ObjectEntry × Expr) := #[]
  for entry in (← semanticState).objects do
    discard <| checkedDeclaration entry.declaration
    let family ← mkConstWithFreshMVarLevels entry.declaration
    let (parameters, _, _) ← forallMetaTelescopeReducing (← inferType family)
    let object := mkAppN family parameters
    let applicable ← liftM (m := MetaM) <| withoutModifyingState do
      unless ← withReducible (isDefEq object type) do return false
      return !(← instantiateMVars object).hasMVar
    if applicable then
      discard <| liftM (m := MetaM) <| withReducible (isDefEq object type)
      let object ← liftM (m := MetaM) <| instantiateMVars object
      found := found.push (entry, object)
  match found with
  | #[(entry, object)] =>
    let #[category] := (← semanticState).categories.filter (·.id == entry.category)
      | liftM (m := TermElabM) <| throwError "the source domain lost its original registered category"
    SourceReadM.select (← sourceReferenceAt (.named (.registered (.inl entry) category)) object object)
  | _ => return type




def sourceAdmissionDomain? (type : Expr) : SourceReadM (Option ObjectEntry) := do
  let state ← semanticState
  let (_, declared) ← registeredSourceDomain type
  if !declared.isEmpty then
    let #[entry] := declared
      | liftM (m := TermElabM) <| throwSemanticAmbiguity
          "several registered objects declare this admission domain"
    return if entry.admission.isSome then some entry else none
  if (← SourceReadM.selection? type).isSome then return none
  let mut found := #[]
  for entry in state.objects do
    unless entry.admission.isSome do continue
    discard <| checkedDeclaration entry.declaration
    let family ← mkConstWithFreshMVarLevels entry.declaration
    let (parameters, _, _) ← forallMetaTelescopeReducing (← inferType family)
    let applicable ← liftM (m := MetaM) <| withoutModifyingState <| withReducible <|
      isDefEq (mkAppN family parameters) type
    if applicable then found := found.push entry
  match found with
  | #[] => return none
  | #[entry] => return some entry
  | _ =>
    liftM (m := TermElabM) <|
      throwSemanticAmbiguity "several admitted subobjects have this carrier"




private def establish (entry : ObjectEntry) (obligation : Expr) : TermElabM Expr := do
  let some evidence := entry.evidence
    | throwStratum .invalid m!"{entry.name} registers no evidence for its admission"
  let closed ← zetaReduce (← instantiateMVars obligation)
  if closed.hasFVar || closed.hasMVar then
    throwStratum .invalid
      m!"the hypothesis {closed} of {entry.name} is about a value that is not closed"

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


    return ← mkExpectedTypeHint term obligation







def sourceAdmissionApplicable (entry : ObjectEntry) (target : Expr)
    (read : Expr → SourceReadM (Except MessageData Expr)) :
    SourceReadM (Except MessageData Expr) := do
  let some admission := entry.admission
    | liftM (m := TermElabM) <| throwStratum .invalid m!"{entry.name} registers no admission"
  discard <| checkedDeclaration admission
  let previous ← liftM (m := MetaM) getMCtx
  let constant ← mkConstWithFreshMVarLevels admission
  let (arguments, infos, type) ← forallMetaTelescopeReducing (← inferType constant)
  let type ← whnfR type
  unless type.isAppOfArity ``Quiver.Hom 4 do
    liftM (m := TermElabM) <| throwError "the admission of {entry.name} is not a point map"
  let explicit := (List.range arguments.size).toArray.filter (infos[·]!.isExplicit)
  let some element := explicit.find? fun index =>
      (type.findMVar? (· == arguments[index]!.mvarId!)).isNone
    | liftM (m := TermElabM) <| throwError "the admission of {entry.name} takes no value"
  let mut retainedArguments : Array (Option Expr) := Array.replicate arguments.size none
  let (original, references) ← registeredSourceDomain target
  if !references.isEmpty then
    let #[selected] := references
      | liftM (m := TermElabM) <| throwStratum .invalid m!"the admission of {entry.name} has ambiguous selected objects"
    unless reprStr selected == reprStr entry do
      liftM (m := TermElabM) <| throwStratum .invalid m!"the admission of {entry.name} has another selected object"
  if !references.isEmpty || original.getAppFn.isConstOf entry.declaration then



    let some retained ← alignSourceArguments? entry.declaration arguments type.getAppArgs[3]!
        original
      | liftM (m := TermElabM) <| throwStratum .invalid m!"the admission of {entry.name} has different original target parameters"
    retainedArguments := retained
  unless ← liftM (m := MetaM) <| withReducible (isDefEq type.getAppArgs[3]! original) do
    liftM (m := TermElabM) <| throwStratum .invalid m!"the admission of {entry.name} does not land in the selected domain"



  let parameterPrefix ← liftM (m := MetaM) <| ((arguments.take element).mapIdx fun index argument =>
    retainedArguments[index]!.getD argument).mapM instantiateMVars
  let .forallE _ dataType _ _ ← whnfR (← inferType (mkAppN constant parameterPrefix))
    | liftM (m := TermElabM) <| throwError "the admission of {entry.name} lost its declared datum binder"
  let dataType ← liftM (m := MetaM) <| instantiateMVars dataType


  let current ← liftM (m := MetaM) getMCtx
  let owned := current.decls.foldl (fun result identity _ =>
    if previous.decls.contains identity then result else result.push identity) #[]
  let datum ← withSynthesizeApplicableScoped <| read dataType
  let read ← match datum with
    | .ok value => liftM (m := MetaM) <| instantiateMVars value
    | .error message => return .error message



  extendSourceApplicationScope owned
  unless ← isDefEq arguments[element]! read do
    liftM (m := TermElabM) <| throwStratum .invalid m!"the value is not in the set that {entry.name} is included in"
  for argument in arguments, info in infos do
    if info.isInstImplicit && (← liftM (m := MetaM) <| instantiateMVars argument).isMVar then
      let some instanceValue ← synthInstance? (← inferType argument)
        | liftM (m := TermElabM) <| throwError "the admission of {entry.name} lacks its declared instance"
      discard <| isDefEq argument instanceValue
  for index in explicit.filter (element < ·) do
    let obligation ← liftM (m := MetaM) <| instantiateMVars (← inferType arguments[index]!)
    let proof ← SourceReadM.prove obligation fun original _ => establish entry original
    extendSourceApplicationScope owned
    unless ← isDefEq arguments[index]! proof do
      liftM (m := TermElabM) <| throwStratum .invalid m!"the evidence of {entry.name} does not apply"
  let constant ← liftM (m := MetaM) <| instantiateMVars constant
  let mut arguments ← liftM (m := MetaM) <| (arguments.set! element read).mapM instantiateMVars


  for original in retainedArguments, index in [:retainedArguments.size] do
    if let some original := original then
      arguments := arguments.set! index (← liftM (m := MetaM) <| instantiateMVars original)
  let admitted := mkAppN constant arguments
  if admitted.hasMVar || admitted.hasLevelMVar then
    liftM (m := TermElabM) <| throwStratum .invalid m!"the parameters or evidence of {entry.name} are not determined"



  let family ← liftM (m := TermElabM) <| forallTelescope (← inferType constant) fun parameters _ => do
    let value ← sourcePointValueSelection (mkAppN constant parameters) none
    mkLambdaFVars parameters value.value (usedOnly := false) (usedLetOnly := false)
  let value := mkAppN family arguments
  let scope ← get
  let agrees ← scope.context.withOriginalSources #[← inferType value, target] fun original =>
    isDefEq original[0]! original[1]!
  unless agrees do
    liftM (m := TermElabM) <| throwStratum .invalid m!"the admitted point is not in the selected domain of {entry.name}"
  let selected ← retainSourcePoint admitted {
    value
    admission := some ⟨entry, family, arguments, element⟩ }
  return .ok (← SourceReadM.select selected (some target))




def sourceAdmission (entry : ObjectEntry) (target : Expr) (read : Expr → SourceReadM Expr) :
    SourceReadM Expr := do
  let admitted ← sourceAdmissionApplicable entry target fun type => do
    return .ok (← read type)
  match admitted with
  | .ok value => pure value
  | .error message => liftM (m := TermElabM) <| throwStratum .invalid message








def sourceBinder (token : String)
    (arguments : Array (Expr → SourceReadM (Except MessageData Expr)))
    (bound : Name) (readBody : Expr → SourceReadM Expr) : SourceReadM Expr := do
  let state ← semanticState
  let rows := state.binders.filter (·.token == token)
  let attempt : BinderEntry → SourceReadM (Except MessageData Expr) := fun row => do
    discard <| checkedDeclaration row.operation
    discard <| checkedDeclaration row.domain
    let previous ← liftM (m := MetaM) getMCtx
    let operation ← mkConstWithFreshMVarLevels row.operation
    let (parameters, infos, arrow) ← forallMetaTelescopeReducing (← inferType operation)
    let explicit := (parameters.zip infos).filter (·.2.isExplicit) |>.map (·.1)
    let current ← liftM (m := MetaM) getMCtx
    let owned := current.decls.foldl (fun result identity _ =>
      if previous.decls.contains identity then result else result.push identity) #[]
    unless arguments.size ≤ explicit.size do
      return .error m!"the binder takes fewer arguments"
    let rec visitArguments (remaining : List Expr) (index : Nat) :
        SourceReadM (Except MessageData Unit) := do
      match remaining with
      | [] => return .ok ()
      | parameter :: remaining => do
        let some read := arguments[index]?
          | liftM (m := TermElabM) <| throwError "the binder lost its original argument position"
        let type ← whnfR (← liftM (m := MetaM) <| instantiateMVars (← inferType parameter))
        let value : Except MessageData Expr ← if type.isAppOfArity ``Quiver.Hom 4 then do
            let expected ← liftM (m := MetaM) <| instantiateMVars type.getAppArgs[3]!
            let datum ← read expected
            let element ← match datum with
              | .ok value => pure value
              | .error message => return .error message
            unless ← isDefEq (← inferType element) expected do
              return .error m!"the binder argument has another type"
            let constant ← liftM (m := MetaM) <| withLocalDeclD `point type.getAppArgs[2]! fun point =>
              mkLambdaFVars #[point] element
            pure (.ok (← elabAppArgs (← mkConstWithFreshMVarLevels ``TypeCat.ofHom)
              #[] #[Arg.expr constant] (some type) false false))
          else read type
        let value ← match value with
          | .ok value => pure value
          | .error message => return .error message
        unless ← isDefEq (← inferType value) type do
          return .error m!"the binder argument has another type"
        extendSourceApplicationScope owned
        unless ← isDefEq parameter value do
          return .error m!"the binder argument has another type"
        visitArguments remaining (index + 1)
    match ← visitArguments
        (explicit.extract (explicit.size - arguments.size) explicit.size).toList 0 with
    | .ok () => pure ()
    | .error message => return .error message
    let domainConstant ← mkConstWithFreshMVarLevels row.domain

    let domain ← sourceRegisteredForm (← liftM (m := MetaM) <| instantiateMVars (mkAppN domainConstant parameters))
    let arrow ← whnfR arrow
    unless arrow.isAppOfArity ``Quiver.Hom 4 do liftM (m := TermElabM) <| throwError "the binder operation is not a map"
    let some entry ← sourceAdmissionDomain? (← liftM (m := MetaM) <| instantiateMVars arrow.getAppArgs[2]!)
      | liftM (m := TermElabM) <| throwError "the binder operation does not act on an admitted object of maps"
    let admitted ← sourceAdmissionApplicable entry (← liftM (m := MetaM) <| instantiateMVars arrow.getAppArgs[2]!) fun base => do
      let function ← SourceReadM.withLambda bound domain .default readBody
      let scope ← get
      let agrees ← scope.context.withOriginalSources #[← inferType function, base] fun original =>
        isDefEq original[0]! original[1]!
      unless agrees do
        return .error m!"the binder body is not a map of the operation's source"
      return .ok (← SourceReadM.select { value := function } (some base))
    let point ← match admitted with
      | .ok value => pure value
      | .error message => return .error message
    let applied ← liftM (m := MetaM) <| instantiateMVars (mkAppN operation parameters)
    if applied.hasMVar || applied.hasLevelMVar then
      liftM (m := TermElabM) <| throwUnsupportedSource m!"the binder {token} has parameters its arguments do not determine"
    let selected ← SourceReadM.select (← sourceReferenceAt (.binder row) applied applied)
    let function ← sourceSetFunction selected
    return .ok (← elabAppArgs function #[] #[Arg.expr point] none false false)
  let require : BinderEntry → SourceReadM Expr := fun row => do
    match ← attempt row with
    | .ok value => pure value
    | .error message => liftM (m := TermElabM) <| throwStratum .invalid message
  if let #[row] := rows then return ← require row
  match ← SourceReadM.chooseApplicable (rows.map attempt)
      m!"no registered binder {token} reads these arguments and body"
      m!"several registered binders {token} read this statement" with
  | .ok value => return value
  | .error message => liftM (m := TermElabM) <| throwStratum .invalid message



private def registeredObjectAt? (type : Expr) : SourceReadM (Option (ObjectEntry × Expr)) := do
  let (original, entries) ← registeredSourceDomain type
  if (← SourceReadM.selection? type).isSome then
    match entries with
    | #[entry] => return if entry.refines.isNone then some (entry, original) else none
    | _ => return none
  let mut found := #[]
  for entry in (← semanticState).objects do
    if entry.refines.isSome then continue
    discard <| checkedDeclaration entry.declaration
    let family ← mkConstWithFreshMVarLevels entry.declaration
    let (parameters, _, _) ← forallMetaTelescopeReducing (← inferType family)
    let object := mkAppN family parameters
    let applicable ← liftM (m := MetaM) <| withoutModifyingState do
      unless ← withReducible (isDefEq object type) do return false
      return !(← instantiateMVars object).hasMVar
    if applicable then
      discard <| liftM (m := MetaM) <| withReducible (isDefEq object type)
      found := found.push (entry, ← liftM (m := MetaM) <| instantiateMVars object)
  match found with
  | #[unique] => return some unique
  | _ => return none



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



private partial def inclusionChains (state : SemanticState) (current : Expr)
    (visited : List String) : SourceReadM (Array (Array Expr × Expr)) := do
  let mut found := #[(#[], current)]
  let some (entry, original) ← registeredObjectAt? (← sourceRegisteredForm current) | return found
  if visited.contains entry.id.raw then return found
  for inclusion in state.inclusions do
    unless inclusion.sub == entry.id do continue
    let some (arrow, next) ← mapFrom? inclusion.declaration original | continue
    for (maps, last) in ← inclusionChains state next (entry.id.raw :: visited) do
      found := found.push (#[arrow] ++ maps, last)
  return found





def sourceCoercion? (value target : Expr) : SourceReadM (Option Expr) := do
  let state ← semanticState
  let source ← liftM (m := MetaM) <| instantiateMVars (← inferType value)
  let some _ ← registeredObjectAt? (← sourceRegisteredForm source) | return none
  let some (goal, originalTarget) ← registeredObjectAt? (← sourceRegisteredForm target) | return none
  let chains ← inclusionChains state source []
  let mut readings := #[]
  for (maps, last) in chains do
    if maps.isEmpty then continue
    if ← liftM (m := MetaM) <| withoutModifyingState (isDefEq last originalTarget) then readings := readings.push maps
  if let some constants := goal.constants then
    if let some (arrow, coefficients) ← mapInto? constants originalTarget then
      for (maps, last) in chains do
        if ← liftM (m := MetaM) <| withoutModifyingState (isDefEq last coefficients) then
          readings := readings.push (maps.push arrow)
  match readings with
  | #[] => return none
  | #[maps] =>
    let mut result := value
    for arrow in maps do
      let type ← whnfR (← inferType arrow)
      unless type.isAppOfArity ``Quiver.Hom 4 do
        liftM (m := TermElabM) <| throwError "the selected inclusion lost its original native map"
      let selected := (← SourceReadM.selection? result).getD { value := result }
      result ← SourceReadM.select { selected with value := result } (some type.getAppArgs[2]!)
      let function ← sourceSetFunction arrow
      result ← elabAppArgs function #[] #[Arg.expr result] none false false
    return some (← SourceReadM.select { value := result } (some target))
  | _ => liftM (m := TermElabM) <| throwSemanticAmbiguity "several registered maps read this element in the expected set"




def sourceCommonDomain (types : Array Expr) : SourceReadM (Option Expr) := do
  let mut distinct : Array Expr := #[]
  for type in types do
    unless ← liftM (m := MetaM) <| distinct.anyM fun other =>
        withoutModifyingState (isDefEq other type) do
      distinct := distinct.push type
  if distinct.size ≤ 1 then return distinct[0]?
  let mut common := #[]
  for candidate in distinct do
    let reaches ← distinct.allM fun other => do
      if ← liftM (m := MetaM) <| withoutModifyingState (isDefEq other candidate) then return true
      SourceReadM.inspect <| SourceReadM.withBinder `operand other none .default
        (fun _ result => pure result) fun operand => do
          return (← sourceCoercion? operand candidate).isSome
    if reaches then common := common.push candidate
  match common with
  | #[candidate] => return some candidate
  | _ => return distinct[0]?






def sourceIncludedNumeral (target : Expr) (readAt : Expr → SourceReadM (Option Expr)) :
    SourceReadM (Option Expr) := do
  let originalTarget := target
  let target ← sourceRegisteredForm target
  let (nativeTarget, _) ← registeredSourceDomain target
  let mut readings := #[]
  for inclusion in (← semanticState).inclusions do
    let some (arrow, source) ← mapInto? inclusion.declaration nativeTarget | continue
    let applicable ← SourceReadM.inspect do return (← readAt source).isSome
    if applicable then readings := readings.push (arrow, source)
  match readings with
  | #[] => return none
  | #[(arrow, source)] =>
    let function ← sourceSetFunction arrow
    let some numeral ← readAt source
      | liftM (m := TermElabM) <| throwError "the selected inclusion lost its admitted source numeral"
    let value ← elabAppArgs function #[] #[Arg.expr numeral] none false false
    return some (← SourceReadM.select { value } (some originalTarget))
  | _ => liftM (m := TermElabM) <| throwSemanticAmbiguity "several registered inclusions read this numeral"

end CasCompiler
