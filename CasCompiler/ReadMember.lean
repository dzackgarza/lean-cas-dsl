module

public import CasCompiler.ReadContext
public import CasCompiler.ReadApplication
public import CasCompiler.SourceMethod
public import CasCompiler.SourceMember
public import CasCompiler.SourceSubset
import CasCompiler.SourceCarrier

public section

namespace CasCompiler

open Lean Meta Elab Term CasCatalogue

namespace SourceReader

/-- The actual producer of a typed member reading, retained for competition and observation. -/
inductive MemberEvidence where
  | projection
  | image
  | method (choice : SourceMemberChoice SourceMethodEvidence)
  | family (row : MorphismEntry) (slot : Nat)
  | property (choice : SourceMemberChoice SourcePropertyEvidence)
  | element (row : MorphismEntry)

private def memberChoice (choice : SourceMemberChoice α) (evidence : MemberEvidence) :
    SourceMemberChoice MemberEvidence :=
  ⟨choice.path, evidence, choice.judgement, choice.nativeState⟩

-- A family was already formed at its complete source parameters. Its additional operands
-- are read once at their declared domains; the result's common final check runs afterward.
private def applyMemberFamily (context : ReadContext) (family : NativeSourceJudgement)
    (arguments : Array (TSyntax `cas_term)) :
    TermElabM (Except MessageData NativeSourceJudgement) := do
  if arguments.isEmpty then return .ok family
  if arguments.size == 1 then
    return ← applicationResultApplicable context family arguments none
  let function ← sourceFunction family
  let hole ← mkFreshExprMVar none
  discard <| elabAppArgs function #[] #[Arg.expr hole] none false false
  let type ← instantiateMVars (← inferType hole)
  let argument ← sourceTupleApplicable arguments type fun source type => do
    match ← context.readExpressionApplicable context.categoryOf source (some type) with
    | .ok value => return .ok value.value
    | .error message => return .error message
  let argument ← match argument with
    | .ok value => pure value
    | .error message => return .error message
  return .ok ⟨← elabAppArgs function #[] #[Arg.expr argument] none false false, none⟩

/-- Resolve the actual candidate states. Discovery uses this same selection boundary,
without rerunning the receiver or its candidate producers. -/
def completeMemberChoices (context : ReadContext) (complete : ReadCompletion)
    (name : String) (arguments : Array (TSyntax `cas_term))
    (considered : Array NativeSourceCategory)
    (choices : Array (SourceMemberChoice MemberEvidence))
    (priorMismatches : Array MessageData := #[]) :
    TermElabM (Except MessageData NativeSourceJudgement) := do
  let original ← saveState
  let mut readings : Array (SourceMemberChoice MemberEvidence) := #[]
  let mut mismatches := priorMismatches
  try
    for choice in choices do
      choice.nativeState.restore
      let applied ← match choice.evidence with
        | .method _ | .family .. => applyMemberFamily context choice.judgement arguments
        | _ => pure (.ok choice.judgement)
      match applied with
      | .error message => mismatches := mismatches.push (← addMessageContext message)
      | .ok value =>
        match ← complete value with
        | .error message => mismatches := mismatches.push (← addMessageContext message)
        | .ok value =>
          let nativeState ← saveState
          readings := readings.push { choice with judgement := value, nativeState }
  catch error =>
    original.restore
    throw error
  original.restore
  let considered := considered ++ choices.filterMap (·.path.receiver.category)
  let preferred : Option (Array (Nat × Route)) ←
    sourceMemberPreference name considered (readings.map (·.path))
  let surviving : Array (SourceMemberChoice MemberEvidence × Option Route) := match preferred with
    | none => readings.map fun choice => (choice, none)
    | some selected => selected.filterMap fun (selection : Nat × Route) =>
        readings[selection.1]?.map fun choice => (choice, some selection.2)
  let some (first, preference) := surviving[0]?
    | if let some message := mismatches[0]? then return .error message
      else throwError "no declared member family accepts this complete selected receiver"
  first.nativeState.restore
  let methods := surviving.filterMap fun (choice, _) =>
    match choice.evidence with | .method original => some original | _ => none
  let properties := surviving.filterMap fun (choice, _) =>
    match choice.evidence with | .property original => some original | _ => none
  let judgement ← if methods.size == surviving.size then
    let result ← retainSourceMethodAgreements methods first.judgement
    checkSourceMemberSelections (surviving.map (·.1))
    pure result
  else if properties.size == surviving.size then
    let result ← retainSourcePropertyAgreements name properties first.judgement
    checkSourceMemberSelections (surviving.map (·.1))
    pure result
  else if surviving.size == 1 then
    pure first.judgement
  else if surviving.all (fun (choice, _) =>
      match choice.evidence with | .family .. => true | _ => false) then
    throwSemanticAmbiguity "several declared member parameters accept this selected receiver"
  else if surviving.all (fun (choice, _) =>
      match choice.evidence with | .element _ => true | _ => false) then
    throwSemanticAmbiguity s!"several registered morphisms {name} accept this element"
  else if surviving.size == 2 && methods.size == 1 && surviving.any (fun (choice, _) =>
      match choice.evidence with | .family .. => true | _ => false) then
    throwSemanticAmbiguity "a method and a member family both accept this selected receiver"
  else
    throwSemanticAmbiguity
      "several declared member readings accept this complete selected receiver"
  return .ok (retainMemberPreference judgement preference)

/-- Notation which explicitly denotes an inherited method (for example cardinality bars)
uses the same completed choices without rereading its already formed receiver. -/
def methodCompleting (context : ReadContext) (complete : ReadCompletion)
    (receiver : NativeSourceJudgement) (name : String) :
    TermElabM (Except MessageData NativeSourceJudgement) := do
  let original ← saveState
  try
    let methods ← sourceMethodChoices receiver name
    if methods.isEmpty then
      throwError "the selected source object has no declared {name} method"
    let result ← completeMemberChoices context complete name #[] receiver.category.toArray
      (methods.map fun choice => memberChoice choice (.method choice))
    if let .error _ := result then original.restore
    return result
  catch error =>
    original.restore
    throw error

/-- The uncompleted readings of an actual receiver. The considered category data
also retain those source routes whose native candidate was rejected. -/
structure MemberCandidates where
  choices : Array (SourceMemberChoice MemberEvidence)
  considered : Array NativeSourceCategory
  mismatches : Array MessageData

/-- Collect the same alternatives for ordinary source reading and discovery.
No receiver is reread and no additional argument is manufactured. -/
def memberChoicesAtReceiver (context : ReadContext)
    (receiver : NativeSourceJudgement) (name : String)
    (arguments : Array (TSyntax `cas_term))
    (readArguments : Option (Expr → TermElabM (Except MessageData Expr))) :
    TermElabM MemberCandidates := do
  let object ← match ← sourceExtent? receiver with
    | some extent => pure extent
    | none => pure receiver
  let baseline ← saveState
  let mut choices : Array (SourceMemberChoice MemberEvidence) := #[]

  if let some value ← context.project receiver name arguments then
    choices := choices.push ⟨⟨receiver, none⟩, .projection, value, ← saveState⟩

  baseline.restore
  if name == "image" && arguments.isEmpty then
    if let some (domain, codomain) ← mapEnds receiver.value then
      let value ← sourceImageOf (← sourcePowerObjectAt codomain) domain receiver.value none
      choices := choices.push ⟨⟨receiver, none⟩, .image, ⟨value, none⟩, ← saveState⟩

  baseline.restore
  let methods ← sourceMethodChoices object name
  choices := choices ++ methods.map fun choice => memberChoice choice (.method choice)

  baseline.restore
  let families ← sourceMemberFamilyChoices object name context.qualification
  choices := choices ++ families.map fun choice =>
    memberChoice choice (.family choice.evidence.1 choice.evidence.2)

  baseline.restore
  if arguments.isEmpty then
    let properties ← sourcePropertyChoices object name
    choices := choices ++ properties.map fun choice => memberChoice choice (.property choice)

  baseline.restore
  let (elements, mismatches) ← sourceElementMemberChoices name (some receiver)
    (fun _ => pure (.ok receiver.value)) readArguments
  choices := choices ++ elements.map fun choice => memberChoice choice (.element choice.evidence)

  baseline.restore
  return ⟨choices, receiver.category.toArray ++ object.category.toArray, mismatches⟩

/-- All actual member kinds compete with their complete native source and route data.
The dispatcher's common completion runs once in each candidate state. C6 then selects
only among the surviving readings, and the exact chosen state is returned without replay. -/
def memberCompleting (context : ReadContext) (complete : ReadCompletion)
    (receiverSource : TSyntax `cas_term) (name : String)
    (arguments : Array (TSyntax `cas_term)) :
    TermElabM (Except MessageData NativeSourceJudgement) := do
  let original ← saveState
  try
    let result ← readMember
    if let .error _ := result then original.restore
    return result
  catch error =>
    original.restore
    throw error
where
  readMember : TermElabM (Except MessageData NativeSourceJudgement) := do
    let readArguments : Option (Expr → TermElabM (Except MessageData Expr)) :=
      if arguments.isEmpty then none else some fun type => do
        if let #[argument] := arguments then
          return (← context.readExpressionApplicable context.categoryOf argument (some type)).map
            (·.value)
        sourceTupleApplicable arguments type fun source type => do
          return (← context.readExpressionApplicable context.categoryOf source (some type)).map
            (·.value)
    -- A numeral has no selected source object until an actual declared element map supplies
    -- its domain. Number-system atoms still name objects and enter the ordinary competition.
    if sourceNumeric receiverSource.raw &&
        !receiverSource.raw.isOfKind ``CasCatalogue.Language.casAtom then
      let (elements, mismatches) ← sourceElementMemberChoices name none
        (fun type => do
          return (← context.readExpressionApplicable context.categoryOf receiverSource
            (some type)).map (·.value)) readArguments
      if elements.isEmpty && mismatches.isEmpty then
        throwError "no registered morphism {name} accepts this numeral"
      return ← completeMemberChoices context complete name arguments #[]
        (elements.map fun choice => memberChoice choice (.element choice.evidence)) mismatches

    let receiver ← context.readExpression context.categoryOf receiverSource none
    let candidates ← memberChoicesAtReceiver context receiver name arguments readArguments
    completeMemberChoices context complete name arguments candidates.considered
      candidates.choices candidates.mismatches

/-- Compatibility entrance for a rule which leaves final completion to its caller. -/
def member (context : ReadContext) (receiver : TSyntax `cas_term) (name : String)
    (arguments : Array (TSyntax `cas_term)) : TermElabM NativeSourceJudgement := do
  match ← memberCompleting context (fun value => pure (.ok value)) receiver name arguments with
  | .ok value => pure value
  | .error message => throwError message

end SourceReader

end CasCompiler
