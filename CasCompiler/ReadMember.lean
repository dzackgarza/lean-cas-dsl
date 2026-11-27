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


inductive MemberEvidence where
  | projection
  | image
  | method (choice : SourceMemberChoice SourceMethodEvidence)
  | family (row : MorphismEntry) (slot : Nat)
  | property (choice : SourceMemberChoice SourcePropertyEvidence)
  | element (row : MorphismEntry)

private def memberChoice (choice : SourceMemberChoice α) (evidence : MemberEvidence) :
    SourceMemberChoice MemberEvidence :=
  { path := choice.path
    evidence := evidence
    judgement := choice.judgement
    nativeState := choice.nativeState
    sourceScope := choice.sourceScope
    localContext := choice.localContext
    localInstances := choice.localInstances }



private def applyMemberFamily (context : ReadContext) (family : NativeSourceJudgement)
    (arguments : Array (TSyntax `cas_term)) :
    SourceReadM (Except MessageData NativeSourceJudgement) := do
  if arguments.isEmpty then return .ok family
  if arguments.size == 1 then
    return ← applicationResultApplicable context family arguments none
  let function ← sourceFunction family
  let applied ← elabSourceApplicationApplicableScoped function #[Syntax.missing] none
    fun _ type => sourceTupleApplicable arguments type fun source type => do
      match ← context.readExpressionApplicable context.categoryOf source (some type) with
      | .ok value => return .ok value.value
      | .error message => return .error message
  match applied with
  | .ok (value, _) => return .ok ⟨value, none⟩
  | .error message => return .error message



def completeMemberChoices (context : ReadContext) (complete : ReadCompletion)
    (name : String) (arguments : Array (TSyntax `cas_term))
    (considered : Array NativeSourceCategory)
    (choices : Array (SourceMemberChoice MemberEvidence))
    (priorMismatches : Array MessageData := #[]) :
    SourceReadM (Except MessageData NativeSourceJudgement) := do
  let (readings, completedMismatches) ← SourceMemberChoice.collectApplicable <|
    choices.map fun choice => choice.withScope do
      let applied ← match choice.evidence with
        | .method _ | .family .. => applyMemberFamily context choice.judgement arguments
        | _ => pure (.ok choice.judgement)
      let value ← match applied with
        | .error message => return .error message
        | .ok value => pure value
      match ← complete value with
      | .error message => return .error message
      | .ok value =>
        return .ok (some (← SourceMemberChoice.capture choice.path choice.evidence value))
  let mismatches := priorMismatches ++ completedMismatches
  let considered := considered ++ choices.filterMap (·.path.receiver.category)
  let preferred ← sourceMemberPreference name considered (readings.map (·.path))
  let surviving : Array (SourceMemberChoice MemberEvidence × Option Route) := match preferred with
    | none => readings.map fun choice => (choice, none)
    | some selected => selected.filterMap fun (selection : Nat × Route) =>
        readings[selection.1]?.map fun choice => (choice, some selection.2)
  let some (first, preference) := surviving[0]?
    | if let some message := mismatches[0]? then return .error message
      else liftM (m := TermElabM) <|
        throwError (MessageData.tagged `CasCompiler.SourceReader.memberReceiver
          m!"no declared member family accepts this complete selected receiver")
  first.withScope do
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
      liftM (m := TermElabM) <|
        throwSemanticAmbiguity "several declared member parameters accept this selected receiver"
    else if surviving.all (fun (choice, _) =>
        match choice.evidence with | .element _ => true | _ => false) then
      liftM (m := TermElabM) <|
        throwSemanticAmbiguity s!"several registered morphisms {name} accept this element"
    else if surviving.size == 2 && methods.size == 1 && surviving.any (fun (choice, _) =>
        match choice.evidence with | .family .. => true | _ => false) then
      liftM (m := TermElabM) <|
        throwSemanticAmbiguity "a method and a member family both accept this selected receiver"
    else
      liftM (m := TermElabM) <|
        throwSemanticAmbiguity
          "several declared member readings accept this complete selected receiver"
    return .ok (← retainMemberPreference judgement preference)



def methodCompleting (context : ReadContext) (complete : ReadCompletion)
    (receiver : NativeSourceJudgement) (name : String) :
    SourceReadM (Except MessageData NativeSourceJudgement) := do
  let methods ← sourceMethodChoices receiver name
  if methods.isEmpty then
    liftM (m := TermElabM) <| throwError "the selected source object has no declared {name} method"
  completeMemberChoices context complete name #[] receiver.category.toArray
    (methods.map fun choice => memberChoice choice (.method choice))



structure MemberCandidates where
  choices : Array (SourceMemberChoice MemberEvidence)
  considered : Array NativeSourceCategory
  mismatches : Array MessageData



def memberChoicesAtReceiver (context : ReadContext)
    (receiver : NativeSourceJudgement) (name : String)
    (arguments : Array (TSyntax `cas_term))
    (readArguments : Option (Expr → SourceReadM (Except MessageData Expr))) :
    SourceReadM MemberCandidates := do
  let object ← match ← sourceExtent? receiver with
    | some extent => pure extent
    | none => pure receiver
  let direct : Array (SourceReadM
      (Except MessageData (Option (SourceMemberChoice MemberEvidence)))) := #[
    do
      let some value ← context.project receiver name arguments | return .ok none
      return .ok (some (← SourceMemberChoice.capture ⟨receiver, none⟩ .projection value)),
    do
      unless name == "image" && arguments.isEmpty do return .ok none
      let some (domain, codomain) ← mapEnds receiver.value | return .ok none
      let value ← sourceImageOf (← sourcePowerObjectAt codomain) domain receiver.value none
      return .ok (some (← SourceMemberChoice.capture ⟨receiver, none⟩ .image ⟨value, none⟩))]
  let (direct, _) ← SourceMemberChoice.collectApplicable direct
  let methods ← sourceMethodChoices object name
  let families ← sourceMemberFamilyChoices object name context.qualification
  let properties ← if arguments.isEmpty then sourcePropertyChoices object name else pure #[]
  let (elements, mismatches) ← sourceElementMemberChoices name (some receiver)
    (fun _ => pure (.ok receiver.value)) readArguments
  let choices := direct ++
    methods.map (fun choice => memberChoice choice (.method choice)) ++
    families.map (fun choice => memberChoice choice (.family choice.evidence.1 choice.evidence.2)) ++
    properties.map (fun choice => memberChoice choice (.property choice)) ++
    elements.map (fun choice => memberChoice choice (.element choice.evidence))
  return ⟨choices, receiver.category.toArray ++ object.category.toArray, mismatches⟩




def memberCompleting (context : ReadContext) (complete : ReadCompletion)
    (receiverSource : TSyntax `cas_term) (name : String)
    (arguments : Array (TSyntax `cas_term)) :
    SourceReadM (Except MessageData NativeSourceJudgement) := do
  let readArguments : Option (Expr → SourceReadM (Except MessageData Expr)) :=
    if arguments.isEmpty then none else some fun type => do
      if let #[argument] := arguments then
        return (← context.readExpressionApplicable context.categoryOf argument (some type)).map
          (·.value)
      sourceTupleApplicable arguments type fun source type => do
        return (← context.readExpressionApplicable context.categoryOf source (some type)).map
          (·.value)


  if sourceNumeric receiverSource.raw &&
      !receiverSource.raw.isOfKind ``CasCatalogue.Language.casAtom then
    let (elements, mismatches) ← sourceElementMemberChoices name none
      (fun type => do
        return (← context.readExpressionApplicable context.categoryOf receiverSource
          (some type)).map (·.value)) readArguments
    if elements.isEmpty && mismatches.isEmpty then
      liftM (m := TermElabM) <| throwError "no registered morphism {name} accepts this numeral"
    return ← completeMemberChoices context complete name arguments #[]
      (elements.map fun choice => memberChoice choice (.element choice.evidence)) mismatches

  let receiver ← context.readExpression context.categoryOf receiverSource none
  let candidates ← memberChoicesAtReceiver context receiver name arguments readArguments
  completeMemberChoices context complete name arguments candidates.considered
    candidates.choices candidates.mismatches


def member (context : ReadContext) (receiver : TSyntax `cas_term) (name : String)
  (arguments : Array (TSyntax `cas_term)) : SourceReadM NativeSourceJudgement := do
  match ← memberCompleting context
      (checkReadJudgementApplicable { context with qualification := none, expectedCategory := none })
      receiver name arguments with
  | .ok value => pure value
  | .error message => liftM (m := TermElabM) <| throwError message

end SourceReader

end CasCompiler
