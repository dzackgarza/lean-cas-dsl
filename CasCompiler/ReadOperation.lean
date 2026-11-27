module

public import CasCompiler.ReadContext
public import CasCompiler.SourceOperation
public import CasCompiler.SourceTuple
public import CasCompiler.SourceRing
public import CasCompiler.SourceAdmission
public import CasCompiler.SourceMember
import CasCompiler.SourceCarrier

public section

namespace CasCompiler

open Lean Meta Elab Term

namespace SourceReader




private def retainedOperandApplicable (reference : Syntax) (value expected : Expr) :
    SourceReadM (Except MessageData Expr) := SourceReadM.withRef reference do
  let actual ← inferType value
  let nativeFits ← withoutModifyingState (isDefEq actual expected)
  let scope ← get
  let sourceFits ← if nativeFits then pure true else
    scope.context.withOriginalSources #[actual, expected] fun original =>
      withoutModifyingState (isDefEq original[0]! original[1]!)
  unless sourceFits do
    if let some mapped ← sourceCoercion? value expected then return .ok mapped
  match ← registeredSourceDomainsApplicable actual expected with
  | .error message => return .error message
  | .ok () => pure ()
  unless sourceFits do
    return .error m!"the retained operand has a different declared domain"
  if nativeFits then
    unless ← isDefEq actual expected do
      return .error m!"the retained operand has a different declared domain"
    return .ok value
  let selected := (← SourceReadM.selection? value).getD { value }
  return .ok (← SourceReadM.select { selected with value } (some expected))

private def elementOperationCore (context : ReadContext) :
    String → Array (TSyntax `cas_term) → Array (TSyntax `cas_term) → Array (Option Expr) → Option Expr → ExceptT MessageData SourceReadM NativeSourceJudgement :=
  let readExpression := @ReadContext.readExpression context
  let categoryOf := context.categoryOf
  let expected := context.expected
  fun (name : String) (operands : Array (TSyntax `cas_term))
      (numerals : Array (TSyntax `cas_term)) (known : Array (Option Expr))
      (domainHint : Option Expr) => do
    let phase : String → List (String × Json) → SourceReadM Unit := fun event details => do
      try
        let scope ← get
        let heartbeats ← liftM (m := BaseIO) IO.getNumHeartbeats
        liftM (m := CoreM) <| CasTools.Diagnostics.emit event (Json.mkObj ([
          ("operation", toJson name),
          ("heartbeats", toJson heartbeats),
          ("contextBindings", toJson scope.context.bindings.size),
          ("formals", toJson scope.formals.size),
          ("operands", toJson operands.size),
          ("numerals", toJson numerals.size)] ++ details))
      catch _ => pure ()
    liftM <| phase "source.operation.read.started" []
    let mut retained : Array (Option Expr) := Array.replicate operands.size none
    let mut hints : Array Expr := #[]
    for operand in operands, index in [:operands.size] do
      if let some (some value) := known[index]? then
        retained := retained.set! index (some value)
        hints := hints.push (← inferType value)
        continue
      if let `(cas_term| $identifier:ident) := operand then
        if ((← liftM (m := MetaM) getLCtx).findFromUserName? identifier.getId).isSome then
          let value ← readExpression categoryOf operand none
          retained := retained.set! index (some value.value)
          hints := hints.push (← inferType value.value)
    let contextual ← liftM (m := MetaM) <| expected.mapM instantiateMVars
    let contextual := contextual.filter (! ·.headBeta.consumeMData.getAppFn.isMVar)
    let inputContext := contextual.filter (! ·.headBeta.consumeMData.isSort)


    let domain ← match domainHint.or (← sourceCommonDomain hints) |>.or inputContext with
      | some type => pure type
      | none => do
        let mut domain := hints[0]?
        if domain.isNone then
          for operand in operands, index in [:operands.size] do
            if let `(cas_term| $_:num) := operand then continue
            let value ← readExpression categoryOf operand none
            retained := retained.set! index (some value.value)
            hints := hints.push (← inferType value.value)
          domain ← sourceCommonDomain hints
        if let some selectedDomain := domain then pure selectedDomain
        else do
          let defaults := (← CasCatalogue.semanticState).objects.filter
            (·.notations.contains "literal.integral.domain")
          let #[entry] := defaults
            | liftM (m := TermElabM) <| CasCatalogue.throwSemanticAmbiguity "the source operation requires its scalar domain"
          discard <| checkedDeclaration entry.declaration
          mkConstWithFreshMVarLevels entry.declaration
    liftM <| phase "source.operation.domain.finished" [
      ("hints", toJson hints.size), ("hasDomainHint", toJson domainHint.isSome),
      ("hasContextualType", toJson contextual.isSome)]
    let originalOperand := retained
    let operationHints := if domainHint.isSome then #[domain] else hints
    let operation ← sourceOperation categoryOf name domain contextual operationHints operands.size
      (numerals.map fun numeral type => do
        return (← readExpression categoryOf numeral (some type)).value)
    let function ← sourceSetFunction operation.value
    let argument ← mkFreshExprMVar none
    discard <| elabAppArgs function #[] #[Arg.expr argument] none false false
    let cursor : IO.Ref Nat ← liftM (m := IO) (IO.mkRef 0)
    let readOperand : TSyntax `cas_term → Expr → ExceptT MessageData SourceReadM Expr := fun source type => do
      let index : Nat ← liftM (m := IO) cursor.get
      liftM (m := IO) (cursor.set (index + 1))
      let some transport := operation.inputTransports[index]?
        | liftM (m := TermElabM) <| throwError "the source operation lost its declared operand position"
      let read : Expr → ExceptT MessageData SourceReadM Expr := fun expected => do
        if let some (some value) := originalOperand[index]? then
          return ← ExceptT.mk <| retainedOperandApplicable source value expected
        let result ← ExceptT.mk <|
          context.readExpressionApplicable categoryOf source (some expected)
        return result.value
      let value ← if transport then do
          let some comparison := operation.comparison
            | liftM (m := TermElabM) <| throwError "the source operand lost its supplied comparison"
          let iso ← whnfR (← inferType comparison)
          let value ← read iso.getAppArgs[3]!
          let inverse ← mkAppM ``CategoryTheory.Iso.inv #[comparison]
          let inverse ← sourceSetFunction inverse
          liftM <| elabRetainedSourceApplication inverse #[value] (some type)
        else if operation.inputDomains[index]?.getD false then read domain
        else read type
      if ← withoutModifyingState (isDefEq (← inferType value) type) then return value



      let selected := (← SourceReadM.selection? value).getD { value }
      liftM <| SourceReadM.select { selected with value } (some type)
    let type ← liftM (m := MetaM) <| instantiateMVars (← inferType argument)
    let value ← if operands.size == 1 then do
        let some operand := operands[0]?
          | liftM (m := TermElabM) <| throwError "the source operation requires its original operand"
        readOperand operand type
      else ExceptT.mk <| sourceTupleApplicable operands type fun source type =>
        (readOperand source type).run
    let value ← elabAppArgs function #[] #[Arg.expr value] none false false
    let value ← if operation.outputTransport then do
        let some comparison := operation.comparison
          | liftM (m := TermElabM) <| throwError "the source result lost its supplied comparison"
        let forward ← mkAppM ``CategoryTheory.Iso.hom #[comparison]
        let forward ← sourceSetFunction forward
        liftM <| elabRetainedSourceApplication forward #[value] expected
      else if operation.outputDomain then mkExpectedTypeHint value domain
      else pure value
    liftM <| phase "source.operation.read.finished" []
    return (⟨value, none⟩ : NativeSourceJudgement)



def elementOperationApplicable (context : ReadContext)
    (name : String) (operands numerals : Array (TSyntax `cas_term))
    (known : Array (Option Expr)) (domainHint : Option Expr) :
    SourceReadM (Except MessageData NativeSourceJudgement) :=
  (elementOperationCore context name operands numerals known domainHint).run

def elementOperation (context : ReadContext)
    (name : String) (operands numerals : Array (TSyntax `cas_term))
    (known : Array (Option Expr)) (domainHint : Option Expr) :
    SourceReadM NativeSourceJudgement := do
  match ← elementOperationApplicable context name operands numerals known domainHint with
  | .ok value => pure value
  | .error message => liftM (m := TermElabM) <| throwError message

def action (context : ReadContext) :
    TSyntax `cas_term → TSyntax `cas_term → SourceReadM NativeSourceJudgement :=
  let readExpression := @ReadContext.readExpression context
  let categoryOf := context.categoryOf
  let expected := context.expected
  let elementOperation := elementOperation context
  fun (left right : TSyntax `cas_term) => do
    let rightExpected := if sourceNumeric right.raw then expected else none
    let value ← readExpression categoryOf right rightExpected
    elementOperation "•" #[left, right] #[] #[none, some value.value]
      (some (← inferType value.value))




def juxtapose (context : ReadContext) :
    TSyntax `cas_term → TSyntax `cas_term → SourceReadM NativeSourceJudgement :=
  let readExpression := @ReadContext.readExpression context
  let categoryOf := context.categoryOf
  let expected := context.expected
  fun (left right : TSyntax `cas_term) => do
    let rightExpected := if sourceNumeric right.raw then expected else none
    let rightValue ← readExpression categoryOf right rightExpected
    let leftValue ← if sourceNumeric left.raw then pure none
      else pure (some (← readExpression categoryOf left none))
    let names ← sourceJuxtapositionNames categoryOf leftValue rightValue
    let unavailable : MessageData :=
      "no declared juxtaposition reading accepts the original operands"
    let direct : Array (SourceReadM (Except MessageData NativeSourceJudgement)) :=
      leftValue.toArray.flatMap fun originalLeft => #[do
        let pair ← mkAppM ``Prod #[← inferType originalLeft.value, ← inferType rightValue.value]
        let some action ← sourceMorphismFrom? "•" pair | return .error unavailable
        let function ← sourceSetFunction action
        let argument ← mkAppM ``Prod.mk #[originalLeft.value, rightValue.value]
        return .ok ⟨← elabAppArgs function #[] #[Arg.expr argument] none false false, none⟩,
      do
        let result ← sourceDirectApplicationApplicable? originalLeft.value fun domain =>
          retainedOperandApplicable right rightValue.value domain
        match result with
        | .ok (some value) => return .ok ⟨value, none⟩
        | .ok none | .error _ => return .error unavailable]
    let trials := direct ++ names.map fun name => do
        let owner ← if name == "•" then pure (some (← inferType rightValue.value)) else pure none
        elementOperationApplicable context name #[left, right] #[]
          #[leftValue.map (·.value), some rightValue.value] owner
    match ← SourceReadM.chooseApplicable trials unavailable
        m!"juxtaposition has several declared readings of its original operands" with
    | .ok value => return value
    | .error _ =>
      if let some left := leftValue then
        let type ← inferType left.value
        let domains ← sourceOperationDomains categoryOf type none #[type]
        if domains.isEmpty && (left.category.any (·.role == .morphism) ||
            (← whnf type).isForall) then
          liftM (m := TermElabM) <| CasCatalogue.throwUnsupportedSource
            "callable juxtaposition requires its declared action and application comparison"
      liftM (m := TermElabM) <| CasCatalogue.throwStratum .invalid
        "no declared juxtaposition reading accepts the original operands"

def relation (context : ReadContext) :
    String → TSyntax `cas_term → TSyntax `cas_term → SourceReadM NativeSourceJudgement :=
  let readExpression := @ReadContext.readExpression context
  let categoryOf := context.categoryOf
  let elementOperation := elementOperation context
  fun (name : String) (left right : TSyntax `cas_term) => do


    match right with
    | `(cas_term| $operand:cas_term in $domain:cas_term) =>
      let domain ← sourceCarrier (← readExpression categoryOf domain none)
      elementOperation name #[left, operand] #[] #[] (some domain.value)
    | _ => elementOperation name #[left, right] #[] #[] none

end SourceReader

end CasCompiler
