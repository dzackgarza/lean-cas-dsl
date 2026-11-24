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

/-- Reuse an already read operand at its declared operation input. The same registered
coercions and exact-domain checks as ordinary operations apply; only their own explicit
native mismatch is a rejected candidate. The source expression is never read again. -/
private def retainedOperandApplicable (reference : Syntax) (value expected : Expr) :
    TermElabM (Except MessageData Expr) := withRef reference do
  unless ← withoutModifyingState (isDefEq (← inferType value) expected) do
    if let some mapped ← sourceCoercion? value expected then return .ok mapped
  match ← registeredDomainsApplicable (← inferType value) expected with
  | .error message => return .error message
  | .ok () => pure ()
  unless ← isDefEq (← inferType value) expected do
    return .error m!"the retained operand has a different declared domain"
  return .ok value

private def elementOperationCore (context : ReadContext) :
    String → Array (TSyntax `cas_term) → Array (TSyntax `cas_term) → Array (Option Expr) → Option Expr → ExceptT MessageData TermElabM NativeSourceJudgement :=
  let readExpression := @ReadContext.readExpression context
  let categoryOf := context.categoryOf
  let expected := context.expected
  fun (name : String) (operands : Array (TSyntax `cas_term))
      (numerals : Array (TSyntax `cas_term)) (known : Array (Option Expr))
      (domainHint : Option Expr) => do
    let mut retained : Array (Option Expr) := Array.replicate operands.size none
    let mut hints : Array Expr := #[]
    for operand in operands, index in [:operands.size] do
      if let some (some value) := known[index]? then
        retained := retained.set! index (some value)
        hints := hints.push (← inferType value)
        continue
      if let `(cas_term| $identifier:ident) := operand then
        if ((← getLCtx).findFromUserName? identifier.getId).isSome then
          let value ← readExpression categoryOf operand none
          retained := retained.set! index (some value.value)
          hints := hints.push (← inferType value.value)
    let contextual ← expected.mapM instantiateMVars
    let contextual := contextual.filter (! ·.headBeta.consumeMData.getAppFn.isMVar)
    let inputContext := contextual.filter (! ·.headBeta.consumeMData.isSort)
    -- Actual typed operands determine the input domain before the expected result.
    -- Relations land in Ω; that result must not replace their selected operand owner.
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
            | CasCatalogue.throwSemanticAmbiguity "the source operation requires its scalar domain"
          discard <| checkedDeclaration entry.declaration
          mkConstWithFreshMVarLevels entry.declaration
    let originalOperand := retained
    let operationHints := if domainHint.isSome then #[domain] else hints
    let operation ← sourceOperation categoryOf name domain contextual operationHints operands.size
      (numerals.map fun numeral type => do
        return (← readExpression categoryOf numeral (some type)).value)
    let function ← sourceSetFunction operation.value
    let argument ← mkFreshExprMVar none
    discard <| elabAppArgs function #[] #[Arg.expr argument] none false false
    let cursor : IO.Ref Nat ← liftM (m := IO) (IO.mkRef 0)
    let readOperand : TSyntax `cas_term → Expr → ExceptT MessageData TermElabM Expr := fun source type => do
      let index : Nat ← liftM (m := IO) cursor.get
      liftM (m := IO) (cursor.set (index + 1))
      let some transport := operation.inputTransports[index]?
        | throwError "the source operation lost its declared operand position"
      let read : Expr → ExceptT MessageData TermElabM Expr := fun expected => do
        if let some (some value) := originalOperand[index]? then
          return ← ExceptT.mk <| retainedOperandApplicable source value expected
        let result ← ExceptT.mk <|
          context.readExpressionApplicable categoryOf source (some expected)
        return result.value
      if transport then
        let some comparison := operation.comparison
          | throwError "the source operand lost its supplied comparison"
        let iso ← whnfR (← inferType comparison)
        let value ← read iso.getAppArgs[3]!
        let inverse ← mkAppM ``CategoryTheory.Iso.inv #[comparison]
        let inverse ← sourceSetFunction inverse
        elabAppArgs inverse #[] #[Arg.expr value] (some type) false false
      else if operation.inputDomains[index]?.getD false then read domain
      else read type
    let type ← instantiateMVars (← inferType argument)
    let value ← if operands.size == 1 then do
        let some operand := operands[0]?
          | throwError "the source operation requires its original operand"
        readOperand operand type
      else ExceptT.mk <| sourceTupleApplicable operands type fun source type =>
        (readOperand source type).run
    let value ← elabAppArgs function #[] #[Arg.expr value] none false false
    let value ← if operation.outputTransport then do
        let some comparison := operation.comparison
          | throwError "the source result lost its supplied comparison"
        let forward ← mkAppM ``CategoryTheory.Iso.hom #[comparison]
        let forward ← sourceSetFunction forward
        elabAppArgs forward #[] #[Arg.expr value] expected false false
      else if operation.outputDomain then mkExpectedTypeHint value domain
      else pure value
    return (⟨value, none⟩ : NativeSourceJudgement)

/-- Ordinary operation formation with explicit applicability of its own typed operands.
Selected family, evidence, instance and recursive-reader errors remain exceptions. -/
def elementOperationApplicable (context : ReadContext)
    (name : String) (operands numerals : Array (TSyntax `cas_term))
    (known : Array (Option Expr)) (domainHint : Option Expr) :
    TermElabM (Except MessageData NativeSourceJudgement) :=
  (elementOperationCore context name operands numerals known domainHint).run

def elementOperation (context : ReadContext)
    (name : String) (operands numerals : Array (TSyntax `cas_term))
    (known : Array (Option Expr)) (domainHint : Option Expr) :
    TermElabM NativeSourceJudgement := do
  match ← elementOperationApplicable context name operands numerals known domainHint with
  | .ok value => pure value
  | .error message => throwError message

def action (context : ReadContext) :
    TSyntax `cas_term → TSyntax `cas_term → TermElabM NativeSourceJudgement :=
  let readExpression := @ReadContext.readExpression context
  let categoryOf := context.categoryOf
  let expected := context.expected
  let elementOperation := elementOperation context
  fun (left right : TSyntax `cas_term) => do
    let rightExpected := if sourceNumeric right.raw then expected else none
    let value ← readExpression categoryOf right rightExpected
    elementOperation "•" #[left, right] #[] #[none, some value.value]
      (some (← inferType value.value))

/-- All declared juxtaposition readings compete at the same original typed operands.
Every successful native state is retained, so the unique chosen reading is not replayed.
An exception from a matched reader is never discarded to choose another interpretation. -/
def juxtapose (context : ReadContext) :
    TSyntax `cas_term → TSyntax `cas_term → TermElabM NativeSourceJudgement :=
  let readExpression := @ReadContext.readExpression context
  let categoryOf := context.categoryOf
  let expected := context.expected
  fun (left right : TSyntax `cas_term) => do
    let rightExpected := if sourceNumeric right.raw then expected else none
    let rightValue ← readExpression categoryOf right rightExpected
    let leftValue ← if sourceNumeric left.raw then pure none
      else pure (some (← readExpression categoryOf left none))
    let mut trials : Array (TermElabM (Option NativeSourceJudgement)) := #[]
    if let some originalLeft := leftValue then
      trials := trials.push do
        let pair ← mkAppM ``Prod #[← inferType originalLeft.value, ← inferType rightValue.value]
        let some action ← sourceMorphismFrom? "•" pair | return none
        let function ← sourceSetFunction action
        let argument ← mkAppM ``Prod.mk #[originalLeft.value, rightValue.value]
        return some ⟨← elabAppArgs function #[] #[Arg.expr argument] none false false, none⟩
      trials := trials.push do
        let result ← sourceDirectApplicationApplicable? originalLeft.value fun domain =>
          retainedOperandApplicable right rightValue.value domain
        match result with
        | .ok value => return value.map fun value => ⟨value, none⟩
        | .error _ => return none
    for name in ← sourceJuxtapositionNames categoryOf leftValue rightValue do
      trials := trials.push do
        let owner ← if name == "•" then pure (some (← inferType rightValue.value)) else pure none
        match ← elementOperationApplicable context name #[left, right] #[]
            #[leftValue.map (·.value), some rightValue.value] owner with
        | .ok value => return some value
        | .error _ => return none
    let original ← saveState
    let mut readings : Array (NativeSourceJudgement × Lean.Elab.Term.SavedState) := #[]
    try
      for trial in trials do
        original.restore
        if let some value ← trial then readings := readings.push (value, ← saveState)
    catch error =>
      original.restore
      throw error
    original.restore
    match readings with
    | #[(value, selected)] =>
      selected.restore
      return value
    | #[] =>
      if let some left := leftValue then
        let type ← inferType left.value
        let domains ← sourceOperationDomains categoryOf type none #[type]
        if domains.isEmpty && (left.category.any (·.role == .morphism) ||
            (← whnf type).isForall) then
          CasCatalogue.throwUnsupportedSource
            "callable juxtaposition requires its declared action and application comparison"
      CasCatalogue.throwStratum .invalid
        "no declared juxtaposition reading accepts the original operands"
    | _ =>
      CasCatalogue.throwSemanticAmbiguity
        "juxtaposition has several declared readings of its original operands"

def relation (context : ReadContext) :
    String → TSyntax `cas_term → TSyntax `cas_term → TermElabM NativeSourceJudgement :=
  let readExpression := @ReadContext.readExpression context
  let categoryOf := context.categoryOf
  let elementOperation := elementOperation context
  fun (name : String) (left right : TSyntax `cas_term) => do
    -- The public precedence grammar places a trailing domain on the right operand.
    -- Its actual selected structure types both operands through the registered map.
    match right with
    | `(cas_term| $operand:cas_term in $domain:cas_term) =>
      let domain ← sourceCarrier (← readExpression categoryOf domain none)
      elementOperation name #[left, operand] #[] #[] (some domain.value)
    | _ => elementOperation name #[left, right] #[] #[] none

end SourceReader

end CasCompiler
