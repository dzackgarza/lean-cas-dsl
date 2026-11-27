module

public import CasCompiler.ReadAtomNotation
public import CasCompiler.ReadMemberNotation
public import CasCompiler.ReadSubsetNotation
public import CasCompiler.ReadRingNotation
public import CasCompiler.ReadBinderNotation
public import CasCompiler.ReadProductNotation
public import CasCompiler.ReadLiftRules
public import CasCompiler.ReadLimitRules
public import CasCompiler.ReadOperationRules
public import CasCompiler.ReadSubsetRules
public import CasCompiler.ReadPowerRules
public import CasCompiler.ReadGraphRules
public import CasCompiler.ReadEquationRules
public import CasCompiler.ReadMemberRules
public import CasCompiler.ReadLambdaRules
public import CasCompiler.ReadNumeralRules
public import CasCompiler.ReadFunctorRules
public import CasCompiler.ReadCellRules
public import CasCompiler.ReadTupleRules
public import CasCompiler.ReadNameRules
public import CasCompiler.ReadAnnotationRules
public import CasCompiler.ReadApplicationRules
public import CasCompiler.ReadProjection
public import CasCompiler.ReadDispatch
public import CasCompiler.SourceRing
import CasCompiler.SourceCarrier

public section

namespace CasCompiler

open Lean Meta Elab Term

private def sourceRules : Array ReadCompletingRule := #[
  ReadApplicableRule.completing ReadAtomNotation.ruleApplicable,
  ReadMemberNotation.ruleCompleting,
  ReadRule.completing ReadSubsetNotation.rule,
  ReadRule.completing ReadRingNotation.rule,
  ReadRule.completing ReadBinderNotation.rule,
  ReadRule.completing ReadProductNotation.rule,
  ReadRule.completing ReadLiftRules.rule,
  ReadRule.completing ReadLimitRules.rule,
  ReadRule.completing ReadOperationRules.rule,
  ReadRule.completing ReadSubsetRules.rule,
  ReadRule.completing ReadPowerRules.rule,
  ReadRule.completing ReadGraphRules.rule,
  ReadRule.completing ReadEquationRules.rule,
  ReadMemberRules.ruleCompleting,
  ReadRule.completing ReadLambdaRules.rule,
  ReadRule.completing ReadNumeralRules.rule,
  ReadRule.completing ReadFunctorRules.rule,
  ReadRule.completing ReadCellRules.rule,
  ReadRule.completing ReadTupleRules.rule,
  ReadNameRules.ruleCompleting,
  ReadRule.completing ReadAnnotationRules.rule,
  ReadApplicationRules.ruleCompleting
]

partial def readExpressionApplicable
    (categoryOf : FVarId → TermElabM (Option NativeSourceCategory))
    (source : TSyntax `cas_term) (expected : Option Expr)
    (qualification : Option String := none)
    (expectedCategory : Option NativeSourceCategory := none) :
    SourceReadM (Except MessageData NativeSourceJudgement) := do
  let scope ← get
  let categoryOf := fun id => do
    if let some selected := scope.selections.findAt? scope.context (mkFVar id) then
      if selected.formalBindings.isEmpty then
        if let some category := selected.category then return some category
    categoryOf id
  readWithCompletingRules sourceRules ⟨categoryOf, source, expected, qualification, expectedCategory,
    readProjection, fun categoryOf source expected qualification expectedCategory =>
      readExpressionApplicable categoryOf source expected qualification expectedCategory⟩

def readExpression
    (categoryOf : FVarId → TermElabM (Option NativeSourceCategory))
    (source : TSyntax `cas_term) (expected : Option Expr)
    (qualification : Option String := none)
    (expectedCategory : Option NativeSourceCategory := none) : SourceReadM NativeSourceJudgement :=
  SourceReadM.withRef source do
    match ← readExpressionApplicable categoryOf source expected qualification expectedCategory with
    | .ok value => pure value
    | .error message => liftM (m := TermElabM) <| throwError message





partial def withRingVariables
    (categoryOf : FVarId → TermElabM (Option NativeSourceCategory))
    (recorded : Array (Name × Expr × Option Nat))
    (source : TSyntax `cas_term) (read : SourceReadM NativeSourceJudgement) :
    SourceReadM NativeSourceJudgement := do
  let mut written : Array (Name × Syntax × Option Nat) := #[]
  for (name, ring, index) in sourceRingVariables source.raw do
    unless sourceUses name source.raw && !sourceBinds name source.raw do continue
    if let some (_, other, _) := written.find? (·.1 == name) then
      unless other.reprint == ring.reprint do
        liftM (m := TermElabM) <| CasCatalogue.throwSemanticAmbiguity m!"{name} is the variable of several rings"
      continue
    written := written.push (name, ring, index)

  let mut inherited : Array (Name × Expr × Option Nat) := #[]
  for (name, carrier, index) in recorded do
    unless sourceUses name source.raw && !sourceBinds name source.raw do continue
    if written.any (·.1 == name) then continue
    if let some (_, other, _) := inherited.find? (·.1 == name) then
      unless other == carrier do
        liftM (m := TermElabM) <| CasCatalogue.throwSemanticAmbiguity m!"{name} is the variable of several rings"
      continue
    inherited := inherited.push (name, carrier, index)
  let mut bindings : Array (Name × Sum Syntax Expr × Option Nat) := #[]
  for (name, ring, index) in written do bindings := bindings.push (name, .inl ring, index)
  for (name, carrier, index) in inherited do bindings := bindings.push (name, .inr carrier, index)
  bind bindings.toList
where
  bind : List (Name × Sum Syntax Expr × Option Nat) → SourceReadM NativeSourceJudgement
    | [] => read
    | (name, ring, index) :: rest => do
      if ((← liftM (m := MetaM) getLCtx).findFromUserName? name).isSome then return ← bind rest
      let carrier ← match ring with
        | .inl ring => pure (← sourceCarrier (← readExpression categoryOf ⟨ring⟩ none)).value
        | .inr carrier => pure carrier
      let some generator ← sourceGeneratorAt? carrier index
        | liftM (m := TermElabM) <| throwError "the ring of {name} has no registered generator"
      SourceReadM.withBinder name carrier (some generator) .default
        (fun bound judgement => do
          let close := fun value => mkLetFVars #[bound.expression] value
            (usedLetOnly := false) (generalizeNondepLet := false)
          return { judgement with
            value := ← close judgement.value
            category := ← judgement.category.mapM (NativeSourceCategory.mapM close) })
        (fun _ => bind rest)


def readSourceTerm (categoryOf : FVarId → TermElabM (Option NativeSourceCategory))
    (recorded : Array (Name × Expr × Option Nat))
    (source : TSyntax `cas_term) (expected : Option Expr) : SourceReadM NativeSourceJudgement :=
  withRingVariables categoryOf recorded source (readExpression categoryOf source expected)



def sourceEquation (categoryOf : FVarId → TermElabM (Option NativeSourceCategory))
    (left right : TSyntax `cas_term) : SourceReadM Expr := do
  let equation ← liftM (m := TermElabM) `(cas_term| $left:cas_term = $right:cas_term)
  return (← readExpression categoryOf equation (some (mkSort .zero))).value

end CasCompiler
