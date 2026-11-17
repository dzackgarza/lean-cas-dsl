module

public import CasCompiler.Declaration

public section

namespace CasCompiler

open Lean Meta Elab Term CasCatalogue

/-- Check native conversion or an actual supplied equality of complete rigid families.
Reuse: SourceSession.operationConversion's native equality and SourceEquality's exact
proof-type validation. Mathematical agreement evidence is an input to this consumer. -/
def sourceFamilyConversion (left right : Expr) (evidence : Array Expr) :
    MetaM (Option Expr) := do
  if left.hasMVar || left.hasLevelMVar || right.hasMVar || right.hasLevelMVar then
    throwError "whole source family comparison requires rigid parameters and universes"
  unless ← isDefEq (← inferType left) (← inferType right) do return none
  let proposition ← mkEq left right
  if ← withoutModifyingState <| isDefEq left right then
    let proof ← mkExpectedTypeHint (← mkEqRefl left) proposition
    checkWithKernel proof
    return some proof
  for proof in evidence do
    if proof.hasMVar || proof.hasLevelMVar then
      throwError "whole source agreement evidence has undetermined parameters"
    if ← withoutModifyingState <| isDefEq (← inferType proof) proposition then
      let proof ← mkExpectedTypeHint proof proposition
      checkWithKernel proof
      return some proof
  return none

end CasCompiler
