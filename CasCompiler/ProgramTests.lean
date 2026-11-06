module

import CasCompiler.Program
import LeanCategories.Catalogue.Semantics.Algebra.ComputationDerivations
public meta import Lean.Elab.Command
meta import CasCompiler.Program
meta import LeanCategories.Catalogue.Semantics.Algebra.ComputationDerivations

open Lean Meta CasCompiler CasCatalogue

run_cmd Lean.Elab.Command.liftTermElabM do
  let programs ← SourceProgram.forTarget (.operation ⟨"op.rings.mul"⟩)
  unless programs.size == 2 do
    throwError "source intake must retain both published derivations"
  for program in programs do
    let source := program.source
    check source.correctness
    unless ← isDefEq (← inferType source.correctness) (← mkEq source.plan source.target) do
      throwError "source intake lost the checked whole-family equality"
    let previous ← program.withPrerequisites fun slots body => do
      unless slots.size == source.prerequisites.size do
        throwError "source intake changed the prerequisite arity"
      for slot in slots, index in [:slots.size] do
        unless slot.index == index &&
            slot.source.reference == source.prerequisites[index]!.reference do
          throwError "source intake changed an exact ordered prerequisite address"
        check slot.expression
      check body
      return slots.map (·.expression.fvarId!)
    program.withPrerequisites fun slots body => do
      for slot in slots do
        if previous.contains slot.expression.fvarId! then
          throwError "opening a source program reused a local identity"
      check body
