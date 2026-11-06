module

import CasCompiler.Program
import CasCompiler.Context
import LeanCategories.Catalogue.Semantics.Algebra.ComputationDerivations
import Mathlib.CategoryTheory.Limits.IsLimit
public meta import Lean.Elab.Command
meta import CasCompiler.Program
meta import CasCompiler.Context
meta import LeanCategories.Catalogue.Semantics.Algebra.ComputationDerivations
meta import Mathlib.CategoryTheory.Limits.IsLimit

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
      for slot in slots, expected in source.prerequisites, index in [:slots.size] do
        unless slot.index == index &&
            slot.source.reference == expected.reference do
          throwError "source intake changed an exact ordered prerequisite address"
        check slot.expression
      check body
      return slots.map (·.expression.fvarId!)
    program.withPrerequisites fun slots body => do
      for slot in slots do
        if previous.contains slot.expression.fvarId! then
          throwError "opening a source program reused a local identity"
      check body

run_cmd Lean.Elab.Command.liftTermElabM do
  let info ← getConstInfo ``CategoryTheory.Limits.IsLimit
  let family := mkConst info.name (info.levelParams.map Level.param)
  forallTelescope (← inferType family) fun parameters _ => do
    let type := mkAppN family parameters
    withLocalDeclD `selectedLimit type fun selected => do
      let declarations := (← getLCtx).foldl (fun result decl => result.push decl) #[]
      let bindings := declarations.mapIdx fun index decl =>
        { id := ⟨"limit-layout", index⟩, role := .parameter,
          expression := mkFVar decl.fvarId : LocalBinding }
      let context ← ContextTelescope.capture bindings
      let layout ← SourceLayout.ofTerm (← context.close selected)
      unless layout.kind == .record do
        throwError "the selected limit witness lost its record layout"
      let some lift := layout.fields.find? (·.projection == ``CategoryTheory.Limits.IsLimit.lift)
        | throwError "the selected limit witness lost its mediator field"
      unless lift.kind == .function && lift.wireIndex == some 0 do
        throwError "the mediator of a data-bearing subsingleton was erased"
      let callable ← lift.toLayout
      unless callable.address == #[lift.projection] &&
          callable.kind.actions.contains .apply do
        throwError "the mediator lost its projection address or application action"
      let some fac := layout.fields.find? (·.projection == ``CategoryTheory.Limits.IsLimit.fac)
        | throwError "the selected limit witness lost its formal equation"
      unless fac.kind == .proof && fac.wireIndex.isNone &&
          fac.precedingDependencies.contains lift.sourceIndex do
        throwError "the formal equation lost its dependency on the retained mediator"
      fac.typeFamily.withOpen fun _ family => do
        lambdaTelescope family fun earlier type => do
          unless earlier.size == fac.sourceIndex &&
              type.containsFVar earlier[lift.sourceIndex]!.fvarId! do
            throwError "the field type lost its preceding-field parameterization"
      let some uniq := layout.fields.find? (·.projection == ``CategoryTheory.Limits.IsLimit.uniq)
        | throwError "the selected limit witness lost its uniqueness law"
      uniq.typeFamily.withOpen fun _ family => do
        lambdaTelescope family fun earlier _ => do
          unless earlier.size == uniq.sourceIndex do
            throwError "the field type dropped an unused preceding formal slot"
      lift.source.withOpen fun _ expression => do
        unless (← whnf (← inferType expression)).isForall do
          throwError "the retained mediator lost its complete callable type"

run_cmd Lean.Elab.Command.liftTermElabM do
  let empty ← ContextTelescope.capture #[]
  let function ← SourceLayout.ofTerm (← empty.close (mkConst ``Fin.last))
  withLocalDeclD `n (mkConst ``Nat) fun n => do
    let context ← ContextTelescope.capture #[{
      id := ⟨"application-test", 0⟩, role := .parameter, expression := n }]
    let argument ← context.close n
    let result ← function.applyIn context #[argument]
    result.source.withOpen fun bindings expression => do
      let expected := mkApp (mkConst ``Fin) (mkApp (mkConst ``Nat.succ) bindings[0]!.expression)
      unless ← isDefEq (← inferType expression) expected do
        throwError "callable application lost its dependent result type"

run_cmd Lean.Elab.Command.liftTermElabM do
  let context ← ContextTelescope.capture #[]
  let equivalence ← mkAppM ``Equiv.refl #[mkConst ``Nat]
  let layout ← SourceLayout.ofTerm (← context.close equivalence)
  unless layout.kind == .record && !layout.fields.isEmpty do
    throwError "the callable record lost its retained fields"
  let result ← layout.applyIn context #[← context.close (mkNatLit 1)]
  result.source.withOpen fun _ expression => do
    unless ← isDefEq (← inferType expression) (mkConst ``Nat) do
      throwError "source application lost the record's accepted function coercion"
