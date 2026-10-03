/- Copyright (c) 2026 Dzack Garza. Released under Apache 2.0 license. -/
module
import LeanCategories.Catalogue.Semantics
import CasCatalogue.EquationData
meta import LeanCategories.Catalogue.Semantics
meta import CasCatalogue.EquationData

open Lean Meta Elab Term Command
namespace CasCatalogue.EquationDataProbes

-- A local engineering fixture models equation-metadata wrapping without a semantic row,
-- mathematical family, backend, or acceptance assertion.
opaque wrapped : { f : Nat → Nat // f = Nat.succ } := ⟨Nat.succ, rfl⟩
def data (n : Nat) : Nat := wrapped.val n
theorem data_eq (n : Nat) : data n = Nat.succ n := congrFun wrapped.property n
attribute [irreducible] data
attribute [eqns data_eq] data
def enclosedData (n : Nat) : Nat := data n
def exposureOnly (n : Nat) : Nat := n + 1

run_cmd liftTermElabM do
  let value ← elabTermAndSynthesize (← `(exposureOnly 4)) none
  let original ← mkEq value (mkNatLit 5)
  let some proof ← EquationData.prove original CasCatalogue.Decide.decisionProof
    | throwError "definition exposure without equation rewriting discarded a valid proof"
  unless (← inferType proof) == original &&
      (← CasCatalogue.Decide.kernelAccepts original proof) do
    throwError "exposure-only reconstruction lost the original typed proposition"
  if (← EquationData.prove (← mkEq value (mkNatLit 6))
      CasCatalogue.Decide.decisionProof).isSome then
    throwError "exposure-only reconstruction accepted a false equality"
  let ofNat ← mkEq (mkNatLit 5) (mkNatLit 5)
  let some ofNatProof ← EquationData.prove ofNat CasCatalogue.Decide.decisionProof
    | throwError "supplied numeral dictionary exposure discarded its valid proof"
  unless ← CasCatalogue.Decide.kernelAccepts ofNat ofNatProof do
    throwError "numeral dictionary exposure lost the original proposition"
  let literal := Expr.lit (.natVal 5)
  let unchanged ← mkEq literal literal
  unless (← EquationData.exposeDefinitions unchanged) == unchanged do
    throwError "no-reentry fixture unexpectedly required definition exposure"
  if (← EquationData.prove unchanged (fun _ => throwError
      "unchanged data reentered the normalized solver")).isSome then
    throwError "unchanged data fabricated a normalized proof"

class SelectedOperation where
  apply : Nat → Nat

run_cmd liftTermElabM do
  let selected ← elabTermAndSynthesize
    (← `(@SelectedOperation.apply (⟨data⟩ : SelectedOperation) 4)) none
  let some projected ← EquationData.selectedProjection? selected
    | throwError "fully supplied selected operation projection was not exposed"
  unless projected.getAppFn.isConstOf ``data do
    throwError "selected projection unfolded its metadata-bearing operation body"
  let original ← mkEq selected (mkNatLit 5)
  let some proof ← EquationData.prove original CasCatalogue.Decide.decisionProof
    | throwError "selected dictionary operation equality was not reconstructed"
  unless ← CasCatalogue.Decide.kernelAccepts original proof do
    throwError "selected dictionary operation lost the original proposition"
  let other ← elabTermAndSynthesize
    (← `(@SelectedOperation.apply (⟨fun n => n + 2⟩ : SelectedOperation) 4)) none
  if (← EquationData.prove (← mkEq other (mkNatLit 5))
      CasCatalogue.Decide.decisionProof).isSome then
    throwError "projection normalization replaced the selected dictionary"
  let bare ← mkConstWithFreshMVarLevels ``SelectedOperation.apply
  if (← EquationData.selectedProjection? bare).isSome then
    throwError "projection normalization unfolded an unsupplied operation"

opaque polymorphicWrapped (α : Type u) : { f : α → α // f = id } := ⟨id, rfl⟩
def polymorphicData {α : Type u} (value : α) : α := (polymorphicWrapped α).val value
theorem polymorphicData_eq {α : Type u} (value : α) : polymorphicData value = value :=
  congrFun (polymorphicWrapped α).property value
attribute [irreducible] polymorphicData
attribute [eqns polymorphicData_eq] polymorphicData

run_cmd liftTermElabM do
  let value ← elabTermAndSynthesize (← `(enclosedData 4)) none
  let original ← mkEq value (mkNatLit 5)
  if (← CasCatalogue.Decide.decisionProof original).isSome then
    throwError "opaque fixture did not exercise equation-metadata reconstruction"
  let some proof ← EquationData.prove original CasCatalogue.Decide.decisionProof
    | throwError "equation metadata did not reconstruct the original typed equality"
  unless (← inferType proof) == original do
    throwError "equation reconstruction did not preserve the original proposition"
  unless ← CasCatalogue.Decide.kernelAccepts original proof do
    throwError "equation reconstruction returned an unchecked original proof"
  let wrong ← mkEq value (mkNatLit 6)
  if (← EquationData.prove wrong CasCatalogue.Decide.decisionProof).isSome then
    throwError "equation metadata supplied a proof of a false equality"
  let noEquation ← mkEq (mkNatLit 5) (mkNatLit 5)
  if (← EquationData.prove noEquation (fun _ => pure none)).isSome then
    throwError "equation metadata invented evidence outside its supplied solver"
  let highUniverse ← elabTermAndSynthesize (← `(polymorphicData (ULift.up.{1, 0} (4 : Nat)))) none
  let expected ← elabTermAndSynthesize (← `(ULift.up.{1, 0} (4 : Nat))) (some (← inferType highUniverse))
  let polymorphicCondition ← mkEq highUniverse expected
  let some polymorphicProof ← EquationData.prove polymorphicCondition
      CasCatalogue.Decide.decisionProof
    | throwError "equation metadata lost the provider theorem's universe parameters"
  unless ← CasCatalogue.Decide.kernelAccepts polymorphicCondition polymorphicProof do
    throwError "polymorphic equation reconstruction failed the original kernel check"
  let indexedValue ← elabTermAndSynthesize
    (← `((⟨enclosedData 4, rfl⟩ : { n : Nat // n = n }))) none
  let indexedExpected ← elabTermAndSynthesize
    (← `((⟨5, rfl⟩ : { n : Nat // n = n }))) none
  let indexedCondition ← mkEq indexedValue indexedExpected
  let some indexedProof ← EquationData.prove indexedCondition CasCatalogue.Decide.decisionProof
    | throwError "equation reconstruction failed to transport dependent proof evidence"
  unless ← CasCatalogue.Decide.kernelAccepts indexedCondition indexedProof do
    throwError "dependent evidence reconstruction failed the original kernel check"
  let classicalChoice ← elabTermAndSynthesize
    (← `(letI : Decidable ((1 : ZMod 3) = 0) := Classical.decEq (ZMod 3) 1 0
          if (1 : ZMod 3) = 0 then (4 : Nat) else 5)) none
  let classicalCondition ← mkEq classicalChoice (mkNatLit 5)
  if (← CasCatalogue.Decide.decisionProof classicalCondition).isSome then
    throwError "classical coefficient fixture did not exercise selected decision evidence"
  let some classicalProof ← EquationData.prove classicalCondition CasCatalogue.Decide.decisionProof
    | throwError "selected classical coefficient decision was not reconstructed"
  unless ← CasCatalogue.Decide.kernelAccepts classicalCondition classicalProof do
    throwError "classical coefficient reconstruction failed the original kernel check"
  let wrongClassicalCondition ← mkEq classicalChoice (mkNatLit 4)
  if (← EquationData.prove wrongClassicalCondition CasCatalogue.Decide.decisionProof).isSome then
    throwError "classical coefficient reconstruction proved the incorrect branch"
  let symbolicChoice ← elabTermAndSynthesize
    (← `(fun n : Nat =>
      letI : Decidable (n = 1) := Classical.decEq Nat n 1
      if n = 1 then (1 : Nat) else 0)) none
  let symbolicExpected ← elabTermAndSynthesize
    (← `(fun n : Nat => if n = 1 then (1 : Nat) else 0)) none
  let symbolicCondition ← mkEq symbolicChoice symbolicExpected
  let reflexive := fun (condition : Expr) => do
    let some (_, left, right) := condition.eq? | return none
    unless ← withTransparency .all <| isDefEq left right do return none
    return some (mkExpectedPropHint (← mkEqRefl left) condition)
  let some symbolicProof ← EquationData.prove symbolicCondition reflexive
    | throwError "selected symbolic decision did not retain a computable predicate algorithm"
  unless ← CasCatalogue.Decide.kernelAccepts symbolicCondition symbolicProof do
    throwError "symbolic decision reconstruction failed the original kernel check"
  let localDecisionType ← mkAppM ``Decidable #[← mkEq (mkNatLit 1) (mkNatLit 1)]
  withLocalDeclD `unknownDecision localDecisionType fun unknownDecision => do
    if ← EquationData.computationalDecision unknownDecision then
      throwError "an opaque local decision was mistaken for an executable algorithm"

end CasCatalogue.EquationDataProbes
