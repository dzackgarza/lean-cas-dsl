module

import CasCompiler.PublishedSource
import CasRuntime.Literal
public meta import Lean.Elab.Command
meta import CasCompiler.PublishedSource
meta import CasRuntime.Literal

namespace CasCompiler.PublishedSourceTests

open Lean Meta Elab Term CasCatalogue

-- The complete external entrance and ordinary source entrance must substitute the same
-- actual arguments. Equal native values do not identify two original source occurrences.
-- These native local functions test application preservation; they publish no mathematics.
run_cmd Lean.Elab.Command.liftTermElabM do
  withLetDecl `first (mkConst ``Nat) (mkNatLit 7) fun first =>
    withLetDecl `second (mkConst ``Nat) (mkNatLit 7) fun second => do
      let type ← mkArrow (mkConst ``Nat) (← mkArrow (mkConst ``Nat) (mkConst ``Nat))
      withLocalDeclD `originalFunction type fun function => do
        let operands := #[first, second]
        let seen ← IO.mkRef (#[] : Array Nat)
        let complete ← applySourceArguments function #[Syntax.missing, Syntax.missing]
          fun index _ => do
            seen.modify (·.push index)
            pure operands[index]!
        let (ordinary, actual) ← elabSourceApplication function
          #[Syntax.missing, Syntax.missing] none fun index _ => pure operands[index]!
        unless complete.getAppFn == function && complete.getAppArgs == operands &&
            ordinary.getAppArgs == operands && actual == operands &&
            (← seen.get) == #[0, 1] do
          throwError "the shared native entrance replayed or replaced an original operand"
        unless ← isDefEq first second do
          throwError "the occurrence control lost its equal-valued original inputs"

-- A source hypothesis has no provider wire slot. It remains the original proof variable
-- in the actual native application. Without that source hypothesis the same request is
-- NoImplementation; no provider packet or native decision manufactures the premise.
run_cmd Lean.Elab.Command.liftTermElabM do
  withLocalDeclD `original (mkConst ``Nat) fun original => do
    let proposition ← mkEq original original
    let functionType ← mkArrow proposition (← mkArrow (mkConst ``Nat) (mkConst ``Nat))
    withLocalDeclD `originalFunction functionType fun function => do
      withLocalDeclD `originalPremise proposition fun premise => do
        let result ← applySourceArguments function #[Syntax.missing]
          fun _ _ => pure original
        unless result.getAppFn == function && result.getAppArgs == #[premise, original] do
          throwError "the published application changed its actual source hypothesis"
      let failure : Option Exception ← try
          discard <| applySourceArguments function #[Syntax.missing] fun _ _ => pure original
          pure none
        catch error => pure (some error)
      let some failure := failure
        | throwError "a published request manufactured its missing formal premise"
      unless CasCatalogue.Exception.stratum? failure == some .noImplementation do throw failure

-- Scoped references are supplied as already retained native source values. The common
-- operand gate rejects a changed native type before any occurrence binding or execution.
run_cmd Lean.Elab.Command.liftTermElabM do
  withLocalDeclD `original (mkConst ``Nat) fun original => do
    let untouched : {α : Type} → MetaM α := throwError "the source input executed before typing"
    let binding : LocalBinding := {
      id := ⟨"published-source-input", 0⟩
      role := .parameter
      expression := original }
    let scope ← ContextTelescope.capture #[binding]
    let context : PublishedSourceContext := {
      scope
      retained := fun packet => pure (if packet == toJson (0 : Nat) then some original else none)
      literal := CasRuntime.ScalarLiteral.readAt
      bind := fun _ => untouched
      rebind := fun _ _ => untouched
      methodParameters := fun _ _ _ => untouched
      checkInput := fun _ _ => untouched
      admitMethod := fun _ _ _ => untouched
      admitProperty := fun _ _ _ => untouched
      admitPoint := fun _ _ => untouched
      projection := fun _ _ => untouched }
    let result ← PublishedSource.operand context (mkConst ``Nat) (toJson (0 : Nat))
    unless result == original do throwError "the source input replaced its original scoped operand"
    let failure : Option Exception ← try
        discard <| PublishedSource.operand context (mkConst ``Int) (toJson (0 : Nat))
        pure none
      catch error => pure (some error)
    let some failure := failure | throwError "the source input accepted a different declared type"
    unless CasCatalogue.Exception.stratum? failure == some .malformed do throw failure

end CasCompiler.PublishedSourceTests
