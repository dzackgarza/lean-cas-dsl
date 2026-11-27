module

import CasCompiler.PublishedSource
import CasRuntime.Literal
public meta import Lean.Elab.Command
meta import CasCompiler.PublishedSource
meta import CasRuntime.Literal

namespace CasCompiler.PublishedSourceTests

open Lean Meta Elab Term CasCatalogue




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



run_cmd Lean.Elab.Command.liftTermElabM do
  withLocalDeclD `original (mkConst ``Nat) fun original => do
    let untouched : {α : Type} → MetaM α := throwError "the source input executed before typing"
    let binding : LocalBinding := {
      id := ⟨"published-source-input", 0⟩
      role := .parameter
      expression := original }
    let scope ← ContextTelescope.capture #[binding]
    let identities ← CasRuntime.IdentitySupply.new
    let context : PublishedSourceContext OpenContext := {
      scope := id
      identities := fun _ => identities
      selections := fun _ => {}
      select := fun _ _ => liftM (m := MetaM) untouched
      actionSource := fun _ => liftM (m := MetaM) untouched
      retained := fun _ packet => pure (if packet == toJson (0 : Nat) then some original else none)
      literal := CasRuntime.ScalarLiteral.readAt
      bind := fun _ => liftM (m := MetaM) untouched
      bindAt := fun _ _ => liftM (m := MetaM) untouched
      rebind := fun _ _ => liftM (m := MetaM) untouched
      methodParameters := fun _ _ _ => liftM (m := MetaM) untouched
      checkInput := fun _ _ _ => untouched
      admitMethod := fun _ _ _ _ => untouched
      admitProperty := fun _ _ _ _ => untouched
      admitPoint := fun _ _ _ => untouched
      projection := fun _ _ => liftM (m := MetaM) untouched }
    let result ← (PublishedSource.operand context (mkConst ``Nat) (toJson (0 : Nat))).run' scope
    unless result == original do throwError "the source input replaced its original scoped operand"
    let failure : Option Exception ← try
        discard <| (PublishedSource.operand context (mkConst ``Int) (toJson (0 : Nat))).run' scope
        pure none
      catch error => pure (some error)
    let some failure := failure | throwError "the source input accepted a different declared type"
    unless CasCatalogue.Exception.stratum? failure == some .malformed do throw failure




run_cmd Lean.Elab.Command.liftTermElabM do
  let natural := mkConst ``Nat
  let functionType ← withLocalDeclD `n natural fun n => do
    let type ← mkArrow (← mkAppM ``Fin #[n]) natural
    mkForallFVars #[n] type
  withLocalDeclD `originalFunction functionType fun function => do
    let initial ← ContextTelescope.capture #[{
      id := ⟨"published-dependent-input", 0⟩, role := .parameter, expression := function }]
    initial.withLocalBinding ⟨"published-dependent-input", 1⟩ .result `originalN natural
      (fun scope n => do
        let original ← mkAppM ``Fin.last #[mkNatLit 6]
        scope.withLocalBinding ⟨"published-dependent-input", 2⟩ .result `originalPoint
          (← inferType original) (fun scope point => do
            let domain ← mkAppM ``Fin #[n.expression]
            if ← withoutModifyingState <| isDefEq (← inferType point.expression) domain then
              throwError "the dependent input control did not preserve its opaque index"
            let external ← mkFreshExprMVar natural
            let externalBefore ← external.mvarId!.getDecl
            let unavailable : {α : Type} → MetaM α := fun {_} =>
              throwError "the dependent source control requested an unrelated runtime operation"
            let identities ← CasRuntime.IdentitySupply.new
            let context : PublishedSourceContext OpenContext := {
              scope := id
              identities := fun _ => identities
              selections := fun _ => {}
              select := fun _ _ => liftM (m := MetaM) unavailable
              actionSource := fun packet =>
                pure (if packet == toJson (0 : Nat) then some function else none)
              retained := fun _ packet => pure <|
                if packet == toJson (0 : Nat) then some function
                else if packet == toJson (1 : Nat) then some n.expression
                else if packet == toJson (2 : Nat) then some point.expression
                else none
              literal := fun _ _ => pure none
              bind := pure
              bindAt := fun source type _ scope finish =>
                scope.withLocalBinding ⟨"published-dependent-input", 3⟩ .result `typedPoint type
                  (fun scope binding => finish binding.expression scope)
                  (originalSource := some source)
              rebind := fun _ value => pure value
              methodParameters := fun _ _ _ => liftM (m := MetaM) unavailable
              checkInput := fun _ _ _ => unavailable
              admitMethod := fun _ _ _ _ => unavailable
              admitProperty := fun _ _ _ _ => unavailable
              admitPoint := fun _ _ _ => unavailable
              projection := fun _ _ => liftM (m := MetaM) unavailable }
            let call := Json.mkObj [("op", toJson "$cas.apply"),
              ("args", Json.mkObj [("value", toJson (0 : Nat)),
                ("arguments", toJson (#[1, 2] : Array Nat))])]
            let originalLocals := (← getLCtx).foldl
              (fun result declaration => result.push declaration.fvarId) #[]
            (PublishedSource.prepare context call).runK scope fun result completed => do
              let some binding := completed.bindings.back?
                | throwError "the dependent request lost its complete final native scope"
              unless result.getAppFn == function &&
                  result.getAppArgs == #[n.expression, binding.expression] &&
                  binding.id == ⟨"published-dependent-input", 3⟩ &&
                  binding.originalSource == some point.expression &&
                  binding.expression != point.expression do
                throwError "the public request changed an original dependent operand position"
              unless ← isDefEq (← inferType binding.expression) domain do
                throwError "the public request did not retain its dependent native binder type"
              let externalAfter ← external.mvarId!.getDecl
              unless (externalBefore.lctx.foldl
                  (fun result declaration => result.push declaration.fvarId) #[]) ==
                  (externalAfter.lctx.foldl
                    (fun result declaration => result.push declaration.fvarId) #[]) &&
                  !externalAfter.lctx.contains binding.expression.fvarId! do
                throwError "the source producer extended an external metavariable scope"
              checkWithKernel result
              discard <| completed.close result
            unless (← getLCtx).foldl (fun result declaration => result.push declaration.fvarId) #[] ==
                originalLocals do
              throwError "the public dependent request leaked a scoped native binder")
          (originalSource := some original))
      (originalSource := some (mkNatLit 7))



run_cmd Lean.Elab.Command.liftTermElabM do
  let natural := mkConst ``Nat
  let type ← mkArrow natural (← mkArrow natural natural)
  withLocalDeclD `originalFunction type fun function => do
    let external ← mkFreshExprMVar natural
    let before ← getMCtx
    let locals := (← getLCtx).foldl
      (fun result declaration => result.push declaration.fvarId) #[]
    let read : Nat → Expr → StateCpsT Unit TermElabM (Except MessageData Expr) :=
      fun index domain _ state finish =>
        withLocalDeclD `scopedOperand domain fun value =>
          finish (if index == 0 then .ok value else .error m!"the original reader rejected its second slot") state
    (elabSourceApplicationApplicableScoped function #[Syntax.missing, Syntax.missing] none read).runK ()
      fun result _ => do
        unless result matches .error _ do
          throwError "the source application suppressed its original reader mismatch"
        unless (← getLCtx).foldl (fun result declaration => result.push declaration.fvarId) #[] == locals do
          throwError "the rejected source reader leaked a native operand scope"
        let after ← getMCtx
        unless before.decls.toArray.size == after.decls.toArray.size &&
            !(← external.mvarId!.isAssignedOrDelayedAssigned) do
          throwError "the rejected source reader changed the original metavariable context"
        let original ← external.mvarId!.getDecl
        unless original.lctx.foldl (fun result declaration => result.push declaration.fvarId) #[] == locals do
          throwError "the rejected source reader changed an external native scope"

end CasCompiler.PublishedSourceTests
