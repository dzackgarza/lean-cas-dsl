module

import CasCompiler.Context
public meta import Lean.Elab.Command
meta import CasCompiler.Context

open Lean Meta CasCompiler

-- A complete source telescope remains part of every transported term, even when the
-- expression itself does not use one of its declarations.
run_cmd Lean.Elab.Command.liftTermElabM do
  let originalEnvironment ← getEnv
  try
    let dName ← mkAuxDeclName `mapPolicyDomain
    let sName ← mkAuxDeclName `mapPolicySignal
    for name in #[dName, sName] do
      addDecl (.defnDecl {
        name, levelParams := [], type := mkSort (.succ .zero),
        value := mkConst ``Nat, hints := .abbrev, safety := .safe })
    let functionType ← mkArrow (mkConst sName) (mkConst ``Nat)
    let sources ← withLocalDeclD `x (mkConst ``Nat) fun x =>
      withLocalDeclD `f functionType fun f => do
        let source ← ContextTelescope.capture #[
          { id := ⟨"context-map-policy", 0⟩, role := .parameter, expression := x },
          { id := ⟨"context-map-policy", 1⟩, role := .parameter, expression := f }]
        return #[← source.close (mkApp f (mkNatLit 0)), ← source.close (mkNatLit 1)]
    let #[first, second] := sources
      | throwError "the map-policy control lost its complete common source telescope"
    unless first.context.entries.size == 2 && second.context.entries.size == 2 &&
        first.context.exactlyMatches second.context do
      throwError "the map-policy control lost its complete common source telescope"
    withLocalDeclD `x (mkConst dName) fun x =>
      withLocalDeclD `f functionType fun f => do
        let target ← ContextTelescope.capture #[
          { id := ⟨"context-map-policy", 0⟩, role := .parameter, expression := x },
          { id := ⟨"context-map-policy", 1⟩, role := .parameter, expression := f }]
        let stableDomain ← IO.mkRef 0
        let stableSignal ← IO.mkRef 0
        let stable ← withCanUnfoldPred (fun _ info => do
          if info.name == dName then stableDomain.modify (· + 1)
          if info.name == sName then stableSignal.modify (· + 1)
          return true) <| ClosedTerm.inContextMany sources target
        unless (← stableDomain.get) > 0 && (← stableSignal.get) > 0 &&
            stable.size == 2 && stable[0]!.equal (mkApp f (mkNatLit 0)) &&
            stable[1]!.equal (mkNatLit 1) do
          throwError "stable native unfolding changed the original transported terms"
        let requireChangedPolicyFailure
            (label : String) (transport : MetaM (Array Expr)) : MetaM Unit := do
          let changed ← IO.mkRef false
          let allowedDomain ← IO.mkRef 0
          let deniedDomain ← IO.mkRef 0
          let signal ← IO.mkRef 0
          let failure : Option Exception ← try
            discard <| withCanUnfoldPred (fun _ info => do
              if info.name == sName then
                signal.modify (· + 1)
                changed.set true
                return true
              if info.name == dName then
                if ← changed.get then
                  deniedDomain.modify (· + 1)
                  return false
                allowedDomain.modify (· + 1)
                return true
              return true) transport
            pure none
          catch failure => pure (some failure)
          unless (← changed.get) && (← allowedDomain.get) > 0 && (← signal.get) > 0 do
            throwError "{label}: the actual native callback transition was not reached"
          let some failure := failure
            | throwError "{label}: transport reused a context map after its unfolding policy changed"
          unless (← deniedDomain.get) > 0 &&
              (← failure.toMessageData.toString) ==
                "the target context changed a captured binding type" do
            throw failure
        requireChangedPolicyFailure "separate public transports" <|
          sources.mapM fun source => source.inContext target
        requireChangedPolicyFailure "consecutive public transport" <|
          ClosedTerm.inContextMany sources target
  finally
    setEnv originalEnvironment
