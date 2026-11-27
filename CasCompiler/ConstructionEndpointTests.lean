module

import CasCompiler.ConstructionEndpoint
import LeanCategories.Catalogue.Semantics.Limits.Registration
public meta import Lean.Elab.Command
meta import CasCompiler.ConstructionEndpoint
meta import LeanCategories.Catalogue.Semantics.Limits.Registration

open Lean Meta Elab Command CasCompiler CasCatalogue




run_cmd liftTermElabM do
  let identities ← liftM (m := IO) CasRuntime.IdentitySupply.new
  for identifier in #["lim.sets.product", "colim.sets.coproduct"] do
    let family ← LimitFamily.forId ⟨identifier⟩
    for levels in #[family.universeParams.map (fun _ => Level.zero),
        family.universeParams.map Level.param] do
      let declaration := family.presentationFamily.instantiateLevelParams
        family.universeParams levels
      forallTelescopeReducing (← inferType declaration) fun actual _ => do
        unless actual.size == 2 do
          throwError "the original binary presentation changed its complete input telescope"
        let some first := actual[0]?
          | throwError "the binary presentation lost its first original input"
        let parameters := actual.set! 1 first
        let construction ← mkFreshUserName `originalEndpointControl
        let original ← family.prepareOwner identities levels construction
        let whole ← family.selectedAtOwner original levels parameters
        let some application := whole.application
          | throwError "the original whole cone lost its source selection"
        let some ownerFamily := application.ownerSelection
          | throwError "the original whole cone lost its complete selected owner"
        let some selected := whole.limit
          | throwError "the original whole cone lost its native construction selection"
        unless application.family.exactlyMatches (.limit family) &&
            application.universes == levels &&
            application.parameters.size == parameters.size &&
            (application.parameters.zip parameters).all (fun (left, right) => left.equal right) do
          throwError "the original whole cone changed its complete native parameter positions"
        let expectedOwner : SourceSelection Expr := {
          value := original.selection.receiver, limit := some original.selection,
          formalBindings := original.formalBindings }
        let retainedOwner : SourceSelection Expr := {
          value := ownerFamily.selection.receiver, limit := some ownerFamily.selection,
          formalBindings := ownerFamily.formalBindings }
        unless retainedOwner.exactlyMatches Expr.equal expectedOwner &&
            (← family.ownerFamily ownerFamily).equal original.selection.receiver do
          throwError "the endpoint checker replaced the original formal owner family"
        let left ← instantiateMVars
          (← mkAppM ``CategoryTheory.Discrete.mk
            #[mkConst ``CategoryTheory.Limits.WalkingPair.left])
        let right ← instantiateMVars
          (← mkAppM ``CategoryTheory.Discrete.mk
            #[mkConst ``CategoryTheory.Limits.WalkingPair.right])
        let indexFamily ← withConstructionParameters ownerFamily construction parameters.size
          fun formals _ => mkLambdaFVars formals left
            (usedOnly := false) (usedLetOnly := false)
        checkConstructionLegEndpointAt ownerFamily selected parameters indexFamily left
          (!family.entry.colimit) 0


        checkConstructionLegEndpointAt ownerFamily selected parameters indexFamily left
          (!family.entry.colimit) 1 #[] #[(0, #[])]
        let invalidAlias ← try
            checkConstructionLegEndpointAt ownerFamily selected parameters indexFamily left
              (!family.entry.colimit) 0 #[] #[(2, #[])]
            pure false
          catch _ => pure true
        unless invalidAlias do
          throwError "a matching endpoint hid an invalid original alias position"
        let wrongPosition ← try
            checkConstructionLegEndpointAt ownerFamily selected parameters indexFamily left
              (!family.entry.colimit) 1
            pure false
          catch _ => pure true
        unless wrongPosition do
          throwError "equal specialized objects selected another original endpoint position"
        let wrongIndex ← try
            checkConstructionLegEndpointAt ownerFamily selected parameters indexFamily right
              (!family.entry.colimit) 0
            pure false
          catch _ => pure true
        unless wrongIndex do
          throwError "the endpoint checker replaced the original typed native index"
        let changed ← family.prepareOwner identities levels (← mkFreshUserName `anotherEndpointControl)
        let wrongOwner ← try
            checkConstructionLegEndpointAt changed selected parameters indexFamily left
              (!family.entry.colimit) 0
            pure false
          catch _ => pure true
        unless wrongOwner do
          throwError "an equal native construction replaced the original retained owner"
