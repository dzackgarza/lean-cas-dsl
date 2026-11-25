module

import CasCompiler.ConstructionEndpoint
import LeanCategories.Catalogue.Semantics.Limits.Registration
public meta import Lean.Elab.Command
meta import CasCompiler.ConstructionEndpoint
meta import LeanCategories.Catalogue.Semantics.Limits.Registration

open Lean Meta Elab Command CasCompiler CasCatalogue

-- Both declared parameter positions specialize to the same native object. Only
-- the original rigid position, not that specialized equality, validates the leg.
-- The existing native diagram and index are used for limits and colimits.
run_cmd liftTermElabM do
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
        let original ← family.prepareOwner levels construction
        let whole ← family.markSelected original levels parameters
        let .mdata _ body := whole
          | throwError "the original whole cone lost its source selection"
        let (_, _, owner, selected) ← family.application body
        let ownerFamily ← family.ownerFamily owner
        unless ownerFamily.equal original do
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
        -- Runtime may authenticate the same actual binding at both original
        -- parameter slots. The explicit alias table admits the matching slot.
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
        let changed ← family.prepareOwner levels (← mkFreshUserName `anotherEndpointControl)
        let wrongOwner ← try
            checkConstructionLegEndpointAt changed selected parameters indexFamily left
              (!family.entry.colimit) 0
            pure false
          catch _ => pure true
        unless wrongOwner do
          throwError "an equal native construction replaced the original retained owner"
