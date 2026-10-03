/- Copyright (c) 2026 Dzack Garza. Released under Apache 2.0 license. -/
module

public import CasCatalogue.Semantic
public import CasCatalogue.Decide
public import CasCatalogue.Codec

@[expose] public section

open Lean Meta Elab Term

namespace CasCatalogue.ConstructionData

/-- Read canonical categorical data explicitly named in a reply. These descriptors carry no
proof, and never assert that another apex is isomorphic to the accepted apex. The registered
presentation is instantiated at the complete decoded diagram before projecting any data. -/
def decode (expected : Expr) (json : Json)
    (decodeArg : Expr → Json → TermElabM (Except String Expr)) :
    TermElabM (Option (Except String Expr)) := do
  let .ok ctor := json.getObjValAs? String "ctor" | return none
  unless ["limitApex", "limitLeg", "zero", "identity"].contains ctor do return none
  let work : TermElabM (Except String Expr) := do
    let .ok args := (json.getObjVal? "args").bind (·.getArr?)
      | return .error s!"{ctor} requires an ordered args array"
    let value ← if ctor == "limitApex" || ctor == "limitLeg" then do
      let arity := if ctor == "limitApex" then 2 else 3
      unless args.size == arity do
        return .error s!"{ctor} requires the registered limit id, full diagram{if arity == 3 then ", and index" else ""}"
      let .ok id := args[0]!.getStr?
        | return .error "a canonical limit descriptor requires a registered limit id"
      let state ← registryState
      let some row := state.limits.find? (·.id.raw == id)
        | return .error "the canonical descriptor names an unregistered limit"
      let family ← instantiateFresh row.declaration
      let diagramType ← inferType (← whnfR (← inferType family)).appArg!
      let .ok diagram ← decodeArg diagramType args[1]!
        | return .error "the canonical descriptor has an invalid complete diagram"
      let familyDiagram := (← whnfR (← inferType family)).appArg!
      unless ← withReducible <| isDefEq familyDiagram diagram do
        let some isoName := standardFormIso row.shape
          | return .error "the registered limit has no supported standard diagram form"
        let iso ← mkAppM isoName #[diagram]
        let standard := (← whnfR (← inferType iso)).getAppArgs.back!
        unless ← withTransparency .all <| isDefEq familyDiagram standard do
          return .error "the registered limit does not apply to the supplied complete diagram"
      let presentation ← Semantic.limitPresentation row diagram
      let cone ← mkAppM (if row.colimit then ``CategoryTheory.Limits.ColimitCocone.cocone
        else ``CategoryTheory.Limits.LimitCone.cone) #[presentation]
      if ctor == "limitApex" then
        mkAppM (if row.colimit then ``CategoryTheory.Limits.Cocone.pt
          else ``CategoryTheory.Limits.Cone.pt) #[cone]
      else do
        let transformation ← mkAppM (if row.colimit then ``CategoryTheory.Limits.Cocone.ι
          else ``CategoryTheory.Limits.Cone.π) #[cone]
        let diagramType ← whnfR (← inferType diagram)
        unless diagramType.isAppOf ``CategoryTheory.Functor do
          return .error "the defining leg has no diagram index"
        let indexType := diagramType.getAppArgs[0]!
        let .ok index ← Codec.decode indexType args[2]!
          | return .error "the defining leg has an invalid diagram index"
        mkAppM ``CategoryTheory.NatTrans.app #[transformation, index]
    else do
      unless args.size == 2 do return .error s!"{ctor} requires both exact endpoints"
      let homType ← whnfR expected
      unless homType.isAppOf ``Quiver.Hom do
        return .error s!"{ctor} requires a categorical morphism result type"
      let homArgs := homType.getAppArgs
      let source := homArgs[homArgs.size - 2]!
      let target := homArgs[homArgs.size - 1]!
      let .ok suppliedSource ← decodeArg (← inferType source) args[0]!
        | return .error s!"{ctor} has an invalid source endpoint"
      let .ok suppliedTarget ← decodeArg (← inferType target) args[1]!
        | return .error s!"{ctor} has an invalid target endpoint"
      unless ← isDefEq suppliedSource source do return .error s!"{ctor} has the wrong source endpoint"
      unless ← isDefEq suppliedTarget target do return .error s!"{ctor} has the wrong target endpoint"
      if ctor == "identity" then
        unless ← isDefEq source target do return .error "identity requires the same exact endpoint"
        mkAppM ``CategoryTheory.CategoryStruct.id #[source]
      else
        let zeroMorphisms ← elabTermAndSynthesize
          (← `(CategoryTheory.Limits.HasZeroMorphisms $(← exprToSyntax homArgs[0]!))) none
        unless (← trySynthInstance zeroMorphisms).toOption.isSome do
          return .error "zero requires the accepted category's zero-morphism structure"
        elabTermEnsuringType (← `(0)) expected
    unless ← isDefEq (← inferType value) expected do
      return .error s!"{ctor} has incompatible declared endpoints or result type"
    let value ← instantiateMVars value
    if value.hasMVar || value.hasLevelMVar then
      return .error s!"{ctor} has unresolved parameters"
    -- `kernelAccepts` checks theorem declarations. Put the data in a reflexive equality at
    -- its declared type so Lean checks the entire data term without treating data as a proof.
    let equality ← mkAppM ``Eq #[value, value]
    let reflexivity ← mkAppM ``Eq.refl #[value]
    unless ← Decide.kernelAccepts equality reflexivity do
      return .error s!"{ctor} did not produce kernel-checked categorical data"
    return .ok value
  return some (← work)

end CasCatalogue.ConstructionData
