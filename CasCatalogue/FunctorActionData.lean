/- Copyright (c) 2026 Dzack Garza. Released under Apache 2.0 license. -/
module
public import CasCatalogue.Semantic
public import CasCatalogue.Decide

@[expose] public section
open Lean Meta Elab Term

namespace CasCatalogue.FunctorActionData

/-- Decode an explicitly named accepted functor action and its complete source data.
The callbacks consume registered edge metadata and selected source data; replies supply no
semantics or evidence. A direct presentation or lift receiver additionally requires a callback
closed over the independently retained child object and operation provenance. Subobject
projections retain the actual defining inclusion. -/
def decodeInferred (json : Json)
    (decodeFunctor : Json → TermElabM (Except String (Expr × CategoryExpr × CategoryExpr)))
    (decodeSource : CategoryExpr → Expr → Json → TermElabM (Except String Expr))
    (decodeReceiver : Option (Json → TermElabM (Except String (Expr × CategoryExpr))) := none) :
    TermElabM (Option (Except String (Expr × CategoryExpr))) := do
  let .ok tag := json.getObjValAs? String "ctor" | return none
  unless ["functorAction", "subobjectApex", "subobjectInclusion"].contains tag do return none
  let work : TermElabM (Except String (Expr × CategoryExpr)) := do
    let .ok outerArgs := (json.getObjVal? "args").bind (·.getArr?)
      | return .error s!"{tag} requires ordered complete data"
    let action ← if tag == "functorAction" then pure json else do
      let #[action] := outerArgs | return .error s!"{tag} requires one complete subobject receiver"
      pure action
    let (image, targetCategory) ← if tag != "functorAction" && decodeReceiver.isSome then do
      unless ["functorAction", "objectPresentation", "liftedSubobject"].any
          (fun receiver => (action.getObjValAs? String "ctor").toOption == some receiver) do
        return .error "a subobject projection requires a complete checked receiver descriptor"
      let some readReceiver := decodeReceiver
        | return .error "the subobject receiver has no independently retained operation context"
      let .ok receiver ← readReceiver action
        | return .error "the complete subobject receiver failed its independent contextual check"
      pure receiver
    else if
        (action.getObjValAs? String "ctor").toOption == some "functorAction" then do
      let .ok #[edgeJson, sourceJson] := (action.getObjVal? "args").bind (·.getArr?)
        | return .error "functorAction requires an exact registered edge and complete source data"
      let .ok (F, sourceCategory, targetCategory) ← decodeFunctor edgeJson
        | return .error "the functor action has no accepted exact registered edge"
      let F ← if (← withTransparency .all <| whnf (← inferType F)).isAppOf
          ``CategoryTheory.Cat.Hom then
        mkAppM ``CategoryTheory.Cat.Hom.toFunctor #[F] else pure F
      let functorType ← withTransparency .all <| whnf (← inferType F)
      unless functorType.isAppOf ``CategoryTheory.Functor do
        return .error "the registered edge does not instantiate a categorical functor"
      let endpoints := functorType.getAppArgs
      let .ok source ← decodeSource sourceCategory endpoints[0]! sourceJson
        | return .error "the functor action has invalid selected source data"
      unless ← isDefEq (← inferType source) endpoints[0]! do
        return .error "the functor action source belongs to a different category"
      let image ← Semantic.objOf F source
      pure (image, targetCategory)
    else do
      if tag == "functorAction" then
        return .error "functorAction requires its complete registered action descriptor"
      unless ["objectPresentation", "liftedSubobject"].any
          (fun receiver => (action.getObjValAs? String "ctor").toOption == some receiver) do
        return .error "a subobject projection requires a complete checked receiver descriptor"
      let some decodeReceiver := decodeReceiver
        | return .error "the subobject receiver has no independently retained operation context"
      let .ok receiver ← decodeReceiver action
        | return .error "the complete subobject receiver failed its independent contextual check"
      pure receiver
    let (value, resultCategory) ← if tag == "functorAction" then
        pure (image, targetCategory)
      else do
        let .construct constructor #[.category base] := targetCategory
          | return .error "the complete receiver is not in a registered subobject category"
        let state ← registryState
        unless (state.constructors.find? (·.id == constructor)).any
            (·.semantics == `CasCatalogue.Constructors.subobjects) do
          return .error "the complete receiver is not in the accepted subobject constructor"
        let arrow ← mkAppM ``CategoryTheory.ObjectProperty.FullSubcategory.obj #[image]
        let value ← mkAppM (if tag == "subobjectApex" then ``CategoryTheory.Arrow.left
          else ``CategoryTheory.Arrow.hom) #[arrow]
        pure (value, base)
    let value ← instantiateMVars value
    if value.hasMVar || value.hasLevelMVar || value.hasFVar || value.hasLooseBVars then
      return .error s!"{tag} has unresolved categorical data"
    let equality ← mkAppM ``Eq #[value, value]
    let refl ← mkAppM ``Eq.refl #[value]
    unless ← Decide.kernelAccepts equality refl do
      return .error s!"{tag} did not produce kernel-checked categorical data"
    return .ok (value, resultCategory)
  return some (← work)

/-- Check inferred registered categorical data at an independently supplied exact result type.
Inference comes only from the accepted functor signature and its typed complete source. -/
def decode (expected : Expr) (json : Json)
    (decodeFunctor : Json → TermElabM (Except String (Expr × CategoryExpr × CategoryExpr)))
    (decodeSource : CategoryExpr → Expr → Json → TermElabM (Except String Expr))
    (decodeReceiver : Option (Json → TermElabM (Except String (Expr × CategoryExpr))) := none) :
    TermElabM (Option (Except String Expr)) := do
  let some result ← decodeInferred json decodeFunctor decodeSource decodeReceiver | return none
  match result with
  | .error message => return some (.error message)
  | .ok (value, _) =>
    unless ← isDefEq (← inferType value) expected do
      return some (.error "categorical data has incompatible selected result type or exact endpoints")
    return some (.ok value)

end CasCatalogue.FunctorActionData
