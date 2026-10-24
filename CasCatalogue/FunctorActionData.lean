/- Copyright (c) 2026 Dzack Garza. Released under Apache 2.0 license. -/
module
public import CasCatalogue.Semantic
public import CasCatalogue.Decide

@[expose] public section
open Lean Meta Elab Term

namespace CasCatalogue.FunctorActionData

/-- An accepted action whose original receiver is literally retained inside a reduced
parameter. This is presentation metadata, not data from another equal result. -/
structure RetainedParameterAction where
  receiver : Expr
  route : Array EdgeRef
  applications : Array Expr

def closedParameter (value : Expr) : Bool :=
  !value.hasMVar && !value.hasLevelMVar && !value.hasFVar && !value.hasLooseBVars

/-- Recover only an action of an actual source occurrence in the requested parameter.
The complete bundled result, the full registered functors, and their ordered parameters
are checked before any data callback runs. Equal cached objects are never searched.

Different retained actions remain ambiguous even when their values happen to agree at
this object. Only repeated records of exactly the same source and applications coalesce. -/
def retainedParameterAction? (trace : Trace) (value : Expr) :
    TermElabM (Option RetainedParameterAction) := do
  let value ← instantiateMVars value
  unless closedParameter value && (← isTypeCorrect value) do
    throwError "the reduced action parameter is not a closed well-typed value"
  let state ← registryState
  let mut selected := value.consumeMData
  while selected.isAppOfArity ``id 2 do selected := selected.appArg!.consumeMData
  -- A literal named object supplies its own selected presentation. An action
  -- recorded elsewhere cannot replace it merely because the full values agree.
  if state.objects.any (fun row => selected.getAppFn.constName? == some row.declaration) then
    return none
  let mut candidates : Array RetainedParameterAction := #[]
  for (recorded, node) in (← trace.get).toArray do
    let source? := match node with
      | .functor _ _ receiver => some receiver
      | .retainedRoute _ _ _ _ receiver => some receiver
      | .contextualRoute _ _ _ _ receiver false => some receiver
      | _ => none
    let some receiver := source? | continue
    -- Literal occurrence is the provenance boundary: a definitionally equal
    -- receiver elsewhere in the trace does not identify this actual child.
    unless receiver != value && (value.find? (· == receiver)).isSome do continue
    let sameResult ← withoutModifyingState do
      unless closedParameter recorded && (← isTypeCorrect recorded) do return false
      withTransparency .all do
        isDefEq (← inferType recorded) (← inferType value) <&&> isDefEq recorded value
    unless sameResult do continue
    let candidate ← withoutModifyingState do
      unless closedParameter receiver && (← isTypeCorrect receiver) do
        throwError "the retained parameter action lost its exact closed source"
      let (route, applications) ← match node with
        | .retainedRoute _ _ route applications _ => pure (route, applications)
        | .contextualRoute _ _ route applications _ false => pure (route, applications)
        | .functor id parameters _ => do
          let some entry := state.functor? id
            | throwError "the retained parameter action is not registered"
          let declaration ← mkConstWithFreshMVarLevels entry.declaration
          let (arguments, infos, _) ← forallMetaTelescopeReducing (← inferType declaration)
          let explicit := (arguments.zip infos).filterMap fun (argument, info) =>
            if info.isExplicit then some argument else none
          unless explicit.size == parameters.size do
            throwError "the retained parameter action lost its ordered declaration parameters"
          for (argument, parameter) in explicit.zip parameters do
            unless closedParameter parameter && (← isTypeCorrect parameter) &&
                (← isDefEq (← inferType argument) (← inferType parameter)) &&
                (← isDefEq argument parameter) do
              throwError "the retained parameter action changed a complete declaration parameter"
          let action := mkAppN declaration arguments
          discard <| Semantic.objOf action receiver
          pure (#[.functor id], #[← instantiateMVars action])
        | _ => unreachable!
      unless !route.isEmpty && route.size == applications.size do
        throwError "the retained parameter action lost its complete ordered route"
      let mut image := receiver
      for (edge, application) in route.zip applications do
        unless closedParameter application && (← isTypeCorrect application) do
          throwError "the retained parameter action has unresolved categorical data"
        let accepted ← Semantic.asFunctor (← Semantic.edgeFunctor state edge)
        let actual ← Semantic.asFunctor application
        unless ← withTransparency .all <| isDefEq accepted actual do
          throwError "the retained parameter action is not its full registered functor"
        image ← Semantic.objOf actual image
      let finalImage ← instantiateMVars image
      unless closedParameter finalImage && (← isTypeCorrect finalImage) &&
          (← withTransparency .all <| isDefEq (← inferType finalImage) (← inferType value)) &&
          (← withTransparency .all <| isDefEq finalImage value) do
        throwError "the retained action changes the parameter's complete bundled object"
      unless ← Decide.kernelAccepts (← mkEq finalImage value) (← mkEqRefl finalImage) do
        throwError "the reduced parameter action failed its complete object identification"
      return ({ receiver, route, applications } : RetainedParameterAction)
    unless candidates.any (fun previous => previous.receiver == candidate.receiver &&
        previous.route == candidate.route && previous.applications == candidate.applications) do
      candidates := candidates.push candidate
  match candidates with
  | #[] => return none
  | #[candidate] => return some candidate
  | _ => throwStratum .ambiguousRealization m!"the reduced parameter retains several distinct accepted source actions"

/-- Encode the checked action through its exact source child. The callbacks retain all
actual computational dependencies, including owners; this helper never reads a cache or
chooses a presentation according to available implementations. -/
def encodeRetainedParameterAction? {Dependency : Type} (trace : Trace) (value : Expr)
    (encodeSource : Expr → TermElabM (Json × Array Dependency))
    (encodeAction : EdgeRef → Expr → TermElabM (Json × Array Dependency))
    (recovering : Array Expr := #[]) :
    TermElabM (Option (Json × Array Dependency)) := do
  if recovering.contains value then
    throwStratum .noImplementation m!"the complete parameter action has cyclic data dependencies"
  let some selected ← retainedParameterAction? trace value | return none
  let (source, sourceDependencies) ← encodeSource selected.receiver
  let mut data := source
  let mut dependencies := sourceDependencies
  for (edge, action) in selected.route.zip selected.applications do
    let (descriptor, actionDependencies) ← encodeAction edge action
    data := Json.mkObj [("ctor", "functorAction"), ("args", Json.arr #[descriptor, data])]
    dependencies := dependencies ++ actionDependencies
  return some (data, dependencies)

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
