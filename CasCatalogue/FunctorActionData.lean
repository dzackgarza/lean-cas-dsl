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

/-- Read the literal full action and receiver of an object projection. The two
public functor projections have the same selected data; neither is reduced to a
carrier, and transparent wrappers around the whole value do not change its child. -/
def objectAction? (value : Expr) : Option (Expr × Expr) := Id.run do
  let mut selected := Trace.unanchor value.consumeMData
  while selected.isAppOfArity ``id 2 do
    selected := Trace.unanchor selected.appArg!.consumeMData
  if selected.isAppOfArity ``CategoryTheory.Functor.obj 6 then
    return some (selected.getAppArgs[4]!.consumeMData, selected.appArg!)
  if selected.isAppOfArity ``Prefunctor.obj 6 then
    let prefunctor := selected.getAppArgs[4]!.consumeMData
    if prefunctor.isAppOfArity ``CategoryTheory.Functor.toPrefunctor 5 then
      return some (prefunctor.appArg!.consumeMData, selected.appArg!)
  return none

/-- A whole accepted action together with the literal declaration application
that supplies its exact parameters. Fresh unification never replaces that child. -/
structure RegisteredAction where
  edge : EdgeRef
  declarationApplication : Expr
  application : Expr

/-- A directly named action fixes its own presentation before nested occurrences
are considered. Beta reduction, public action projections and outer identity wrappers
preserve the selected declaration arguments as literal source expressions. -/
def directActionDeclaration? (state : RegistryState) (action : Expr) : Option Expr := Id.run do
  let mut selected := Trace.unanchor action.consumeMData.headBeta
  while true do
    if state.functors.any (fun row => selected.getAppFn.constName? == some row.declaration) ||
        state.classifiers.any (fun row => selected.getAppFn.constName? == some row.declaration) then
      return some selected
    if selected.isAppOfArity ``id 2 ||
        selected.isAppOf ``CategoryTheory.Cat.Hom.toFunctor ||
        selected.isAppOf ``LeanCategories.Classifier.forget ||
        selected.isAppOf ``LeanCategories.PropertyClassifier.toClassifier ||
        selected.isAppOf ``LeanCategories.StructureClassifier.toClassifier then
      selected := Trace.unanchor selected.appArg!.consumeMData.headBeta
    else return none
  return none

/-- Identify a declared whole action by a literal complete declaration application.
Every surviving occurrence is checked against the entire functor, not its action
at one object. Distinct parameter presentations are never chosen by traversal order. -/
def registeredAction? (state : RegistryState) (action : Expr) :
    TermElabM (Option RegisteredAction) := do
  let direct := directActionDeclaration? state action
  let mut candidates : Array RegisteredAction := #[]
  for (edge, declaration) in
      (state.functors.map fun row => (EdgeRef.functor row.id, row.declaration)) ++
      (state.classifiers.map fun row => (EdgeRef.classifierForget row.id, row.declaration)) do
    let arity ← forallTelescopeReducing (← getConstInfo declaration).type
      fun fields _ => pure fields.size
    let applications ← IO.mkRef (#[] : Array Expr)
    let collect := fun expression => do
      if expression.getAppFn.constName? == some declaration &&
          expression.getAppNumArgs == arity && closedParameter expression &&
          !(← applications.get).contains expression then
        applications.modify (·.push expression)
    if let some direct := direct then collect direct
    else action.forEach collect
    for declarationApplication in ← applications.get do
      let accepted ← withoutModifyingState do
        unless ← isTypeCorrect declarationApplication do return none
        let application ← match edge with
          | .functor _ => Semantic.asFunctor declarationApplication
          | .classifierForget _ => do
            let mut classifier := declarationApplication
            let type ← whnf (← inferType classifier)
            if type.isAppOf ``LeanCategories.PropertyClassifier then
              classifier ← mkAppM ``LeanCategories.PropertyClassifier.toClassifier #[classifier]
            else if type.isAppOf ``LeanCategories.StructureClassifier then
              classifier ← mkAppM ``LeanCategories.StructureClassifier.toClassifier #[classifier]
            Semantic.asFunctor (← mkAppM ``LeanCategories.Classifier.forget #[classifier])
          | _ => unreachable!
        let sameAction ← withTransparency .all do
            isDefEq (← inferType application) (← inferType action) <&&>
              isDefEq application action
        unless sameAction do return none
        let application ← instantiateMVars application
        unless closedParameter application && (← isTypeCorrect application) do return none
        return some application
      if let some application := accepted then
        candidates := candidates.push { edge, declarationApplication, application }
  match candidates with
  | #[] => return none
  | #[candidate] => return some candidate
  | _ =>
      throwStratum .ambiguousRealization m!"the complete object parameter names several accepted actions"

/-- Decompose a literal composite in its declared order. Each component keeps its
original complete application and parameters; no equality at an object selects it. -/
partial def registeredComposite? (state : RegistryState) (action : Expr) :
    TermElabM (Option (Array RegisteredAction)) := do
  let mut selected := Trace.unanchor action.consumeMData
  while selected.isAppOfArity ``id 2 do
    selected := Trace.unanchor selected.appArg!.consumeMData
  if selected.isAppOfArity ``CategoryTheory.Functor.comp 8 then
    let fields := selected.getAppArgs
    let some first ← registeredComposite? state fields[6]! | return none
    let some second ← registeredComposite? state fields[7]! | return none
    return some (first ++ second)
  let some accepted ← registeredAction? state selected | return none
  return some #[accepted]

/-- Recover only an action of an actual source occurrence in the requested parameter.
The complete bundled result, the full registered functors, and their ordered parameters
are checked before any data callback runs. A complete intermediate image retains its
already selected route prefix. Equal cached objects are never searched.

An explicit object projection fixes its exact receiver and whole action. Other
literal descendants with an equal final carrier are not alternative sources for it.
Different retained actions remain ambiguous even when their values happen to agree at
this object. Only repeated records of exactly the same source and applications coalesce. -/
def retainedParameterAction? (trace : Trace) (value : Expr) :
    TermElabM (Option RetainedParameterAction) := do
  let value ← instantiateMVars value
  unless closedParameter value && (← isTypeCorrect value) do
    throwError "the reduced action parameter is not a closed well-typed value"
  let state ← registryState
  let mut selected := Trace.unanchor value.consumeMData
  while selected.isAppOfArity ``id 2 do
    selected := Trace.unanchor selected.appArg!.consumeMData
  -- A literal named object supplies its own selected presentation. An action
  -- recorded elsewhere cannot replace it merely because the full values agree.
  if state.objects.any (fun row => selected.getAppFn.constName? == some row.declaration) then
    return none
  let explicitAction := objectAction? value
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
    if let some (_, selectedReceiver) := explicitAction then
      unless receiver == selectedReceiver do continue
    let prefixes ← withoutModifyingState do
      unless closedParameter recorded && (← isTypeCorrect recorded) do return #[]
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
      let mut prefixes : Array RetainedParameterAction := #[]
      for ((edge, application), index) in (route.zip applications).zipIdx do
        unless closedParameter application && (← isTypeCorrect application) do
          throwError "the retained parameter action has unresolved categorical data"
        let accepted ← Semantic.asFunctor (← Semantic.edgeFunctor state edge)
        let actual ← Semantic.asFunctor application
        unless ← withTransparency .all <| isDefEq accepted actual do
          throwError "the retained parameter action is not its full registered functor"
        image ← Semantic.objOf actual image
        if ← withTransparency .all <|
            isDefEq (← inferType image) (← inferType value) <&&> isDefEq image value then
          let prefixImage ← instantiateMVars image
          unless closedParameter prefixImage && (← isTypeCorrect prefixImage) &&
              (← Decide.kernelAccepts (← mkEq prefixImage value) (← mkEqRefl prefixImage)) do
            throwError "the retained prefix failed its complete object identification"
          prefixes := prefixes.push {
            receiver
            route := route.extract 0 (index + 1)
            applications := applications.extract 0 (index + 1) }
      if prefixes.isEmpty then return #[]
      let finalImage ← instantiateMVars image
      unless closedParameter finalImage && (← isTypeCorrect finalImage) &&
          (← withTransparency .all <| isDefEq (← inferType finalImage) (← inferType recorded)) &&
          (← withTransparency .all <| isDefEq finalImage recorded) do
        throwError "the retained route changed its complete originally recorded result"
      unless ← Decide.kernelAccepts (← mkEq finalImage recorded) (← mkEqRefl finalImage) do
        throwError "the retained route failed its complete original object identification"
      return prefixes
    for candidate in prefixes do
      if let some (selectedAction, _) := explicitAction then
        let sameAction ← withoutModifyingState do
          let composite ← Semantic.compositeOfApplications candidate.applications
          withTransparency .all do
            isDefEq (← inferType composite) (← inferType selectedAction) <&&>
              isDefEq composite selectedAction
        unless sameAction do continue
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
def encodeRetainedParameterWith? {Data Dependency : Type} (trace : Trace) (value : Expr)
    (encodeSource : Expr → TermElabM (Data × Array Dependency))
    (encodeAction : EdgeRef → Expr → TermElabM (Data × Array Dependency))
    (assemble : Data → Data → TermElabM Data)
    (recovering : Array Expr := #[]) :
    TermElabM (Option (Data × Array Dependency)) := do
  if recovering.contains value then
    throwStratum .noImplementation m!"the complete parameter action has cyclic data dependencies"
  let some selected ← retainedParameterAction? trace value | return none
  let (source, sourceDependencies) ← encodeSource selected.receiver
  let mut data := source
  let mut dependencies := sourceDependencies
  for (edge, action) in selected.route.zip selected.applications do
    let (descriptor, actionDependencies) ← encodeAction edge action
    data ← assemble descriptor data
    dependencies := dependencies ++ actionDependencies
  return some (data, dependencies)

/-- The metadata interface uses the same selected action traversal. Runtime
callers supply an assembly function that also retains exact data ownership. -/
def encodeRetainedParameterAction? {Dependency : Type} (trace : Trace) (value : Expr)
    (encodeSource : Expr → TermElabM (Json × Array Dependency))
    (encodeAction : EdgeRef → Expr → TermElabM (Json × Array Dependency))
    (recovering : Array Expr := #[]) :
    TermElabM (Option (Json × Array Dependency)) :=
  encodeRetainedParameterWith? trace value encodeSource encodeAction
    (fun descriptor data => pure (Json.mkObj [("ctor", "functorAction"),
      ("args", Json.arr #[descriptor, data])])) recovering

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
