module

import CasCompiler.CategoricalPointSource
import LeanCategories.Catalogue.Semantics.Foundation.Lists
import LeanCategories.Catalogue.Semantics.ConstructorRegistration
import LeanCategories.Catalogue.Semantics.Modules.CatalogueRegistration
import LeanCategories.Catalogue.Semantics.Algebra.FiniteSums
import LeanCategories.Catalogue.Semantics.Algebra.PolynomialPresentations
import LeanCategories.Catalogue.Semantics.Algebra.Polynomials
public meta import Lean.Elab.Command
meta import CasCompiler.CategoricalPointSource
meta import LeanCategories.Catalogue.Semantics.Foundation.Lists
meta import LeanCategories.Catalogue.Semantics.ConstructorRegistration
meta import LeanCategories.Catalogue.Semantics.Modules.CatalogueRegistration
meta import LeanCategories.Catalogue.Semantics.Algebra.FiniteSums
meta import LeanCategories.Catalogue.Semantics.Algebra.PolynomialPresentations
meta import LeanCategories.Catalogue.Semantics.Algebra.Polynomials

open Lean Meta Elab Command CasCatalogue CasCompiler


private def withPointSelection {α : Type} (inputs : Array Expr)
    (selection : SourceSelection Expr)
    (action : OpenContext → SourceSelectionScope Expr → Expr → TermElabM α) :
    TermElabM α := do
  let identities ← CasRuntime.IdentitySupply.new
  let bindings ← inputs.mapM fun expression => do
    let allocated ← identities.fresh .sourceBinding
    return ({ id := ⟨allocated.worker, allocated.serial⟩,
      role := .parameter, expression } : LocalBinding)
  let context ← ContextTelescope.capture bindings
  ({} : SourceSelectionScope Expr).withBinding identities context selection action




run_cmd liftTermElabM do
  let state ← semanticState
  let #[unit] := state.cells.filter (·.id == NaturalTransformationId.listUnit)
    | throwError "the independently accepted list unit is absent"
  let #[reverse] := state.cells.filter (·.id == NaturalTransformationId.listReverse)
    | throwError "the independently accepted list reversal is absent"
  let #[cartesian] := state.functors.filter (·.id == FunctorId.modulesReindex)
    | throwError "the independent incompatible owner fixture is absent"
  let otherOwner ← CategoricalPointFamily.forOwner (.cartesian cartesian)
  for owner in #[CategoricalPointOwner.component unit #[] false,
      .component reverse #[] false, .component reverse #[] true,
      .component reverse #[ConstructorId.arrow] false,
      .component reverse #[ConstructorId.arrow] true] do
    let family ← CategoricalPointFamily.forOwner owner
    checkWithKernel family.family
    checkWithKernel family.arrowFamily
    checkWithKernel family.categoryFamily
    for levels in #[family.universeParams.map (fun _ => Level.zero),
        family.universeParams.map Level.param] do
      let type := family.familyType.instantiateLevelParams family.universeParams levels
      forallTelescopeReducing type fun inputs _ => do
        unless inputs.size == family.parameterCount + 2 do
          throwError "a component lost its complete generalized-map telescope"
        let parameters := inputs.extract 0 family.parameterCount
        let domain := inputs[family.parameterCount]!
        let point := inputs[family.parameterCount + 1]!
        let (arrow, bundle) ← family.arrowAt levels parameters
        let arrowSource ← family.arrowSelection levels parameters
        let some original := arrowSource.cell
          | throwError "the component family lost its original native cell envelope"
        unless original.receiver == parameters.back! do
          throwError "the component family replaced its actual selected receiver"
        let (source, target) ← categoricalPointEndpoints arrow
        withPointSelection inputs arrowSource fun context selections supplied => do
          let some wholeNative ← categoricalPointSource? context selections supplied
            | throwError "the native component did not enter the common point source"
          unless ← isDefEq wholeNative.value arrow do
            throwError "native component preparation replaced the original arrow"
          let identities ← CasRuntime.IdentitySupply.new
          let allocated ← identities.fresh .sourceBinding
          context.withLocalBinding ⟨allocated.worker, allocated.serial⟩ .result
              `retainedComponent (← inferType arrow) fun context retained => do
            if (← categoricalPointSource? context selections retained.expression).isSome then
              throwError "an already retained component was reconstructed as a new primitive family"
        let request ← family.withRequest levels parameters arrow domain source target point
        let some (.categorical selectedFamily retained) := request.pointRequest
          | throwError "the component lost its complete generalized request"
        unless (SelectedApplicationFamily.point family).exactlyMatches (.point selectedFamily) &&
            retained.domain == domain && retained.point == point && retained.arrow == arrow do
          throwError "the component replaced an original generalized-map input"
        let result ← family.selected levels parameters domain request
        let composite := (mkAppN
          (family.family.instantiateLevelParams family.universeParams levels) inputs).headBeta
        withPointSelection inputs result fun context selections supplied => do
          let some originalComposite ← categoricalPointSource? context selections supplied
            | throwError "the native generalized component did not enter the common source"
          unless ← isDefEq originalComposite.value composite do
            throwError "native component preparation changed the original preceding map"
          let some binding := context.bindings.find? (·.expression == supplied)
            | throwError "the component lost its exact original source binder"
          let reference ← family.asReference
          let some originalApplication := result.application
            | throwError "the component lost its original application"
          for changed in #[otherOwner, reference] do
            let changedSelection := { result with
              application := some { originalApplication with family := .point changed } }
            let rejected ← try
                discard <| selections.merge
                  (({} : SourceSelectionScope Expr).insert binding.id changedSelection)
                pure false
              catch _ => pure true
            unless rejected do
              throwError "a source component changed its fixed owner or generalized request mode"
        checkWithKernel result.value
        let (resultDomain, resultTarget) ← categoricalPointEndpoints result.value
        unless ← isDefEq resultDomain domain <&&> isDefEq resultTarget target do
          throwError "the component changed the original generalized domain or target"
        let some (restored, actualLevels, parametersAgain) ←
            CategoricalPointFamily.ofSelection? result
          | throwError "the component lost its original application"
        let some application := result.application
          | throwError "the component lost its original application"
        let actual := parametersAgain ++ application.arguments
        unless (SelectedApplicationFamily.point restored).exactlyMatches (.point family) &&
            actualLevels == levels && actual.extract 0 family.parameterCount == parameters &&
            actual[family.parameterCount]? == some domain &&
            actual[family.parameterCount + 1]? == some request.value do
          throwError "the component did not retain the exact actual source positions"
        let identity ← categoricalPointIdentity bundle source
        let whole ← family.selected levels parameters source { value := identity } (whole := true)
        checkWithKernel whole.value
        unless ← isDefEq whole.value arrow do
          throwError "the whole component request replaced its actual native arrow"
        let some (wholeFamily, _, originalParameters) ← CategoricalPointFamily.ofSelection? whole
          | throwError "the whole component request lost its original native source"
        unless wholeFamily.whole do throwError "the whole component became a generalized composite"
        checkWithKernel wholeFamily.family
        let some wholeApplication := whole.application
          | throwError "the whole component request lost its original native application"
        unless originalParameters ++ wholeApplication.arguments == parameters ++ #[source, identity] do
          throwError "the whole component request replaced an original native input"
        let rejected ← try
            discard <| family.selected levels parameters domain { value := point } (whole := true)
            pure false
          catch _ => pure true
        unless rejected do throwError "an arbitrary original point was accepted as the whole arrow"



run_cmd liftTermElabM do
  let #[entry] := (← semanticState).functors.filter (·.id == FunctorId.modulesReindex)
    | throwError "the independently accepted module reindexing is absent"
  let family ← CategoricalPointFamily.forOwner (.cartesian entry)
  checkWithKernel family.family
  checkWithKernel family.arrowFamily
  checkWithKernel family.categoryFamily
  for levels in #[family.universeParams.map (fun _ => Level.zero),
      family.universeParams.map Level.param] do
    let type := family.familyType.instantiateLevelParams family.universeParams levels
    forallTelescopeReducing type fun inputs _ => do
      let parameters := inputs.extract 0 family.parameterCount
      let (arrow, _) ← family.arrowAt levels parameters
      let arrowSource ← family.arrowSelection levels parameters
      let some original := arrowSource.cartesian
        | throwError "the cartesian family lost its original native envelope"
      unless original.entry.id == entry.id && original.receiver == parameters.back! do
        throwError "the cartesian family replaced its reindexing or receiver"
      let explicit ← family.explicitParameters
      let #[baseIndex] := explicit
        | throwError "the original module reindexing changed its actual base-map interface"
      unless original.baseMap == parameters[baseIndex]! do
        throwError "the cartesian family recovered a different base map from its endpoints"
      withPointSelection inputs arrowSource fun context selections supplied => do
        let some wholeNative ← categoricalPointSource? context selections supplied
          | throwError "the native cartesian arrow did not enter the common point source"
        checkWithKernel wholeNative.value
        unless ← isDefEq wholeNative.value arrow do
          throwError "the cartesian whole request replaced the original native lift"
      let result ← family.selected levels parameters inputs[family.parameterCount]!
        { value := inputs[family.parameterCount + 1]! }
      checkWithKernel result.value
      unless result.value.containsFVar parameters[baseIndex]!.fvarId! do
        throwError "the generalized cartesian request discarded its actual base-map input"




run_cmd liftTermElabM do
  for edge in #[EdgeRef.functor FunctorId.setsList,
      .classifierForget ClassifierId.setsFinite,
      .constructMap ConstructorId.arrow (.functor FunctorId.setsList)] do
    let objectFamily ← SourceActionFamily.forEdge edge
    checkWithKernel objectFamily.family
    for levels in #[objectFamily.universeParams.map (fun _ => Level.zero),
        objectFamily.universeParams.map Level.param] do
      forallTelescopeReducing
          (objectFamily.familyType.instantiateLevelParams objectFamily.universeParams levels)
          fun inputs _ => do
        let parameters := inputs.extract 0 objectFamily.parameterCount
        let receiver := inputs[objectFamily.parameterCount]!
        let selected ← objectFamily.selected levels parameters receiver
        checkWithKernel selected.value
        let some (restored, actualLevels, originalParameters, originalReceiver) ←
            SourceActionFamily.ofSelection? selected
          | throwError "the object action lost its complete native source witness"
        unless (SelectedApplicationFamily.objectAction restored).exactlyMatches
            (.objectAction objectFamily) && actualLevels == levels &&
            originalParameters.push originalReceiver == inputs do
          throwError "the canonical object action changed an original parameter or receiver"
    let family ← CategoricalPointFamily.forOwner (.action edge)
    checkWithKernel family.family
    checkWithKernel family.arrowFamily
    checkWithKernel family.categoryFamily
    for levels in #[family.universeParams.map (fun _ => Level.zero),
        family.universeParams.map Level.param] do
      let type := family.familyType.instantiateLevelParams family.universeParams levels
      forallTelescopeReducing type fun inputs _ => do
        unless family.parameterCount == family.declarationParameterCount + 3 do
          throwError "a derived map discarded its actual source, target or arrow input"
        let parameters := inputs.extract 0 family.parameterCount
        let domain := inputs[family.parameterCount]!
        let point := inputs[family.parameterCount + 1]!
        let result ← family.selected levels parameters domain { value := point }
        checkWithKernel result.value
        let some (original, actualLevels, actualParameters) ←
            CategoricalPointFamily.ofSelection? result
          | throwError "a derived map lost its complete original owner"
        let some application := result.application
          | throwError "a derived map lost its complete original input table"
        let actual := actualParameters ++ application.arguments
        unless (SelectedApplicationFamily.point original).exactlyMatches (.point family) &&
            actualLevels == levels &&
            actual.extract family.declarationParameterCount family.parameterCount ==
            parameters.extract family.declarationParameterCount family.parameterCount do
          throwError "a derived map replaced an original input by an equal endpoint"


run_cmd liftTermElabM do
  let state ← semanticState
  unless (← PublishedPorts.family? state "fun.sets.list#map") == some (.functor FunctorId.setsList) do
    throwError "the public list map lost its accepted native family"
  if (← PublishedPorts.family? state "fun.sets.list#invented").isSome then
    throwError "an unregistered suffix acquired a native operation"
  let failed ← try
      let #[entry] := state.cells.filter (·.id == NaturalTransformationId.listUnit)
        | throwError "the original noninvertible cell is absent"
      discard <| CategoricalPointFamily.forOwner (.component entry #[] true)
      pure false
    catch error =>
      unless CasCatalogue.Exception.stratum? error == some .invalid do throw error
      pure true
  unless failed do throwError "a noninvertible native component acquired an inverse"



run_cmd liftTermElabM do
  for id in #["bind.sets.finite_sum", "bind.sets.finite_product"] do
    let #[entry] := (← semanticState).binders.filter (·.id.raw == id)
      | throwError "the original finite binder is absent"
    let family ← CategoricalPointFamily.forOwner (.binder entry)
    checkWithKernel family.family
    checkWithKernel family.arrowFamily
    for levels in #[family.universeParams.map (fun _ => Level.zero),
        family.universeParams.map Level.param] do
      forallTelescopeReducing
          (family.familyType.instantiateLevelParams family.universeParams levels) fun inputs _ => do
        let parameters := inputs.extract 0 family.parameterCount
        let (arrow, _) ← family.arrowAt levels parameters
        let arrowSource ← family.arrowSelection levels parameters
        withPointSelection inputs arrowSource fun context selections supplied => do
          let some whole ← categoricalPointSource? context selections supplied
            | throwError "the original binder did not enter the common native source"
          checkWithKernel whole.value
          unless ← isDefEq whole.value arrow do
            throwError "the native binder was replaced by another arrow"
        let result ← family.selected levels parameters inputs[family.parameterCount]!
          { value := inputs[family.parameterCount + 1]! }
        let some (restored, actualLevels, actualParameters) ←
            CategoricalPointFamily.ofSelection? result
          | throwError "the binder lost its original point selection"
        let some application := result.application
          | throwError "the binder lost its original application inputs"
        unless (SelectedApplicationFamily.point restored).exactlyMatches (.point family) &&
            actualLevels == levels && actualParameters ++ application.arguments == inputs do
          throwError "the binder changed a complete original parameter"



run_cmd liftTermElabM do
  let state ← semanticState
  let mut owners : Array PointFamilyOwner := #[]
  for declaration in #[
      ``CasCatalogue.Algebra.PolynomialPresentations.firstConstants,
      ``CasCatalogue.Algebra.PolynomialPresentations.secondConstants] do
    let #[entry] := state.morphisms.filter (·.declaration == declaration)
      | throwError "the original named map fixture is absent"
    owners := owners.push (.morphism entry)
  let #[application] := state.objects.filter (·.id.raw == "obj.sets.polynomials")
    | throwError "the original polynomial application is absent"
  owners := owners.push (.application application)
  for owner in owners do
    let family ← CategoricalPointFamily.forOwner (.named owner)
    unless family.operation == owner.operation do
      throwError "the whole named map acquired another public operation"
    checkWithKernel family.family
    checkWithKernel family.arrowFamily
    checkWithKernel family.categoryFamily
    for levels in #[family.universeParams.map (fun _ => Level.zero),
        family.universeParams.map Level.param] do
      forallTelescopeReducing
          (family.familyType.instantiateLevelParams family.universeParams levels) fun inputs _ => do
        let parameters := inputs.extract 0 family.parameterCount
        let (arrow, bundle) ← family.arrowAt levels parameters
        let (source, _) ← categoricalPointEndpoints arrow
        let identity ← categoricalPointIdentity bundle source
        let whole ← family.selected levels parameters source { value := identity } (whole := true)
        checkWithKernel whole.value
        unless ← isDefEq whole.value arrow do
          throwError "the whole named request changed the original native map"
        let some (restored, actualLevels, originalParameters) ←
            CategoricalPointFamily.ofSelection? whole
          | throwError "the whole named map lost its source selection"
        let some application := whole.application
          | throwError "the whole named map lost its original native inputs"
        unless restored.whole && actualLevels == levels &&
            originalParameters ++ application.arguments == parameters ++ #[source, identity] do
          throwError "the whole named map replaced its original complete input slots"
