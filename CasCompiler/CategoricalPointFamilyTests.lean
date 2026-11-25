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

-- Ordinary list components, their inverse, and their Arrow-induced component retain
-- arbitrary generalized domains. The Arrow case must not require a named category row
-- or a fabricated carrier functor to Sets. Every assertion is on the actual native term.
run_cmd liftTermElabM do
  let state ← semanticState
  let #[unit] := state.cells.filter (·.id == NaturalTransformationId.listUnit)
    | throwError "the independently accepted list unit is absent"
  let #[reverse] := state.cells.filter (·.id == NaturalTransformationId.listReverse)
    | throwError "the independently accepted list reversal is absent"
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
        let some original ← sourceCellComponent? arrow
          | throwError "the component family lost its original native cell envelope"
        unless original.receiver == parameters.back! do
          throwError "the component family replaced its actual selected receiver"
        let (source, target) ← categoricalPointEndpoints arrow
        let some wholeNative ← categoricalPointSource? arrow
          | throwError "the native component did not enter the common point source"
        unless ← isDefEq wholeNative arrow do
          throwError "native component preparation replaced the original arrow"
        let composite := (mkAppN
          (family.family.instantiateLevelParams family.universeParams levels) inputs).headBeta
        let some originalComposite ← categoricalPointSource? composite
          | throwError "the native generalized component did not enter the common source"
        unless ← isDefEq originalComposite composite do
          throwError "native component preparation changed the original preceding map"
        let retained := Expr.mdata (KVMap.empty.setNat `CasCompiler.lower.value 0) arrow
        if (← categoricalPointSource? retained).isSome then
          throwError "an already retained component was reconstructed as a new primitive family"
        let request ← family.withRequest levels parameters arrow domain source target point
        let some retained ← family.request? request
          | throwError "the component lost its complete generalized request"
        unless retained.domain == domain && retained.point == point && retained.arrow == arrow do
          throwError "the component replaced an original generalized-map input"
        let result ← family.mark levels parameters domain request
        checkWithKernel result
        let (resultDomain, resultTarget) ← categoricalPointEndpoints result
        unless ← isDefEq resultDomain domain <&&> isDefEq resultTarget target do
          throwError "the component changed the original generalized domain or target"
        let .mdata data body := result
          | throwError "the component lost its original application marker"
        let restored ← CategoricalPointFamily.fromMark data
        for changed in #[
            data.setName `CasCompiler.source.point.owner ``CategoricalPointOwner.cartesian,
            data.setBool `CasCompiler.source.point.reference true] do
          let rejected ← try
              discard <| CategoricalPointFamily.fromMark changed
              pure false
            catch _ => pure true
          unless rejected do
            throwError "a source component changed its fixed owner or generalized request mode"
        let (actualLevels, actual) ← restored.application body
        unless actualLevels == levels && actual.extract 0 family.parameterCount == parameters &&
            actual[family.parameterCount]? == some domain &&
            actual[family.parameterCount + 1]? == some request do
          throwError "the component did not retain the exact actual source positions"
        let identity ← categoricalPointIdentity bundle source
        let whole ← family.mark levels parameters source identity (whole := true)
        checkWithKernel whole
        unless ← isDefEq whole arrow do
          throwError "the whole component request replaced its actual native arrow"
        let .mdata wholeData wholeBody := whole
          | throwError "the whole component request lost its original native source marker"
        let wholeFamily ← CategoricalPointFamily.fromMark wholeData
        unless wholeFamily.whole do throwError "the whole component became a generalized composite"
        checkWithKernel wholeFamily.family
        let (_, actualWhole) ← wholeFamily.application wholeBody
        unless actualWhole == parameters ++ #[source, identity] do
          throwError "the whole component request replaced an original native input"
        let rejected ← try
            discard <| family.mark levels parameters domain point (whole := true)
            pure false
          catch _ => pure true
        unless rejected do throwError "an arbitrary original point was accepted as the whole arrow"

-- The canonical family transport retains the actual selected base map even under
-- rigid independent source-ring, target-ring and module parameters.
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
      let some original ← sourceCartesian? arrow
        | throwError "the cartesian family lost its original native envelope"
      unless original.entry.id == entry.id && original.receiver == parameters.back! do
        throwError "the cartesian family replaced its reindexing or receiver"
      let explicit ← family.explicitParameters
      let #[baseIndex] := explicit
        | throwError "the original module reindexing changed its actual base-map interface"
      unless original.baseMap == parameters[baseIndex]! do
        throwError "the cartesian family recovered a different base map from its endpoints"
      let some wholeNative ← categoricalPointSource? arrow
        | throwError "the native cartesian arrow did not enter the common point source"
      checkWithKernel wholeNative
      unless ← isDefEq wholeNative arrow do
        throwError "the cartesian whole request replaced the original native lift"
      let result ← family.mark levels parameters inputs[family.parameterCount]!
        inputs[family.parameterCount + 1]!
      checkWithKernel result
      unless result.containsFVar parameters[baseIndex]!.fvarId! do
        throwError "the generalized cartesian request discarded its actual base-map input"

-- A derived action keeps both actual original endpoints and its source arrow as
-- separate inputs. The classifier and constructor cases use the unchanged native
-- action mechanism; no finite published-path inventory bounds their formation.
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
        let marked ← objectFamily.mark levels parameters receiver
        checkWithKernel marked
        let .mdata data body := marked
          | throwError "the object action lost its complete native source witness"
        let restored ← SourceActionFamily.fromMark data
        let (_, original) ← restored.application body
        unless original == inputs do
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
        let result ← family.mark levels parameters domain point
        checkWithKernel result
        let .mdata data body := result
          | throwError "a derived map lost its complete original owner"
        let original ← CategoricalPointFamily.fromMark data
        let (_, actual) ← original.application body
        unless actual.extract family.declarationParameterCount family.parameterCount ==
            parameters.extract family.declarationParameterCount family.parameterCount do
          throwError "a derived map replaced an original input by an equal endpoint"

-- Public field admission checks the original native field, never an arbitrary suffix.
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

-- Binders use their independently accepted complete operation family. The actual
-- bound/range parameters and supplied admitted map remain native source inputs.
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
        let some whole ← categoricalPointSource? arrow
          | throwError "the original binder did not enter the common native source"
        checkWithKernel whole
        unless ← isDefEq whole arrow do
          throwError "the native binder was replaced by another arrow"
        let result ← family.mark levels parameters inputs[family.parameterCount]!
          inputs[family.parameterCount + 1]!
        let .mdata data body := result | throwError "the binder lost its original point marker"
        let restored ← CategoricalPointFamily.fromMark data
        let (_, actual) ← restored.application body
        unless actual == inputs do throwError "the binder changed a complete original parameter"

-- Whole named morphisms and object applications use the same native categorical family;
-- their existing scalar carrier path remains a separately checked consumer of that family.
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
        let whole ← family.mark levels parameters source identity (whole := true)
        checkWithKernel whole
        unless ← isDefEq whole arrow do
          throwError "the whole named request changed the original native map"
        let .mdata data body := whole | throwError "the whole named map lost its source marker"
        let restored ← CategoricalPointFamily.fromMark data
        let (_, original) ← restored.application body
        unless original == parameters ++ #[source, identity] do
          throwError "the whole named map replaced its original complete input slots"
