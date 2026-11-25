module

import CasCompiler.PublishedSource
import LeanCategories.Catalogue
public meta import Lean.Elab.Command
meta import CasCompiler.PublishedSource
meta import LeanCategories.Catalogue

namespace CasCompiler.PublishedCategoricalRequestTests

open Lean Meta Elab Term CasCatalogue CasCatalogue.Backend

-- The public seven-field entrance consumes the complete original native parameter table.
-- No provider is available in this source-only context; every read reference is its exact
-- original local slot, and the returned source retains the arbitrary generalized point.
run_cmd Lean.Elab.Command.liftTermElabM do
  let state ← semanticState
  let #[component] := state.cells.filter (·.id == NaturalTransformationId.listReverse)
    | throwError "the original component is absent"
  let #[cartesian] := state.functors.filter (·.id == FunctorId.modulesReindex)
    | throwError "the original family reindexing is absent"
  let mut owners : Array CategoricalPointOwner := #[
    .component component #[] false, .component component #[] true,
    .component component #[ConstructorId.arrow] false, .cartesian cartesian,
    .action (.functor FunctorId.setsList),
    .action (.classifierForget ClassifierId.setsFinite),
    .action (.constructMap ConstructorId.arrow (.functor FunctorId.setsList))]
  for identifier in #["bind.sets.finite_sum", "bind.sets.finite_product"] do
    let #[entry] := state.binders.filter (·.id.raw == identifier)
      | throwError "the original binder is absent"
    owners := owners.push (.binder entry)
  for owner in owners do
    let family ← CategoricalPointFamily.forOwner owner
    let levels := family.universeParams.map Level.param
    let type := family.familyType.instantiateLevelParams family.universeParams levels
    forallTelescopeReducing type fun inputs _ => do
      let parameters := inputs.extract 0 family.parameterCount
      let domain := inputs[family.parameterCount]!
      let point := inputs[family.parameterCount + 1]!
      let (arrow, _) ← family.arrowAt levels parameters
      let (source, target) ← categoricalPointEndpoints arrow
      let table := inputs ++ #[source, target]
      let reference := fun (index : Nat) =>
        Json.mkObj [("ctor", .str "scopeRef"), ("args", .arr #[toJson index])]
      let publicParameters := (← family.explicitParameters).map reference
      let node := fun (tag : String) (arguments : Array Json) =>
        Json.mkObj [("ctor", toJson tag), ("args", .arr arguments)]
      let (packets, descriptor) ← match owner with
        | .component entry constructors inverse =>
          let receiver := reference family.declarationParameterCount
          let descriptor : ConstructedCellComponent := {
            constructors := constructors.map (·.raw)
            component := { cell := entry.id.raw, parameters := publicParameters, receiver, inverse } }
          pure (#[.arr publicParameters, receiver, toJson inverse],
            if constructors.isEmpty then descriptor.component.encode else descriptor.encode)
        | .cartesian entry =>
          let receiver := reference family.declarationParameterCount
          pure (#[.arr publicParameters, receiver],
            ({ reindex := entry.id.raw, parameters := publicParameters, receiver } : CartesianMap).encode)
        | .binder entry =>
          pure (publicParameters, node entry.id.raw publicParameters)
        | .action edge =>
          let action := routedActionDescriptor edge publicParameters
          let packets := match edge with
            | .functor _ => publicParameters
            | _ => #[action]
          pure (packets, node "map" #[action, TypedMap.encode {
            source := reference family.declarationParameterCount
            target := reference (family.declarationParameterCount + 1)
            callable := reference (family.declarationParameterCount + 2) }])
        | .named owner =>
          pure (publicParameters, node owner.operation publicParameters)
      let packet : PointInvocation := {
        operation := family.operation
        parameters := packets
        arrow := descriptor
        domain := reference family.parameterCount
        source := reference inputs.size
        target := reference (inputs.size + 1)
        argument := reference (family.parameterCount + 1) }
      let bindings := inputs.mapIdx fun index expression =>
        ({ id := ⟨"published-original-native-request", index⟩, role := .parameter, expression } : LocalBinding)
      let unavailable : {α : Type} → MetaM α := fun {_} =>
        throwError "source formation attempted to execute or recover a provider result"
      let context : PublishedSourceContext := {
        scope := ← ContextTelescope.capture bindings
        retained := fun packet => do
          unless (packet.getObjValAs? String "ctor").toOption == some "scopeRef" do
            return none
          let #[position] ← ofExcept <| (packet.getObjVal? "args").bind Json.getArr?
            | throwError "the public reference lost its original positional field"
          let index ← ofExcept <| position.getNat?
          let some value := table[index]?
            | throwError "the public input changed an original source position"
          unless packet == reference index do
            throwError "the public input changed its released reference fields"
          pure (some value)
        literal := fun _ _ => pure none
        bind := pure
        rebind := fun _ value => pure value
        methodParameters := fun _ _ _ => unavailable
        checkInput := fun expected actual => do
          checkRegisteredDomains expected actual
          unless ← isDefEq expected actual do
            throwError "the public input changed its complete native endpoint"
        admitMethod := fun _ _ _ => unavailable
        admitProperty := fun _ _ _ => unavailable
        admitPoint := fun _ _ => unavailable
        admitCategorical := fun _ _ _ => unavailable
        projection := fun _ _ => unavailable }
      let call := fun (packet : PointInvocation) => Json.mkObj [("op", toJson family.operation),
        ("input", toJson family.operation), ("args", packet.encode)]
      let result ← PublishedSource.prepare context (call packet)
      let .mdata data body := result
        | throwError "the public categorical request lost its native source boundary"
      let restored ← CategoricalPointFamily.fromMark data
      let (actualLevels, actual) ← restored.application body
      unless actualLevels == levels && restored.operation == family.operation &&
          actual.extract 0 family.parameterCount == parameters do
        throwError "the public request changed an original declaration parameter position"
      let some retained ← restored.request? actual[family.parameterCount + 1]!
        | throwError "the public request lost its complete generalized request envelope"
      unless retained.domain.equal domain && retained.point.equal point &&
          retained.source.equal source && retained.target.equal target do
        throwError "the public request replaced one of its actual generalized-point fields"
      checkWithKernel (← mkLambdaFVars inputs result (usedOnly := false) (usedLetOnly := false))
      let rejected ← try
          discard <| PublishedSource.prepare context
            (call { packet with target := reference family.parameterCount })
          pure false
        catch _ => pure true
      unless rejected do throwError "the public request accepted a changed native target"

end CasCompiler.PublishedCategoricalRequestTests
