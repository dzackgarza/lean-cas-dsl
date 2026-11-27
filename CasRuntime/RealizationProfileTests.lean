module

import CasRuntime.Realization
import CasCompiler.PublishedPorts
import LeanCategories.Catalogue.Semantics.Algebra.ComputationDerivations
import LeanCategories.Catalogue.Semantics.Foundation.Cardinality
import LeanCategories.Catalogue.Semantics.Foundation.Lists
import LeanCategories.Catalogue.Semantics.ConstructorRegistration
import LeanCategories.Catalogue.Semantics.Modules.CatalogueRegistration
import LeanCategories.Catalogue.Semantics.Algebra.FiniteSums
import LeanCategories.Catalogue.Semantics.Limits.Registration
import LeanCategories.Catalogue.Semantics.Limits.Lifts
public meta import Lean.Elab.Command
meta import CasRuntime.Realization
meta import CasCompiler.PublishedPorts
meta import LeanCategories.Catalogue.Semantics.Algebra.ComputationDerivations
meta import LeanCategories.Catalogue.Semantics.Foundation.Cardinality
meta import LeanCategories.Catalogue.Semantics.Foundation.Lists
meta import LeanCategories.Catalogue.Semantics.ConstructorRegistration
meta import LeanCategories.Catalogue.Semantics.Modules.CatalogueRegistration
meta import LeanCategories.Catalogue.Semantics.Algebra.FiniteSums
meta import LeanCategories.Catalogue.Semantics.Limits.Registration
meta import LeanCategories.Catalogue.Semantics.Limits.Lifts

open Lean Meta CasRuntime CasCatalogue

private def registrationJson (registration : Registration) : Json :=
  Json.mkObj [("operation", toJson registration.operation), ("input", toJson registration.input),
    ("backend", toJson registration.backend)]

private def target (kind id : String) : Json :=
  Json.mkObj [("kind", toJson kind), ("id", toJson id)]

private def only (key : String) (values : Array Json) : Json :=
  Json.mkObj [("mode", toJson "only"), (key, Json.arr values)]

private def all : Json := Json.mkObj [("mode", toJson "all")]

private def rule (target primitives derivations : Json) : Json :=
  Json.mkObj [("target", target), ("primitive_registrations", primitives),
    ("derivations", derivations)]

private def configuration (rules : Array Json) : Json :=
  Json.mkObj [("format", toJson "cas-realization-profile/1"), ("id", toJson "profile-control"),
    ("default", toJson "all"), ("rules", Json.arr rules)]

private def rejected (manifest : Manifest) (json : Json) : MetaM Unit := do
  let rejected ← try
    discard <| RealizationProfile.prepare manifest (some json)
    pure false
  catch _ => pure true
  unless rejected do throwError "an invalid realization profile was admitted"

run_cmd Lean.Elab.Command.liftTermElabM do
  let path : System.FilePath := (← IO.getEnv "CAS_LEAVES").getD ".lake/packages/cas_leaves"
  let path := if path.extension == some "json" then path else path / manifestFile
  let .ok manifest ← Manifest.read path | throwError "the original manifest is unreadable"
  let registrations := manifest.registrations.filter (·.operation == "meth.cardinality")
  unless registrations.size >= 2 do throwError "the original cardinality registrations are missing"
  let cardinality := ComputationRef.method ⟨"meth.cardinality"⟩
  let multiply := ComputationRef.operation ⟨"op.rings.mul"⟩
  let programs ← checkedComputationDerivations multiply
  unless programs.size >= 2 do throwError "the published alternative derivations are missing"
  let some first := programs[0]? | throwError "the first published derivation is missing"
  let some second := programs[1]? | throwError "the second published derivation is missing"
  let selected := first.entry.id
  let other := second.entry.id
  let primitiveRule := rule (target "method" "meth.cardinality")
    (only "entries" #[registrationJson registrations[0]!]) all
  let derivationRule := rule (target "operation" "op.rings.mul") all
    (only "ids" #[toJson selected.raw])
  let frozen ← RealizationProfile.prepare manifest (some (configuration #[primitiveRule, derivationRule]))
  unless frozen.allowsPrimitive cardinality registrations[0]! &&
      !frozen.allowsPrimitive cardinality registrations[1]! &&
      frozen.allowsDerivation first.entry && !frozen.allowsDerivation second.entry do
    throwError "the frozen profile changed exact selected registration or derivation identities"
  unless frozen.normalized == configuration #[primitiveRule, derivationRule] do
    throwError "the existing computation profile changed its normalized encoding"
  let permuted ← RealizationProfile.prepare manifest
    (some (configuration #[derivationRule, primitiveRule]))
  unless frozen.sha256 == permuted.sha256 && frozen.normalized == permuted.normalized &&
      frozen.sha256.length == 64 do
    throwError "profile normalization depends on rule order or lost its SHA-256 receipt"
  let defaultProfile ← RealizationProfile.prepare manifest none
  unless defaultProfile.allowsPrimitive cardinality registrations[1]! &&
      defaultProfile.allowsDerivation first.entry &&
      defaultProfile.allowsDerivation second.entry do
    throwError "the default profile excluded an existing alternative"
  let emptyProfile ← RealizationProfile.prepare manifest (some (configuration #[
    rule (target "method" "meth.cardinality") (only "entries" #[]) all]))
  unless !emptyProfile.allowsPrimitive cardinality registrations[0]! &&
      emptyProfile.allowsDerivation first.entry do
    throwError "an empty only set or an unlisted target changed its meaning"
  rejected manifest (configuration #[primitiveRule, primitiveRule])
  rejected manifest (configuration #[rule (target "method" "meth.cardinality")
    (only "entries" #[registrationJson registrations[0]!, registrationJson registrations[0]!]) all])
  rejected manifest (configuration #[rule (target "method" "meth.cardinality")
    (only "entries" #[registrationJson { registrations[0]! with backend := "unregistered" }]) all])
  rejected manifest (configuration #[rule (target "operation" "op.rings.mul")
    (only "entries" #[registrationJson registrations[0]!]) all])
  rejected manifest (configuration #[rule (target "operation" "op.rings.mul") all
    (only "ids" #[toJson selected.raw, toJson selected.raw])])
  rejected manifest (configuration #[rule (target "method" "meth.cardinality") all
    (only "ids" #[toJson selected.raw])])
  rejected manifest (configuration #[rule (target "operation" "op.rings.mul") all
    (only "ids" #[toJson (other.raw ++ ".unregistered")])])
  rejected manifest (configuration #[rule (target "operation" "unregistered") all all])
  for kind in #["lift", "presentation", "property"] do
    rejected manifest (configuration #[rule (target kind "meth.cardinality") all all])

-- New categorical boundaries use the same frozen exact-registration sets. Their
-- registry owners and canonical addresses cannot be replaced by similar prefixes,
-- another component, or the map port in place of its complete action family.
run_cmd Lean.Elab.Command.liftTermElabM do
  let path : System.FilePath := (← IO.getEnv "CAS_LEAVES").getD ".lake/packages/cas_leaves"
  let path := if path.extension == some "json" then path else path / manifestFile
  let .ok original ← Manifest.read path | throwError "the original manifest is unreadable"
  let some backend := original.backends[0]? | throwError "the original backend inventory is empty"
  let state ← semanticState
  let some binder := state.binders[0]? | throwError "the accepted binder inventory is empty"
  let some limit := state.limits.find? (·.id.raw == "lim.sets.product")
    | throwError "the original product presentation is absent"
  let cell := NaturalTransformationId.listReverse
  let component := CasCompiler.PublishedPorts.componentAddress cell #[]
  let constructed := CasCompiler.PublishedPorts.componentAddress cell #[ConstructorId.arrow]
  let cartesian := FunctorId.modulesReindex.raw ++ "#cartesian"
  let edge : EdgeRef := .constructMap ConstructorId.arrow
    (.constructMap ConstructorId.arrow (.functor FunctorId.setsList))
  let action := "action:" ++ (CasCatalogue.edgeImageDescriptor edge).compress
  let cases : Array (String × String × ProfileTarget × Array String) := #[
    ("limit", limit.id.raw, .limit limit.id, #[limit.id.raw]),
    ("component", cell.raw, .component cell, #[component, constructed]),
    ("cartesian", FunctorId.modulesReindex.raw, .cartesian FunctorId.modulesReindex,
      #[cartesian]),
    ("binder", binder.id.raw, .binder binder.id, #[binder.id.raw]),
    ("edge", action, .edge action, #[action, action ++ "#map"])]
  for (kind, id, owner, addresses) in cases do
    let entries := addresses.map fun operation =>
      ({ operation, input := operation, backend := backend.name } : Registration)
    let manifest := { original with registrations := entries }
    let selected := rule (target kind id) (only "entries" #[registrationJson entries[0]!])
      (only "ids" #[])
    let profile ← RealizationProfile.prepare manifest (some (configuration #[selected]))
    unless profile.normalized == configuration #[selected] &&
        profile.allowsRegistration owner entries[0]! do
      throwError "a categorical profile changed its exact canonical target or selected registration"
    for entry in entries.extract 1 entries.size do
      unless !profile.allowsRegistration owner entry do
        throwError "an unselected categorical primitive remained available"
    for address in addresses do
      unless ← owner.containsAddress state address do
        throwError "a categorical profile rejected an original published family port"
      if ← owner.containsAddress state (address ++ ".unpublished") then
        throwError "a categorical profile accepted an unpublished address suffix"
    rejected manifest (configuration #[rule (target kind (id ++ ".unregistered")) all all])
    rejected manifest (configuration #[rule (target kind id) all
      (only "ids" #[toJson "derive.rings.mul.monoid"])])
  let direct : Registration := { operation := component, input := component, backend := backend.name }
  for suffix in #["#leg", "#apex", "#map"] do
    if ← (ProfileTarget.limit limit.id).containsAddress state (limit.id.raw ++ suffix) then
      throwError "a raw limit profile invented a published projection or application port"
  let otherComponent :=
    CasCompiler.PublishedPorts.componentAddress NaturalTransformationId.listUnit #[]
  let different : Registration := { direct with operation := otherComponent }
  let manifest := { original with registrations := #[direct, different] }
  rejected manifest (configuration #[rule (target "component" cell.raw)
    (only "entries" #[registrationJson different]) all])
  rejected manifest (configuration #[rule (target "edge" (action ++ "#map")) all all])
  rejected manifest (configuration #[rule (target "edge"
    ("action:" ++ (CasCatalogue.edgeImageDescriptor (.functor FunctorId.setsList)).compress)) all all])


-- Universal records have their exact original presentation owner but a distinct
-- complete input. A creation publishes one whole result under its original lift.
-- Neither path manufactures raw #leg/#apex aliases or creation field registrations.
run_cmd Lean.Elab.Command.liftTermElabM do
  let path : System.FilePath := (← IO.getEnv "CAS_LEAVES").getD ".lake/packages/cas_leaves"
  let path := if path.extension == some "json" then path else path / manifestFile
  let .ok original ← Manifest.read path | throwError "the original manifest is unreadable"
  let some backend := original.backends[0]? | throwError "the original backend inventory is empty"
  let state ← semanticState
  for identifier in #["lim.sets.product", "colim.sets.coproduct"] do
    let family ← CasCompiler.LimitUniversalFamily.forId ⟨identifier⟩
    let owner := ProfileTarget.limit family.presentation.entry.id
    let universal : Registration := {
      operation := family.operation, input := family.input, backend := backend.name }
    let raw : Registration := {
      operation := identifier, input := identifier, backend := backend.name }
    let manifest := { original with registrations := #[raw, universal] }
    let (admitted, defects) ← admitManifest manifest
    unless defects.isEmpty && admitted.registrations == manifest.registrations do
      throwError "a declared native universal family was rejected at manifest admission"
    let selected := rule (target "limit" identifier)
      (only "entries" #[registrationJson universal]) (only "ids" #[])
    let frozen ← RealizationProfile.prepare manifest (some (configuration #[selected]))
    unless frozen.normalized == configuration #[selected] &&
        frozen.allowsRegistration owner universal &&
        !frozen.allowsRegistration owner raw &&
        (← owner.containsAddress state family.operation) do
      throwError "universal availability failed to retain its original owner or exact selection"
    for input in #[identifier, identifier ++ "#input", family.operation, "cat.sets"] do
      let invalid := { universal with input }
      let (installed, rejectedRows) ← admitManifest { manifest with registrations := #[invalid] }
      unless installed.registrations.isEmpty && rejectedRows.size == 1 do
        throwError "a universal registration accepted a substituted complete input"
    for suffix in #["#leg", "#apex", "#map", "#isLimit#leg", "#isColimit#apex"] do
      let address := identifier ++ suffix
      if ← owner.containsAddress state address then
        throwError "a limit profile invented an unpublished universal or raw projection"
      if ← publishedOperation state address then
        throwError "manifest operation admission invented a raw limit alias"
    let wrongOwner := if identifier == "lim.sets.product" then
      "colim.sets.coproduct" else "lim.sets.product"
    rejected manifest (configuration #[rule (target "limit" wrongOwner)
      (only "entries" #[registrationJson universal]) all])
  let identifier := "lift.finite_sets.pullbacks"
  let owner := ProfileTarget.lift ⟨identifier⟩
  let creation : Registration := {
    operation := identifier, input := identifier ++ "#input", backend := backend.name }
  let manifest := { original with registrations := #[creation] }
  let (admitted, defects) ← admitManifest manifest
  unless defects.isEmpty && admitted.registrations == #[creation] do
    throwError "the existing creates-limits family has no complete public input"
  let selected := rule (target "lift" identifier)
    (only "entries" #[registrationJson creation]) (only "ids" #[])
  let frozen ← RealizationProfile.prepare manifest (some (configuration #[selected]))
  unless frozen.normalized == configuration #[selected] &&
      frozen.allowsRegistration owner creation &&
      (← owner.containsAddress state identifier) do
    throwError "creation availability changed its original registered lift owner"
  let ports ← CasCompiler.PublishedPorts.forCreation ⟨identifier⟩
  unless ports.size == 1 && ports.all (fun port =>
      port.operation == identifier && port.path.isEmpty) do
    throwError "creation publication advertised independently selected partial results"
  for suffix in #["#liftedCone", "#validLift", "#makesLimit", "#leg", "#apex", "#map"] do
    let invalid := { creation with operation := identifier ++ suffix }
    let (installed, rejectedRows) ← admitManifest { manifest with registrations := #[invalid] }
    unless installed.registrations.isEmpty && rejectedRows.size == 1 &&
        !(← owner.containsAddress state invalid.operation) do
      throwError "creation admission accepted an independently registered result field"
  for input in #[identifier, "cat.finite_sets", "lim.sets.pullback#input"] do
    let (installed, rejectedRows) ← admitManifest
      { manifest with registrations := #[{ creation with input }] }
    unless installed.registrations.isEmpty && rejectedRows.size == 1 do
      throwError "creation admission accepted a substituted native input"
  rejected manifest (configuration #[rule (target "limit" "lim.sets.pullback")
    (only "entries" #[registrationJson creation]) all])
  rejected manifest (configuration #[rule (target "lift" identifier) all
    (only "ids" #[toJson "derive.rings.mul.monoid"])])
