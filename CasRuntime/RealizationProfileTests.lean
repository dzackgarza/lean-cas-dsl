module

import CasRuntime.Realization
import LeanCategories.Catalogue.Semantics.Algebra.ComputationDerivations
import LeanCategories.Catalogue.Semantics.Foundation.Cardinality
public meta import Lean.Elab.Command
meta import CasRuntime.Realization
meta import LeanCategories.Catalogue.Semantics.Algebra.ComputationDerivations
meta import LeanCategories.Catalogue.Semantics.Foundation.Cardinality

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
  let some path ← IO.getEnv "CAS_REALIZATION_TEST_MANIFEST"
    | throwError "provide the unchanged original manifest for realization profile controls"
  let .ok manifest ← Manifest.read path | throwError "the original manifest is unreadable"
  let registrations := manifest.registrations.filter (·.operation == "meth.cardinality")
  unless registrations.size >= 2 do throwError "the original cardinality registrations are missing"
  let cardinality := ComputationRef.method ⟨"meth.cardinality"⟩
  let multiply := ComputationRef.operation ⟨"op.rings.mul"⟩
  let programs ← checkedComputationDerivations multiply
  unless programs.size >= 2 do throwError "the published alternative derivations are missing"
  let selected := programs[0]!.entry.id
  let other := programs[1]!.entry.id
  let primitiveRule := rule (target "method" "meth.cardinality")
    (only "entries" #[registrationJson registrations[0]!]) all
  let derivationRule := rule (target "operation" "op.rings.mul") all
    (only "ids" #[toJson selected.raw])
  let frozen ← RealizationProfile.prepare manifest (some (configuration #[primitiveRule, derivationRule]))
  unless frozen.allowsPrimitive cardinality registrations[0]! &&
      !frozen.allowsPrimitive cardinality registrations[1]! &&
      frozen.allowsDerivation programs[0]!.entry && !frozen.allowsDerivation programs[1]!.entry do
    throwError "the frozen profile changed exact selected registration or derivation identities"
  let permuted ← RealizationProfile.prepare manifest
    (some (configuration #[derivationRule, primitiveRule]))
  unless frozen.sha256 == permuted.sha256 && frozen.normalized == permuted.normalized &&
      frozen.sha256.length == 64 do
    throwError "profile normalization depends on rule order or lost its SHA-256 receipt"
  let defaultProfile ← RealizationProfile.prepare manifest none
  unless defaultProfile.allowsPrimitive cardinality registrations[1]! &&
      defaultProfile.allowsDerivation programs[0]!.entry &&
      defaultProfile.allowsDerivation programs[1]!.entry do
    throwError "the default profile excluded an existing alternative"
  let emptyProfile ← RealizationProfile.prepare manifest (some (configuration #[
    rule (target "method" "meth.cardinality") (only "entries" #[]) all]))
  unless !emptyProfile.allowsPrimitive cardinality registrations[0]! &&
      emptyProfile.allowsDerivation programs[0]!.entry do
    throwError "an empty only set or an unlisted target changed its meaning"
  rejected manifest (configuration #[primitiveRule, primitiveRule])
  rejected manifest (configuration #[rule (target "method" "meth.cardinality")
    (only "entries" #[registrationJson registrations[0]!, registrationJson registrations[0]!]) all])
  rejected manifest (configuration #[rule (target "method" "meth.cardinality")
    (only "entries" #[registrationJson { registrations[0]! with backend := "unregistered" }]) all])
  rejected manifest (configuration #[rule (target "operation" "op.rings.mul") all
    (only "ids" #[toJson selected.raw, toJson selected.raw])])
  rejected manifest (configuration #[rule (target "method" "meth.cardinality") all
    (only "ids" #[toJson selected.raw])])
  rejected manifest (configuration #[rule (target "operation" "op.rings.mul") all
    (only "ids" #[toJson (other.raw ++ ".unregistered")])])
  rejected manifest (configuration #[rule (target "operation" "unregistered") all all])
