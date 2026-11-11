module

public import LeanCategories.Catalogue.Registry.Computation
public import CasContract.Registration
public import CasRuntime.GroundedRealizations
import CasContract.Port

@[expose] public section

namespace CasRuntime

open Lean Meta CasCatalogue

private inductive Selection (α : Type)
  | all
  | only (entries : Array α)

private def Selection.contains [DecidableEq α] : Selection α → α → Bool
  | .all, _ => true
  | .only entries, entry => entries.contains entry

private structure ProfileRule where
  target : ComputationRef
  primitives : Selection Registration
  derivations : Selection ComputationDerivationId

/-- Kernel-owned immutable availability sets, fixed before any invocation.
Source: execution contract v2 §5.3, issue 69 comment 6664277464.
The source registry fixes meanings; these sets only filter computational alternatives. -/
structure RealizationProfile where
  private mk ::
  id : String
  normalized : Json
  sha256 : String
  private rules : Array ProfileRule

private def fields (names : Array String) (json : Json) : Except String Unit :=
  CasCatalogue.Backend.checkServiceFields names json |>.mapError ("realization profile: " ++ ·)

private def text (json : Json) (key : String) : Except String String := do
  let value ← json.getObjValAs? String key
  if value.isEmpty then throw s!"realization profile: {key} must be nonempty"
  return value

private def targetJson : ComputationRef → Json
  | .operation id => Json.mkObj [("kind", toJson "operation"), ("id", toJson id.raw)]
  | .functor id => Json.mkObj [("kind", toJson "functor"), ("id", toJson id.raw)]
  | .method id => Json.mkObj [("kind", toJson "method"), ("id", toJson id.raw)]
  | .construction id => Json.mkObj [("kind", toJson "construction"), ("id", toJson id.raw)]
  | .morphism id => Json.mkObj [("kind", toJson "morphism"), ("id", toJson id.raw)]

private def parseTarget (json : Json) : Except String ComputationRef := do
  fields #["kind", "id"] json
  let id ← text json "id"
  match ← text json "kind" with
  | "operation" => return .operation ⟨id⟩
  | "functor" => return .functor ⟨id⟩
  | "method" => return .method ⟨id⟩
  | "construction" => return .construction ⟨id⟩
  | "morphism" => return .morphism ⟨id⟩
  | _ => throw "realization profile: unknown computation target kind"

private def registrationJson (registration : Registration) : Json :=
  Json.mkObj [("operation", toJson registration.operation), ("input", toJson registration.input),
    ("backend", toJson registration.backend)]

private def parseRegistration (json : Json) : Except String Registration := do
  fields #["operation", "input", "backend"] json
  return ⟨← text json "operation", ← text json "input", ← text json "backend"⟩

private def selection [DecidableEq α] (key : String) (parse : Json → Except String α)
    (json : Json) : Except String (Selection α) := do
  match ← text json "mode" with
  | "all" =>
    fields #["mode"] json
    return .all
  | "only" =>
    fields #["mode", key] json
    let values ← (← json.getObjValAs? (Array Json) key).mapM parse
    let mut seen := #[]
    for value in values do
      if seen.contains value then throw "realization profile: duplicate selection entry"
      seen := seen.push value
    return .only values
  | _ => throw "realization profile: selection mode must be all or only"

private def selectionJson (key : String) (encode : α → Json) : Selection α → Json
  | .all => Json.mkObj [("mode", toJson "all")]
  | .only entries => Json.mkObj [("mode", toJson "only"),
      (key, Json.arr ((entries.map encode).qsort fun a b => a.compress < b.compress))]

private def parseRule (json : Json) : Except String ProfileRule := do
  fields #["target", "primitive_registrations", "derivations"] json
  let target ← parseTarget (← json.getObjVal? "target")
  let primitives ← selection "entries" parseRegistration (← json.getObjVal? "primitive_registrations")
  let derivations ← selection "ids" (fun json => do
    let id ← json.getStr?
    if id.isEmpty then throw "realization profile: a derivation ID must be nonempty"
    pure (⟨id⟩ : ComputationDerivationId)) (← json.getObjVal? "derivations")
  return ⟨target, primitives, derivations⟩

private def parseProfile (json : Json) : Except String (String × Array ProfileRule) := do
  fields #["format", "id", "default", "rules"] json
  unless (← text json "format") == "cas-realization-profile/1" do
    throw "realization profile: unsupported format"
  unless (← text json "default") == "all" do
    throw "realization profile: default must be all"
  let id ← text json "id"
  let rules ← (← json.getObjValAs? (Array Json) "rules").mapM parseRule
  let mut seen := #[]
  for rule in rules do
    if seen.contains rule.target then throw "realization profile: duplicate target"
    seen := seen.push rule.target
  return (id, rules.qsort fun a b => (targetJson a.target).compress < (targetJson b.target).compress)

private def normalizedProfile (id : String) (rules : Array ProfileRule) : Json :=
  Json.mkObj [("format", toJson "cas-realization-profile/1"), ("id", toJson id),
    ("default", toJson "all"), ("rules", Json.arr (rules.map fun rule => Json.mkObj [
      ("target", targetJson rule.target),
      ("primitive_registrations", selectionJson "entries" registrationJson rule.primitives),
      ("derivations", selectionJson "ids" (toJson ∘ ComputationDerivationId.raw) rule.derivations)]))]

/-- SHA-256 of immutable configuration text.
Reuse: GNU Coreutils sha256sum through Lean's IO.Process.output stdin API;
https://www.gnu.org/software/coreutils/manual/html_node/sha2-utilities.html. -/
def sha256Hex (text : String) : IO String := do
  let hashed ← IO.Process.output { cmd := "sha256sum", args := #["-"] } (some text)
  unless hashed.exitCode == 0 do throw <| IO.userError s!"SHA-256 failed: {hashed.stderr}"
  let digest := (hashed.stdout.splitOn " ").head!
  unless digest.length == 64 && digest.toList.all (fun c =>
      c.isDigit || ('a' ≤ c && c ≤ 'f')) do
    throw <| IO.userError "SHA-256 returned an invalid digest"
  return digest

/-- Validate exact published targets, installed triples and checked target-specific derivations.
Normalize set order once and retain the SHA-256 of that immutable configuration.
Reuse: ComputationRef.declaration, checkedComputationDerivations, the released registration
schema, the strict field checker and sha256Hex. -/
opaque RealizationProfile.prepare (manifest : Manifest) (configuration : Option Json) :
    MetaM RealizationProfile := do
  let (id, rules) ← match configuration with
    | none => pure ("all", #[])
    | some json => IO.ofExcept (parseProfile json)
  let state ← semanticState
  for rule in rules do
    discard <| rule.target.declaration state
    if let .only entries := rule.primitives then
      for entry in entries do
        unless manifest.registrations.contains entry do
          throwError "realization profile: unknown primitive registration {repr entry}"
    if let .only ids := rule.derivations then
      let checked ← checkedComputationDerivations rule.target
      for id in ids do
        unless checked.any (·.entry.id == id) do
          throwError "realization profile: unknown or wrong-target derivation {id.raw}"
  let normalized := normalizedProfile id rules
  return ⟨id, normalized, ← sha256Hex normalized.compress, rules⟩

/-- Apply the frozen primitive set for this exact source target; unlisted targets allow all. -/
opaque RealizationProfile.allowsPrimitive (profile : RealizationProfile)
    (target : ComputationRef) (registration : Registration) : Bool :=
  match profile.rules.find? (·.target == target) with
  | none => true
  | some rule => rule.primitives.contains registration

/-- Apply the frozen derivation set without changing the checked mathematical plan. -/
opaque RealizationProfile.allowsDerivation (profile : RealizationProfile)
    (entry : ComputationDerivationEntry) : Bool :=
  match profile.rules.find? (·.target == entry.target) with
  | none => true
  | some rule => rule.derivations.contains entry.id

end CasRuntime
