module

public import LeanCategories.Catalogue.Registry.Computation
public import CasContract.Registration
public import CasContract.Failure
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

/-- A registration's record: its triple, and its declared preferred routes when it has any
(contract api/manifest.md). -/
private def registrationJson (registration : Registration) : Json :=
  let triple := [("operation", toJson registration.operation),
    ("input", toJson registration.input), ("backend", toJson registration.backend)]
  if registration.preferredRoutes.isEmpty then Json.mkObj triple
  else Json.mkObj (triple ++ [("preferredRoutes", .arr (registration.preferredRoutes.map fun route =>
    Json.mkObj [("name", toJson route.name), ("receiver", toJson route.receiver),
      ("route", toJson route.route)]))])

private def parseRegistration (json : Json) : Except String Registration := do
  let preferredRoutes ← match json.getObjVal? "preferredRoutes" with
    | .error _ => do fields #["operation", "input", "backend"] json; pure #[]
    | .ok _ => do
      fields #["operation", "input", "backend", "preferredRoutes"] json
      (← Manifest.arrayField json "preferredRoutes").mapM Manifest.preferredRouteOf
        |>.mapError ("realization profile: " ++ ·)
  let operation ← text json "operation"
  let input ← text json "input"
  let backend ← text json "backend"
  return { operation, input, backend, preferredRoutes }

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

def referenceId : ComputationRef → String
  | .operation id => id.raw
  | .functor id => id.raw
  | .method id => id.raw
  | .construction id => id.raw
  | .morphism id => id.raw

/-- Select the registration of one exact lift-port demand. **M** publishes no derivation of a
lift's computation, so the alternatives are the eligible registrations (execution contract v2
§5.1); zero and many dispatch nothing. -/
def selectLift (manifest : Manifest) (address : String) (forms : Array String) :
    MetaM Registration := do
  let eligible := manifest.registrations.filter fun registration =>
    registration.operation == address && forms.contains registration.input &&
      manifest.backends.any (·.name == registration.backend)
  match eligible with
  | #[registration] => return registration
  | #[] => throwStratum .noImplementation m!"{address} on {forms}"
  | _ => throwStratum .ambiguousRealization m!"{address} on {forms}"

inductive Realization
  | registration (selected : Registration)
  | derivation (checked : CheckedComputationDerivation)

/-- Select the realization of one exact demand by the saturated grounded count.
Source: execution contract v2 §5.1 and §5.2. The root alternatives are the eligible
registrations and the profile's checked derivations. A prerequisite is a delayed demand: an
installed registration or a grounded derivation makes it present, and its own realization is
selected when its actual arguments exist. Zero and many dispatch nothing.
Reuse: RealizationGraph.grounded and GroundedRealizations.uniqueAlternative. -/
private def selectBoundaries (profile : RealizationProfile) (manifest : Manifest)
    (reference : ComputationRef) (address : String) (boundaries : Array (Array String)) :
    MetaM (Nat × Realization) := do
  if boundaries.isEmpty then throwError "realization selection requires a complete source boundary"
  let eligible := (boundaries.mapIdx fun index forms =>
    (manifest.registrations.filter fun registration =>
      registration.operation == address && forms.contains registration.input &&
        manifest.backends.any (·.name == registration.backend) &&
        profile.allowsPrimitive reference registration).map (index, ·)).flatten
  let forms := boundaries.flatten
  let mut nodes : Array ComputationRef := #[reference]
  let mut derivations : Array (Array CheckedComputationDerivation) := #[]
  let mut next := 0
  while next < nodes.size do
    let some node := nodes[next]? | break
    let checked := (← checkedComputationDerivations node).filter fun derivation =>
      profile.allowsDerivation derivation.entry
    for derivation in checked do
      for prerequisite in derivation.prerequisites do
        unless nodes.contains prerequisite.reference do nodes := nodes.push prerequisite.reference
    derivations := derivations.push checked
    next := next + 1
  let size := nodes.size
  let present := fun (node : ComputationRef) =>
    manifest.registrations.any fun registration =>
      (registration.operation == referenceId node ||
        registration.operation.startsWith s!"{referenceId node}#") &&
        profile.allowsPrimitive node registration
  let rows : Array (Array (Array Nat)) := nodes.mapIdx fun index node =>
    let primitive : Array (Array Nat) :=
      if index == 0 then eligible.map fun _ => #[]
      else if present node then #[#[]] else #[]
    primitive ++ (derivations[index]?.getD #[]).map fun derivation =>
      derivation.prerequisites.filterMap fun prerequisite =>
        nodes.findIdx? (· == prerequisite.reference)
  let graph : RealizationGraph size := ⟨Vector.ofFn fun node =>
    (rows[node.val]?.getD #[]).map fun children =>
      children.filterMap fun child => if bound : child < size then some ⟨child, bound⟩ else none⟩
  let some grounded := graph.grounded
    | throwError "internal: the realization grounding did not stabilize"
  if root : 0 < size then
    match ← IO.ofExcept <| (grounded.uniqueAlternative ⟨0, root⟩).mapError IO.userError with
    | some alternative =>
      if let some (boundary, registration) := eligible[alternative]? then
        return (boundary, .registration registration)
      let some derivation := (derivations[0]?.getD #[])[alternative - eligible.size]?
        | throwError "internal: the selected realization is outside its alternatives"
      return (boundaries.size - 1, .derivation derivation)
    | none =>
      if grounded.counts[(⟨0, root⟩ : Fin size)] == .zero then
        throwStratum .noImplementation m!"{address} on {forms}"
      throwStratum .ambiguousRealization m!"{address} on {forms}"
  else throwError "internal: the realization graph has no root demand"


/-- One exact native demand uses the same saturated grounded selection as routed methods. -/
opaque RealizationProfile.select (profile : RealizationProfile) (manifest : Manifest)
    (reference : ComputationRef) (address : String) (forms : Array String) : MetaM Realization := do
  return (← selectBoundaries profile manifest reference address #[forms]).2

/-- Count every admitted registration at every exact route boundary before executing a prefix.
Two occurrences of one registration at different boundaries are distinct alternatives; a source
or category-wide row has no priority. A checked derivation belongs to the owner boundary.
Reuse: the same grounded realization graph and frozen profile as ordinary source demands. -/
opaque RealizationProfile.selectMethod (profile : RealizationProfile) (manifest : Manifest)
    (method : MethodId) (boundaries : Array (Array String)) : MetaM (Nat × Realization) :=
  selectBoundaries profile manifest (.method method) method.raw boundaries

end CasRuntime
