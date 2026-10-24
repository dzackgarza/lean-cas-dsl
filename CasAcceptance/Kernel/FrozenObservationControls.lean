/- Copyright (c) 2026 Dzack Garza. Released under Apache 2.0 license. -/
module

import CasCatalogue.QuestionComparison
meta import CasCatalogue.QuestionComparison
import CasCatalogue.FileItems
meta import CasCatalogue.FileItems
import LeanCategories.Catalogue.Semantics.Independent.ScalarAndFormExtensions
meta import LeanCategories.Catalogue.Semantics.Independent.ScalarAndFormExtensions

/-! Optional engineering observations of the independently supplied frozen inputs.
The four resolution environments are explicit immutable selections of already accepted
rows, passed to the existing public resolver. They register no new mathematics. The negative
admission input is read unchanged, and its actual typed diagnostic is compared with the
independent theorem's exact obligation; a parser error cannot satisfy that observation.

Run against the integrated dependency tuple, from the repository root:
`lake env lean CasAcceptance/Kernel/FrozenObservationControls.lean`.
Set `CAS_EXTENSION_CONTROL_REPORT` to retain the complete typed-term observation JSON.
`CAS_EXTENSION_CONTROL=RX05` or `RX09` selects one engineering control; the default runs both. -/

open Lean Meta Elab Term CategoryTheory CasCatalogue CasCatalogue.Language

meta section

private def selectionOrder (state : RegistryState) : RegistryState :=
  { state with
    cells := state.cells.reverse
    methods := state.methods.reverse
    functors := state.functors.reverse
    classifiers := state.classifiers.reverse
    categories := state.categories.reverse }

private def resolutionKey (resolution : Resolution) : String :=
  reprStr resolution.method ++ reprStr resolution.route.source ++
    reprStr resolution.route.target ++
    reprStr (resolution.route.steps.map fun edge => (edge.source, edge.target, edge.ref)) ++
    reprStr (resolution.comparisons.qsort (fun a b => a.raw < b.raw)) ++
    reprStr (resolution.comparisonWitnesses.map reprStr |>.qsort (· < ·)) ++
    reprStr resolution.lifts

private def requestTerms (state : RegistryState) (receiver : Expr)
    (resolution : Resolution) : TermElabM (Array Expr) := do
  let (route, applications) ← Semantic.routeFunctorWithApplications state resolution.route.refs
  let image ← Semantic.objOf route receiver
  let some row := state.functor? resolution.method.functor
    | throwError "the selected method lost its accepted functor"
  let operation ← registeredFunctorInstance row
  let input ← methodArgument resolution.method image
  let result ← Semantic.objOf operation input
  let comparisons ← Semantic.validateResolutionComparisons state resolution (some receiver)
  let mut terms := #[receiver, route] ++ applications ++ #[image, operation, input, result]
  for comparison in comparisons do
    let hom ← mkAppM ``CategoryTheory.Iso.hom #[comparison]
    let inverse ← mkAppM ``CategoryTheory.Iso.inv #[comparison]
    let forward ← mkAppM ``CategoryTheory.NatTrans.app #[hom, receiver]
    let backward ← mkAppM ``CategoryTheory.NatTrans.app #[inverse, receiver]
    terms := terms ++ #[comparison, forward, backward]
  terms ← terms.mapM instantiateMVars
  discard <| QuestionIdentity.questionTypes terms #[]
  return terms

private def termRecord (terms : Array Expr) (labels : Array String := #[]) : TermElabM Json := do
  unless labels.isEmpty || labels.size == terms.size do
    throwError "the typed-term observation labels do not match its ordered values"
  let table ← Realize.TermTable.new
  let types ← QuestionIdentity.questionTypes terms #[]
  let values ← terms.mapM table.encode
  let types ← types.mapM table.encode
  let text ← table.finish (Json.mkObj [
    ("values", toJson values), ("types", toJson types), ("labels", toJson labels)])
  let .ok result := Json.parse text | throwError "the typed-term observation failed to encode"
  return result

private def requestLabels (resolution : Resolution) : Array String :=
  #["receiver", "routeFunctor"] ++
    resolution.route.steps.zipIdx.map (fun (step, index) => s!"routeStep[{index}]:{step.ref.label}") ++
    #["routeImage", "operationFunctor", "operationInput", "operationResult"] ++
    resolution.comparisonWitnesses.zipIdx.flatMap (fun (witness, index) =>
      #[s!"comparison[{index}]:{witness.cell.raw}", s!"forwardComponent[{index}]",
        s!"inverseComponent[{index}]"])

private def resolutionRecord (resolution : Resolution) : Json :=
  Json.mkObj [
    ("method", toJson (reprStr resolution.method)),
    ("source", toJson (reprStr resolution.route.source)),
    ("target", toJson (reprStr resolution.route.target)),
    ("steps", Json.arr (resolution.route.steps.map fun step => Json.mkObj [
      ("ref", toJson (reprStr step.ref)), ("source", toJson (reprStr step.source)),
      ("target", toJson (reprStr step.target)), ("expression", toJson (reprStr step.expression))])),
    ("comparisons", toJson (resolution.comparisons.map (·.raw))),
    ("comparisonWitnesses", Json.arr (resolution.comparisonWitnesses.map fun witness =>
      Json.mkObj [("cell", toJson witness.cell.raw),
        ("constructors", toJson (witness.constructors.map (·.raw))),
        ("before", toJson (witness.before.map reprStr)),
        ("after", toJson (witness.after.map reprStr))])),
    ("lifts", toJson (resolution.lifts.map (·.raw)))]

private def selectedInventory (state : RegistryState) : Json :=
  Json.mkObj [
    ("rows", Json.arr (state.registryEntries.toArray.map fun row => Json.mkObj [
      ("id", toJson row.stableId), ("declarations", toJson (row.declarations.map Name.toString)),
      ("completeMetadata", toJson (reprStr row))])),
    ("cells", Json.arr (state.cells.map fun cell => Json.mkObj [
      ("id", toJson cell.id.raw), ("declaration", toJson cell.declaration.toString),
      ("source", toJson (reprStr cell.source)), ("target", toJson (reprStr cell.target)),
      ("left", toJson (cell.left.map reprStr)), ("right", toJson (cell.right.map reprStr)),
      ("invertible", toJson cell.invertible)]))]

private def observeCarrierEnvironments : TermElabM Json := do
  let state ← registryState
  let some rings := state.categories.find? (·.id.raw == "cat.rings")
    | throwError "the independently selected ring category is absent"
  let some carrier := state.cells.find? (·.id.raw == "cmp.rings.carrier")
    | throwError "the independently selected ring carrier comparison is absent"
  let multiplicative : Array EdgeRef := #[.functor FunctorId.ringsMultiplicative,
    .functor FunctorId.monoidsSemigroup, .classifierForget ClassifierId.magmasAssociative,
    .classifierForget ClassifierId.setsBinaryOperation]
  let additive : Array EdgeRef := #[.functor FunctorId.ringsAdditive,
    .functor FunctorId.additiveGroupsToGroups, .functor FunctorId.groupsMonoid,
    .functor FunctorId.monoidsSemigroup, .classifierForget ClassifierId.magmasAssociative,
    .classifierForget ClassifierId.setsBinaryOperation]
  unless carrier.left == multiplicative && carrier.right == additive do
    throwError "the actual comparison changed its independently specified directed routes"
  let selectedProof ← elabTermAndSynthesize
    (← `(CasCatalogue.Algebra.PrimeResidueFields.underlying_ring 5 (by decide))) none
  let selectedType ← inferType selectedProof
  unless selectedType.isAppOfArity ``Eq 3 do
    throwError "the independent selected-ring theorem changed its public proposition"
  let receiver := selectedType.getAppArgs[1]!
  let oldRing := selectedType.getAppArgs[2]!
  unless ← isDefEq receiver oldRing do
    throwError "the selected prime residue field lost its existing forgotten ring"
  let coherent (selected : RegistryState) : TermElabM (Resolution × Array Expr) := do
    let .ok resolution := selected.resolveMethod rings.expression "cardinality"
      | throwError "a supplied coherent declaration environment did not resolve"
    unless resolution.comparisons.contains carrier.id &&
        resolution.comparisonWitnesses.any (fun witness =>
          witness.cell == carrier.id && witness.constructors.isEmpty &&
          witness.before.isEmpty && witness.after.isEmpty) do
      throwError "the cardinality request lost the complete actual carrier-cell witness"
    return (resolution, ← requestTerms selected receiver resolution)
  let (normal, normalTerms) ← coherent state
  let reordered := selectionOrder state
  let (reversed, reversedTerms) ← coherent reordered
  let coherentMetadataEqual := resolutionKey normal == resolutionKey reversed
  let coherentTermsEquivalent ← QuestionIdentity.equivalentTerms normalTerms reversedTerms
  unless coherentMetadataEqual && coherentTermsEquivalent do
    throwError "reordering the same coherent declarations changed the full selected request"
  -- Keep every other accepted route and cell. The historical three-route count
  -- predates the additive-group -> additive-monoid edge and its carrier comparison.
  -- The public complete-route inventory determines which candidates must survive;
  -- this control checks retention and ordering, not a second route enumerator.
  let absent := { state with cells := state.cells.filter (·.id != carrier.id) }
  let same (left right : Resolution × Array Expr) : TermElabM Bool := do
    unless resolutionKey left.1 == resolutionKey right.1 do return false
    QuestionIdentity.equivalentTerms left.2 right.2
  let candidateRecord (candidate : Resolution × Array Expr) : TermElabM Json := do
    let (resolution, terms) := candidate
    return Json.mkObj [("resolution", resolutionRecord resolution),
      ("typedRequest", ← termRecord terms (requestLabels resolution))]
  let candidates (selected : RegistryState) :
      TermElabM (Array (Resolution × Array Expr) × Array (Resolution × Array Expr)) := do
    let mut inventory : Array (Resolution × Array Expr) := #[]
    for method in selected.methods.filter (·.name == "cardinality") do
      let .ok routes := selected.completeRoutes rings.expression method.owner
        | throwError "the selected registry's complete route inventory did not close"
      for route in routes do
        let resolution : Resolution := { method, route }
        inventory := inventory.push (resolution, ← requestTerms selected receiver resolution)
    let .error (.ambiguous _ resolutions) :=
      selected.resolveMethod rings.expression "cardinality"
      | throwError "the absent-cell declaration environment did not retain ambiguity"
    unless resolutions.any (·.route.refs == multiplicative) &&
        resolutions.any (·.route.refs == additive) do
      throwError "the absent-cell environment lost a complete competing route"
    let actual ← resolutions.mapM fun resolution => do
      return (resolution, ← requestTerms selected receiver resolution)
    unless ← QuestionIdentity.equivalentUnordered same inventory actual do
      throwError "the ambiguity did not retain the complete selected-registry candidate inventory"
    return (actual, inventory)
  let (first, firstInventory) ← candidates absent
  let absentReordered := selectionOrder absent
  let (second, secondInventory) ← candidates absentReordered
  let candidatesEquivalent ← QuestionIdentity.equivalentUnordered same first second
  unless candidatesEquivalent do
    throwError "reordering absent-cell declarations changed the complete ambiguity candidates"
  let inventoriesEquivalent ←
    QuestionIdentity.equivalentUnordered same firstInventory secondInventory
  unless inventoriesEquivalent do
    throwError "reordering declarations changed the complete applicable registry inventory"
  let receiverRecord : TermElabM Json :=
    termRecord #[receiver, oldRing] #["selectedForgottenRing", "existingResidueRing"]
  let coherentRecord (name : String) (selected : RegistryState)
      (resolution : Resolution) (terms : Array Expr) : TermElabM Json := do
    return Json.mkObj [
      ("environment", toJson name), ("resolutionKind", "resolved"),
      ("selectedInventory", selectedInventory selected), ("typedReceiver", ← receiverRecord),
      ("resolution", resolutionRecord resolution),
      ("typedRequest", ← termRecord terms (requestLabels resolution))]
  let ambiguousRecord (name : String) (selected : RegistryState)
      (candidates inventory : Array (Resolution × Array Expr)) : TermElabM Json := do
    let records ← candidates.mapM candidateRecord
    let inventory ← inventory.mapM candidateRecord
    return Json.mkObj [
      ("environment", toJson name), ("resolutionKind", "ambiguous"),
      ("selectedInventory", selectedInventory selected), ("typedReceiver", ← receiverRecord),
      ("candidates", Json.arr records), ("registryApplicableCandidates", Json.arr inventory),
      ("completeRegistryInventoryRetained", toJson true)]
  return Json.mkObj [
    ("control", "RX05"),
    ("environments", Json.arr #[
      ← coherentRecord "present" state normal normalTerms,
      ← coherentRecord "present-reversed" reordered reversed reversedTerms,
      ← ambiguousRecord "absent" absent first firstInventory,
      ← ambiguousRecord "absent-reversed" absentReordered second secondInventory]),
    ("crossEnvironmentChecks", Json.mkObj [
      ("presentResolutionMetadataEqual", toJson coherentMetadataEqual),
      ("presentCompleteTypedRequestsEquivalent", toJson coherentTermsEquivalent),
      ("absentCompleteCandidatesEquivalentAsMultisets", toJson candidatesEquivalent),
      ("registryApplicableInventoriesEquivalentAsMultisets", toJson inventoriesEquivalent)])]

/-- Inspect expressions in the real diagnostic, including lazily formatted expressions.
The values come from Lean's typed info nodes, not from matching a printed error string. -/
private partial def diagnosticTerms (naming : NamingContext)
    (context : Option MessageDataContext) : MessageData → BaseIO (Array Expr)
  | .ofFormatWithInfos value =>
      return value.infos.toArray.filterMap fun (_, info) =>
        match info with
        | .ofTermInfo term => some term.expr
        | .ofDelabTermInfo term => some term.expr
        | _ => none
  | .withContext selected body => diagnosticTerms naming (some selected) body
  | .withNamingContext selected body => diagnosticTerms selected context body
  | .ofWidget _ body | .nest _ body | .group body | .tagged _ body |
      .ofOriginatingSyntax _ body => diagnosticTerms naming context body
  | .compose left right =>
      return (← diagnosticTerms naming context left) ++ (← diagnosticTerms naming context right)
  | .trace _ body children => do
      let mut terms ← diagnosticTerms naming context body
      for child in children do terms := terms ++ (← diagnosticTerms naming context child)
      return terms
  | .ofLazy make _ => do
      let value ← make (context.map (MessageData.mkPPContext naming))
      let some body := value.get? MessageData | return #[]
      diagnosticTerms naming context body
  | .ofGoal _ => return #[]

private def parseItem (source : String) (item : SourceItem) : TermElabM Syntax := do
  let .ok parsed := Parser.runParserCategory (← getEnv) `cas_item item.text source
    | throwError "the unchanged input failed to parse at {source}:{item.line}"
  match parsed with
  | `(cas_item| $statement:cas_stmt) => return statement
  | _ => throwError "the negative admission fixture unexpectedly contains a named assertion"

private def observeRejectedAdmission : TermElabM Json := do
  let source := "tests/acceptance/proposals/independent-extension-reconstruction-20261024/" ++
    "completion/rx09-constant-one-rejection.cas"
  let items := itemsWithLocations (← IO.FS.readFile source)
  unless items.size == 5 do throwError "the unchanged negative input lost a source statement"
  let mut scope : Scope := {}
  let trace ← Trace.new
  for item in items.extract 0 4 do
    let statement ← parseItem source item
    let result ← try
      (claim scope statement).run { trace := some trace }
    catch error =>
      throwError "the unchanged prerequisite at {source}:{item.line} failed: {item.text}\n{error.toMessageData}"
    let .binding := result
      | throwError "an admission prerequisite is no longer a binding"
    let some (name, term) ← letBinding? statement
      | throwError "an admission prerequisite lost its binding"
    scope := scope.insert name term
  let item := items[4]!
  let statement ← parseItem source item
  let some (name, value) ← letBinding? statement
    | throwError "the rejected input no longer attempts a named admission"
  unless name == `impossibleAdmission do throwError "the negative input changed its final binding"
  let `(cas_term| $familySyntax in $domainSyntax) := value
    | throwError "the negative input no longer attempts the declared admission"
  let family ← (eval scope familySyntax).run { trace := some trace }
  let (hom, sourceObject, targetObject) ← match family with
    | .morphism hom source target .. | .derivedMorphism hom source target .. =>
        pure (hom, source, target)
    | _ => throwError "the rejected family's complete map did not elaborate"
  let function ← functionOf hom
  let domain ← (eval scope domainSyntax >>= semanticObject).run { trace := some trace }
  let nonSummable := (← getConstInfo
    ``CasCatalogue.Algebra.SuccessorSeries.integer_constant_one_not_summable).type
  let noAdmission := (← getConstInfo
    ``CasCatalogue.Algebra.SuccessorSeries.no_constant_one_admission).type
  unless nonSummable.isAppOfArity ``Not 1 && noAdmission.isAppOfArity ``Not 1 do
    throwError "the independently published negative theorems changed their propositions"
  let expected := nonSummable.getAppArgs[0]!
  -- Summable's final argument is its selected summation filter. The complete
  -- family immediately precedes that filter; it is not the final argument.
  unless expected.isAppOfArity ``Summable 6 do
    throwError "the independent nonsummability theorem has a different complete signature"
  let expectedFunction := expected.getAppArgs[4]!
  let existential := noAdmission.getAppArgs[0]!
  unless existential.isAppOfArity ``Exists 2 do
    throwError "the independent admission theorem no longer fixes its exact domain"
  let expectedDomain := existential.getAppArgs[0]!
  unless ← withTransparency .all <|
      isDefEq function expectedFunction <&&> isDefEq domain expectedDomain do
    throwError "the attempted family or its selected topological admission domain changed"
  let rejected ← try
    discard <| (claim scope statement).run { trace := some trace }
    pure none
  catch error => pure (some error)
  let some error := rejected | throwError "the nonsummable family was admitted"
  unless Exception.interpretationKind error == .invalid do
    throwError "the nonsummable family did not fail at the mathematical admission boundary"
  let context : MessageDataContext := {
    env := (← getEnv), mctx := (← getMCtx), lctx := (← getLCtx), opts := (← getOptions) }
  let diagnostic ← diagnosticTerms { currNamespace := .anonymous, openDecls := [] }
    (some context) error.toMessageData
  let mut obligation : Option Expr := none
  for term in diagnostic do
    unless term.hasFVar || term.hasLooseBVars || term.hasMVar || term.hasLevelMVar do
      if ← withTransparency .all <| isDefEq term expected then obligation := some term
  let some actualObligation := obligation
    | throwError "the actual rejected diagnostic did not retain the exact summability obligation:\n{error.toMessageData}"
  return Json.mkObj [
    ("control", "RX09"), ("kind", "invalid"), ("stage", "admission"),
    ("file", toJson source), ("sourceLine", toJson item.line), ("source", toJson item.text),
    ("prerequisites", toJson 4), ("dispatches", Json.arr #[]),
    ("actualAttempt", ← termRecord #[hom, sourceObject, targetObject, function, domain, actualObligation]
      #["originalMap", "originalDomain", "originalCodomain", "familyFunction", "admissionDomain",
        "actualDiagnosticObligation"]),
    ("independentObligation", ← termRecord #[expectedFunction, expectedDomain, expected]
      #["independentFamily", "independentAdmissionDomain", "independentSummabilityObligation"]),
    ("detail", toJson (← error.toMessageData.toString))]

run_elab do
  let selected ← IO.getEnv "CAS_EXTENSION_CONTROL"
  unless selected.isNone || selected == some "RX05" || selected == some "RX09" do
    throwError "CAS_EXTENSION_CONTROL must select RX05 or RX09, or be unset for both"
  let mut records : Array Json := #[]
  if selected != some "RX09" then
    records := records.push (← observeCarrierEnvironments)
    logInfo "RX05: both coherent orders retain the exact receiver and comparison request; both absent-cell orders retain the complete registry-derived candidate inventory"
  if selected != some "RX05" then
    records := records.push (← observeRejectedAdmission)
    logInfo "RX09: all four prerequisite bindings elaborate; the unchanged final source binding rejects the exact independently specified summability obligation"
  if let some path ← IO.getEnv "CAS_EXTENSION_CONTROL_REPORT" then
    IO.FS.writeFile path ((Json.arr records).pretty ++ "\n")

end
