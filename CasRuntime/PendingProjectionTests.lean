module

import CasRuntime.Association
public meta import Lean.Elab.Command
meta import CasRuntime.Association

namespace CasRuntime.PendingProjectionTests

open Lean Meta CasCompiler

-- Only existing native Prod and Sigma constructors supply this engineering fixture.
-- A completed projection may name its own freshly produced prefix, but it may not change
-- any previously retained parent, stored field, cached path or dependent field prefix.
run_cmd Lean.Elab.Command.liftTermElabM do
  let empty ← ContextTelescope.capture #[]
  let term ← Elab.Term.elabTermAndSynthesize
    (← `(((⟨7, ⟨0, Nat.zero_lt_succ 7⟩⟩ : Sigma (fun n : Nat => Fin (n + 1))), ()))) none
  let source ← SourceLayout.ofTerm (← empty.close term)
  let innerSource ← SourceLayout.ofTerm (← empty.close (mkProj ``Prod 0 term))
  let innerLayout ← RecordLayout.ofSource innerSource
  let some firstField := innerLayout.fields[0]?
    | throwError "the native pending-projection control lost its first field"
  let some secondField := innerLayout.fields[1]?
    | throwError "the native pending-projection control lost its dependent field"
  let unitSource ← SourceLayout.ofTerm (← empty.close (mkProj ``Prod 1 term))
  let owners ← OwnerRegistry.new
  let ledger ← OccurrenceLedger.new owners
  discard <| SessionSnapshot.initialize owners
  let transaction ← CellTransaction.begin ledger
  try
    let program ← owners.identities.fresh .program
    let occurrence ← ledger.allocate
    let producing := fun role =>
      ({ program, occurrence, role, parameters := #[] } : ValueOrigin)
    let first ← transaction.stage (producing firstField.layout) (.closure program #[])
    let second ← transaction.stage (producing secondField.layout) (.closure program #[])
    let unitValue ← transaction.stage (producing unitSource) (.closure program #[])
    let rawInput ← transaction.stage (producing source) (.closure program #[])
    let wrongInput ← transaction.stage (producing source) (.closure program #[])
    let replacement ← transaction.stage (producing firstField.layout) (.closure program #[])
    let initialDraft ← transaction.draft
    let record ← RecordPrefix.begin owners.identities program occurrence innerLayout
    let (firstDraft, record, _) ← initialDraft.bindField record first
    let (fieldDraft, record, _) ← firstDraft.bindField record second
    let .ok payload := record.finish
      | throwError "the pending-projection source record is incomplete"
    let (recordDraft, result) ← fieldDraft.stage (producing innerSource) payload
    let .ok originalFirst := recordDraft.view.project result 0
      | throwError "the pending-projection source lost its actual first field"
    let .ok originalSecond := recordDraft.view.project result 1
      | throwError "the pending-projection source lost its actual dependent field"
    let (copyDraft, otherResult) ← recordDraft.stage (producing innerSource) payload
    let (mixedDraft, mixedResult) ← copyDraft.stage (producing innerSource)
      (.product #[replacement, originalSecond])
    let (completeDraft, storedInput) ← mixedDraft.stage (producing source)
      (.product #[otherResult, unitValue])
    let .ok () ← transaction.installDraft completeDraft
      | throwError "the native pending-projection fixture could not be retained"
    withLetDecl `x (← inferType term) term fun x => do
      let binding : LocalBinding := {
        id := ⟨"pending-native-projection", 0⟩, role := .definition, expression := x }
      let context ← ContextTelescope.capture #[binding]
      let namedSource ← SourceLayout.ofTerm (← context.close x)
      let named := fun (value : ValueBinding) =>
        IO.ofExcept <| (value.withRole namedSource).mapError IO.userError
      let input ← named rawInput
      let wrong ← named wrongInput
      let stored ← named storedInput
      let graph ← transaction.view
      let requestFor (graph : ValueGraph) (operand : ValueBinding)
          (current : Option ValueBinding) : MetaM PreparedRequest := do
        let parameters ← match current with
          | none => pure #[]
          | some current => do
            let parameter ← IO.ofExcept <|
              (RuntimeParameter.ofValue graph binding.id current).mapError IO.userError
            pure #[parameter]
        PreparedRequest.forProjection owners.identities program (← ledger.allocate)
          context graph operand 0 parameters
      let failureFor (request : PreparedRequest) (draft : CellDraft)
          (candidate : ValueBinding) : MetaM (Option Exception) := do
        try
          let (draft, selected) ← request.associateResult owners.identities request.source
            draft candidate
          discard <| request.admitResult draft.view selected
          pure none
        catch error => pure (some error)
      let requireFailure (failure : Option Exception) (label : String) : MetaM Exception := do
        let some failure := failure
          | throwError "the pending projection accepted {label}"
        pure failure
      let request ← requestFor graph input (some input)
      let ordinaryFailure : Option Exception ← try
        discard <| request.environment.checkResult graph request.source result
        pure none
      catch error => pure (some error)
      let ordinaryFailure ← requireFailure ordinaryFailure "an unpublished generic result"
      unless (← ordinaryFailure.toMessageData.toString).startsWith
          "the runtime value has an unresolved consuming dependent reference" do
        throw ordinaryFailure
      let missing ← requestFor graph input none
      let missingFailure ← requireFailure
        (← failureFor missing (← transaction.draft) result) "a missing named parent"
      unless missingValueOf missingFailure binding.id do throw missingFailure
      let wrongRequest ← requestFor graph input (some wrong)
      let wrongFailure ← requireFailure
        (← failureFor wrongRequest (← transaction.draft) result) "a different named parent"
      unless (← wrongFailure.toMessageData.toString).startsWith
          "the runtime value has an unresolved consuming dependent reference" do throw wrongFailure
      let mixedFailure ← requireFailure
        (← failureFor request (← transaction.draft) mixedResult) "a changed actual prefix"
      unless (← mixedFailure.toMessageData.toString).startsWith
          "the runtime value has a different consuming dependent reference" do throw mixedFailure
      let storedRequest ← requestFor graph stored (some stored)
      let storedFailure ← requireFailure
        (← failureFor storedRequest (← transaction.draft) result) "a changed stored field"
      unless (← storedFailure.toMessageData.toString).startsWith
          "the projection changed its retained field reference" do throw storedFailure
      let cacheOrigin ← request.originFor request.source
      let (cachedDraft, _) ← (← transaction.draft).bindProjection cacheOrigin otherResult
        #[originalFirst, originalSecond]
      let cachedRequest ← requestFor cachedDraft.view input (some input)
      let cachedFailure ← requireFailure
        (← failureFor cachedRequest cachedDraft result) "a changed cached field"
      unless (← cachedFailure.toMessageData.toString).startsWith
          "the projection changed its retained field reference" do throw cachedFailure
      let nestedLayout ← RecordLayout.ofSource request.source
      let some nestedFirst := nestedLayout.fields[0]?
        | throwError "the pending result lost its native first-field path"
      let nestedOrigin ← request.originFor nestedFirst.layout
      let (nestedDraft, _) ← (← transaction.draft).bindProjection nestedOrigin replacement #[]
      let nestedRequest ← requestFor nestedDraft.view input (some input)
      let nestedFailure ← requireFailure
        (← failureFor nestedRequest nestedDraft result) "a changed cached descendant"
      unless (← nestedFailure.toMessageData.toString).startsWith
          "the runtime value has a different consuming dependent reference" do throw nestedFailure
      let (accepted, projected) ← request.associateResult owners.identities request.source
        (← transaction.draft) result
      discard <| request.admitResult accepted.view projected
      unless projected.value == result.value do
        throwError "pending projection admission replaced the actual result node"
      let .ok (some selected) := accepted.view.projected? input #[``Prod.fst]
        | throwError "pending projection admission lost its exact original input relation"
      unless selected.value == result.value && selected.associationIds == result.associationIds do
        throwError "pending projection admission changed the original result baseline"
      let .ok none := (← transaction.view).projected? input #[``Prod.fst]
        | throwError "pending projection admission escaped its isolated reply draft"
  finally discard <| transaction.abort

end CasRuntime.PendingProjectionTests
