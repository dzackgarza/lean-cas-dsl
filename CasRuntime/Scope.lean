module

public import CasRuntime.Occurrence
public import CasContract.Port
public import CasRuntime.ScopeReference

public section

namespace CasRuntime

open Lean CasCatalogue.Backend

/-- An exact complete input position already retained by the request encoder. -/
structure InputPosition where
  path : Array InputPathStep
  binding : ValueBinding

private def sameDispatch (left right : DispatchReservation) : Bool :=
  left.occurrence == right.occurrence && left.transaction == right.transaction &&
    left.connection == right.connection && left.selected == right.selected

/-- Active request authority stores references and roles, with no completed payload cache. -/
structure RequestScope where
  private mk ::
  id : RuntimeId .scope
  reservation : DispatchReservation
  slots : Array ValueBinding
  captureCount : Nat
  inputs : Array InputPosition
  priorResults : Array ValueBinding
  private ledger : OccurrenceLedger
  private active : Std.Mutex Bool

def RequestScope.wireId (scope : RequestScope) : String :=
  s!"{scope.id.worker}:{scope.id.serial}"

private def RequestScope.issueWith (ledger : OccurrenceLedger) (reservation : DispatchReservation)
    (graph : ValueGraph) (captures slots : Array ValueBinding) (inputs : Array InputPosition)
    (priorResults : Array ValueBinding) : IO RequestScope := do
  let slots := captures ++ slots
  let mut paths : Array (Array InputPathStep) := #[]
  for input in inputs do
    if paths.contains input.path then
      throw <| IO.userError "a request input position has duplicate authority"
    paths := paths.push input.path
  let required ← IO.ofExcept <| (graph.requiredOwners
    (slots ++ inputs.map (·.binding) ++ priorResults)).mapError IO.userError
  unless required.all reservation.dependencies.contains do
    throw <| IO.userError "the request scope has an owner outside its reservation"
  return ⟨← ledger.owners.identities.fresh .scope, reservation, slots, captures.size, inputs, priorResults,
    ledger, ← Std.Mutex.new true⟩

private def RequestScope.checkPending (ledger : OccurrenceLedger) (reservation : DispatchReservation)
    (graph : ValueGraph) : IO Unit := do
  unless graph.worker == ledger.owners.worker do
    throw <| IO.userError "the request scope belongs to a different worker"
  let some pending ← ledger.pendingFor reservation.occurrence reservation.transaction
    | throw <| IO.userError "the request scope has no pending invocation"
  unless sameDispatch pending reservation do
    throw <| IO.userError "the request scope changed its dispatch identity"

/-- Issue fresh authority for an actual pending invocation and exact retained positions.
Reuse: the worker identity supply, occurrence ledger and immutable value-graph visibility checks. -/
opaque RequestScope.issue (ledger : OccurrenceLedger) (reservation : DispatchReservation)
    (graph : ValueGraph) (slots : Array ValueBinding) (inputs : Array InputPosition)
    (priorResults : Array ValueBinding) : IO RequestScope := do
  RequestScope.checkPending ledger reservation graph
  let captures ← match reservation.selected with
    | .primitive _ => pure #[]
    | .native code token => do
      let some node := graph.find code
        | throw <| IO.userError "the native code is outside the request graph"
      let .ownedToken owner actual captures := node.payload.data
        | throw <| IO.userError "the native code has no stored export"
      unless owner == reservation.connection && actual == token do
        throw <| IO.userError "the native capture table changed its supplying export"
      pure captures
  RequestScope.issueWith ledger reservation graph captures slots inputs priorResults

/-- Issue the scope of a resume request: exactly the captures declared by the suspension,
then the ordered child results, numbered from zero (python-sdk.md, "Generator suspension"), with
the completed prefix of a following group's results. The suspended invocation's own native
export captures are not part of it. -/
opaque RequestScope.issueResume (ledger : OccurrenceLedger) (reservation : DispatchReservation)
    (graph : ValueGraph) (slots priorResults : Array ValueBinding) : IO RequestScope := do
  RequestScope.checkPending ledger reservation graph
  RequestScope.issueWith ledger reservation graph #[] slots #[] priorResults

private def RequestScope.lookup (scope : RequestScope) (reference : ScopedReference) :
    Except String ValueBinding := do
  match reference with
  | .scope slot =>
    let some binding := scope.slots[slot]? | throw "the scope slot is outside this request"
    return binding
  | .input path =>
    let some position := scope.inputs.find? (·.path == path)
      | throw "the input reference is not a retained complete typed position"
    return position.binding
  | .result index =>
    let some binding := scope.priorResults[index]?
      | throw "the result reference is self, forward or outside the completed prefix"
    return binding

/-- Resolve only within this live invocation, then verify visibility in the supplied graph.
The scope's metadata cannot recover values absent from that Environment/transaction graph. -/
opaque RequestScope.resolveMany (scope : RequestScope) (actual : DispatchReservation)
    (graph : ValueGraph) (wireId : String) (references : Array ScopedReference) :
    IO (Array ValueBinding) :=
  scope.active.atomically do
    unless ← get do throw <| IO.userError "the request scope has retired"
    unless wireId == scope.wireId && sameDispatch actual scope.reservation do
      throw <| IO.userError "the reference belongs to a different request scope"
    let some pending ← scope.ledger.pendingFor actual.occurrence actual.transaction
      | throw <| IO.userError "the scoped invocation has settled"
    unless sameDispatch pending actual do
      throw <| IO.userError "the scoped invocation changed its dispatch identity"
    unless graph.worker == scope.id.worker do
      throw <| IO.userError "the scoped value graph belongs to a different worker"
    let bindings ← references.mapM fun reference =>
      IO.ofExcept <| (scope.lookup reference).mapError IO.userError
    discard <| IO.ofExcept <| (graph.requiredOwners bindings).mapError IO.userError
    return bindings

/-- Capture exact addresses in order. Distinct addresses keep their roles even when values alias. -/
opaque RequestScope.capture (scope : RequestScope) (actual : DispatchReservation)
    (graph : ValueGraph) (wireId : String) (references : Array ScopedReference) :
    IO (Array ValueBinding) := do
  let mut seen : Array ScopedReference := #[]
  for reference in references do
    if seen.contains reference then
      throw <| IO.userError "a capture address is repeated"
    seen := seen.push reference
  scope.resolveMany actual graph wireId references

/-- Retire authority independently of semantic snapshots and retained value identity. -/
opaque RequestScope.retire (scope : RequestScope) : BaseIO Unit :=
  scope.active.atomically (set false)

end CasRuntime
