/- Copyright (c) 2026 Dzack Garza. Released under Apache 2.0 license. -/
module

import CasCatalogue.Realize
meta import CasCatalogue.Realize

/-! Engineering controls for complete retained-context comparison. The existing
finite-set object and its identity supply the formal interfaces. Arbitrary owned
packets and deliberately changed metadata exercise occurrence identity only;
they are never executed or treated as mathematical answers.

Repeated ordered child slots form a shared DAG. Two separately built DAGs have
equal complete selections, while a changed right-hand occurrence below an equal
branch must remain distinct. These controls impose no timing threshold and do
not change the ordinary elaboration budget. -/

open Lean Meta Elab Term
open CasCatalogue CasCatalogue.Realize

namespace CasCatalogue.CompleteContextSharingProbes
meta section

private def sharedDag (parent leaf : Wire) : Nat → Wire
  | 0 => leaf
  | depth + 1 =>
      let child := sharedDag parent leaf depth
      { parent with productComponents := #[child, child] }

/-- The first branch compares the same left node with an equal right node.
The second compares that left node with a different right occurrence, within
one complete comparison. A store keyed only by the left node would merge them. -/
private def rejectAfterEqualBranch (parent : Wire) (label : String)
    (original changed : Wire) : TermElabM Unit := do
  let left := sharedDag parent original 6
  let equalRight := sharedDag parent
    { original with serviceHandles := original.serviceHandles ++ #[91] } 6
  let changedRight := sharedDag parent changed 6
  unless sameCompleteWireContext left equalRight do
    throwError "the {label} control lost its equal first branch"
  let left := { parent with productComponents := #[left, left] }
  let right := { parent with productComponents := #[equalRight, changedRight] }
  if sameCompleteWireContext left right then
    throwError "complete-context sharing merged a changed {label} in the second branch"

run_elab do
  let state ← registryState
  let some sets := state.categories.find? (·.id == CategoryId.sets)
    | throwError "the context-sharing control lost the accepted set category"
  let some finite := state.objects.find? (·.id.raw == "obj.sets.fin")
    | throwError "the context-sharing control lost the accepted finite-object declaration"
  let formal ← Semantic.object finite #[← `(2)]
  let context ← CategoryContext.ofNamed sets formal
  let packet := Json.arr #[Backend.ComputationalValue.encode (.opaque "same-token")]
  let original : Wire := {
    form := .diagrams sets
    payload := .computed formal (.owned "complete-context-sharing" 41 packet)
    categoryContext := some context }
  let anotherSupplier : Wire := { original with
    payload := .computed formal (.owned "complete-context-sharing" 42 packet) }
  unless original.value == anotherSupplier.value && original.json == anotherSupplier.json &&
      original.ownership != anotherSupplier.ownership do
    throwError "the context-sharing control did not isolate equal packets with different suppliers"

  -- Each graph has thirteen retained nodes, with two references to its child
  -- at every level. Distinct deep administrative handles make the two graphs
  -- independently constructed without changing complete selection identity.
  let first := sharedDag original { original with serviceHandles := #[4] } 12
  let second := sharedDag original { original with serviceHandles := #[7] } 12
  unless sameCompleteWireContext first second do
    throwError "complete-context comparison rejected equal independently retained shared DAGs"
  if sameRetainedServiceHandles first second || sameIntrinsicObservationInput first second then
    throwError "complete selection equality erased a deep original execution handle"

  rejectAfterEqualBranch original "endpoint supplier" original anotherSupplier

  -- This is deliberately forged metadata, not a category declaration. The
  -- expression and carrier-facing fields stay fixed while the full dictionary
  -- field changes; complete context identity must still reject the occurrence.
  let changedContext := { context with bundle := mkNatLit 0 }
  let wrongDictionary := { original with categoryContext := some changedContext }
  unless sameActionOperand original wrongDictionary do
    throwError "the dictionary control failed to isolate the stronger complete-context check"
  rejectAfterEqualBranch original "complete category dictionary" original wrongDictionary

  let completed := { original with objectObserved := true }
  unless sameActionOperand original completed do
    throwError "the completion control failed to isolate the stronger complete-context check"
  rejectAfterEqualBranch original "completion state" original completed

  let position : DataOwnership.Path := #[.index 0]
  let positioned := { original with serviceInputPaths := some #[(position, 4)] }
  let changedPosition := { positioned with serviceInputPaths := some #[(position, 7)] }
  rejectAfterEqualBranch original "positioned request input" positioned changedPosition

  let identity ← identityAtContext context formal
  let callable : Wire := {
    form := .canonicalMorphism sets
    payload := .computed identity (.owned "complete-context-sharing" 41 packet)
    categoryContext := some context }
  let callable ← retainCallableEndpoints callable original original context
  let some endpoints := callable.callableEndpoints
    | throwError "the callable control lost its complete endpoint receipt"
  let changedEndpoints := { callable with
    callableEndpoints := some { endpoints with target := anotherSupplier } }
  rejectAfterEqualBranch original "callable endpoint receipt" callable changedEndpoints

  -- Identical formal maps and public bytes cannot change from whole callable
  -- data to native point data merely by attaching a different retained role.
  let changedRole := { callable with pointDataInterface := some {
    domain := formal, target := formal,
    domainData := original.fragment, targetData := original.fragment } }
  rejectAfterEqualBranch original "point-data role" callable changedRole

  let framed ← presentMorphism callable original original (some context)
  let some frame := framed.morphismFraming
    | throwError "the framing control lost its original complete producer"
  let changedFrame := { framed with
    morphismFraming := some { frame with source := anotherSupplier } }
  unless framed.value == changedFrame.value && framed.fragment == changedFrame.fragment do
    throwError "the framing control changed the public packet instead of its retained endpoint"
  rejectAfterEqualBranch original "framing endpoint occurrence" framed changedFrame

  -- A successful prior comparison cannot authorize a later changed selection.
  unless sameCompleteWireContext first second do
    throwError "another comparison changed an existing complete selection"
  if sameCompleteWireContext original anotherSupplier then
    throwError "comparison reuse escaped its original pair and merged different suppliers"
  logInfo "PASS: shared complete-context comparison preserves suppliers, roles, endpoints and execution handles"

end
end CasCatalogue.CompleteContextSharingProbes
