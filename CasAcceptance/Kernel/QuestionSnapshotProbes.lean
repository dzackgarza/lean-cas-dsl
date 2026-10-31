/- Copyright (c) 2026 Dzack Garza. Released under Apache 2.0 license. -/
module

import CasCatalogue.QuestionComparison
meta import CasCatalogue.QuestionComparison

open Lean Meta Elab Command Term
open CasCatalogue CasCatalogue.Realize

/- Adversarial serialization mechanics only. These inert trace records register no
mathematics or computations and admit no assertion or interpretation record. -/
run_cmd liftTermElabM do
  let read (stx : Syntax) : TermElabM Expr := do
    instantiateMVars (← elabTermAndSynthesize stx none)
  let first ← read (← `(Subtype.mk (p := fun n : Nat => n = n) 3 (Eq.refl 3)))
  let second ← read (← `(Subtype.mk (p := fun n : Nat => n = n) 3 (Eq.symm (Eq.refl 3))))
  unless first != second && (← termIdentity first) == (← termIdentity second) do
    throwError "the ordering fixture did not contain distinct raw keys with one canonical root"
  let zero := mkNatLit 0
  let one := mkNatLit 1
  let two := mkNatLit 2
  let source : CategoryId := ⟨"snapshot.source"⟩
  let target : CategoryId := ⟨"snapshot.target"⟩
  let route : Array EdgeRef := #[.functor ⟨"snapshot.route"⟩]
  let firstNode := Node.retainedRoute source target route #[zero] zero
  let secondNode := Node.retainedRoute source target route #[one] zero
  let entries := #[(first, firstNode), (second, secondNode)]
  let expected ← snapshot entries
  unless expected == (← snapshot entries.reverse) do
    throwError "colliding root keys left the snapshot dependent on enumeration order"
  unless ← QuestionIdentity.equivalentTrace (Std.HashMap.ofArray entries)
      (Std.HashMap.ofArray entries.reverse) do
    throwError "independent comparison disagreed about an unchanged reordered trace"
  let altered := #[(first, firstNode),
    (second, Node.retainedRoute source target route #[two] zero)]
  if expected == (← snapshot altered) then
    throwError "canonical ordering erased an actual structural application"
  if ← QuestionIdentity.equivalentTrace (Std.HashMap.ofArray entries)
      (Std.HashMap.ofArray altered) then
    throwError "independent comparison erased the changed structural application"
  for (before, after) in #[(Node.structuredProjection zero "leg" none,
      Node.structuredProjection zero "leg" (some 0)),
      (Node.cartesian ⟨"snapshot.transport"⟩ #[zero] one two "hom",
        Node.cartesian ⟨"snapshot.transport"⟩ #[zero] two two "hom")] do
    let colliding := #[(first, before), (second, after)]
    unless (← snapshot colliding) == (← snapshot colliding.reverse) do
      throwError "a projection or cartesian record retained an incomplete ordering key"
    if (← snapshot #[(first, before)]) == (← snapshot #[(first, after)]) then
      throwError "a projection port or selected base morphism disappeared from the snapshot"
  -- Both raw keys are retained even when their complete canonical records coincide.
  let duplicates ← snapshot #[(first, firstNode), (second, firstNode)]
  let .ok document := Json.parse duplicates | throwError "the snapshot was not JSON"
  let .ok records := (document.getObjVal? "roots").bind (·.getArr?)
    | throwError "the snapshot lost its operation records"
  unless records.size == 2 && duplicates != (← snapshot #[(first, firstNode)]) do
    throwError "canonical ordering deduplicated proof-irrelevant operation records"

run_cmd liftTermElabM do
  let read (stx : Syntax) : TermElabM Expr := do
    instantiateMVars (← elabTermAndSynthesize stx none)
  let zero := mkNatLit 0
  let one := mkNatLit 1
  let proof ← read (← `(Eq.refl (0 : Nat)))
  let alternate ← read (← `(Eq.symm (Eq.refl (0 : Nat))))
  let different ← read (← `(Eq.refl (1 : Nat)))
  let first : ParameterPresentation := {
    source := ⟨"snapshot.object"⟩
    sourceCategory := ⟨"snapshot.source"⟩
    targetCategory := ⟨"snapshot.target"⟩
    params := #[zero]
    route := #[.functor ⟨"snapshot.route"⟩]
    applications := #[zero]
    carrierRoute := #[.functor ⟨"snapshot.carrier"⟩]
    identifications := #[``Eq.refl]
    object := zero
    image := zero
    identity := proof }
  let second := { first with applications := #[one] }
  let third := { first with carrierRoute := #[.functor ⟨"snapshot.otherCarrier"⟩] }
  -- All three presentations have exactly the old source/route/parameter key.
  -- Their full applications and carrier routes still differ and must be retained.
  let node := Node.parameterEquivalence (mkConst ``Nat) zero #[first, second, third]
  let expected ← snapshot #[(zero, node)]
  for presentations in #[#[first, third, second], #[second, first, third],
      #[second, third, first], #[third, first, second], #[third, second, first]] do
    let reordered := Node.parameterEquivalence (mkConst ``Nat) zero presentations
    unless expected == (← snapshot #[(zero, reordered)]) do
      throwError "colliding presentation keys left the snapshot dependent on source order"
    unless ← QuestionIdentity.equivalentNode node reordered do
      throwError "independent comparison disagreed about reordered complete presentations"
  let proofChanged := Node.parameterEquivalence (mkConst ``Nat) zero
    #[{ first with identity := alternate }, second, third]
  unless expected == (← snapshot #[(zero, proofChanged)]) do
    throwError "complete ordering keys retained an incidental proof implementation"
  let propositionChanged := Node.parameterEquivalence (mkConst ``Nat) zero
    #[{ first with identity := different }, second, third]
  if expected == (← snapshot #[(zero, propositionChanged)]) then
    throwError "complete ordering keys erased the proposition of an identification"
  let duplicate := Node.parameterEquivalence (mkConst ``Nat) zero #[first, second, first]
  if expected == (← snapshot #[(zero, duplicate)]) then
    throwError "a duplicate presentation displaced a distinct retained source"
