module

import CasCatalogue.Realize
import CasCatalogue.QuestionComparison
meta import CasCatalogue.Realize
meta import CasCatalogue.QuestionComparison

open Lean Meta Elab Command Term
open CasCatalogue CasCatalogue.Language CasCatalogue.Realize

/- Typed serialization mechanics only; no acceptance assertion is admitted here. -/
run_cmd liftTermElabM do
  let read (stx : Syntax) : TermElabM Expr := do
    let term ← elabTermAndSynthesize stx none
    instantiateMVars term
  let first ← read (← `(Subtype.mk (p := fun n : Nat => n = n) 3 (Eq.refl 3)))
  let second ← read (← `(Subtype.mk (p := fun n : Nat => n = n) 3 (Eq.symm (Eq.refl 3))))
  unless first != second do throwError "proof probe did not contain different proof syntax"
  unless (← termIdentity first) == (← termIdentity second) do
    throwError "implementations of the same admission proof changed identity"
  let other ← read (← `(Subtype.mk (p := fun n : Nat => n = n) 4 (Eq.refl 4)))
  unless (← termIdentity first) != (← termIdentity other) do
    throwError "selected subtype data was erased"
  let dependentA ← read (← `(fun n : Nat => Subtype.mk (p := fun m : Nat => m = n) n (Eq.refl n)))
  let dependentB ← read (← `(fun n : Nat => Subtype.mk (p := fun m : Nat => m = n) n (Eq.symm (Eq.refl n))))
  unless (← termIdentity dependentA) == (← termIdentity dependentB) do
    throwError "dependent proof identity lost its binder context"
  let premiseA ← read (← `(fun (n : Nat) (h : n = n) =>
    Subtype.mk (p := fun m : Nat => m = n) n h))
  let premiseB ← read (← `(fun (n : Nat) (h : n = n) =>
    Subtype.mk (p := fun m : Nat => m = n) n (Eq.symm h)))
  unless (← termIdentity premiseA) == (← termIdentity premiseB) do
    throwError "bound admission proof identity lost its dependent proposition"
  let scopedA ← read (← `(fun (n : Nat) => fun (m : Nat) =>
    Subtype.mk (p := fun k : Nat => k = n) n (Eq.refl n)))
  let scopedB ← read (← `(fun (n : Nat) => fun (m : Nat) =>
    Subtype.mk (p := fun k : Nat => k = m) m (Eq.refl m)))
  unless (← termIdentity scopedA) != (← termIdentity scopedB) do
    throwError "distinct dependent binder references collapsed"
  let proofA ← read (← `(Eq.refl (3 : Nat)))
  let proofB ← read (← `(Eq.refl (4 : Nat)))
  unless (← termIdentity proofA) != (← termIdentity proofB) do
    throwError "proof token erased its proposition type"
  let mapA ← read (← `(fun n : Nat => n))
  let mapB ← read (← `(fun n : Nat => Nat.succ n))
  unless (← termIdentity mapA) != (← termIdentity mapB) do
    throwError "selected map implementation was erased"
  let dictionaryA ← read (← `((inferInstance : Inhabited Nat)))
  let dictionaryB ← read (← `(({ default := 3 } : Inhabited Nat)))
  unless (← termIdentity dictionaryA) != (← termIdentity dictionaryB) do
    throwError "selected data dictionary was erased"
  let questionA : Question := .judgement "membership" #[first] #[] #[``Nat]
  let questionB : Question := .judgement "membership" #[second] #[] #[``Nat]
  let identity (question : Question) := claimQuestion (.judged question (mkConst ``True) (some true) "probe")
  unless (← identity questionA).1 == (← identity questionB).1 do
    throwError "complete question retained admission proof syntax"
  unless ← QuestionIdentity.equivalentQuestion questionA questionB do
    throwError "independent question comparison retained admission proof syntax"
  let firstType ← inferType first
  let preparedQuestion : Question :=
    .judgement "membership" #[first] #[] #[``Nat] #[firstType]
  unless ← QuestionIdentity.equivalentQuestion questionA preparedQuestion do
    throwError "independently inferred operand types differ from a correctly prepared question"
  for recordedTypes in #[#[Lean.mkConst ``Nat], #[firstType, firstType]] do
    let malformed : Question := .judgement "membership" #[first] #[] #[``Nat] recordedTypes
    let rejected ← try
        discard <| QuestionIdentity.equivalentQuestion questionA malformed
        pure false
      catch _ => pure true
    unless rejected do
      throwError "question comparison trusted an incomplete or incorrect recorded type list"
  for different in #[Question.judgement "typing" #[first] #[] #[``Nat],
      Question.judgement "membership" #[first] #[``Nat.succ] #[``Nat],
      Question.judgement "membership" #[first] #[] #[``Int],
      Question.conjunction questionA questionA, Question.negation questionA] do
    unless (← identity questionA).1 != (← identity different).1 do
      throwError "relation, route, form or logical structure was erased"
    if ← QuestionIdentity.equivalentQuestion questionA different then
      throwError "independent question comparison erased its relation, route, form or logic"
  -- Identity preparation must not replace the expression that evaluation receives.
  let claim := Claim.judged questionA (mkConst ``True) (some true) "probe"
  let prepared : TypedQuestion := {
    claim := claim, trace := {}, identity := ← identity questionA,
    mathematicalRevision := "serialization-mechanics-probe" }
  let harness ← Harness.empty
  discard <| evaluate harness prepared
  let .judged (.judgement _ #[actual] _ _ _) _ _ _ := prepared.claim
    | throwError "execution replaced the prepared claim"
  unless actual == first && actual != second do
    throwError "identity normalization rewrote selected execution data"
  -- The reference comparison traverses paired typed expressions. It does not
  -- share the serializer or its binder-context encoding and cannot accept a
  -- candidate by comparing its own generated JSON with itself.
  for (left, right) in #[(first, second), (dependentA, dependentB), (premiseA, premiseB)] do
    unless ← QuestionIdentity.equivalent left right do
      throwError "the independent typed comparison retained incidental proof syntax"
    unless (← QuestionIdentity.equivalent left right) ==
        ((← termIdentity left) == (← termIdentity right)) do
      throwError "the serializer disagrees with independent typed comparison"
  for (left, right) in #[(first, other), (scopedA, scopedB), (proofA, proofB),
      (mapA, mapB), (dictionaryA, dictionaryB)] do
    if ← QuestionIdentity.equivalent left right then
      throwError "the independent comparison erased selected computational or proposition data"
    unless (← QuestionIdentity.equivalent left right) ==
        ((← termIdentity left) == (← termIdentity right)) do
      throwError "distinct typed questions collided in the identity serialization"
  let table ← TermTable.new
  let root ← table.encode dependentA
  discard <| table.encode scopedB
  unless (← table.rootIdentity root) == (← termIdentity dependentA) do
    throwError "sharing another contextual term changed an existing question root"
