module

import CasCatalogue.Realize
meta import CasCatalogue.Realize

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
  for different in #[Question.judgement "typing" #[first] #[] #[``Nat],
      Question.judgement "membership" #[first] #[``Nat.succ] #[``Nat],
      Question.judgement "membership" #[first] #[] #[``Int],
      Question.conjunction questionA questionA, Question.negation questionA] do
    unless (← identity questionA).1 != (← identity different).1 do
      throwError "relation, route, form or logical structure was erased"
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
