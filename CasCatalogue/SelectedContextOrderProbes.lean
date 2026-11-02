/- Copyright (c) 2026 Dzack Garza. Released under Apache 2.0 license. -/
module

import CasCatalogue.Language
meta import CasCatalogue.Language

/-!
Engineering controls for deterministic evidence ordering. These exercise typed serialization,
shared local contexts, and record metadata; the metadata perturbations are never registered
or admitted as mathematical sources. The mathematical reader assertions remain unchanged.
-/

open Lean Meta Elab Command Term
open CasCatalogue CasCatalogue.Language

namespace SelectedContextOrderControls

def termKey (terms : Array Expr) : TermElabM String := do
  let context ← EvidenceOrder.Context.ofTerms terms
  context.key fun encode => return toJson (← terms.mapM encode)

def localPairKeys (a b : Name) : TermElabM (String × String × String × String) := do
  withLocalDeclD a (mkConst ``Nat) fun left =>
    withLocalDeclD b (mkConst ``Nat) fun right => do
      let context ← EvidenceOrder.Context.ofTerms #[left, right]
      let key (terms : Array Expr) := context.key fun encode => return toJson (← terms.mapM encode)
      return (← key #[left, right], ← key #[right, left], ← key #[left], ← key #[right])

def localTypedKey (type : Expr) : TermElabM String :=
  withLocalDeclD `parameter type fun value => termKey #[value]

def localLetKey (value : Expr) : TermElabM String :=
  withLetDecl `parameter (mkConst ``Nat) value fun boundTerm => termKey #[boundTerm]

run_cmd liftTermElabM <| withoutErrToSorry <| withCurrHeartbeats do
  let first ← mkEqRefl (mkNatLit 0)
  let second ← mkAppM ``Eq.symm #[first]
  unless (← termKey #[first]) == (← termKey #[second]) do
    throwError "proof implementation changed an evidence key"
  unless (← termKey #[first]) != (← termKey #[← mkEqRefl (mkNatLit 1)]) do
    throwError "a proof's exact proposition disappeared from an evidence key"
  let left := mkLambda `left BinderInfo.default (mkConst ``Nat) (.bvar 0)
  let right := mkLambda `right BinderInfo.default (mkConst ``Nat) (.bvar 0)
  unless (← termKey #[left]) == (← termKey #[right]) do
    throwError "binder spelling changed an evidence key"
  unless (← termKey #[mkNatLit 0]) != (← termKey #[mkNatLit 1]) do
    throwError "computational data disappeared from an evidence key"

run_cmd liftTermElabM <| withoutErrToSorry <| withCurrHeartbeats do
  let (forward, backward, first, second) ← localPairKeys `left `right
  unless forward != backward && first != second do
    throwError "distinct shared local slots collapsed in an evidence key"
  let renamed ← localPairKeys `renamedLeft `renamedRight
  unless (forward, backward, first, second) == renamed do
    throwError "local alpha-renaming changed evidence ordering"
  unless (← localTypedKey (mkConst ``Nat)) != (← localTypedKey (mkConst ``Int)) do
    throwError "the shared local telescope lost a complete parameter type"
  unless (← localLetKey (mkNatLit 1)) != (← localLetKey (mkNatLit 2)) do
    throwError "the shared local telescope lost a let value"
  let opaqueKey ← withLetDecl (nondep := true) `opaqueKey (mkConst ``Nat) (mkConst ``Bool.true)
    fun value => termKey #[value]
  unless opaqueKey == (← localTypedKey (mkConst ``Nat)) do
    throwError "an opaqueKey ambient have exposed its hidden value"

run_cmd liftTermElabM <| withoutErrToSorry <| withCurrHeartbeats do
  withLocalDeclD `parameter (mkConst ``Nat) fun value => do
    let proof ← mkEqRefl value
    withLocalDeclD `independentProof (← inferType proof) fun supplied => do
      unless (← termKey #[proof]) == (← termKey #[supplied]) do
        throwError "a proof-only local altered the typed proposition key"
      let rejected ← try
        discard <| QuestionIdentity.equivalent value value
        pure false
      catch _ => pure true
      unless rejected do throwError "private ordering weakened final question closure"

run_cmd liftTermElabM <| withoutErrToSorry <| withCurrHeartbeats do
  let first := mkLambda `first BinderInfo.default (mkConst ``Nat) (.bvar 0)
  let renamed := mkLambda `renamed BinderInfo.default (mkConst ``Nat) (.bvar 0)
  let value := Value.answer first
  let same := Value.answer renamed
  let changed := Value.answer (mkNatLit 2)
  let a : CheckedParameterView := (value, value, #[], #[], #[])
  let b : CheckedParameterView := (changed, changed, #[], #[], #[])
  let a' : CheckedParameterView := (same, same, #[], #[], #[])
  let keys (views : Array CheckedParameterView) : TermElabM (Array String) := do
    let ordered ← orderCheckedParameterViews views
    let terms ← IO.mkRef (#[] : Array Expr)
    for item in ordered do
      discard <| encodeCheckedParameterView (fun term => do terms.modify (·.push term); pure 0) item
    let context ← EvidenceOrder.Context.ofTerms (← terms.get)
    ordered.mapM fun item => context.key fun encode => encodeCheckedParameterView encode item
  unless (← keys #[a, b, a']) == (← keys #[a', b, a]) do
    throwError "input order or alpha spelling changed complete evidence ordering"
  unless (← orderCheckedParameterViews #[a, b, a']).size == 3 do
    throwError "ordering erased evidence multiplicity"
  let proof ← mkEqRefl (mkConst ``Nat)
  let source : ParameterPresentation := {
    source := ⟨"obj.sets.integers"⟩, sourceCategory := CategoryId.sets,
    targetCategory := CategoryId.sets, params := #[], route := #[], applications := #[],
    carrierRoute := #[], identifications := #[], object := mkConst ``Nat,
    image := mkConst ``Nat, identity := proof }
  let context ← EvidenceOrder.Context.ofTerms #[first, mkConst ``Nat, proof]
  let key (record : CheckedParameterView) := context.key fun encode => encodeCheckedParameterView encode record
  let withSource : CheckedParameterView := (value, value, #[], #[source], #[])
  let withOtherId : CheckedParameterView := (value, value, #[],
    #[{ source with source := ⟨"obj.sets.naturals"⟩ }], #[])
  unless (← key withSource) != (← key withOtherId) do
    throwError "alternative source IDs disappeared from complete evidence keys"
  let withOtherApplication : CheckedParameterView := (value, value, #[],
    #[{ source with applications := #[mkNatLit 2] }], #[])
  unless (← key withSource) != (← key withOtherApplication) do
    throwError "alternative action parameters disappeared from complete evidence keys"

end SelectedContextOrderControls
