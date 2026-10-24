/- Copyright (c) 2026 Dzack Garza. Released under Apache 2.0 license. -/
module

import CasCatalogue.ComputationalData
meta import CasCatalogue.ComputationalData

/-! A complete registered object action supplies its carrier interface without
requiring a separate named row for its result. Equal carriers cannot substitute
different selected structure dictionaries. These are interface controls only. -/

open Lean Meta Elab Term CategoryTheory CasCatalogue

meta section

private def dataNode (tag : String) (arguments : Array Json) : Json :=
  Json.mkObj [("ctor", toJson tag), ("args", Json.arr arguments)]

run_elab do
  let state ← registryState
  let some sourceRow := state.objects.find? (·.id.raw == "obj.rings.integers")
    | throwError "the independently registered source is absent"
  let source ← Semantic.object sourceRow #[]
  let edge := EdgeRef.functor ⟨"fun.rings.multiplicative_monoid"⟩
  let action ← Semantic.asFunctor (← Semantic.edgeFunctor state edge)
  let selected ← Semantic.objOf action source
  let descriptor := dataNode "functorAction" #[
    dataNode "fun.rings.multiplicative_monoid" #[], dataNode sourceRow.id.raw #[]]
  let .ok carrier ← ComputationalData.interfaceCarrier selected descriptor
    | throwError "the registered action result lost its complete carrier interface"
  let expected ← withTransparency .all <| mkAppM ``MonCat.carrier #[selected]
  unless ← withTransparency .all <| isDefEq carrier expected do
    throwError "the action changed its independently selected carrier"
  let sourceCarrier ← withTransparency .all <| mkAppM ``RingCat.carrier #[source]
  let different ← withTransparency .all <| elabTermAndSynthesize
    (← `(MonCat.of (Multiplicative $(← exprToSyntax sourceCarrier)))) none
  let differentCarrier ← withTransparency .all <| mkAppM ``MonCat.carrier #[different]
  unless (← withTransparency .all <| isDefEq expected differentCarrier) &&
      !(← withTransparency .all <| isDefEq selected different) do
    throwError "the interface fixture does not distinguish complete selected dictionaries"
  if (← ComputationalData.interfaceCarrier different descriptor).isOk then
    throwError "the action descriptor accepted a different structure on the same carrier"

end
