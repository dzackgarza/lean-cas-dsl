/- Copyright (c) 2026 Dzack Garza. Released under Apache 2.0 license. -/
module

import CasCatalogue.ComputationalData
meta import CasCatalogue.ComputationalData
meta import CasCatalogue.Language
meta import CasCatalogue.OperationAgreement
meta import CasCatalogue.Semantic

open Lean Meta Elab Term CasCatalogue

/-! Short tags use the fixed selected interface. These controls check framing,
not a computational answer's equality to an independently requested result. -/

private def node (tag : String) (args : Array Json) : Json :=
  Json.mkObj [("ctor", toJson tag), ("args", Json.arr args)]

private def checkTag (id : String) (parameters : Array Term) (arguments : Array Json)
    (expression : Json) (accepted : Bool) : TermElabM Unit := do
  let state ← registryState
  let some row := state.objects.find? (·.id.raw == id)
    | throwError "the independently registered probe object is absent"
  let some category := state.categories.find? (·.id == row.category)
    | throwError "the independently registered probe category is absent"
  let selected ← Semantic.object row parameters
  let value ← (Language.recognize state selected category).run {}
  let carrier ← (Language.semanticObject (← (Language.carrierObject value).run {})).run {}
  let expected ← mkAppM ``Quiver.Hom #[← Language.globalPointSource.run {}, carrier]
  let descriptor := node row.id.raw arguments
  let result ← ComputationalData.validateElementAt selected descriptor
    (← mkFreshExprMVar expected) (node "element" #[descriptor, expression])
  unless result.isOk == accepted do
    throwError "short-tag selected-interface control failed for {id}: {repr result}"

run_elab do
  let numeral := fun (n : Nat) => node "numeral" #[toJson n]
  let point := node "point" #[node "opaqueData" #[toJson "actual point"]]
  for expression in #[numeral 73,
      node "add" #[numeral 100, numeral 200],
      node "mul" #[numeral 8, numeral 17],
      node "neg" #[numeral 9]] do
    checkTag "obj.rings.integers" #[] #[] expression true
  checkTag "obj.sets.rational_dual_x" #[] #[] (node "generator" #[]) true
  checkTag "obj.sets.naturals" #[] #[] (node "generator" #[]) false
  checkTag "obj.sets.rational_dual_x" #[] #[] (node "generator" #[toJson (0 : Nat)]) false
  for expression in #[node "add" #[point, point], node "mul" #[point, point],
      node "neg" #[point], node "generator" #[]] do
    checkTag "obj.sets.fin" #[Syntax.mkNumLit "5"] #[toJson (5 : Nat)] expression false
  checkTag "obj.sets.fin" #[Syntax.mkNumLit "5"] #[toJson (5 : Nat)] (numeral 4) true
  checkTag "obj.sets.fin" #[Syntax.mkNumLit "5"] #[toJson (5 : Nat)] (numeral 5) false
  checkTag "obj.rings.integers" #[] #[] (node "numeral" #[toJson "not a natural"]) false

/-! An explicit structural view fixes its own operation owner. The retained
ring parameter supplies the actual action; it cannot restore a binding absent
from the selected monoid interface. -/
run_elab do
  let state ← registryState
  let some ring := state.objects.find? (·.id.raw == "obj.rings.integers")
    | throwError "the declared source ring is unavailable"
  let some functor := state.functor? FunctorId.ringsMultiplicative
    | throwError "the declared structural view is unavailable"
  let original ← Semantic.object ring #[]
  let action ← Semantic.asFunctor (← Semantic.edgeFunctor state (.functor functor.id))
  let selected ← Semantic.objOf action original
  let (_, bundle) ← functorCategoryBundles action
  let value ← (Language.objectInContext selected { expression := functor.target, bundle }).run {}
  let carrier ← (Language.semanticObject (← (Language.carrierObject value).run {})).run {}
  let expected ← mkAppM ``Quiver.Hom #[← Language.globalPointSource.run {}, carrier]
  let descriptor := node "functorAction" #[node functor.id.raw #[], node ring.id.raw #[]]
  let point := node "point" #[node "opaqueData" #[toJson "actual selected-view operand"]]
  for (tag, accepted) in #[("mul", true), ("add", false)] do
    let result ← ComputationalData.validateElementAt selected descriptor
      (← mkFreshExprMVar expected) (node "element" #[descriptor, node tag #[point, point]])
    unless result.isOk == accepted do
      throwError "the short tag borrowed an operation from a different selected owner: {repr result}"

/- An operation with a separate result object obtains each operand's selection
from its exact declaration parameters, rather than from that result object. -/
run_elab do
  let state ← registryState
  let some order := state.objects.find? (·.declaration ==
      ``CasCatalogue.Foundation.PowerSets.orderIntegers)
    | throwError "the accepted integer order is unavailable"
  let expression := node "operationExpression" #[toJson "op.linear_orders.le",
    Json.arr #[node order.id.raw #[]],
    Json.arr #[node "numeral" #[toJson (37 : Nat)], node "numeral" #[toJson (12 : Nat)]]]
  checkTag "obj.sets.truth_values" #[] #[] expression true
