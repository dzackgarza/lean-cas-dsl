/- Copyright (c) 2026 Dzack Garza. Released under Apache 2.0 license. -/
module

import CasCatalogue.Semantic
import CasCatalogue.CategoryContext
import CasCatalogue.QuestionIdentity
import LeanCategories.Catalogue.Semantics
meta import CasCatalogue.Semantic
meta import CasCatalogue.CategoryContext
meta import CasCatalogue.QuestionIdentity
meta import LeanCategories.Catalogue.Semantics

/-! Engineering controls for generic producer addresses. Inert nodes below add no
registry row or mathematical assertion. The live control uses existing cardinality
and its existing underlying functor, and evaluates no computational answer. -/

open Lean Meta Elab Command Term CasCatalogue CasCatalogue.Realize

private def completeEntries (trace : Trace) : TermElabM (Array (Expr × Node)) := do
  (← trace.get).toArray.mapM fun (value, node) => do
    return (← instantiateMVars value, ← node.mapTermsM fun term => instantiateMVars term)

private def rejected (action : TermElabM Unit) : TermElabM Bool := do
  try
    action
    return false
  catch _ => return true

run_cmd liftTermElabM <| withoutErrToSorry <| withCurrHeartbeats do
  let trace ← Trace.new
  let zero := mkRawNatLit 0
  let one := mkRawNatLit 1
  let firstNode := Node.functor ⟨"engineering.producer.first"⟩ #[one] zero
  let secondNode := Node.construction ⟨"engineering.producer.second"⟩ #[one] zero
  let first ← Trace.recordProduced (some trace) zero firstNode
  let second ← Trace.recordProduced (some trace) zero secondNode
  unless first != second && Trace.unanchor first == Trace.unanchor second do
    throwError "distinct producers did not retain separate keys at an equal formal value"
  unless (← trace.node? first) == some firstNode &&
      (← trace.node? second) == some secondNode do
    throwError "a later producer replaced an earlier selected record"
  if ← QuestionIdentity.equivalent first second then
    throwError "producer comparison discarded the selected operation association"
  let repeated ← Trace.recordProduced (some trace) zero firstNode
  unless repeated != first && (← QuestionIdentity.equivalent first repeated) &&
      (← termIdentity first) == (← termIdentity repeated) do
    throwError "anonymous allocation history became part of the selected question"
  let entries ← completeEntries trace
  Trace.checkProducedEntries entries #[first, second, repeated]
  unless entries.size == 3 && (Trace.identityEntries entries).size == 2 do
    throwError "administrative duplication changed the semantic operation inventory"
  unless ← rejected (do Trace.checkProducedEntries #[(first, secondNode)] #[first]) do
    throwError "a producer description self-certified a different actual node"
  unless ← rejected (do Trace.checkProducedEntries #[(zero, firstNode), (zero, secondNode)]) do
    throwError "closing legacy trace keys silently discarded a selected operation"
  unless (Trace.identityEntries #[(zero, firstNode), (zero, firstNode)]).size == 2 do
    throwError "the administrative quotient erased legacy explicit multiplicity"
  let legacy ← Trace.new
  Trace.record (some legacy) zero firstNode
  Trace.record (some legacy) zero firstNode
  unless ← rejected (do Trace.record (some legacy) zero secondNode) do
    throwError "legacy recovery silently replaced a different producer"
  Trace.record (some legacy) one secondNode
  unless ← rejected (do Trace.alias (some legacy) zero one) do
    throwError "legacy alias recovery silently replaced a different producer"
  unless (← legacy.node? zero) == some firstNode &&
      (← legacy.node? one) == some secondNode do
    throwError "a rejected legacy recovery changed the retained records"
  let selected ← mkAppM ``Trace.operationResult #[mkStrLit "engineering.binding", mkConst ``Nat.succ]
  let callable ← Trace.recordProduced (some trace) selected firstNode
  unless Trace.unanchor (mkApp callable zero) == mkApp selected zero do
    throwError "applied producer inspection lost the meaningful binding or actual argument"
  let originalProof ← instantiateMVars (← elabTermAndSynthesize (← `(Eq.refl (0 : Nat))) none)
  let otherProof ← instantiateMVars
    (← elabTermAndSynthesize (← `(Eq.symm (Eq.refl (0 : Nat)))) none)
  unless (← QuestionIdentity.equivalent originalProof otherProof) &&
      (Trace.identityEntries #[(originalProof, firstNode), (otherProof, firstNode)]).size == 2 do
    throwError "administrative coalescing changed the existing proof-key multiplicity"

/- Identical selected calls may be shared or separately allocated. Ordered operands
still retain their complete selected producer, independently of equal formal values. -/
run_cmd liftTermElabM <| withoutErrToSorry <| withCurrHeartbeats do
  let trace ← Trace.new
  let zero := mkRawNatLit 0
  let leaf := Node.functor ⟨"engineering.producer.leaf"⟩ #[] zero
  let first ← Trace.recordProduced (some trace) zero leaf
  let repeated ← Trace.recordProduced (some trace) zero leaf
  let shared ← Trace.recordProduced (some trace) zero
    (.construction ⟨"engineering.producer.pair"⟩ #[first, first] zero)
  let duplicated ← Trace.recordProduced (some trace) zero
    (.construction ⟨"engineering.producer.pair"⟩ #[first, repeated] zero)
  unless (← QuestionIdentity.equivalent shared duplicated) &&
      (← termIdentity shared) == (← termIdentity duplicated) do
    throwError "sharing identical selected producers changed their question"
  let changed ← Trace.recordProduced (some trace) zero
    (.functor ⟨"engineering.producer.other_leaf"⟩ #[] zero)
  let ordered ← Trace.recordProduced (some trace) zero
    (.construction ⟨"engineering.producer.pair"⟩ #[first, changed] zero)
  let reversed ← Trace.recordProduced (some trace) zero
    (.construction ⟨"engineering.producer.pair"⟩ #[changed, first] zero)
  if ← QuestionIdentity.equivalent ordered reversed then
    throwError "equal formal values concealed changed producer operand positions"
  let entries ← completeEntries trace
  Trace.checkProducedEntries entries #[shared, duplicated, ordered, reversed]
  unless (Trace.identityEntries entries).size == 5 do
    throwError "the semantic inventory lost selected content or retained allocation duplication"
  let forkA ← IO.mkRef (← trace.get)
  let forkB ← IO.mkRef (← trace.get)
  let a ← withoutModifyingState <| Trace.recordProduced (some forkA) zero leaf
  let b ← withoutModifyingState <| Trace.recordProduced (some forkB) zero leaf
  unless a != b && (← QuestionIdentity.equivalent a b) do
    throwError "trace forks or elaborator rollback reused an execution occurrence"
  for (value, node) in (← forkA.get).toArray ++ (← forkB.get).toArray do
    trace.modify (·.insert value node)
  unless (← trace.node? a) == some leaf && (← trace.node? b) == some leaf do
    throwError "merging independent branches lost an occurrence"

/- Closing two values must retain both original execution keys. -/
run_cmd liftTermElabM <| withoutErrToSorry <| withCurrHeartbeats do
  let trace ← Trace.new
  let first ← mkFreshExprMVar (mkConst ``Nat)
  let second ← mkFreshExprMVar (mkConst ``Nat)
  let a ← Trace.recordProduced (some trace) first
    (.functor ⟨"engineering.producer.open_first"⟩ #[] first)
  let b ← Trace.recordProduced (some trace) second
    (.functor ⟨"engineering.producer.open_second"⟩ #[] second)
  first.mvarId!.assign (mkRawNatLit 0)
  second.mvarId!.assign (mkRawNatLit 0)
  let a ← instantiateMVars a
  let b ← instantiateMVars b
  let entries ← completeEntries trace
  Trace.checkProducedEntries entries #[a, b]
  unless a != b && Trace.unanchor a == Trace.unanchor b &&
      (Std.HashMap.ofArray entries).size == 2 do
    throwError "trace finalization merged independently selected producers"

/- The actual source collision: the selected method and direct registered object
action have the same underlying functor application but distinct public producers. -/
run_cmd liftTermElabM <| withoutErrToSorry <| withCurrHeartbeats do
  let state ← registryState
  let some sets := state.categories.find? (·.id == CategoryId.sets)
    | throwError "the existing Sets category is absent"
  let #[method] := state.methods.filter fun entry =>
      entry.name == "cardinality" && entry.owner.syntacticEq sets.expression
    | throwError "the existing cardinality method is absent or ambiguous"
  let some functor := state.functor? method.functor
    | throwError "the existing cardinality functor is absent"
  let receiver ← instantiateMVars (← elabTermAndSynthesize (← `(Fin 3)) none)
  for reversed in #[false, true] do
    let trace ← Trace.new
    let (methodValue, _) ← Semantic.methodIn method.name receiver sets.expression (some trace)
    let some (.method selected route source comparisons application) ← trace.node? methodValue
      | throwError "the actual method lost its retained application"
    let (direct, _) ← Semantic.applyRegisteredFunctor functor application.input #[] (some trace)
    let methodValue ← if reversed then do
        pure (← Semantic.methodIn method.name receiver sets.expression (some trace)).1
      else pure methodValue
    unless Trace.unanchor methodValue == Trace.unanchor direct && methodValue != direct do
      throwError "the existing collision control did not retain one raw action and distinct producers"
    let some (.method actual actualRoute actualSource actualComparisons actualApplication) ←
        trace.node? methodValue
      | throwError "the direct functor action replaced the selected method"
    unless actual == selected && actualRoute == route && actualSource == source &&
        actualComparisons == comparisons && actualApplication == application do
      throwError "a producer changed the complete original method application"
    let some (.functor actual _ actualInput) ← trace.node? direct
      | throwError "the method replaced the directly selected functor action"
    unless actual == functor.id && actualInput == application.input do
      throwError "the direct action changed its selected functor or exact input"
    Trace.checkProducedEntries (← completeEntries trace) #[methodValue, direct]
  let trace ← Trace.new
  let context ← CategoryContext.ofNamed sets receiver
  let identity ← mkAppM ``CategoryTheory.CategoryStruct.id #[receiver]
  let parent ← Trace.recordProduced (some trace) identity (.contextualIdentity context receiver)
  let source ← Trace.recordProduced (some trace) receiver (.callableEndpoint context parent true)
  let target ← Trace.recordProduced (some trace) receiver (.callableEndpoint context parent false)
  unless source != target && Trace.unanchor source == Trace.unanchor target &&
      (parent.find? (fun term => term == source || term == target)).isNone do
    throwError "equal callable endpoints lost their positions or introduced a parent cycle"
  if ← QuestionIdentity.equivalent source target then
    throwError "the selected source and target endpoint roles were identified by their values"
  Trace.checkProducedEntries (← completeEntries trace) #[parent, source, target]

/- Repeated typed fields share existing expression subterms. This observes the
representation and serializer size; it changes no evaluation or heartbeat budget. -/
run_cmd liftTermElabM <| withoutErrToSorry <| withCurrHeartbeats do
  let trace ← Trace.new
  let mut value := mkRawNatLit 0
  let mut sizes := #[]
  for index in [:16] do
    value ← Trace.recordProduced (some trace) (mkRawNatLit 0)
      (.functor ⟨"engineering.producer.chain"⟩ #[value, value] value)
    if index == 7 || index == 15 then
      let table ← TermTable.new
      discard <| table.encode value
      sizes := sizes.push (← table.nodes.get).size
  let #[short, long] := sizes | throwError "the producer chain size control lost its checkpoints"
  unless short > 0 && long > short && long <= 3 * short do
    throwError "a repeated-field producer chain expanded its serialized expression DAG"
  logInfo m!"producer occurrence DAG: 8 stages = {short} nodes; 16 stages = {long} nodes"
