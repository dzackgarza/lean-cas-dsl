/- Copyright (c) 2026 Dzack Garza. Released under Apache 2.0 license. -/
module

import CasCatalogue.Realize
meta import CasCatalogue.Realize

/-! Engineering checks of actual portable reply provenance and reuse. The existing
wrong-answer port specimen is deliberately used: preserving its returned data is
required regardless of mathematical correctness. No expected mathematical answer
is obtained from the specimen and no permanent assertion is changed. -/

open Lean Meta Elab Term CasCatalogue CasCatalogue.Language CasCatalogue.Realize

run_elab do
  let .ok parsed := Parser.runParserCategory (← getEnv) `cas_term "|Fin(3)|"
    | throwError "the portable-reply probe did not parse"
  let trace ← Trace.new
  discard <| (eval {} parsed).run { trace := some trace }
  let candidates := (← trace.get).toArray.filter fun (_, node) => match node with
    | .method id _ _ _ _ => id.raw == "meth.cardinality"
    | _ => false
  let #[(formal, _)] := candidates
    | throwError "the portable-reply probe lost its unique declared operation"
  let observations ← IO.mkRef #[]
  let harness ← Harness.load (some ("CasAcceptance" / "Strata" / "registration_wrong.json"))
  let harness := { harness with dispatches := some observations }
  try
    let first ← realize harness trace "the first actual portable answer" formal
    let .computed actual (.inline data) := first.payload
      | throwError "a portable backend answer became ordinary formal input"
    unless actual == formal && data == first.json && first.owner?.isNone do
      throwError "portable reply provenance changed its original formal term or actual data"
    let #[sent] ← observations.get
      | throwError "the first portable computation did not dispatch exactly once"
    let .ok answer := sent.getObjVal? "response"
      | throwError "the kernel did not retain its actual received answer"
    unless data == answer do
      throwError "the returned computational data were replaced with the formal plan"
    let again ← realize harness trace "the same retained portable answer" formal
    unless again.json == data && again.value == formal &&
        (← observations.get).size == 1 do
      throwError "a reused portable result was replaced or executed a second time"
    unless again.payload matches .computed _ (.inline _) do
      throwError "reuse erased the actual portable answer's computational origin"
  finally
    harness.stop

-- Encoding a computed operand must use its returned data even when its retained
-- mathematical trace is an ordinary operation expression. Tokens here are data
-- flow witnesses only; they are not asserted to denote a mathematical value.
run_elab do
  let .ok parsed := Parser.runParserCategory (← getEnv) `cas_term "2 + 3"
    | throwError "the computed-operand probe did not parse"
  let trace ← Trace.new
  discard <| (eval {} parsed).run { trace := some trace }
  let candidates := (← trace.get).toArray.filter fun (_, node) => match node with
    | .operationApply .. => true
    | _ => false
  let #[(formal, _)] := candidates
    | throwError "the computed-operand probe lost its declared operation"
  let state ← registryState
  let some sets := state.categories.find? (·.id == CategoryId.sets)
    | throwError "the fixed point category is unavailable"
  for payload in #[WirePayload.computed formal (.inline (toJson (91 : Nat))),
      WirePayload.computed formal (.opaque "retained-point" 51 "actual computed operand")] do
    let actual : Wire := { form := .canonicalMorphism sets, payload }
    let harness ← Harness.empty
    harness.results.modify (·.insert formal actual)
    let (encoded, dependencies) ← elementExpression harness trace formal
    let .ok ("point", #[data]) := ComputationalData.envelope encoded
      | throwError "a computed operand was expanded back into its formal operation"
    let #[dependency] := dependencies
      | throwError "the computed operand lost its original data dependency"
    unless data == actual.json && dependency.json == actual.json &&
        dependency.value == formal && dependency.owner? == actual.owner? do
      throwError "the computed operand replaced actual data or lost its owning session"
