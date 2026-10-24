/- Copyright (c) 2026 Dzack Garza. Released under Apache 2.0 license. -/
module

import CasCatalogue.Realize
meta import CasCatalogue.Realize

/-! A numeral read under a variable retains its actual closed point and the
registered terminal-map composition. These controls inspect the complete public
callable interface and forwarding of an actual point packet; they do not compute
or prescribe a mathematical answer. -/

open Lean Meta Elab Term CategoryTheory
open CasCatalogue CasCatalogue.Language CasCatalogue.Realize

meta section

private def readTerm (text : String) : TermElabM Syntax := do
  let .ok term := Parser.runParserCategory (← getEnv) `cas_term text
    | throwError "the staged-numeral fixture did not parse"
  pure term

private def checkStagedNumeral (selected : String) : TermElabM Unit := do
  let trace ← Trace.new
  let stage ← (eval {} (← readTerm "ℕ in Sets")).run { trace := some trace }
  let selectedValue ← (eval {} (← readTerm selected)).run { trace := some trace }
  let .element stagedPoint _ ← (toElement (.nat 2) selectedValue).run {
      trace := some trace, stage := some stage }
    | throwError "the staged numeral did not retain its typed point"
  let some (.morphismComposition _ terminal closedPoint domain one target) ←
      trace.node? stagedPoint
    | throwError "a staged numeral overwrote its registered terminal-map composition"
  let some (.elementNumeral 2 closedTarget _) ← trace.node? closedPoint
    | throwError "the numeral was not recorded at its original closed point"
  unless ← withTransparency .all <|
      isDefEq domain (← (semanticObject stage).run {}) <&&>
      isDefEq one (← Language.globalPointSource.run {}) <&&>
      isDefEq target closedTarget <&&>
      isDefEq (← inferType closedPoint) (← mkAppM ``Quiver.Hom #[one, target]) do
    throwError "the staged numeral changed its complete original endpoints"
  let expected ← mkAppM ``Quiver.Hom #[domain, target]
  unless ← withTransparency .all <| isDefEq (← inferType stagedPoint) expected do
    throwError "the numeral's complete variable domain was changed"
  let harness ← Harness.empty
  let wire ← realize harness trace "the staged numeral" stagedPoint
  let .ok ("compose", #[_, closedData]) := ComputationalData.envelope wire.json
    | throwError "the staged numeral did not use the existing composition encoding"
  if let .error message ← ComputationalData.validateCallableAt #[] expected wire.json then
    throwError "the staged numeral has an invalid complete callable interface: {message}"
  if (← ComputationalData.validateCallableAt #[] expected closedData).isOk then
    throwError "a closed point packet was silently treated as a generalized map"
  let original ← realize harness trace "the original numeral" closedPoint
  let owned := { original with
    payload := .computed closedPoint (.owned "staged-point-owner" 509
      (Json.mkObj [("ctor", "opaqueData"), ("args", Json.arr #[toJson "actual point"])])) }
  let reuse ← Harness.empty
  reuse.results.modify (·.insert closedPoint owned)
  let forwarded ← realize reuse trace "the staged actual point" stagedPoint
  let .ok ("compose", #[terminalData, actualData]) := ComputationalData.envelope forwarded.json
    | throwError "the staged actual point lost its original composition"
  let actualTerminal ← realize reuse trace "the retained terminal map" terminal
  unless actualData == owned.json && terminalData == actualTerminal.json &&
      forwarded.owner? == owned.owner? do
    throwError "restaging replaced the actual point packet or its live owner"

run_elab checkStagedNumeral "ℤ"
run_elab checkStagedNumeral "ℤ in Rings"

end
