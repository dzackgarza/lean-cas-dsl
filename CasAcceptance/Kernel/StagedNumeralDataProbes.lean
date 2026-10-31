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
  let some context := original.categoryContext
    | throwError "the original closed point lost its complete category"
  CategoryContext.checkMorphism context closedPoint one target
  let closedType ← inferType closedPoint
  let node := fun (tag : String) (arguments : Array Json) =>
    Json.mkObj [("ctor", toJson tag), ("args", Json.arr arguments)]
  let root : System.FilePath := (← IO.getEnv "CAS_OWNERSHIP_PROTOCOL_DIR").getD
    ("CasAcceptance" / "Strata" : System.FilePath).toString
  let backend := "staged-point-probe"
  -- This existing protocol-only process supplies an arbitrary owned callable
  -- witness. It registers no mathematical operation and computes no answer.
  let reuse ← Harness.ofManifest root {
    backends := #[{
      name := backend
      command := "python3"
      args := #["probe_owned_callable.py", "staged-point"] }]
    registrations := #[] }
  try
    let .ok session ← reuse.connection backend
      | throwError "the staged-point ownership process did not start"
    let .ok answer ← Backend.call session.connection "staged-point"
        (node "staged-point" #[original.json])
      | throwError "the staged-point ownership process did not return its input witness"
    match Backend.ComputationalValue.decode answer with
    | .ok (.opaque _) => pure ()
    | _ => throwError "the staged-point fixture did not return an anonymous packet"
    let received ← receiveComputationalData reuse backend "staged-point" answer
    -- The original full Hom fixes this supplied point-map's formal interface.
    -- Fresh data do not inherit the old recipe's framing or producer receipts.
    let supplied : Wire := {
      form := original.form
      payload := .computed closedPoint received
      categoryContext := some context }
    if let .error message ← ComputationalData.validateCallableAt #[] closedType supplied.json then
      throwError "the staged actual point changed its original complete Hom: {message}"
    checkDataOwners reuse supplied.fragment
    let owned ← captureCompleteCallable reuse trace supplied context
    let .ok ("typedMap", #[_, _, actualPacket]) := ComputationalData.envelope owned.json
      | throwError "the staged actual point lost its complete callable frame"
    unless actualPacket == supplied.json && owned.value == closedPoint &&
        owned.owner? == some (backend, session.identity) do
      throwError "capturing the staged point changed its actual packet, original value or live supplier"
    checkDataOwners reuse owned.fragment
    if let .error message ← ComputationalData.validateCallableAt #[] closedType owned.json then
      throwError "the captured staged point lost its original complete callable interface: {message}"
    -- Supply the authenticated complete occurrence at the original fixture's
    -- exact closed-point key. The ordinary reader-generated staging path below
    -- remains the subject of this regression; no composite is built here.
    reuse.results.modify (·.insert closedPoint owned)
    let forwarded ← realize reuse trace "the staged actual point" stagedPoint
    let .ok ("compose", #[terminalData, actualData]) := ComputationalData.envelope forwarded.json
      | throwError "the staged actual point lost its original composition"
    let actualTerminal ← captureCompleteCallable reuse trace
      (← realize reuse trace "the retained terminal map" terminal) context
    unless actualData == owned.json && terminalData == actualTerminal.json &&
        forwarded.owner? == owned.owner? do
      throwError "restaging replaced the actual point packet or its live owner"
    checkDataOwners reuse forwarded.fragment
    let unavailable (active : Harness) : TermElabM Bool := do
      try
        checkDataOwners active forwarded.fragment
        return false
      catch error => return Exception.stratum? error == some .unavailable
    unless ← unavailable (← Harness.empty) do
      throwError "the restaged point became available outside its actual owning session"
    reuse.stop
    unless ← unavailable reuse do
      throwError "the restaged point survived expiry of its actual owning session"
  finally reuse.stop

run_elab checkStagedNumeral "ℤ"
run_elab checkStagedNumeral "ℤ in Rings"

end
