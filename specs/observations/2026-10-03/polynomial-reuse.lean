module
import CasCatalogue.Realize
meta import CasCatalogue.Realize
open Lean Meta Elab Command Term
open CasCatalogue CasCatalogue.Language CasCatalogue.Realize
run_cmd liftTermElabM do
  let parse (text : String) : TermElabM Syntax := do
    let .ok stx := Parser.runParserCategory (← getEnv) `cas_term text
      | throwError "the existing polynomial expression does not parse"
    return stx
  let scope : Language.Scope := ({} : Language.Scope).insert `p
    (← parse "x ↦ x³ - 2x + 1 in ℤ[x]")
  let trace : Trace ← IO.mkRef {}
  let .ok assertion := Parser.runParserCategory (← getEnv) `cas_stmt
      "assert ((p in ℤ[x] ∖ 0).factorization()).product().deg() = 3"
    | throwError "the connected scalar observation does not parse"
  let question ← (Language.claim scope assertion).run { trace := some trace }
  let harness ← Harness.load (some "/workspace/lean-cas-dsl-leaves/leaves.json")
  let requests ← IO.mkRef #[]
  let harness := { harness with computationOnly := true, dispatches := some requests }
  try
    let outcome ← realizeClaim harness trace question
    logInfo m!"CONNECTED OBSERVATION {repr outcome}"

  catch error => logInfo m!"PRODUCTION FAILURE {← error.toMessageData.toString}"
  IO.FS.writeFile "/tmp/b0-root-independent-polynomial-observation-full.json" (Json.arr (← requests.get)).pretty
  IO.FS.writeFile "/tmp/b0-root-independent-polynomial-observation-full.json" (Json.arr (← requests.get)).pretty
  let inputs := (← requests.get).map fun request => Json.mkObj [
    ("operation", (request.getObjVal? "operation").toOption.get!),
    ("input", (request.getObjVal? "input").toOption.get!),
    ("request", (request.getObjVal? "request").toOption.get!)]
  IO.FS.writeFile "/tmp/b0-root-independent-polynomial-observation-input-only.json" (Json.arr inputs).pretty
  harness.stop
