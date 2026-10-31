module

import CasCatalogue.Language
meta import CasCatalogue.Language

open Lean Elab Command Term
open CasCatalogue CasCatalogue.Language

/- Reader boundary regression: an applied, closed carrier projection inside a supplied
presentation must not hide its carrier from the registered admission procedure. The kernel
retains the mathematical value and obtains all evidence from that procedure. -/
run_cmd liftTermElabM do
  let .ok parsed := Parser.runParserCategory (← getEnv) `cas_term
      "[1, 2; 3, 4] in Mat₂(ℚ)ˣ"
    | throwError "the matrix-unit binding did not parse"
  let .element .. ← (eval {} parsed).run {}
    | throwError "the registered admission did not produce its point"

/- Exposing a carrier does not remove the original admission obligation. -/
run_cmd liftTermElabM do
  let .ok parsed := Parser.runParserCategory (← getEnv) `cas_term
      "[1, 2; 2, 4] in Mat₂(ℚ)ˣ"
    | throwError "the singular-matrix binding did not parse"
  let refused ← try
    discard <| (eval {} parsed).run {}
    pure false
  catch error =>
    if (← Outcome.ofException error).kind == "invalid" then pure true else throw error
  unless refused do
    throwError "exposing the carrier discarded the registered admission obligation"
