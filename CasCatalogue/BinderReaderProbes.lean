module

import CasCatalogue.Language
meta import CasCatalogue.Language

open Lean Meta Elab Command Term
open CasCatalogue CasCatalogue.Language

/- These probes check one generic interpretation path and retained maps, rather than judging
numerical answers or admitting mathematical assertions. All mathematics is from binder rows. -/
run_cmd liftTermElabM do
  for text in #["assert implemented ∫_{0}^{1} t² dt", "assert implemented ∫_{0}^{1} sin(t) dt",
      "assert implemented lim_{t → 0} t²",
      "assert implemented lim_{t → 0} sin(t)/t", "assert implemented lim_{t → ∞} 1/t"] do
    let .ok statement := Parser.runParserCategory (← getEnv) `cas_stmt text
      | throwError "binder reader probe failed to parse: {text}"
    let trace ← Trace.new
    discard <| (claim {} statement).run { trace := some trace }
    let records := (← trace.get).toArray.filterMap fun (_, node) => match node with
      | .binder id params domain body admitted => some (id, params, domain, body, admitted)
      | _ => none
    let #[(id, params, domain, body, admitted)] := records
      | throwError "binding syntax did not use exactly one recorded registered binder"
    let some row := (← registryState).binders.find? (·.id == id)
      | throwError "the binder trace has no accepted registered row"
    unless !(params.any (·.hasMVar)) && !domain.hasMVar && !body.hasMVar && !admitted.hasMVar do
      throwError "a binder trace retained unresolved parameters"
    let some (actualDomain, _) := homEnds? (← whnfR (← inferType body))
      | throwError "the binder trace lost its map"
    unless ← isDefEq actualDomain domain do
      throwError "the binder trace replaced its actual domain"
    unless row.token == "∫" || row.token == "lim" do
      throwError "the binder interpretation changed its registered surface token"
