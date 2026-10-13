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

/- The admitted root-sum and root-product statements must also read within the ordinary
budget. Their expensive, context-free argument is shared across binder candidates; each
candidate still checks its own complete signature. No numerical answer is checked here. -/
run_cmd liftTermElabM do
  let .ok binding := Parser.runParserCategory (← getEnv) `cas_stmt
      "let r(x) := x³ - 2x + 1 in ℚ[x]"
    | throwError "the admitted polynomial binding failed to parse"
  let some (name, value) ← letBinding? binding
    | throwError "the admitted polynomial binding has no bound value"
  let scope : Language.Scope := ({} : Language.Scope).insert name value
  for text in #[
      "assert ∑_{a ∈ ((map r to ℂ[x]) in ℂ[x] ∖ 0).roots()} a = 0",
      "assert ∏_{a ∈ ((map r to ℂ[x]) in ℂ[x] ∖ 0).roots()} a = -1"] do
    withCurrHeartbeats do
      let .ok statement := Parser.runParserCategory (← getEnv) `cas_stmt text
        | throwError "the admitted root binder failed to parse"
      let trace ← Trace.new
      discard <| (claim scope statement).run { trace := some trace }
      let records := (← trace.get).toArray.filterMap fun (_, node) => match node with
        | .binder id params domain body admitted => some (id, params, domain, body, admitted)
        | _ => none
      let #[(id, params, domain, body, admitted)] := records
        | throwError "the root binder did not retain one selected operation"
      let some row := (← registryState).binders.find? (·.id == id)
        | throwError "the root binder lost its published declaration"
      unless row.token == "∑" || row.token == "∏" do
        throwError "the selected root binder has a different token"
      for term in params ++ #[domain, body, admitted] do
        unless !term.hasMVar && !term.hasLevelMVar && (← isTypeCorrect term) do
          throwError "the root binder retained incomplete or ill-typed data"
      let some (source, _) := homEnds? (← inferType body)
        | throwError "the root binder lost its body map"
      unless ← isDefEq source domain do
        throwError "the root binder changed its generalized-point domain"
