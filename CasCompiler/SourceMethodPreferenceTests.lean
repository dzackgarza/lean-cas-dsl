module

import CasCompiler.Read
import CasCompiler.SourceTestSupport
import CasCompiler.SourceCarrier
import CasCompiler.SourceRoutes
import CasCompiler.RoutedMethodFamily
import LeanCategories.Catalogue
public meta import Lean.Elab.Command
meta import CasCompiler.Read
meta import CasCompiler.SourceTestSupport
meta import CasCompiler.SourceCarrier
meta import CasCompiler.SourceRoutes
meta import CasCompiler.RoutedMethodFamily
meta import LeanCategories.Catalogue

namespace CasCompiler.SourceMethodPreferenceTests

open Lean Meta Elab Term CasCatalogue CasCompiler.SourceTest

private def sourceTerm (text : String) : TermElabM (TSyntax `cas_term) := do
  let .ok source := Parser.runParserCategory (← getEnv) `cas_term text
    | throwError "the preferred member source did not parse"
  return ⟨source⟩

private def failedReading (read : TermElabM α) : TermElabM Exception :=
  withoutModifyingState do
    let result ← try
      discard <| read
      pure none
    catch error => pure (some error)
    let some error := result | throwError "the invalid member preference was accepted"
    return error



run_cmd Lean.Elab.Command.liftTermElabM do
  let previous := preferredRoutesExtension.getState (← getEnv)
  try
    setPreferredRoutes #[]
    let state ← semanticState
    let rings ← selectCategory state "Rings"
    let query ← SourceRoutes.forMethod rings.expression "cardinality"
    let some routes ← query.finiteRoutes
      | throwError "the actual ring methods require a finite registered route control"
    let distinct := routes.foldl (fun found route =>
      if found.any (·.refs == route.refs) then found else found.push route) (#[] : Array Route)
    let some first := distinct[0]?
      | throwError "the original ring cardinality has no registered route"
    let some chosen := distinct[1]?
      | throwError "the preference control requires two actual distinct ring-method routes"
    let #[method] := state.methods.filter (fun method =>
      method.name == "cardinality" && method.owner.syntacticEq chosen.target)
      | throwError "the selected actual route does not have one cardinality binding"
    let labels := chosen.refs.map (·.label)
    unless !labels.isEmpty do
      throwError "the selected ring-to-cardinality route lost its actual edges"
    let identities ← liftM (m := IO) CasRuntime.IdentitySupply.new
    let empty ← SourceSession.empty identities
    let session ← empty.defineTerm `R (← empty.read (← sourceTerm "ℚ in Rings"))
    let some original := session.context.entries.back?
      | throwError "the preferred method lost its original receiver binding"
    setPreferredRoutes #[{ receiver := rings.id.raw, name := "cardinality", route := labels }]
    let result ← session.read (← sourceTerm "R.cardinality()")
    checkSelected result fun value => do
      let scope ← get
      let some receiver := scope.context.bindings.find? (·.id == original.id)
        | liftM (m := TermElabM) <| throwError "the preferred method lost the actual source occurrence"
      let some selected ← SourceReadM.selection? value
        | liftM (m := TermElabM) <| throwError "the preferred method lost its exact selected source"
      let some application := selected.application
        | liftM (m := TermElabM) <| throwError "the preferred method lost its complete original application"
      let .routedMethod family := application.family
        | liftM (m := TermElabM) <| throwError "the preferred method changed its selected family"
      let #[actual] := application.arguments
        | liftM (m := TermElabM) <| throwError "the preferred method lost its original receiver position"
      unless selected.preferredRoute == some chosen.refs &&
          family.entry.id == method.id && family.route.refs == chosen.refs &&
          (← originatesAt scope.context scope.selections actual receiver.expression) do
        liftM (m := TermElabM) <| throwError "the method did not retain its admitted route and original receiver"
      checkOriginal #[value] fun native => checkWithKernel native[0]!



    let families ← RoutedMethodFamily.atSource rings.expression "cardinality"
    let #[selected] := families.filter (fun family =>
      family.entry.id == method.id && family.route.refs == chosen.refs)
      | throwError "the actual preferred method lost its complete native family"
    discard <| selected.agreements #[]
    let some discarded := families.find? (·.route.refs == first.refs)
      | throwError "the actual alternate route disappeared before the native boundary control"
    let rejected ← failedReading <| discarded.agreements #[]
    unless CasCatalogue.Exception.stratum? rejected == some .invalid do throw rejected


    setPreferredRoutes #[
      { receiver := rings.id.raw, name := "cardinality", route := first.refs.map (·.label) },
      { receiver := rings.id.raw, name := "cardinality", route := labels }]
    let conflict ← failedReading <| session.read (← sourceTerm "R.cardinality()")
    unless CasCatalogue.Exception.isSemanticAmbiguity conflict do throw conflict


    let sets ← selectCategory state "Sets"
    setPreferredRoutes #[{ receiver := sets.id.raw, name := "is_finite", route := #[] }]
    let property ← empty.read (← sourceTerm "Fin(3).is_finite()")
    checkSelected property fun value => do
      let some selected ← SourceReadM.selection? value
        | liftM (m := TermElabM) <| throwError "the preferred property lost its exact selected source"
      unless selected.preferredRoute == some #[] do
        liftM (m := TermElabM) <| throwError "the property discarded its explicitly selected identity route"
      unless ← isProp value do
        liftM (m := TermElabM) <| throwError "the preferred property lost its original proposition"
      checkOriginal #[value] fun native => checkWithKernel native[0]!


    setPreferredRoutes #[{ receiver := sets.id.raw, name := "is_finite", route := labels }]
    let absent ← failedReading <| empty.read (← sourceTerm "Fin(3).is_finite()")
    unless CasCatalogue.Exception.stratum? absent == some .invalid do throw absent
  finally
    setPreferredRoutes previous

end CasCompiler.SourceMethodPreferenceTests
