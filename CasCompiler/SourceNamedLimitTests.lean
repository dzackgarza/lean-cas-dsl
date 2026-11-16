module

import CasCompiler.Read
import LeanCategories.Catalogue.Semantics.Limits.Registration
import LeanCategories.Catalogue.Semantics.Foundation.Morphisms
public meta import Lean.Elab.Command
meta import CasCompiler.Read
meta import LeanCategories.Catalogue.Semantics.Limits.Registration
meta import LeanCategories.Catalogue.Semantics.Foundation.Morphisms

open Lean Meta Elab Term CasCompiler CasCatalogue

private def sourceTerm (text : String) : TermElabM (TSyntax `cas_term) := do
  let .ok source := Parser.runParserCategory (← getEnv) `cas_term text
    | throwError "the limit source did not parse"
  return ⟨source⟩

/- A registered limit named by its shape and applied to the maps of its diagram reads as the
apex of the declared cone at those maps: `pullback(rev(3), rev(3))` is the apex of
`setsPullback (rev 3) (rev 3)`, an object of sets (LimitEntry `lim.sets.pullback`). -/
run_cmd Lean.Elab.Command.liftTermElabM do
  let identities ← liftM (m := IO) CasRuntime.IdentitySupply.new
  let session ← SourceSession.empty identities
  let result ← session.read (← sourceTerm "pullback(rev(3), rev(3))")
  unless result.category.any (·.role == .object) do
    throwError "the pullback did not read as an object"
  result.source.withOpen fun _ value => do
    let value ← instantiateMVars value
    let some presentation := value.find?
        (·.isAppOf ``CasCatalogue.Limits.Registration.setsPullback)
      | throwError "the pullback is not the declared presentation: {value}"
    let rev ← mkAppM ``CasCatalogue.Foundation.Morphisms.finRev #[mkNatLit 3]
    unless ← isDefEq presentation.appFn!.appArg! rev <&&> isDefEq presentation.appArg! rev do
      throwError "the pullback lost its diagram maps: {presentation}"
