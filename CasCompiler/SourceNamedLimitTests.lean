module

import CasCompiler.Read
import CasCompiler.Layout
import LeanCategories.Catalogue.Semantics.Limits.Registration
import LeanCategories.Catalogue.Semantics.Foundation.Morphisms
import LeanCategories.Catalogue
public meta import Lean.Elab.Command
meta import CasCompiler.Read
meta import CasCompiler.Layout
meta import LeanCategories.Catalogue.Semantics.Limits.Registration
meta import LeanCategories.Catalogue.Semantics.Foundation.Morphisms
meta import LeanCategories.Catalogue

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

/- A limit in a category that only creates it is the registered limit of the image diagram,
returned along the registered creation lift: `pullback(f', g')` of finite sets is the lifted apex
of the pullback of sets (`lift.finite_sets.pullbacks`, tests/acceptance/sets.cas). -/
run_cmd Lean.Elab.Command.liftTermElabM do
  let identities ← liftM (m := IO) CasRuntime.IdentitySupply.new
  let empty ← SourceSession.empty identities
  let f ← empty.read (← sourceTerm "{0 ↦ 0, 1 ↦ 1, 2 ↦ 1} : (Fin(3) in FiniteSets) → (Fin(2) in FiniteSets)")
  let session ← empty.defineTerm `f' f
  let g ← session.read (← sourceTerm "{0 ↦ 1, 1 ↦ 0} : (Fin(2) in FiniteSets) → (Fin(2) in FiniteSets)")
  let session ← session.defineTerm `g' g
  let result ← session.read (← sourceTerm "pullback(f', g')")
  unless result.category.any (·.role == .object) do
    throwError "the created pullback did not read as an object"
  result.source.withOpen fun _ value => do
    let value ← instantiateMVars value
    unless (value.find? (·.isAppOf ``CategoryTheory.liftLimit)).isSome &&
        (value.find? (·.isAppOf ``CasCatalogue.Limits.Registration.setsPullback)).isSome do
      throwError "the pullback is not the lifted registered pullback of sets: {value}"
  let session ← session.defineTerm `P result
  let session ← session.defineTerm `retainedP (← session.read (← sourceTerm "P"))
  let session ← session.defineTerm `f' g
  let session ← session.defineTerm `g' f
  let retained ← session.read (← sourceTerm "retainedP")
  let some selection := retained.category.bind (·.limit)
    | throwError "the created pullback alias lost its selected interface"
  retained.source.withOpen fun bindings _ => do
    let context ← ContextTelescope.capture bindings
    let interface ← selection.interface.mapM (·.inContext context)
    let sourceDiagram ← selection.diagram.inContext context
    let sourcePresentation ← selection.presentation.inContext context
    let some comparison := interface.standardization
      | throwError "the created pullback lost its accepted diagram transport"
    unless sourcePresentation.containsConst (· == ``CategoryTheory.liftLimit) &&
        sourcePresentation.containsConst (· == ``CategoryTheory.liftedLimitIsLimit) &&
        interface.presentation.consumeMData.getAppFn.isConstOf
          ``CasCatalogue.Limits.Registration.setsPullback do
      throwError "creation lost its source lifted presentation or accepted target presentation"
    for original in #[bindings[0]!, bindings[1]!] do
      unless sourceDiagram.containsFVar original.expression.fvarId! &&
          interface.presentation.containsFVar original.expression.fvarId! &&
          comparison.containsFVar original.expression.fvarId! do
        throwError "created pullback transport replaced an original source map"
    let some constructor := interface.dataConstructor
      | throwError "the created pullback lost its target cone constructor"
    let cone ← mkAppM ``CategoryTheory.Limits.LimitCone.cone #[interface.presentation]
    let arguments ← #[
      ``CategoryTheory.Limits.Cone.pt, ``CategoryTheory.Limits.PullbackCone.fst,
      ``CategoryTheory.Limits.PullbackCone.snd,
      ``CategoryTheory.Limits.PullbackCone.condition].mapM fun projection =>
        mkAppM projection #[cone]
    let callable ← SourceLayout.ofTerm (← context.close constructor)
    let (_, application) ← ApplicationLayout.ofSource callable context
      (← arguments.mapM context.close)
    unless application.arguments.map (·.wireIndex) == #[some 0, some 1, some 2, none] &&
        application.arguments.map (·.precedingDependencies) == #[#[], #[0], #[0], #[0, 1, 2]] &&
        application.arguments.map (·.binderInfo) == #[.implicit, .default, .default, .default] do
      throwError "the selected pullback constructor changed its dependent computational ports"
    let some conditionArgument := application.arguments[3]?
      | throwError "the prepared pullback omitted its formal commutation condition"
    let condition ← conditionArgument.typeFamily.inContext context
    unless condition.containsFVar bindings[0]!.expression.fvarId! &&
        condition.containsFVar bindings[1]!.expression.fvarId! do
      throwError "the prepared pullback condition replaced an original source map"
