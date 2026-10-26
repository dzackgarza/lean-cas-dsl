/- Copyright (c) 2026 Dzack Garza. Released under Apache 2.0 license. -/
module

import CasCatalogue.Language
meta import CasCatalogue.Language
import LeanCategories.Catalogue.Semantics.Independent.ScalarAndFormExtensions
meta import LeanCategories.Catalogue.Semantics.Independent.ScalarAndFormExtensions

open Lean Meta Elab Command Term CasCatalogue CasCatalogue.Language

/- Both a closed object and a genuinely open local object keep the original complete
route result. The latter cannot retain its trial image after speculative state restoration. -/
run_cmd liftTermElabM <| withoutErrToSorry <| withCurrHeartbeats do
  let state ← registryState
  let some groups := state.categories.find? (·.id == CategoryId.groups)
    | throwError "the route control has no complete group category"
  let some sets := state.categories.find? (·.id == CategoryId.sets)
    | throwError "the route control has no Sets category"
  let expected ← elabTermAndSynthesize (← `(Type)) none
  let check (receiver : Expr) (openReceiver : Bool) : TermElabM Unit := do
    let trace ← Trace.new
    let context : Ctx := { trace := some trace }
    let value := Value.object receiver groups none none none
    let (image, route, applications) ←
      (transportedStructureWithAction expected value (some sets.id)).run context
    let (freshImage, freshApplications) ←
      (checkedRouteAction state groups.id sets.id route receiver expected).run {}
    unless image == freshImage && applications == freshApplications &&
        (← inferType image) == (← inferType freshImage) && (← isTypeCorrect image) do
      throwError "retaining a local route trial changed its complete checked construction"
    unless image.hasFVar == openReceiver && closedReadingTerm image == !openReceiver do
      throwError "the route control lost its genuinely open or closed receiver"
    let some (.retainedRoute source target recorded actual original) ← trace.node? image
      | throwError "the selected route lost its actual provenance"
    unless source == groups.id && target == sets.id && recorded == route &&
        actual == applications && original == receiver do
      throwError "the selected route changed its full receiver or edge applications"
  let closed ← elabTermAndSynthesize (← `(GrpCat.of (Equiv.Perm (Fin 3)))) none
  check closed false
  let objectType ← elabTermAndSynthesize (← `(GrpCat.{0})) none
  withLocalDeclD `actualGroup objectType fun receiver => check receiver true
