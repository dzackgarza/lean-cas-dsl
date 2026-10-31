module

import CasCatalogue.Semantic
import LeanCategories.Catalogue.Semantics
meta import CasCatalogue.Semantic
meta import LeanCategories.Catalogue.Semantics

open Lean Meta Elab Term CasCatalogue

/- Engineering regression: infer complete bundled parameters from public family
witnesses, rather than trying to recover their structure from carrier projections. -/
run_elab do
  let state ← registryState
  let route : Array EdgeRef := #[.functor ⟨"fun.integral_lattice.forget_form"⟩,
    .functor ⟨"fun.bilin_module.fixed_value"⟩]
  let (F, applications) ← Semantic.routeFunctorWithApplications state route
  let X ← elabTermAndSynthesize (← `(LeanCategories.Lattices.Valued.e8Lattice)) none
  let image ← Semantic.objOf F X
  for term in applications.push image do
    let term ← instantiateMVars term
    unless !term.hasMVar && !term.hasLevelMVar && (← isTypeCorrect term) do
      throwError "a composed structural action lost complete selected parameters"
  let some category := state.categories.find? (·.id.raw == "cat.integral_lattice")
    | throwError "the public source category is absent"
  let (result, _) ← Semantic.method "rank" X category
  unless !result.hasMVar && !result.hasLevelMVar && (← isTypeCorrect result) do
    throwError "a registered method lost its complete structural application"

run_elab do
  let state ← registryState
  let some entry := state.functor? ⟨"fun.bilin_module.fixed_value"⟩
    | throwError "the public fixed-value inclusion is absent"
  let X ← elabTermAndSynthesize (← `(
    LeanCategories.Modules.Bilinear.Valued.BilinModuleCat.ofBilinMap
      (0 : LinearMap.BilinMap ℤ ℤ ℤ))) none
  let F ← registeredFunctorInstance entry
  let image ← Semantic.objOf F X
  let F ← instantiateMVars F
  unless !F.hasMVar && !F.hasLevelMVar && !image.hasMVar && !image.hasLevelMVar do
    throwError "the actual structured receiver did not determine its full family parameter"
  let explicit ← elabTermAndSynthesize (← `(
    CasCatalogue.Modules.Bilinear.Valued.Transport.fixedValue ℤ (ModuleCat.of ℤ ℤ))) none
  unless ← withTransparency .all <| isDefEq F explicit do
    throwError "inference selected a different complete value module"
  unless ← isTypeCorrect image do throwError "the public action produced an ill-typed image"
  logInfo "PASS: composed and applied structural actions retain complete family parameters"
