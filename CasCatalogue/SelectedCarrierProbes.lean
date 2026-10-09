module

import CasCatalogue.Language
meta import CasCatalogue.Language

open Lean Meta Elab Command Term
open CasCatalogue CasCatalogue.Language

/- Reader mechanics only. The probe uses an accepted group-valued construction, then reads
inversion at its generic element. It adds no operation row or mathematical expected answer. -/
run_cmd liftTermElabM do
  let state ← registryState
  let some construction := state.functors.find? (·.id == FunctorId.coreSetsAutomorphisms)
    | throwError "selected-carrier probe has no accepted group-valued construction"
  let some groups := state.categories.find? (·.id == CategoryId.groups)
    | throwError "selected-carrier probe has no registered target category"
  let finite ← (object state "Fin" #[.nat 3] none).run {}
  let coreObject ← mkAppM ``CategoryTheory.Core.mk #[← (semanticObject finite).run {}]
  let formed ← Semantic.objOf (← registeredFunctorInstance construction) coreObject
  let selected := Value.object formed groups none none none
  let carrier ← (carrierObject selected).run {}
  let .object _ _ none (some retained) _ := carrier
    | throwError "an anonymous construction lost its selected structure at its carrier"
  unless retained.terms == selected.terms do
    throwError "taking a carrier replaced its selected construction"
  let identity ← (identityAt carrier).run {}
  let inverse ← (applyOperation "⁻¹" #[.element identity carrier] carrier).run
    { stage := some carrier }
  let .element inverseMap result := inverse
    | throwError "the constructed group did not inherit inversion"
  unless result.terms == carrier.terms && !(inverseMap.hasMVar) do
    throwError "inversion erased the selected carrier or retained unresolved parameters"
  unless ← isTypeCorrect inverseMap do
    throwError "the constructed group's inverse was outside its declared map type"

/- An indexed generator's bound comes from its instantiated signature, after all parameters. -/
run_cmd liftTermElabM do
  let signature ← elabTermAndSynthesize
    (← `(fun (_first second : Nat) (index : Fin second) => index)) none
  let applied := Lean.mkAppN signature #[Lean.mkNatLit 2, Lean.mkNatLit 5]
  let indexSyntax ← (generatorIndex applied 4).run {}
  let index ← elabTermAndSynthesize indexSyntax none
  unless ← Lean.Meta.isDefEq (← Lean.Meta.inferType index)
      (Lean.mkApp (Lean.mkConst ``Fin) (Lean.mkNatLit 5)) do
    throwError "a generator index used an unrelated numerical parameter"
  let rejected ← try
      discard <| (generatorIndex applied 5).run {}
      pure false
    catch error =>
      if Exception.stratum? error == some .invalid then pure true else throw error
  unless rejected do throwError "an out-of-bound declared generator index was admitted"
