/- Copyright (c) 2026 Dzack Garza. Released under Apache 2.0 license. -/
module
import CasCatalogue.Codec
import Mathlib.CategoryTheory.Types.Basic
import Mathlib.CategoryTheory.Limits.Shapes.FiniteLimits
meta import CasCatalogue.Codec

open Lean Meta Elab Term Command
namespace CasCatalogue.CodecConditionProbes

-- Engineering checks of generic proof assembly on finite functions and their record wrappers.
run_cmd liftTermElabM do
  let proposition ← elabTermAndSynthesize (← `(
    TypeCat.ofHom (fun x : Fin 2 => x) =
      TypeCat.ofHom (fun x : Fin 2 => if x = 0 then 0 else 1))) none
  let some _ ← Codec.conditionProof proposition
    | throwError "the structural codec could not establish a finite bundled-function equation"
  let wrong ← elabTermAndSynthesize (← `(
    TypeCat.ofHom (fun x : Fin 2 => x) =
      TypeCat.ofHom (fun _ : Fin 2 => (0 : Fin 2)))) none
  if (← Codec.conditionProof wrong).isSome then
    throwError "the structural codec accepted a false bundled-function equation"
  let quantified ← elabTermAndSynthesize (← `(
    ∀ j : CategoryTheory.Discrete CategoryTheory.Limits.WalkingPair,
      TypeCat.ofHom (fun x : Fin 2 => x) =
        TypeCat.ofHom (fun x : Fin 2 =>
          match j.as with
          | .left => if x = 0 then 0 else 1
          | .right => x))) none
  let some _ ← Codec.conditionProof quantified
    | throwError "the structural codec could not establish defining-map equations over a finite shape"
  let permutation ← elabTermAndSynthesize (← `(Equiv.swap (0 : Fin 3) 1)) none
  let graph ← match ← Codec.encode permutation with
    | .ok graph => pure graph
    | .error message => throwError "finite permutation function fields failed structural encoding: {message}"
  let decoded ← match ← Codec.decode (← inferType permutation) graph with
    | .ok value => pure value
    | .error message => throwError "finite permutation graph failed structural decoding: {message}"
  let some _ ← Codec.conditionProof (← mkEq permutation decoded)
    | throwError "finite permutation graph changed the represented function"
  let functionType ← elabTermAndSynthesize (← `(Fin 2 → Fin 2)) none
  let .ok repeated := Json.parse "[[0,0],[0,1]]" | throwError "invalid graph fixture"
  if (← Codec.decode functionType repeated).isOk then
    throwError "a finite function graph repeated a key and omitted another"

end CasCatalogue.CodecConditionProbes
