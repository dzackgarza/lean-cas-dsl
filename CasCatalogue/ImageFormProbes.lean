module

import CasCatalogue.Admission
import LeanCategories.Catalogue.Semantics
meta import CasCatalogue.Admission
meta import LeanCategories.Catalogue.Semantics

open Lean Elab Command
open CasCatalogue

/- Engineering checks of registration identity against actual derived registry edges. -/
run_cmd liftTermElabM do
  let state ← registryState
  let mut derived := 0
  for source in state.categories do
    for edge in state.edgesFrom source.expression do
      for target in state.categories do
        if !target.expression.syntacticEq edge.target then continue
        let key := edgeImageId edge.ref target.id
        let some (.edgeImage found category) := state.form? key
          | throwError "registered structural image did not roundtrip: {key}"
        unless found == edge.ref && category.id == target.id do
          throwError "structural image changed its edge or target"
        if let .constructMap constructor _ := edge.ref then
          derived := derived + 1
          let missing := EdgeRef.constructMap constructor
            (.functor ⟨"fun.unregistered_image_probe"⟩)
          unless (state.form? (edgeImageId missing target.id)).isNone do
            throwError "an unregistered inner edge was admitted"
        for other in state.categories do
          let compatible := other.expression.syntacticEq edge.target ||
            match other.expression, edge.target with
            | .familyApp left _, .familyApp right _ => left == right
            | _, _ => false
          if !compatible && (state.form? (edgeImageId edge.ref other.id)).isSome then
            throwError "a structural image admitted a different target schema"
  unless derived > 0 do
    throwError "no actual constructor-map image was exercised"
