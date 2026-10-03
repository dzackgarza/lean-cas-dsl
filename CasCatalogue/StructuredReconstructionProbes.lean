/- Copyright (c) 2026 Dzack Garza. Released under Apache 2.0 license. -/
module
import LeanCategories.Catalogue.Semantics
import CasCatalogue.Realize
meta import LeanCategories.Catalogue.Semantics
meta import CasCatalogue.Realize

open Lean Meta Elab Term Command
namespace CasCatalogue.StructuredReconstructionProbes

-- Engineering probe: a changed finite presentation retains both defining maps and reconstructs
-- its universal evidence from checked map data. This is not a computational acceptance assertion.
run_cmd liftTermElabM do
  let state ← registryState
  let some category := state.categories.find? (·.id.raw == "cat.sets")
    | throwError "missing set category"
  let some row := state.limits.find? (·.id.raw == "lim.sets.product")
    | throwError "missing product registration"
  let some fin := state.objects.find? (·.id.raw == "obj.sets.fin")
    | throwError "missing finite set constructor"
  let trace ← (Trace.new : IO _)
  let X ← Semantic.object fin #[Syntax.mkNumLit "2"] (some trace)
  let Y ← Semantic.object fin #[Syntax.mkNumLit "1"] (some trace)
  let diagram ← mkAppM ``CategoryTheory.Limits.pair #[X, Y]
  let apex := Json.mkObj [("ctor", fin.id.raw), ("args", toJson (#[2] : Array Nat))]
  let .ok first := Json.parse "[[0,1],[1,0]]" | throwError "invalid probe first leg"
  let .ok second := Json.parse "[[0,0],[1,0]]" | throwError "invalid probe second leg"
  let .ok hom := Json.parse "[[[0,0],1],[[1,0],0]]" | throwError "invalid probe hom"
  let .ok inv := Json.parse "[[0,[1,0]],[1,[0,0]]]" | throwError "invalid probe inv"
  let answer := Json.mkObj [("ctor", "cone"), ("args", Json.arr #[apex, first, second]),
    ("presentation", Json.mkObj [("hom", hom), ("inv", inv)])]
  let decode := fun constructor expected args =>
    Realize.decodeFamily constructor expected args (Realize.decodeValue trace category)
  let result ← match ← StructuredResult.decode row diagram answer decode with
    | .ok (result, _) => pure result
    | .error message => throwError "cone decode failed: {message}"
  let accepted ← Semantic.limitPresentation row diagram
  match ← StructuredResult.reconstruct row result accepted decode with
  | .error message => throwError "nonidentity reconstruction failed: {message}"
  | .ok rebuilt =>
    let cone ← mkAppM ``CategoryTheory.Limits.LimitCone.cone #[rebuilt]
    unless ← isDefEq cone result.cone do throwError "reconstruction replaced the defining maps"
  -- Changing either inverse map data or a defining leg must fail independent reconstruction.
  let .ok badInv := Json.parse "[[0,[0,0]],[1,[1,0]]]" | throwError "invalid bad inverse fixture"
  let badAnswer := Json.mkObj [("ctor", "cone"), ("args", Json.arr #[apex, first, second]),
    ("presentation", Json.mkObj [("hom", hom), ("inv", badInv)])]
  if (← StructuredResult.reconstruct row { result with answer := badAnswer } accepted decode).isOk then
    throwError "reconstruction accepted noninverse map data"
  let acceptedCone ← mkAppM ``CategoryTheory.Limits.LimitCone.cone #[accepted]
  let acceptedApex ← mkAppM ``CategoryTheory.Limits.Cone.pt #[acceptedCone]
  let .ok canonicalHom := Json.parse "[[[0,0],[0,0]],[[1,0],[1,0]]]"
    | throwError "invalid canonical identity fixture"
  let .ok canonicalBadInv := Json.parse "[[[0,0],[0,0]],[[1,0],[0,0]]]"
    | throwError "invalid canonical noninverse fixture"
  let canonicalBadAnswer := Json.mkObj [("ctor", "cone"),
    ("args", Json.arr #[apex, first, second]),
    ("presentation", Json.mkObj [("hom", canonicalHom), ("inv", canonicalBadInv)])]
  let canonicalWithBadMaps := { result with
    cone := acceptedCone
    apex := acceptedApex
    answer := canonicalBadAnswer }
  if (← StructuredResult.reconstruct row canonicalWithBadMaps accepted decode).isOk then
    throwError "canonical reconstruction ignored explicitly supplied invalid presentation maps"
  let .ok badLeg := Json.parse "[[0,0],[1,1]]" | throwError "invalid bad leg fixture"
  let badAnswer := Json.mkObj [("ctor", "cone"), ("args", Json.arr #[apex, badLeg, second]),
    ("presentation", Json.mkObj [("hom", hom), ("inv", inv)])]
  let badResult ← match ← StructuredResult.decode row diagram badAnswer decode with
    | .ok (result, _) => pure result
    | .error message => throwError "a cone with a different leg failed decoding: {message}"
  if (← StructuredResult.reconstruct row badResult accepted decode).isOk then
    throwError "reconstruction ignored a defining leg"
  -- The defining-leg envelope keeps the changed cone and checks its full presentation.
  let XJson := Json.mkObj [("ctor", fin.id.raw), ("args", toJson (#[2] : Array Nat))]
  let YJson := Json.mkObj [("ctor", fin.id.raw), ("args", toJson (#[1] : Array Nat))]
  let diagramJson := Json.mkObj [("ctor", "pair"), ("args", Json.arr #[XJson, YJson])]
  let index ← elabTermAndSynthesize
    (← `(CategoryTheory.Discrete.mk CategoryTheory.Limits.WalkingPair.left)) none
  let .ok indexJson ← Codec.encode index | throwError "the actual diagram index did not encode"
  let acceptedLegs ← mkAppM ``CategoryTheory.Limits.Cone.π #[acceptedCone]
  let expectedLeg ← elabTermAndSynthesize
    (← `(CategoryTheory.NatTrans.app $(← exprToSyntax acceptedLegs) $(← exprToSyntax index))) none
  let legAnswer := Json.mkObj [("ctor", "constructionLeg"),
    ("args", Json.arr #[toJson row.id.raw, diagramJson, answer, indexJson])]
  let .ok (actualLeg, _) ← Realize.decodeValue trace category (← inferType expectedLeg) legAnswer
    | throwError "the full noncanonical construction leg did not roundtrip"
  let some _ ← Codec.conditionProof (← mkEq actualLeg expectedLeg)
    | throwError "the actual returned leg lost its checked apex alignment"
  let badLegAnswer := Json.mkObj [("ctor", "constructionLeg"),
    ("args", Json.arr #[toJson row.id.raw, diagramJson, badAnswer, indexJson])]
  if (← Realize.decodeValue trace category (← inferType expectedLeg) badLegAnswer).isOk then
    throwError "defining-leg projection ignored invalid supplied inverse maps"
  let wrongIndex := Json.mkObj [("ctor", "constructionLeg"),
    ("args", Json.arr #[toJson row.id.raw, diagramJson, answer, toJson (0 : Nat)])]
  if (← Realize.decodeValue trace category (← inferType expectedLeg) wrongIndex).isOk then
    throwError "defining-leg projection interpreted a differently typed index"
  let plainAnswer := Json.mkObj [("ctor", "cone"), ("args", Json.arr #[apex, first, second])]
  match ← StructuredResult.reconstruct row { result with answer := plainAnswer } accepted decode with
  | .ok _ => pure ()
  | .error message => throwError "canonical finite reconstruction failed: {message}"

-- The fixed request boundary rejects a different canonical kernel of the same category,
-- and a valid monic subobject with a different inclusion into the same ambient module.
run_cmd liftTermElabM do
  let state ← registryState
  let some kernel := state.functors.find? (·.id.raw == "fun.arrows_modules.kernel")
    | throwError "missing accepted kernel functor"
  let target ← Semantic.namedCategoryFor state kernel.target
  let R ← elabTermAndSynthesize (← `(RingCat.of ℤ)) none
  let F ← mkAppM kernel.declaration #[R]
  let Z ← elabTermAndSynthesize (← `(ModuleCat.of ℤ ℤ)) none
  let identity ← elabTermAndSynthesize (← `(CategoryTheory.CategoryStruct.id $(← exprToSyntax Z))) none
  let identityArrow ← mkAppM ``CategoryTheory.Arrow.mk #[identity]
  let zeroType ← mkAppM ``Quiver.Hom #[Z, Z]
  let zero ← elabTermAndSynthesize (← `(0)) (some zeroType)
  let zeroArrow ← mkAppM ``CategoryTheory.Arrow.mk #[zero]
  let expected ← Semantic.objOf F identityArrow
  let wrong ← Semantic.objOf F zeroArrow
  unless ← isDefEq (← inferType expected) (← inferType wrong) do
    throwError "fixed request negative changed its result category"
  let canonical := Json.mkObj [("ctor", "functorAction"), ("args", Json.arr #[])]
  Realize.checkFixedConstruction target expected expected canonical
  let result : Realize.ExecutionOutcome ← tryCatchRuntimeEx
    (do Realize.checkFixedConstruction target expected wrong canonical; pure .holds)
    Realize.executionFailure
  unless result matches .malformed _ do
    throwError "a canonical reply for a different same-type receiver passed the fixed request boundary"
  let raw := Json.mkObj [("ctor", "subobject"), ("args", Json.arr #[])]
  let result : Realize.ExecutionOutcome ← tryCatchRuntimeEx
    (do Realize.checkFixedConstruction target expected wrong raw; pure .holds)
    Realize.executionFailure
  unless result matches .gap _ do
    throwError "monicity authenticated a different inclusion as the requested kernel"

-- Stored-map projection validates the complete registered receiver and fixed endpoints.
run_cmd liftTermElabM do
  let state ← registryState
  let some category := state.categories.find? (·.id == CategoryId.sets)
    | throwError "missing sets category for arrow projection"
  let some fin := state.objects.find? (·.id.raw == "obj.sets.fin")
    | throwError "missing finite endpoint declaration"
  let trace ← (Trace.new : IO _)
  let X ← Semantic.object fin #[Syntax.mkNumLit "2"] (some trace)
  let Y ← Semantic.object fin #[Syntax.mkNumLit "3"] (some trace)
  let identity ← mkAppM ``CategoryTheory.CategoryStruct.id #[X]
  let wire := Json.mkObj [("ctor", fin.id.raw), ("args", toJson (#[2] : Array Nat))]
  let identityWire := Json.mkObj [("ctor", "identity"), ("args", Json.arr #[wire, wire])]
  let arrowWire := Json.mkObj [("ctor", "arrow"),
    ("args", Json.arr #[wire, wire, identityWire])]
  let projection := Json.mkObj [("ctor", "arrowHom"), ("args", Json.arr #[arrowWire])]
  let .ok (projected, _) ← Realize.decodeValue trace category (← inferType identity) projection
    | throwError "the complete stored arrow did not roundtrip"
  unless ← isDefEq projected identity do throwError "projection replaced the stored map"
  let wrongType ← mkAppM ``Quiver.Hom #[Y, Y]
  if (← Realize.decodeValue trace category wrongType projection).isOk then
    throwError "projection admitted different fixed endpoints"
  let wrongConstructor := Json.mkObj [("ctor", "arrowHom"), ("args", Json.arr #[wire])]
  if (← Realize.decodeValue trace category (← inferType identity) wrongConstructor).isOk then
    throwError "projection admitted an object of a different constructor"

-- A finite bundled map retains and independently checks its homomorphism laws.
run_cmd liftTermElabM do
  let state ← registryState
  let some category := state.categories.find? (·.id == CategoryId.groups)
    | throwError "missing groups category"
  let some cyclic := state.objects.find? (·.id.raw == "obj.groups.cyclic")
    | throwError "missing cyclic object"
  let trace ← (Trace.new : IO _)
  let X ← Semantic.object cyclic #[Syntax.mkNumLit "2"] (some trace)
  let identity ← mkAppM ``CategoryTheory.CategoryStruct.id #[X]
  let type ← inferType identity
  let .ok graph := Json.parse "[[0,0],[1,1]]" | throwError "invalid graph fixture"
  match ← Realize.decodeValue trace category type graph with
  | .error message => throwError "finite bundled hom reconstruction failed: {message}"
  | .ok (hom, _) =>
      let some _ ← Codec.conditionProof (← mkEq hom identity)
        | throwError "the reconstructed identity changed its function"
  let .ok wrong := Json.parse "[[0,1],[1,0]]" | throwError "invalid false-law fixture"
  if (← Realize.decodeValue trace category type wrong).isOk then
    throwError "finite bundled hom reconstruction accepted a map that violates its unit law"

-- Forward carrier views retain the exact selected arithmetic source and generalized domain.
run_cmd liftTermElabM do
  let state ← registryState
  let some category := state.categories.find? (·.id == CategoryId.sets) | unreachable!
  let trace ← (Trace.new : IO _)
  let source := Json.mkObj [("ctor", "obj.rings.integers"), ("args", Json.arr #[])]
  let descriptor := Json.mkObj [("ctor", "fun.rings.multiplicative_monoid"),
    ("args", Json.arr #[])]
  let target := Json.mkObj [("ctor", "functorAction"), ("args", Json.arr #[descriptor, source])]
  let numeral := Json.mkObj [("ctor", "numeral"), ("args", toJson (#[3] : Array Nat))]
  let point := Json.mkObj [("ctor", "element"), ("args", Json.arr #[source, numeral])]
  let domain := Json.mkObj [("ctor", "obj.sets.fin"), ("args", toJson (#[1] : Array Nat))]
  let answer := Json.mkObj [("ctor", "pointView"), ("args", Json.arr #[target, point, domain])]
  let expected ← elabTermAndSynthesize (← `(TypeCat.ofHom (fun _ : Fin 1 => (3 : ℤ)))) none
  let decoded ← Realize.decodeValue trace category (← inferType expected) answer
  let actual ← match decoded with
    | .ok (actual, some _) => pure actual
    | .ok (_, none) => throwError "the complete forward selected point view has no decoded form"
    | .error message => throwError "the complete forward selected point view did not roundtrip: {message}"
  let some _ ← Codec.conditionProof (← mkEq actual expected)
    | throwError "the forward view changed its checked source arithmetic"
  let otherSource := Json.mkObj [("ctor", "obj.rings.rationals"), ("args", Json.arr #[])]
  let otherPoint := Json.mkObj [("ctor", "element"), ("args", Json.arr #[otherSource, numeral])]
  let mismatched := Json.mkObj [("ctor", "pointView"),
    ("args", Json.arr #[target, otherPoint, domain])]
  if (← Realize.decodeValue trace category (← inferType expected) mismatched).isOk then
    throwError "the forward point view substituted another selected source structure"
  let otherDomain := Json.mkObj [("ctor", "obj.sets.fin"), ("args", toJson (#[2] : Array Nat))]
  let wrongDomain := Json.mkObj [("ctor", "pointView"),
    ("args", Json.arr #[target, point, otherDomain])]
  if (← Realize.decodeValue trace category (← inferType expected) wrongDomain).isOk then
    throwError "the forward point view changed its fixed generalized domain"
  let expectedGeneralized ← elabTermAndSynthesize
    (← `(TypeCat.ofHom (fun _ : Fin 2 => (3 : ℤ)))) none
  let .ok (actualGeneralized, some _) ← Realize.decodeValue trace category
      (← inferType expectedGeneralized) wrongDomain
    | throwError "the correctly sealed generalized-domain constant point did not roundtrip"
  let some _ ← Codec.conditionProof (← mkEq actualGeneralized expectedGeneralized)
    | throwError "the generalized forward point changed its selected arithmetic"
  let listTarget := Json.mkObj [("ctor", "functorAction"),
    ("args", Json.arr #[Json.mkObj [("ctor", "fun.sets.list"), ("args", Json.arr #[])], domain])]
  let finitePoint := Json.mkObj [("ctor", "element"), ("args", Json.arr #[domain, numeral])]
  let changedCarrier := Json.mkObj [("ctor", "pointView"),
    ("args", Json.arr #[listTarget, finitePoint, domain])]
  if (← Realize.decodeValue trace category (← inferType expected) changedCarrier).isOk then
    throwError "a carrier-changing functor was treated as structural point identification"

end CasCatalogue.StructuredReconstructionProbes
