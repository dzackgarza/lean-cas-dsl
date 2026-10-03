/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CasCatalogue.Semantic
public import CasCatalogue.Admission
public import CasCatalogue.Codec

@[expose] public section

open Lean Meta Elab Term

namespace CasCatalogue.StructuredResult

/-- The complete decoded construction. The cone retains its defining maps; its diagram and
wire answer are retained separately from the apex's presentation. -/
structure Result where
  diagram : Expr
  cone : Expr
  apex : Expr
  answer : Json
  /-- The accepted comparison of the image of a created apex with the decoded apex. -/
  imageIso : Option Expr := none
  /-- The exact closed universal presentation retained after a registered creation lift. -/
  presentation : Option Expr := none

/-- Check the shape's complete constructor envelope before decoding any dependent fields.
The constructor decoder checks all fields, including the defining maps and their equations. -/
def decode (row : LimitEntry) (diagram : Expr) (answer : Json)
    (decodeConstructor : Name → Expr → Array Json →
      TermElabM (Except String (Expr × Array (Expr × Option Form)))) :
    TermElabM (Except String (Result × Array (Expr × Option Form))) := do
  let kind := if row.colimit then "cocone" else "cone"
  let .ok name := answer.getObjValAs? String "ctor"
    | return .error s!"expected a {kind} constructor"
  unless name == kind do return .error s!"expected {kind}, received {name}"
  let .ok args := (answer.getObjVal? "args").bind (·.getArr?)
    | return .error s!"the {kind} has no args array"
  let some constructor := standardCone row.shape row.colimit
    | return .error s!"no standard constructor for {row.shape} {kind}"
  let expected ← mkAppM (if row.colimit then ``CategoryTheory.Limits.Cocone
    else ``CategoryTheory.Limits.Cone) #[diagram]
  match ← decodeConstructor constructor expected args with
  | .error message => return .error message
  | .ok (cone, fields) =>
      let apex ← mkAppM (if row.colimit then ``CategoryTheory.Limits.Cocone.pt
        else ``CategoryTheory.Limits.Cone.pt) #[cone]
      return .ok ({ diagram, cone, apex := ← instantiateMVars apex, answer }, fields)

/-- Kernel-check a complete reconstructed data term in a discarded environment. -/
def checkReconstruction (value : Expr) : TermElabM Expr := do
  let value ← instantiateMVars value
  let type ← instantiateMVars (← inferType value)
  if value.hasMVar || value.hasLevelMVar || value.hasFVar || value.hasLooseBVars ||
      type.hasMVar || type.hasLevelMVar || type.hasFVar || type.hasLooseBVars then
    throwError "the reconstructed universal object is not closed"
  let declaration := Declaration.defnDecl {
    name := `CasCatalogue.StructuredResult.checked
    levelParams := []
    type
    value
    hints := .opaque
    safety := .safe }
  match (← getEnv).addDeclCore (USize.ofNat (Decide.decideBudget * 1000))
      (USize.ofNat maxRecDepth.defValue) declaration none with
  | .ok _ => return value
  | .error _ => throwError "Lean's kernel rejected the reconstructed universal object"

/-- Reconstruct universal evidence from accepted mathematics and checked map data. The wire
contains no proof. Every inverse equation and defining-map equation is decided by the kernel. -/
def reconstruct (row : LimitEntry) (result : Result) (presentation : Expr)
    (decodeConstructor : Name → Expr → Array Json →
      TermElabM (Except String (Expr × Array (Expr × Option Form)))) :
    TermElabM (Except String Expr) := do
  let coneProjection := if row.colimit then ``CategoryTheory.Limits.ColimitCocone.cocone
    else ``CategoryTheory.Limits.LimitCone.cone
  let pointProjection := if row.colimit then ``CategoryTheory.Limits.Cocone.pt
    else ``CategoryTheory.Limits.Cone.pt
  let acceptedCone ← mkAppM coneProjection #[presentation]
  if (result.answer.getObjVal? "presentation").toOption.isNone then
    if ← isDefEq acceptedCone result.cone then return .ok (← checkReconstruction presentation)
  let .ok maps := result.answer.getObjVal? "presentation"
    | do
      -- Without auxiliary map data, test the canonical comparison supplied by the accepted
      -- universal property. Mathlib identifies bijective maps of types with isomorphisms.
      -- This is a checked computation on finite carriers, with no leaf assertion involved.
      let attempt : TermElabM (Except String Expr) := do
        let evidence ← mkAppM (if row.colimit then
          ``CategoryTheory.Limits.ColimitCocone.isColimit else
          ``CategoryTheory.Limits.LimitCone.isLimit) #[presentation]
        let comparison ← mkAppM (if row.colimit then
          ``CategoryTheory.Limits.IsColimit.desc else
          ``CategoryTheory.Limits.IsLimit.lift) #[evidence, result.cone]
        let criterion ← mkConstWithFreshMVarLevels ``CategoryTheory.isIso_iff_bijective
        let (criterionArgs, _, criterionType) ← forallMetaTelescopeReducing (← inferType criterion)
        let wanted ← mkAppM ``CategoryTheory.IsIso #[comparison]
        let some criterionLeft := criterionType.getAppArgs[0]?
          | return .error "the canonical comparison has no isomorphism criterion"
        unless ← isDefEq criterionLeft wanted do
          return .error "the canonical comparison category has no executable bijectivity criterion"
        let equivalence ← instantiateMVars (mkAppN criterion criterionArgs)
        let equivalenceType ← whnfR (← inferType equivalence)
        let some bijective := equivalenceType.getAppArgs[1]?
          | return .error "the canonical comparison has no bijectivity criterion"
        let some proof ← Codec.conditionProof bijective
          | return .error "the kernel does not establish bijectivity of the canonical comparison"
        -- The normalized carrier is kernel-convertible to the declared carrier; retain the
        -- independently checked original proposition when applying its equivalence.
        let isoProof ← withTransparency .all <| mkAppM ``Iff.mpr #[equivalence, proof]
        let evidence ← mkAppOptM (if row.colimit then
          ``CategoryTheory.Limits.IsColimit.ofPointIso else
          ``CategoryTheory.Limits.IsLimit.ofPointIso)
          #[none, none, none, none, none, some acceptedCone, some result.cone,
            some evidence, some isoProof]
        return .ok (← checkReconstruction (← mkAppM (if row.colimit then
          ``CategoryTheory.Limits.ColimitCocone.mk else
          ``CategoryTheory.Limits.LimitCone.mk) #[result.cone, evidence]))
      attempt
  let .ok hom := maps.getObjVal? "hom" | return .error "presentation has no hom map"
  let .ok inv := maps.getObjVal? "inv" | return .error "presentation has no inv map"
  let acceptedPoint ← mkAppM pointProjection #[acceptedCone]
  let expected ← mkAppM ``CategoryTheory.Iso #[acceptedPoint, result.apex]
  let pointIso ← match ← decodeConstructor ``CategoryTheory.Iso.mk expected #[hom, inv] with
    | .error message => return .error s!"invalid presentation maps: {message}"
    | .ok (iso, _) => pure iso
  let expected ← mkAppM ``CategoryTheory.Iso #[acceptedCone, result.cone]
  let ext ← mkConstWithFreshMVarLevels (if row.colimit then
    ``CategoryTheory.Limits.Cocone.ext else ``CategoryTheory.Limits.Cone.ext)
  let (args, _, type) ← forallMetaTelescopeReducing (← inferType ext)
  unless ← isDefEq type expected do return .error "incompatible cone presentation endpoints"
  let mut supplied := false
  for arg in args do
    unless (← instantiateMVars arg).isMVar do continue
    let type ← instantiateMVars (← inferType arg)
    if ← isProp type then
      let some proof ← Codec.conditionProof (← whnfR type)
        | return .error "the presentation maps do not satisfy the complete defining-map equations"
      unless ← isDefEq arg proof do return .error "invalid defining-map proof"
    else if !supplied then
      unless ← isDefEq arg pointIso do return .error "incompatible apex identification"
      supplied := true
    else return .error "the cone identification has undetermined parameters"
  let coneIso ← instantiateMVars (mkAppN ext args)
  if coneIso.hasMVar || coneIso.hasLevelMVar then
    return .error "the cone identification is not closed"
  let evidence ← mkAppM (if row.colimit then
    ``CategoryTheory.Limits.ColimitCocone.isColimit else
    ``CategoryTheory.Limits.LimitCone.isLimit) #[presentation]
  let evidence ← mkAppM (if row.colimit then
    ``CategoryTheory.Limits.IsColimit.ofIsoColimit else
    ``CategoryTheory.Limits.IsLimit.ofIsoLimit) #[evidence, coneIso]
  let rebuilt ← mkAppM (if row.colimit then
    ``CategoryTheory.Limits.ColimitCocone.mk else
    ``CategoryTheory.Limits.LimitCone.mk) #[result.cone, evidence]
  return .ok (← checkReconstruction rebuilt)

/-- Execute a registered creation lift using independently reconstructed universal evidence. -/
def lift (state : RegistryState) (entry : LiftEntry) (sourceDiagram : Expr)
    (result : Result) (presentation : Expr) : TermElabM (Except String Result) := do
  let presentation ← instantiateMVars presentation
  if presentation.hasMVar || presentation.hasLevelMVar then
    return .error s!"{entry.id.raw}: universal-property reconstruction requires closed terms"
  let U ← Semantic.asFunctor (← Semantic.edgeFunctor state entry.edge)
  let expectedDiagram ← withTransparency .all <| mkFunctorComp sourceDiagram U
  unless ← isDefEq result.diagram expectedDiagram do
    return .error s!"{entry.id.raw}: the decoded cone is over a different diagram"
  let acceptedCone ← mkAppM ``CategoryTheory.Limits.LimitCone.cone #[presentation]
  unless ← isDefEq acceptedCone result.cone do
    return .error s!"{entry.id.raw}: reconstructed evidence is over a different cone"
  let evidence ← instantiateFresh entry.evidence
  let functorType ← withTransparency .all <| whnf (← inferType U)
  let diagramType ← withTransparency .all <| whnf (← inferType sourceDiagram)
  unless functorType.isAppOfArity ``CategoryTheory.Functor 4 &&
      diagramType.isAppOfArity ``CategoryTheory.Functor 4 do
    return .error "the creation lift lacks its complete accepted functor and diagram types"
  let endpoints := functorType.getAppArgs
  let shape := diagramType.getAppArgs
  unless (← withTransparency .all <| isDefEq shape[2]! endpoints[0]!) &&
      (← withTransparency .all <| isDefEq shape[3]! endpoints[1]!) do
    return .error "the creation lift has a different full source diagram category"
  let creationDeclaration ← mkConstWithFreshMVarLevels ``CategoryTheory.CreatesLimitsOfShape
  let creationType := mkAppN creationDeclaration #[endpoints[0]!, endpoints[1]!,
    endpoints[2]!, endpoints[3]!, shape[0]!, shape[1]!, U]
  unless ← withTransparency .all <| isDefEq (← inferType evidence) creationType do
    return .error "the creation evidence has different exact categories, shape or functor"
  let evidence ← instantiateMVars evidence
  if evidence.hasMVar || evidence.hasLevelMVar then
    return .error "the complete creation evidence has undetermined universes or parameters"
  let universal ← mkAppM ``CategoryTheory.Limits.LimitCone.isLimit #[presentation]
  let (lifted, mapsTo) ← withLetDecl `creation (← inferType evidence) evidence fun creation => do
    withLocalInstances [← creation.fvarId!.getDecl] do
      let lifted ← mkAppOptM ``CasCatalogue.liftedLimitCone
        #[some endpoints[0]!, some endpoints[1]!, some endpoints[2]!, some endpoints[3]!,
          some shape[0]!, some shape[1]!, some U, some creation,
          some sourceDiagram, some presentation]
      let comparison ← mkConstWithFreshMVarLevels
        ``CategoryTheory.liftedLimitMapsToOriginal
      let mapsTo ← mkAppOptM' comparison
        #[some endpoints[0]!, some endpoints[1]!, some endpoints[2]!, some endpoints[3]!,
          some shape[0]!, some shape[1]!, some sourceDiagram, some U, none,
          some acceptedCone, some universal]
      return (← mkLetFVars #[creation] lifted, ← mkLetFVars #[creation] mapsTo)
  let lifted ← checkReconstruction lifted
  let cone ← mkAppM ``CategoryTheory.Limits.LimitCone.cone #[lifted]
  let apex ← mkAppM ``CategoryTheory.Limits.Cone.pt #[cone]
  let forget ← mkAppM ``CategoryTheory.Limits.Cone.forget #[result.diagram]
  let imageIso ← mkAppM ``CategoryTheory.Functor.mapIso #[forget, mapsTo]
  return .ok { result with diagram := sourceDiagram, cone := ← instantiateMVars cone
                           apex := ← instantiateMVars apex
                           imageIso := some (← instantiateMVars imageIso)
                           presentation := some lifted }

/-- Retain a created cone's universal evidence while moving its apex along an independently
checked isomorphism. The original decoded answer and image comparison remain available. -/
def extendCreated (result : Result) (iso : Expr) : TermElabM (Except String Result) := do
  let some presentation := result.presentation
    | return .error "the created cone has no retained universal presentation"
  let presentation ← checkReconstruction presentation
  let cone ← mkAppM ``CategoryTheory.Limits.LimitCone.cone #[presentation]
  unless ← withTransparency .all <| isDefEq cone result.cone do
    return .error "the created presentation is over a different cone"
  let expectedCone ← mkAppM ``CategoryTheory.Limits.Cone #[result.diagram]
  unless ← withTransparency .all <| isDefEq (← inferType cone) expectedCone do
    return .error "the created presentation is over a different diagram"
  let iso ← checkReconstruction iso
  let isoType ← whnfR (← inferType iso)
  unless isoType.isAppOf ``CategoryTheory.Iso && isoType.getAppNumArgs >= 2 do
    return .error "the created apex comparison is not an isomorphism"
  let source := isoType.getAppArgs[isoType.getAppNumArgs - 2]!
  let expectedIso ← mkAppM ``CategoryTheory.Iso #[source, result.apex]
  unless ← withTransparency .all <| isDefEq isoType expectedIso do
    return .error "the created apex comparison has different endpoints"
  let hom ← mkAppM ``CategoryTheory.Iso.hom #[iso]
  let extended ← mkAppM ``CategoryTheory.Limits.Cone.extend #[cone, hom]
  let evidence ← mkAppM ``CategoryTheory.Limits.LimitCone.isLimit #[presentation]
  let invertible ← mkAppM ``CategoryTheory.Iso.isIso_hom #[iso]
  let evidence ← mkAppOptM ``CategoryTheory.Limits.IsLimit.extendIso
    #[none, none, none, none, some result.diagram, some cone, some source,
      some hom, some invertible, some evidence]
  let rebuilt ← checkReconstruction
    (← mkAppM ``CategoryTheory.Limits.LimitCone.mk #[extended, evidence])
  let extended ← instantiateMVars extended
  let apex ← instantiateMVars (← mkAppM ``CategoryTheory.Limits.Cone.pt #[extended])
  unless ← withTransparency .all <| isDefEq apex source do
    return .error "the extended created cone changed its source apex"
  return .ok { result with cone := extended, apex, presentation := some rebuilt }

/-- Reconstruct a created universal cone at an independently supplied source presentation.
An alternate apex is transported back only through the actual fully faithful lift functor;
its complete image comparison is checked before any source cone is extended. -/
def reconstructCreatedAt (state : RegistryState) (entry : LiftEntry)
    (sourceDiagram : Expr) (targetResult : Result) (targetPresentation sourceApex : Expr)
    (sourceIdentification? : Option Expr := none) : TermElabM (Except String Result) := do
  let result ← match ← lift state entry sourceDiagram targetResult targetPresentation with
    | .ok result => pure result
    | .error message => return .error message
  let sourceApex ← checkReconstruction sourceApex
  unless ← withTransparency .all <| isDefEq (← inferType sourceApex) (← inferType result.apex) do
    return .error s!"{entry.id.raw}: the requested source apex has a different category"
  if sourceIdentification?.isNone then
    if ← withTransparency .all <| isDefEq sourceApex result.apex then return .ok result
  let some identification := sourceIdentification?
    | return .error s!"{entry.id.raw}: the source apex has no accepted image identification"
  let U ← Semantic.asFunctor (← Semantic.edgeFunctor state entry.edge)
  let mappedDiagram ← withTransparency .all <| mkFunctorComp sourceDiagram U
  unless ← withTransparency .all <| isDefEq mappedDiagram targetResult.diagram do
    return .error s!"{entry.id.raw}: the source presentation uses a different lift action"
  let U ← checkReconstruction U
  let identification ← checkReconstruction identification
  let image ← Semantic.objOf U sourceApex
  let expected ← mkAppM ``CategoryTheory.Iso #[image, targetResult.apex]
  unless ← withTransparency .all <| isDefEq (← inferType identification) expected do
    return .error s!"{entry.id.raw}: the source image identification has different endpoints"
  let some imageIso := result.imageIso
    | return .error s!"{entry.id.raw}: creation omitted its image identification"
  let imageIso ← checkReconstruction imageIso
  let createdImage ← Semantic.objOf U result.apex
  let expected ← mkAppM ``CategoryTheory.Iso #[createdImage, targetResult.apex]
  unless ← withTransparency .all <| isDefEq (← inferType imageIso) expected do
    return .error s!"{entry.id.raw}: creation supplied a different apex image identification"
  let full ← trySynthInstance (← mkAppM ``CategoryTheory.Functor.Full #[U])
  let faithful ← trySynthInstance (← mkAppM ``CategoryTheory.Functor.Faithful #[U])
  unless full.toOption.isSome && faithful.toOption.isSome do
    return .error s!"{entry.id.raw}: the source presentation comparison cannot be transported back"
  let reverse ← mkAppM ``CategoryTheory.Iso.symm #[imageIso]
  let below ← mkAppM ``CategoryTheory.Iso.trans #[identification, reverse]
  let above ← checkReconstruction
    (← mkAppM ``CategoryTheory.Functor.preimageIso #[U, below])
  match ← extendCreated result above with
  | .error message => return .error message
  | .ok extended =>
      return .ok { extended with imageIso := some identification }

/-- Retain a checked change of a subobject's apex as an isomorphism of the complete
structured subobjects. The ambient comparison is the identity of the fixed ambient object;
the inclusion square and all inverse evidence remain part of the checked data term. -/
def subobjectComparison (expected returned apexIso forwardSquare : Expr) :
    TermElabM (Except String Expr) := do
  let expected ← checkReconstruction expected
  let returned ← checkReconstruction returned
  unless ← withTransparency .all <| isDefEq (← inferType expected) (← inferType returned) do
    return .error "the compared subobjects have different full categories"
  let originalArrow ← mkAppM ``CategoryTheory.ObjectProperty.FullSubcategory.obj #[expected]
  let returnedArrow ← mkAppM ``CategoryTheory.ObjectProperty.FullSubcategory.obj #[returned]
  let originalAmbient ← mkAppM ``CategoryTheory.Arrow.right #[originalArrow]
  let returnedAmbient ← mkAppM ``CategoryTheory.Arrow.right #[returnedArrow]
  unless ← withTransparency .all <| isDefEq originalAmbient returnedAmbient do
    return .error "the compared subobjects have different full ambient objects"
  let originalApex ← mkAppM ``CategoryTheory.Arrow.left #[originalArrow]
  let returnedApex ← mkAppM ``CategoryTheory.Arrow.left #[returnedArrow]
  let apexIso ← checkReconstruction apexIso
  let wanted ← mkAppM ``CategoryTheory.Iso #[originalApex, returnedApex]
  unless ← withTransparency .all <| isDefEq (← inferType apexIso) wanted do
    return .error "the subobject apex comparison has different full endpoints"
  let originalInclusion ← mkAppM ``CategoryTheory.Arrow.hom #[originalArrow]
  let returnedInclusion ← mkAppM ``CategoryTheory.Arrow.hom #[returnedArrow]
  let apexHom ← mkAppM ``CategoryTheory.Iso.hom #[apexIso]
  let composite ← mkAppM ``CategoryTheory.CategoryStruct.comp #[apexHom, returnedInclusion]
  let forwardSquare ← checkReconstruction forwardSquare
  let squareType ← mkEq composite originalInclusion
  unless ← withTransparency .all <| isDefEq (← inferType forwardSquare) squareType do
    return .error "the subobject comparison does not preserve the actual fixed inclusion"
  let ambientIso ← mkAppM ``CategoryTheory.Iso.refl #[originalAmbient]
  let rightUnit ← mkAppM ``CategoryTheory.Category.comp_id #[originalInclusion]
  let square ← mkEqTrans forwardSquare (← mkEqSymm rightUnit)
  let arrowIso ← mkAppOptM ``CategoryTheory.Arrow.isoMk
    #[none, none, some originalArrow, some returnedArrow, some apexIso,
      some ambientIso, some square]
  let constructor ← mkConstWithFreshMVarLevels
    ``CategoryTheory.ObjectProperty.isoMk
  let (arguments, _, conclusion) ← forallMetaTelescopeReducing (← inferType constructor)
  let wanted ← mkAppM ``CategoryTheory.Iso #[expected, returned]
  unless ← withTransparency .all <| isDefEq conclusion wanted do
    return .error "the full subobject comparison has different selected endpoints"
  let some argument := arguments.back? | return .error "the subobject comparison has no data slot"
  unless ← withTransparency .all <| isDefEq argument arrowIso do
    return .error "the full subobject comparison rejects its defining arrow comparison"
  let comparison ← checkReconstruction (mkAppN constructor arguments)
  return .ok comparison

def comparisonComp (f g : Expr) : TermElabM Expr :=
  mkAppM ``CategoryTheory.CategoryStruct.comp #[f, g]

def comparisonCongr (proof : Expr) (action : Expr → TermElabM Expr) :
    TermElabM Expr := do
  let some (_, lhs, _) := (← inferType proof).eq? | throwError "expected equality"
  withLocalDeclD `map (← inferType lhs) fun value => do
    let function ← mkLambdaFVars #[value] (← action value)
    mkAppM ``congrArg #[function, proof]

def comparisonChain (proofs : Array Expr) : TermElabM Expr := do
  let some first := proofs[0]? | throwError "empty equality chain"
  proofs[1:].toArray.foldlM (fun a b => mkEqTrans a b) first

def comparisonLiftApp (name : Name) (L X i mono : Expr)
    (tail : Array (Option Expr) := #[]) : TermElabM Expr := do
  let type ← whnfR (← inferType L)
  unless type.isAppOfArity ``CasCatalogue.MonoLift 5 do
    throwError "the retained comparison lift lacks its exact full category arguments"
  withTransparency .all <| mkAppOptM name (type.getAppArgs.map some ++
    #[some L, some X, none, some i, some mono] ++ tail)

def comparisonObjectIso (expected returned arrowIso : Expr) : TermElabM Expr := do
  let constructor ← mkConstWithFreshMVarLevels ``CategoryTheory.ObjectProperty.isoMk
  let (arguments, _, conclusion) ← forallMetaTelescopeReducing (← inferType constructor)
  let wanted ← mkAppM ``CategoryTheory.Iso #[expected, returned]
  unless ← withTransparency .all <| isDefEq conclusion wanted do
    throwError "the lifted comparison has different complete selected endpoints"
  let some argument := arguments.back? | throwError "the lifted comparison has no data slot"
  unless ← withTransparency .all <| isDefEq argument arrowIso do
    throwError "the lifted comparison rejects its complete defining arrow isomorphism"
  checkReconstruction (mkAppN constructor arguments)

/-- Assemble the prescribed comparison between two exact cartesian lifts. All source
and base endpoints and the full selected subobject category are independently supplied.
Only the accepted universal witnesses and generic category equalities provide the data. -/
def liftSubobjectComparison (L expectedAmbient returnedAmbient ambientIso
    expectedBase returnedBase baseIso expectedLifted returnedLifted : Expr) :
    TermElabM (Except String Expr) := do
  try
    for value in #[L, expectedAmbient, returnedAmbient, ambientIso, expectedBase,
        returnedBase, baseIso, expectedLifted, returnedLifted] do
      discard <| checkReconstruction value
    let wantedAmbient ← mkAppM ``CategoryTheory.Iso #[expectedAmbient, returnedAmbient]
    unless ← withTransparency .all <| isDefEq (← inferType ambientIso) wantedAmbient do
      return .error "the lift ambient comparison has different complete endpoints"
    let wantedBase ← mkAppM ``CategoryTheory.Iso #[expectedBase, returnedBase]
    unless ← withTransparency .all <| isDefEq (← inferType baseIso) wantedBase do
      return .error "the lift base comparison has different complete endpoints"
    let liftedType ← inferType expectedLifted
    unless ← withTransparency .all <| isDefEq liftedType (← inferType returnedLifted) do
      return .error "the lifted subobjects have different complete selected categories"
    let liftType ← whnfR (← inferType L)
    unless liftType.getAppFn.constName? == some ``CasCatalogue.MonoLift do
      return .error "the prescribed lift evidence is not the accepted MonoLift"
    let some U := liftType.getAppArgs.back? | throwError "MonoLift has no functor"
    let arrow (value : Expr) :=
      mkAppM ``CategoryTheory.ObjectProperty.FullSubcategory.obj #[value]
    let inclusion (value : Expr) := do
      mkAppM ``CategoryTheory.Arrow.hom #[← arrow value]
    let monicity (value : Expr) :=
      mkAppM ``CategoryTheory.ObjectProperty.FullSubcategory.property #[value]
    let i ← inclusion expectedBase
    let j ← inclusion returnedBase
    let mi ← monicity expectedBase
    let mj ← monicity returnedBase
    let hi ← comparisonLiftApp ``CasCatalogue.MonoLift.hom L expectedAmbient i mi
    let hj ← comparisonLiftApp ``CasCatalogue.MonoLift.hom L returnedAmbient j mj
    for (value, hom) in #[(expectedLifted, hi), (returnedLifted, hj)] do
      unless ← withTransparency .all <| isDefEq (← inclusion value) hom do
        return .error "the full lifted subobject is not the exact prescribed defining map"
    let subobjectConstructor ← mkConstWithFreshMVarLevels
      ``CategoryTheory.ObjectProperty.FullSubcategory.mk
    let (subobjectFields, _, subobjectResult) ← forallMetaTelescopeReducing
      (← inferType subobjectConstructor)
    unless ← withTransparency .all <| isDefEq subobjectResult (← inferType expectedBase) do
      return .error "the retained base comparison is outside its full subobject category"
    let propertyType ← mkArrow (← inferType (← arrow expectedBase)) (mkSort levelZero)
    let propertyFields ← subobjectFields.filterM fun field => do
      withTransparency .all <| isDefEq (← instantiateMVars (← inferType field)) propertyType
    let #[propertyField] := propertyFields
      | throwError "the complete base subobject constructor has no unique selected predicate"
    let property ← instantiateMVars propertyField
    if property.hasMVar || property.hasLevelMVar then
      throwError "the complete base subobject predicate retains unresolved selected data"
    let forget ← mkAppM ``CategoryTheory.ObjectProperty.ι #[property]
    let baseArrowIso ← mkAppM ``CategoryTheory.Functor.mapIso #[forget, baseIso]
    let sourceCategory ← inferType expectedAmbient
    let baseCategory ← inferType (← mkAppM ``CategoryTheory.Functor.obj #[U, expectedAmbient])
    let leftFunctor ← elabTermAndSynthesize
      (← `(CategoryTheory.Arrow.leftFunc (C := $(← exprToSyntax baseCategory)))) none
    let rightFunctor ← elabTermAndSynthesize
      (← `(CategoryTheory.Arrow.rightFunc (C := $(← exprToSyntax baseCategory)))) none
    let apexIso ← mkAppM ``CategoryTheory.Functor.mapIso #[leftFunctor, baseArrowIso]
    let rightIso ← mkAppM ``CategoryTheory.Functor.mapIso #[rightFunctor, baseArrowIso]
    let a ← mkAppM ``CategoryTheory.Iso.hom #[ambientIso]
    let b ← mkAppM ``CategoryTheory.Iso.inv #[ambientIso]
    let rightHom ← mkAppM ``CategoryTheory.Iso.hom #[rightIso]
    let rightInv ← mkAppM ``CategoryTheory.Iso.inv #[rightIso]
    for (component, sourceMap) in #[(rightHom, a), (rightInv, b)] do
      unless ← withTransparency .all <| isDefEq component
          (← mkAppM ``CategoryTheory.Functor.map #[U, sourceMap]) do
        return .error "the full base comparison changes the prescribed ambient functor action"
    let factor (X Y inclusion mono targetInclusion targetMono otherHom sourceMap baseMap square : Expr) := do
      let s ← comparisonLiftApp ``CasCatalogue.MonoLift.iso L Y inclusion mono
      let sh ← mkAppM ``CategoryTheory.Iso.hom #[s]
      let g ← comparisonComp sh baseMap
      let f ← comparisonComp otherHom sourceMap
      let targetFac ← comparisonLiftApp ``CasCatalogue.MonoLift.fac L Y inclusion mono
      let mappedSource ← mkAppM ``CategoryTheory.Functor.map #[U, sourceMap]
      let fac ← comparisonChain #[
        ← mkAppM ``CategoryTheory.Functor.map_comp #[U, otherHom, sourceMap],
        ← comparisonCongr targetFac (fun t => comparisonComp t mappedSource),
        ← mkAppM ``CategoryTheory.Category.assoc #[sh, inclusion, mappedSource],
        ← comparisonCongr (← mkEqSymm square) (fun t => comparisonComp sh t),
        ← mkEqSymm (← mkAppM ``CategoryTheory.Category.assoc #[sh, baseMap, targetInclusion])]
      let sourceLifted ← comparisonLiftApp ``CasCatalogue.MonoLift.obj L Y inclusion mono
      let universal ← comparisonLiftApp ``CasCatalogue.MonoLift.universal L X
        targetInclusion targetMono
        #[some sourceLifted, some g, some f, some fac]
      let existence ← mkAppM ``ExistsUnique.exists #[universal]
      let h ← mkAppM ``Classical.choose #[existence]
      let spec ← mkAppM ``Classical.choose_spec #[existence]
      pure (h, ← mkAppM ``And.right #[spec])
    let baseHom ← mkAppM ``CategoryTheory.Iso.hom #[baseArrowIso]
    let baseInv ← mkAppM ``CategoryTheory.Iso.inv #[baseArrowIso]
    let forwardBase ← mkAppM ``CategoryTheory.Arrow.w #[baseHom]
    let reverseBase ← mkAppM ``CategoryTheory.Arrow.w #[baseInv]
    let e ← mkAppM ``CategoryTheory.Iso.hom #[apexIso]
    let ei ← mkAppM ``CategoryTheory.Iso.inv #[apexIso]
    let (h, hs) ← factor returnedAmbient expectedAmbient i mi j mj hi a e forwardBase
    let (k, ks) ← factor expectedAmbient returnedAmbient j mj i mi hj b ei reverseBase
    let inverse (X inclusion otherInclusion h k a b hs ks inverseAmbient : Expr) := do
      let eq ← comparisonChain #[
        ← mkAppM ``CategoryTheory.Category.assoc #[h, k, inclusion],
        ← comparisonCongr ks (fun t => comparisonComp h t),
        ← mkEqSymm (← mkAppM ``CategoryTheory.Category.assoc #[h, otherInclusion, b]),
        ← comparisonCongr hs (fun t => comparisonComp t b),
        ← mkAppM ``CategoryTheory.Category.assoc #[inclusion, a, b],
        ← comparisonCongr inverseAmbient (fun t => comparisonComp inclusion t),
        ← mkAppM ``CategoryTheory.Category.comp_id #[inclusion],
        ← mkEqSymm (← mkAppM ``CategoryTheory.Category.id_comp #[inclusion])]
      let mono ← monicity X
      let id ← mkAppM ``CategoryTheory.CategoryStruct.id
        #[← mkAppM ``CategoryTheory.Arrow.left #[← arrow X]]
      let cancel ← mkAppOptM ``CategoryTheory.cancel_mono
        #[some sourceCategory, none, none, none, none, some inclusion, some mono,
          some (← comparisonComp h k), some id]
      mkAppM ``Iff.mp #[cancel, eq]
    let hk ← inverse expectedLifted hi hj h k a b hs ks
      (← mkAppM ``CategoryTheory.Iso.hom_inv_id #[ambientIso])
    let kh ← inverse returnedLifted hj hi k h b a ks hs
      (← mkAppM ``CategoryTheory.Iso.inv_hom_id #[ambientIso])
    let liftedIso ← mkAppM ``CategoryTheory.Iso.mk #[h, k, hk, kh]
    let arrowIso ← mkAppOptM ``CategoryTheory.Arrow.isoMk
      #[none, none, some (← arrow expectedLifted), some (← arrow returnedLifted),
        some liftedIso, some ambientIso, some hs]
    return .ok (← comparisonObjectIso expectedLifted returnedLifted arrowIso)
  catch ex =>
    return .error (← ex.toMessageData.toString)

end CasCatalogue.StructuredResult
