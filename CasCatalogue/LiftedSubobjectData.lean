/- Copyright (c) 2026 Dzack Garza. Released under Apache 2.0 license. -/
module

public import CasCatalogue.Semantic
public import CasCatalogue.StructuredResult

@[expose] public section

open Lean Meta Elab Term

namespace CasCatalogue.LiftedSubobjectData

/-- A decoder retains the actual object and its complete expected-to-actual comparison. -/
abbrev Decoded := Expr × Option Expr

def expectedEndpoint (actual : Expr) (comparison : Option Expr) : TermElabM Expr := do
  discard <| StructuredResult.checkReconstruction actual
  let some comparison := comparison | return actual
  discard <| StructuredResult.checkReconstruction comparison
  let type ← whnfR (← inferType comparison)
  let #[_, _, expected, returned] := type.getAppArgs
    | throwError "a retained lifted descriptor comparison has no complete endpoints"
  unless type.isAppOf ``CategoryTheory.Iso do
    throwError "a retained lifted descriptor comparison is not an isomorphism"
  unless ← withTransparency .all <| isDefEq returned actual do
    throwError "a retained lifted descriptor comparison ends at another actual object"
  discard <| StructuredResult.checkReconstruction expected
  return expected

/-- Map a comparison using the functor's exact source and target category dictionaries. -/
def mapComparison (F comparison : Expr) : TermElabM Expr := do
  let type ← whnfR (← inferType F)
  unless type.isAppOf ``CategoryTheory.Functor do
    throwError "the retained comparison action is not a complete functor"
  let #[C, categoryC, D, categoryD] := type.getAppArgs
    | throwError "the retained comparison functor has no full category dictionaries"
  withTransparency .all <| mkAppOptM ``CategoryTheory.Functor.mapIso
    #[some C, some categoryC, some D, some categoryD, some F,
      none, none, some comparison]

/-- Obtain the actual object field's type from the independently fixed complete result type. -/
def sourceArrowType (expected : Expr) : TermElabM Expr := do
  let constructor ← mkConstWithFreshMVarLevels
    ``CategoryTheory.ObjectProperty.FullSubcategory.mk
  let (fields, _, result) ← forallMetaTelescopeReducing (← inferType constructor)
  unless ← withTransparency .all <| isDefEq result expected do
    throwError "a lifted descriptor is outside the fixed full subobject category"
  unless fields.size >= 2 do throwError "the full subobject constructor has no defining arrow"
  let type ← instantiateMVars (← inferType fields[fields.size - 2]!)
  let reduced ← whnfR type
  unless reduced.isAppOf ``CategoryTheory.Arrow do
    throwError "the fixed subobject predicate is not over complete arrows"
  if type.hasMVar || type.hasLevelMVar then
    throwError "the fixed subobject category leaves selected arrow data unresolved"
  return type

def subobjectType (arrowType : Expr) : TermElabM Expr := do
  withLocalDeclD `arrow arrowType fun arrow => do
    let inclusion ← mkAppM ``CategoryTheory.Arrow.hom #[arrow]
    let property ← mkLambdaFVars #[arrow] (← mkAppM ``CategoryTheory.Mono #[inclusion])
    mkAppM ``CategoryTheory.ObjectProperty.FullSubcategory #[property]

def arrowLeftComparison (expected actual : Expr) (comparison : Option Expr) :
    TermElabM Expr := do
  let expectedLeft ← mkAppM ``CategoryTheory.Arrow.left #[expected]
  let actualLeft ← mkAppM ``CategoryTheory.Arrow.left #[actual]
  let some comparison := comparison
    | do
      unless ← withTransparency .all <| isDefEq expectedLeft actualLeft do
        throwError "the retained source arrows have no full ambient comparison"
      return ← mkAppM ``CategoryTheory.Iso.refl #[expectedLeft]
  let arrowType ← whnfR (← inferType expected)
  unless arrowType.isAppOf ``CategoryTheory.Arrow do
    throwError "the retained source comparison is outside its complete arrow category"
  let #[category, selectedCategory] := arrowType.getAppArgs
    | throwError "the retained source arrow has no full selected category structure"
  let functor ← withTransparency .all <| mkAppOptM ``CategoryTheory.Arrow.leftFunc
    #[some category, some selectedCategory]
  mapComparison functor comparison

/-- Replay only complete, explicitly registered lifted-subobject envelopes. The callbacks
decode in the independently fixed source and base contexts; no runtime module is imported. -/
def decode (expected : Expr) (sourceCategory : NamedCategoryEntry)
    (fixedSource : Expr) (prescribed : Array LiftId) (json : Json)
    (decodeSource : CategoryExpr → Expr → Json → TermElabM (Except String Decoded))
    (decodeBase : NamedCategoryEntry → Expr → Json → TermElabM (Except String Decoded)) :
    TermElabM (Option (Except String Decoded)) := do
  unless (json.getObjValAs? String "ctor").toOption == some "liftedSubobject" do
    return none
  let work : TermElabM (Except String Decoded) := do
    let .ok args := (json.getObjVal? "args").bind (·.getArr?)
      | return .error "a lifted subobject requires an ordered full envelope"
    unless args.size == 3 do
      return .error "a lifted subobject requires its full base reply, source arrow and exact lift ids"
    let .ok ids := args[2]!.getArr?
      | return .error "a lifted subobject requires its ordered registered lift ids"
    unless !prescribed.isEmpty && ids.size == prescribed.size do
      return .error "the lifted envelope does not retain the independently prescribed lift sequence"
    for index in [:ids.size] do
      unless ids[index]!.getStr?.toOption == some prescribed[index]!.raw do
        return .error "the lifted envelope changes the independently prescribed ordered lift ids"
    let state ← registryState
    let .construct subobjects #[.category source] := sourceCategory.expression
      | return .error "a lifted result has no exact registered subobject constructor context"
    unless (state.constructor? subobjects).any
        (·.semantics == `CasCatalogue.Constructors.subobjects) do
      return .error "the lifted result context is not the registered subobject constructor"
    let arrowConstructors := state.constructors.filter
      (·.semantics == `CasCatalogue.Constructors.arrow)
    let #[arrowConstructor] := arrowConstructors
      | return .error "the complete arrow constructor is absent or ambiguous"
    let originalSource : CategoryExpr := .construct arrowConstructor.id #[.category source]
    let sourceType ← sourceArrowType expected
    discard <| StructuredResult.checkReconstruction fixedSource
    unless ← withTransparency .all <| isDefEq (← inferType fixedSource) sourceType do
      return .error "the independently retained source has different complete arrow parameters"
    let declaredResult ← categoryCarrierInstance sourceCategory
    unless ← withTransparency .all <| isDefEq declaredResult expected do
      return .error "the descriptor context has different complete result parameters"
    let .ok (actualSource, sourceIso) ← decodeSource originalSource sourceType args[1]!
      | return .error "the lifted descriptor source arrow does not decode at its fixed full type"
    unless ← withTransparency .all <| isDefEq (← inferType actualSource) sourceType do
      return .error "the decoded source arrow has different complete selected parameters"
    let expectedSource ← expectedEndpoint actualSource sourceIso
    unless ← withTransparency .all <| isDefEq expectedSource fixedSource do
      return .error "the lifted descriptor changes the independently retained complete operation source"
    let mut actualReceiver := actualSource
    let mut expectedReceiver := expectedSource
    let mut receiverIso := sourceIso
    let mut current := originalSource
    let mut rows : Array LiftEntry := #[]
    let mut receivers : Array (Expr × Expr × Option Expr) := #[]
    for idJson in ids do
      let .ok id := idJson.getStr?
        | return .error "a prescribed lift id is not a registered identifier"
      let some row := state.lifts.find? (·.id.raw == id)
        | return .error s!"the lifted descriptor names an unregistered lift: {id}"
      unless row.kind == .subobjects do
        return .error "the lifted descriptor names a lift of a different construction"
      let .constructMap constructor _ := row.edge
        | return .error "a prescribed subobject lift has no full arrow action"
      unless constructor == arrowConstructor.id do
        return .error "the prescribed lift acts on a different registered constructor"
      let some edge := (state.edgesFrom current).find? (·.ref == row.edge)
        | return .error "the prescribed lift does not start at the retained exact source category"
      unless edge.source.syntacticEq current do
        return .error "the prescribed lift changes its current registered source"
      let .construct targetConstructor #[.category _] := edge.target
        | return .error "the prescribed lift does not land in a complete arrow category"
      unless targetConstructor == arrowConstructor.id do
        return .error "the prescribed lift changes the registered arrow constructor"
      rows := rows.push row
      receivers := receivers.push (expectedReceiver, actualReceiver, receiverIso)
      let F ← Semantic.asFunctor (← Semantic.edgeFunctor state row.edge)
      expectedReceiver ← Semantic.objOf F expectedReceiver
      actualReceiver ← Semantic.objOf F actualReceiver
      receiverIso ← match receiverIso with
        | none => pure none
        | some iso => pure (some (← mapComparison F iso))
      current := edge.target
    let .construct _ #[.category target] := current
      | return .error "the lifted descriptor has no exact base category"
    let baseExpression : CategoryExpr := .construct subobjects #[.category target]
    let baseCategory ← Semantic.namedCategoryFor state baseExpression
    unless baseCategory.expression.syntacticEq baseExpression do
      return .error "the base reply has no exact named subobject context"
    let baseType ← subobjectType (← inferType actualReceiver)
    let .ok (actualBase, baseIso) ← decodeBase baseCategory baseType args[0]!
      | return .error "the complete lifted base reply does not decode at its fixed type"
    unless ← withTransparency .all <| isDefEq (← inferType actualBase) baseType do
      return .error "the lifted base reply has different complete selected parameters"
    let expectedBase ← expectedEndpoint actualBase baseIso
    for (receiver, base) in #[(expectedReceiver, expectedBase), (actualReceiver, actualBase)] do
      let arrow ← mkAppM ``CategoryTheory.ObjectProperty.FullSubcategory.obj #[base]
      unless ← withTransparency .all <| isDefEq
          (← mkAppM ``CategoryTheory.Arrow.right #[arrow])
          (← mkAppM ``CategoryTheory.Arrow.left #[receiver]) do
        return .error "the lifted base reply changes the retained complete source ambient"
    let mut expectedLifted := expectedBase
    let mut actualLifted := actualBase
    let mut comparison ← match baseIso with
      | some iso => pure iso
      | none => mkAppM ``CategoryTheory.Iso.refl #[expectedBase]
    for index in (List.range rows.size).reverse do
      let some row := rows[index]?
        | return .error "the replay lost its exact retained lift row"
      let some (savedExpected, savedActual, sourceComparison) := receivers[index]?
        | return .error "the replay lost its complete retained source arrows"
      let expectedAmbient ← mkAppM ``CategoryTheory.Arrow.left #[savedExpected]
      let actualAmbient ← mkAppM ``CategoryTheory.Arrow.left #[savedActual]
      let ambientIso ← arrowLeftComparison savedExpected savedActual sourceComparison
      let nextExpected ← Semantic.liftSubobject state row savedExpected expectedLifted
      let nextActual ← Semantic.liftSubobject state row savedActual actualLifted
      let L ← instantiateFresh row.evidence
      let arrow ← mkAppM ``CategoryTheory.ObjectProperty.FullSubcategory.obj #[expectedLifted]
      let inclusion ← mkAppM ``CategoryTheory.Arrow.hom #[arrow]
      let mono ← mkAppM ``CategoryTheory.ObjectProperty.FullSubcategory.property #[expectedLifted]
      let freshLiftType ← whnfR (← inferType L)
      unless freshLiftType.isAppOf ``CasCatalogue.MonoLift do
        return .error "the registered reverse lift evidence is not complete MonoLift data"
      let #[C, categoryC, D, categoryD, freshU] := freshLiftType.getAppArgs
        | return .error "the registered reverse lift is missing its full category arguments"
      unless ← withTransparency .all <| isDefEq C (← inferType expectedAmbient) do
        return .error "the reverse lift datum changes the exact selected source category"
      let baseArrow ← mkAppM ``CategoryTheory.ObjectProperty.FullSubcategory.obj #[expectedLifted]
      let baseAmbient ← mkAppM ``CategoryTheory.Arrow.right #[baseArrow]
      unless ← withTransparency .all <| isDefEq D (← inferType baseAmbient) do
        return .error "the reverse lift datum changes the exact selected base category"
      let .constructMap _ inner := row.edge
        | return .error "the accepted reverse lift has lost its exact inner action"
      let U ← Semantic.asFunctor (← Semantic.edgeFunctor state inner)
      unless ← withTransparency .all <| isDefEq freshU U do
        return .error "the reverse lift datum changes the exact accepted full functor action"
      discard <| withTransparency .all <| mkAppOptM ``CasCatalogue.MonoLift.hom
        #[some C, some categoryC, some D, some categoryD, some freshU,
          some L, some expectedAmbient, none, some inclusion, some mono]
      let image ← Semantic.objOf U expectedAmbient
      unless ← withTransparency .all <| isDefEq image
          (← mkAppM ``CategoryTheory.Arrow.right #[baseArrow]) do
        return .error "the exact reverse lift action changes its retained full base ambient"
      let liftType ← whnfR (← inferType L)
      unless liftType.isAppOf ``CasCatalogue.MonoLift do
        return .error "the registered reverse lift evidence is not MonoLift data"
      let some selectedU := liftType.getAppArgs.back?
        | return .error "the registered reverse lift has no full selected functor"
      unless ← withTransparency .all <| isDefEq selectedU U do
        return .error "the reverse lift datum uses a different exact registered functor action"
      let L ← instantiateMVars L
      discard <| StructuredResult.checkReconstruction L
      let liftedComparison ← StructuredResult.liftSubobjectComparison L
        expectedAmbient actualAmbient ambientIso expectedLifted actualLifted comparison
        nextExpected nextActual
      if let .error message := liftedComparison then
        return .error s!"the complete retained comparison does not lift along the exact accepted datum: {message}"
      let .ok nextComparison := liftedComparison
        | return .error "the complete comparison reconstruction returned no data"
      expectedLifted := nextExpected
      actualLifted := nextActual
      comparison := nextComparison
    unless ← withTransparency .all <| isDefEq (← inferType actualLifted) expected do
      return .error "the replayed lift has a different complete selected result category"
    discard <| StructuredResult.checkReconstruction expectedLifted
    let actualClosed ← StructuredResult.checkReconstruction actualLifted
    let retainedClosed ← StructuredResult.checkReconstruction comparison
    return .ok (actualClosed, some retainedClosed)
  return some (← work)

end CasCatalogue.LiftedSubobjectData
