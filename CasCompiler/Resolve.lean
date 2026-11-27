module

public import CasCompiler.SourceRoutes
public import CasCompiler.OperationFamily
public import CasCompiler.FamilyConversion
public import CasCompiler.Surface
public import CasCompiler.SourceCell
public import CasCompiler.SourceProof
public import CasCompiler.CategoricalPointFamily
import all CasCompiler.SelectionData
public import LeanCategories.Catalogue.Registry.Semantic
public import Mathlib.CategoryTheory.NatIso
public import Mathlib.CategoryTheory.Whiskering

public section

namespace CasCompiler

open Lean Meta Elab Term CasCatalogue


private def resolveTerms (session : SourceSession) (reference : Syntax)
    (read : SourceReadM (Array Expr)) : TermElabM (Array SourceTerm) :=
  session.elaborateJudgementsScoped reference do
    return (← read).map fun value => ⟨value, none⟩



private partial def retainResolvedFamily (reference : SelectedSourceReference)
    (value : Expr) : SourceReadM Expr := do
  match value with
  | .lam name type body binderInfo =>
    SourceReadM.withLambda name type binderInfo fun parameter =>
      retainResolvedFamily reference (body.instantiate1 parameter)
  | _ => SourceReadM.select (← sourceReferenceAt reference value value)


structure SourceCategory where
  private mk ::
  expression : CategoryExpr
  value : SourceTerm



opaque SourceSession.namedCategory (session : SourceSession) (reference : Syntax) (name : String)
    (universes : List Level) (arguments : Array SourceTerm) : TermElabM SourceCategory := do
  let entry ← selectCategory (← semanticState) name
  let constant ← session.constant reference entry.declaration universes
  let value ← session.elaborateScoped reference do
    let arguments ← arguments.mapM fun argument => do
      return Arg.expr (← session.readTerm argument)
    let value ← elabAppArgs (← session.readTerm constant) #[] arguments none false false
    discard <| categoryIdentity value
    discard <| SourceReadM.select (← sourceReferenceAt (.category entry) value value)
    return value
  return ⟨entry.expression, value⟩



opaque SourceSession.unaryCategory (session : SourceSession) (reference : Syntax)
    (id : ConstructorId) (argument : SourceCategory) : TermElabM SourceCategory := do
  let some entry := (← semanticState).constructor? id
    | throwError "the source category constructor is absent"
  unless entry.signature == #[.category] do
    throwError "the selected source constructor does not take one category argument"
  discard <| checkedDeclaration entry.semantics
  let value ← session.elaborateScoped reference do
    let category ← session.readTerm argument.value
    let value ← applyConstructorInterface entry.semantics #[category] #[category]
    discard <| categoryIdentity value
    discard <| SourceReadM.select (← sourceReferenceAt (.constructor entry) value value)
    return value
  return ⟨.construct id #[.category argument.expression], value⟩


opaque SourceObject.sourceCategory (object : SourceObject) : SourceCategory :=
  ⟨object.categoryEntry.expression, object.category⟩


structure SourceRoute where
  private mk ::
  route : Route
  source : SourceCategory
  target : SourceCategory
  functor : SourceTerm




opaque SourceRoutes.prepareFunctor (routes : SourceRoutes) (session : SourceSession)
    (reference : Syntax) (trace : RouteGrammar.Word) (source : SourceCategory) :
    TermElabM SourceRoute := do
  unless routes.source.syntacticEq source.expression do
    throwError "the native source category differs from the exact symbolic route source"
  let route ← routes.reconstruct trace
  let #[functor, target] ← resolveTerms session reference do
      let category ← session.readTerm source.value
      let selected : NativeRouteFunctor ← nativeEdgePathFunctorWith (m := SourceReadM)
        routes.state route.refs category
        (fun selected expected => SourceReadM.select selected expected)
      return #[selected.functor, selected.target]
    | throwError "native route formation returned an invalid number of expressions"
  return ⟨route, source, ⟨route.target, target⟩, functor⟩


inductive SourceFunctorDerivation where
  | registered (entry : FunctorEntry) (parameters : Array SourceTerm)
  | structural (route : SourceRoute)
  | identity (category : SourceCategory)
  | composition (first second : SourceFunctorDerivation)
  | constructed (constructor : ConstructorEntry) (functor : SourceFunctorDerivation)


structure SourceFunctor where
  private mk ::
  derivation : SourceFunctorDerivation
  source : SourceCategory
  target : SourceCategory
  functor : SourceTerm


opaque SourceRoute.asFunctor (route : SourceRoute) : SourceFunctor :=
  ⟨.structural route, route.source, route.target, route.functor⟩




opaque SourceSession.namedFunctor (session : SourceSession) (reference : Syntax)
    (id : FunctorId) (parameters : Array SourceTerm) (source : SourceCategory) :
    TermElabM SourceFunctor := do
  let #[entry] := (← semanticState).functors.filter (·.id == id)
    | throwError "explicit source functor selection requires one registered functor"
  let #[functor, target] ← session.elaborateJudgementsScoped reference do
      let arguments ← parameters.mapM fun parameter => do
        return Arg.expr (← session.readTerm parameter)
      let selected ← viewExpressions (.inl entry)
        (some (source.expression, ← session.readTerm source.value)) fun constant =>
          elabAppArgs constant #[] arguments none false false
      return #[⟨selected.functor, none⟩, ⟨selected.targetBundle, none⟩]
    | throwError "registered functor formation returned an invalid expression family"
  return ⟨.registered entry parameters, source, ⟨entry.target, target⟩, functor⟩



opaque SourceSession.identityFunctor (session : SourceSession) (reference : Syntax)
    (category : SourceCategory) : TermElabM SourceFunctor := do
  let functor ← session.elaborateScoped reference do
    categoryIdentity (← session.readTerm category.value)
  return ⟨.identity category, category, category, functor⟩



opaque SourceSession.composeFunctors (session : SourceSession) (reference : Syntax)
    (first second : SourceFunctor) : TermElabM SourceFunctor := do
  unless first.target.expression.syntacticEq second.source.expression do
    throwError "source functor composition has different complete symbolic middle categories"
  let functor ← session.elaborateScoped reference do
    unless ← isDefEq (← session.readTerm first.target.value)
        (← session.readTerm second.source.value) do
      liftM (m := TermElabM) <|
        throwError "source functor composition has different complete native middle categories"
    mkFunctorComp (← session.readTerm first.functor)
      (← session.readTerm second.functor)
  return ⟨.composition first.derivation second.derivation, first.source, second.target, functor⟩



opaque SourceSession.constructFunctor (session : SourceSession) (reference : Syntax)
    (id : ConstructorId) (functor : SourceFunctor) : TermElabM SourceFunctor := do
  let some constructor := (← semanticState).constructor? id
    | throwError "the source functor constructor is absent"
  unless constructor.signature == #[.category] do
    throwError "the source constructor does not expose a unary category functor interface"
  let some action := constructor.functorialAction
    | throwError "the source constructor has no declared functor action"
  discard <| checkedDeclaration constructor.semantics
  discard <| checkedDeclaration action
  let source ← session.unaryCategory reference id functor.source
  let target ← session.unaryCategory reference id functor.target
  let value ← session.elaborateScoped reference do
    let categories := #[← session.readTerm functor.source.value,
      ← session.readTerm functor.target.value]
    let value ← applyConstructorInterface action categories
      #[← session.readTerm functor.functor]
    let (domain, codomain) ← functorCategoryBundles value
    unless ← isDefEq domain (← session.readTerm source.value) <&&>
        isDefEq codomain (← session.readTerm target.value) do
      liftM (m := TermElabM) <|
        throwError "the constructor functor has different complete native category endpoints"
    SourceReadM.select (← sourceReferenceAt
      (.constructorInterface constructor .functorialAction) value value)
  return ⟨.constructed constructor functor.derivation, source, target, value⟩


structure SourceFunctorImage where
  private mk ::
  functor : SourceFunctor
  object : SourceTerm
  value : SourceTerm



opaque SourceSession.functorImage (session : SourceSession) (reference : Syntax)
    (functor : SourceFunctor) (object : SourceTerm) : TermElabM SourceFunctorImage := do
  let value ← session.elaborateScoped reference do
    let native ← session.readTerm functor.functor
    let object ← session.readTerm object
    functorObject native object (← session.readTerm functor.target.value)
  return ⟨functor, object,
    ← value.inCategory functor.target.expression functor.target.value⟩


structure SourceCategoryFamily where
  private mk ::
  expression : CategoryExpr
  family : SourceTerm


opaque SourceSession.categoryFamily (session : SourceSession) (reference : Syntax) (name : String)
    (universes : List Level) : TermElabM SourceCategoryFamily := do
  let entry ← selectCategory (← semanticState) name
  let constant ← session.constant reference entry.declaration universes
  let family ← session.elaborateScoped reference do
    let value ← session.readTerm constant
    discard <| SourceReadM.select (← sourceReferenceAt (.category entry) value value)
    return value
  return ⟨entry.expression, family⟩


opaque SourceSession.unaryCategoryFamily (session : SourceSession) (reference : Syntax)
    (id : ConstructorId) (argument : SourceCategoryFamily) : TermElabM SourceCategoryFamily := do
  let some entry := (← semanticState).constructor? id
    | throwError "the source category constructor is absent"
  unless entry.signature == #[.category] do
    throwError "the selected source constructor does not take one category argument"
  discard <| checkedDeclaration entry.semantics
  let family ← session.elaborateScoped reference do
    let function ← session.readTerm argument.family
    let family ← liftM (m := MetaM) <|
      forallTelescopeReducing (← inferType function) fun parameters _ => do
        let category := mkAppN function parameters
        let value ← applyConstructorInterface entry.semantics #[category] #[category]
        discard <| categoryIdentity value
        mkLambdaFVars parameters value
    discard <| retainResolvedFamily (.constructor entry) family
    return family
  return ⟨.construct id #[.category argument.expression], family⟩


structure SourceOperationFamily where
  private mk ::
  private state : SemanticState
  source : SourceCategoryFamily
  route : Route
  binding : OperationEntry
  term : SourceTerm

private def operationTerm (state : SemanticState) (session : SourceSession) (reference : Syntax)
    (source : SourceCategoryFamily) (route : Route) (binding : OperationEntry) :
    TermElabM SourceTerm :=
  session.elaborateScoped reference do
    let family ← nativeOperationFamily state source.expression
      (← session.readTerm source.family) route binding
    retainResolvedFamily (.operation binding) family




opaque SourceRoutes.operationFamilies (routes : SourceRoutes) (session : SourceSession)
    (reference : Syntax) (trace : RouteGrammar.Word) (source : SourceCategoryFamily) :
    TermElabM (Array SourceOperationFamily) := do
  let .operation _ := routes.query
    | throwError "whole operation preparation requires an operation-name query"
  unless routes.source.syntacticEq source.expression do
    throwError "the whole category family differs from the exact symbolic route source"
  let route ← routes.reconstruct trace
  let bindings := routes.targets.filterMap fun
    | .operation category binding =>
      if category.expression.syntacticEq route.target then some binding else none
    | _ => none
  if bindings.isEmpty then throwError "the selected source target lost its operation binding"
  bindings.mapM fun binding => do
    let term ← operationTerm routes.state session reference source route binding
    return ⟨routes.state, source, route, binding, term⟩


structure SourceOperationRefinement where
  private mk ::
  original : SourceOperationFamily
  base : OperationEntry
  route : Route
  term : SourceTerm
  proposition : SourceTerm
  proof : SourceTerm




opaque SourceSession.operationRefinement (session : SourceSession) (reference : Syntax)
    (family : SourceOperationFamily) : TermElabM SourceOperationRefinement := do
  let some refinement := family.binding.refines
    | throwError "the source operation has no registered restriction equality"
  let state := family.state
  let #[base] := state.operations.filter (·.id == refinement.base)
    | throwError "the source restriction requires one registered general operation"
  let #[owner] := state.categories.filter (·.id == family.binding.category)
    | throwError "the source restriction has no unique original owner category"
  let #[baseOwner] := state.categories.filter (·.id == base.category)
    | throwError "the source restriction has no unique general owner category"
  unless family.route.target.syntacticEq owner.expression do
    throwError "the source restriction has a different complete original owner"
  let some steps := state.routeEdges? owner.expression baseOwner.expression refinement.route
    | throwError "the source restriction lost its actual structural route"
  discard <| checkedDeclaration refinement.identification
  let route : Route := {
    source := family.route.source
    target := baseOwner.expression
    steps := family.route.steps ++ steps }
  let term ← operationTerm state session reference family.source route base
  let #[proposition, proof] ← resolveTerms session reference do
      let left ← session.readTerm family.term
      let right ← session.readTerm term
      unless ← isDefEq (← inferType left) (← inferType right) do
        liftM (m := TermElabM) <|
          throwError "the source restriction has a different complete operation family type"
      let proposition ← mkEq left right
      let proof ← SourceReadM.prove proposition (sources := #[left, right]) fun proposition sources => do
        let letIds := (← getLCtx).foldl (fun ids declaration =>
          if declaration.isLet then ids.push declaration.fvarId else ids) #[]
        let left ← zetaDeltaFVars sources[0]! letIds
        let right ← zetaDeltaFVars sources[1]! letIds
        let proof ← lambdaTelescope left fun parameters body => do
          unless body.getAppFn.constName? == some family.binding.declaration do
            throwError "the retained operation family lost its original source declaration"
          let constant ← mkConstWithFreshMVarLevels refinement.identification
          let (arguments, _, _) ← forallMetaTelescopeReducing (← inferType constant)
          let originalArguments := body.getAppArgs
          unless arguments.size == originalArguments.size do
            throwError "the source restriction equality has different complete declaration parameters"
          for argument in arguments, original in originalArguments do
            unless ← isDefEq (← inferType argument) (← inferType original) <&&>
                isDefEq argument original do
              throwError "the source restriction equality changes a rigid declaration parameter"
          let mut proof ← instantiateMVars (mkAppN constant arguments)
          let expected ← mkEq body (mkAppN right parameters).headBeta
          unless ← isDefEq (← inferType proof) expected do
            throwError "the source restriction equality has a different complete morphism equation"
          for parameter in parameters.reverse do
            proof ← mkAppM ``funext #[← mkLambdaFVars #[parameter] proof]
          return proof
        unless ← isDefEq (← inferType proof) proposition do
          throwError "the restriction evidence has a different complete operation family equation"
        checkWithKernel (← mkExpectedTypeHint proof proposition)
        return proof
      return #[proposition, proof]
    | throwError "source operation restriction returned an invalid evidence family"
  return ⟨family, base, route, term, proposition, proof⟩


structure SourceOperationAgreement where
  private mk ::
  left : SourceOperationFamily
  right : SourceOperationFamily
  proposition : SourceTerm
  proof : SourceTerm




opaque SourceSession.operationConversion (session : SourceSession) (reference : Syntax)
    (left right : SourceOperationFamily) : TermElabM (Option SourceOperationAgreement) := do
  unless left.source.expression.syntacticEq right.source.expression do
    throwError "operation comparison requires the same complete symbolic source"
  let evidence ← resolveTerms session reference do
    let leftCategory ← session.readTerm left.source.family
    let rightCategory ← session.readTerm right.source.family
    unless ← isDefEq (← inferType leftCategory) (← inferType rightCategory) <&&>
        isDefEq leftCategory rightCategory do
      liftM (m := TermElabM) <|
        throwError "operation comparison requires the same complete native category family"
    let left ← session.readTerm left.term
    let right ← session.readTerm right.term
    let scope ← get
    let agrees ← liftM (m := MetaM) <|
      scope.context.withOriginalSources #[left, right] fun sources => do
        isDefEq (← inferType sources[0]!) (← inferType sources[1]!) <&&>
          isDefEq sources[0]! sources[1]!
    unless agrees do return #[]
    let proposition ← mkEq left right
    let proof ← SourceReadM.prove proposition (sources := #[left]) fun proposition sources => do
      let proof ← mkEqRefl sources[0]!
      unless ← isDefEq (← inferType proof) proposition do
        throwError "conversion evidence has a different complete family equation"
      checkWithKernel (← mkExpectedTypeHint proof proposition)
      return proof
    return #[proposition, proof]
  match evidence with
  | #[] => return none
  | #[proposition, proof] => return some ⟨left, right, proposition, proof⟩
  | _ => throwError "operation conversion returned an invalid evidence shape"



structure SourceFiniteOperationAgreement where
  private mk ::
  routes : SourceRoutes
  source : SourceCategoryFamily
  families : Array SourceOperationFamily
  agreements : Array (Array SourceOperationAgreement)




opaque SourceRoutes.finiteOperationConversion (routes : SourceRoutes) (session : SourceSession)
    (reference : Syntax) (source : SourceCategoryFamily) :
    TermElabM (Option SourceFiniteOperationAgreement) := do
  let .operation _ := routes.query
    | throwError "finite operation comparison requires an operation-name query"
  unless routes.source.syntacticEq source.expression do
    throwError "finite operation comparison has a different complete symbolic source"
  Core.checkSystem "finite operation trace extraction"
  let words := routes.language.grammar.finiteWords
  Core.checkSystem "finite operation trace saturation"
  let some words := words | return none
  let mut families : Array SourceOperationFamily := #[]
  for word in words do
    families := families ++ (← routes.operationFamilies session reference word source)
  if families.isEmpty then return none
  let mut agreements : Array (Array SourceOperationAgreement) := #[]
  for left in families do
    let mut row := #[]
    for right in families do
      Core.checkSystem "finite whole operation comparison"
      let some agreement ← session.operationConversion reference left right | return none
      row := row.push agreement
    agreements := agreements.push row
  return some ⟨routes, source, families, agreements⟩

inductive WhiskerSide where
  | left | right
  deriving BEq


inductive ConstructorCoherence where
  | identity (category : SourceCategory)
  | composition (first second : SourceFunctor)


inductive SourceCellDerivation where
  | registered (entry : CellEntry) (parameters : Array SourceTerm) (inverse : Bool)
  | vertical (first second : SourceCellDerivation)
  | horizontal (first second : SourceCellDerivation)
  | whisker (side : WhiskerSide) (functor : SourceFunctor) (cell : SourceCellDerivation)
  | constructed (constructor : ConstructorEntry) (cell : SourceCellDerivation)
  | coherence (constructor : ConstructorEntry) (input : ConstructorCoherence)
  | inverse (original : SourceCellDerivation)


structure SourceCell where
  private mk ::
  derivation : SourceCellDerivation
  source : SourceCategory
  target : SourceCategory
  transformation : SourceTerm
  left : SourceTerm
  right : SourceTerm
  isomorphism : Option SourceTerm




opaque SourceSession.cell (session : SourceSession) (reference : Syntax)
    (id : NaturalTransformationId) (parameters : Array SourceTerm) (source : SourceCategory)
    (inverse : Bool := false) : TermElabM SourceCell := do
  let state ← semanticState
  let #[entry] := state.cells.filter (·.id == id)
    | throwError "a source cell component requires one registered cell"
  unless source.expression.syntacticEq entry.source do
    throwError "the cell has a different complete symbolic source category"
  let terms ← resolveTerms session reference do
    let category ← session.readTerm source.value
    let arguments ← parameters.mapM fun parameter => do
      return Arg.expr (← session.readTerm parameter)
    let constant ← mkConstWithFreshMVarLevels entry.declaration
    let application ← elabAppArgs constant #[] arguments none false false
    let cell ← nativeSourceCell entry application inverse
    unless ← isDefEq cell.sourceBundle category do
      liftM (m := TermElabM) <|
        throwError "the source cell has a different complete native source category"
    let selected ← SourceReadM.select (← sourceReferenceAt (.cell entry)
      cell.application cell.application)
    let transformation ← if entry.invertible then
        mkAppM (if inverse then ``CategoryTheory.Iso.inv else ``CategoryTheory.Iso.hom) #[selected]
      else pure selected
    let isomorphism ← if entry.invertible then do
        let directed ← if inverse then mkAppM ``CategoryTheory.Iso.symm #[selected]
          else pure selected
        pure (some directed)
      else pure none
    let cell := { cell with transformation, isomorphism }
    let transformation ← SourceReadM.select {
      value := transformation, observation := some (.cell entry), cellFamily := some cell }
    let terms := #[transformation, cell.left.functor, cell.right.functor, cell.targetBundle]
    return terms ++ cell.isomorphism.toArray
  match terms with
  | #[transformation, left, right, target] =>
    return ⟨.registered entry parameters inverse, source, ⟨entry.target, target⟩,
      transformation, left, right, none⟩
  | #[transformation, left, right, target, isomorphism] =>
    return ⟨.registered entry parameters inverse, source, ⟨entry.target, target⟩,
      transformation, left, right, some isomorphism⟩
  | _ => throwError "source cell formation returned an invalid expression family"




opaque SourceSession.composeCells (session : SourceSession) (reference : Syntax)
    (first second : SourceCell) : TermElabM SourceCell := do
  unless first.source.expression.syntacticEq second.source.expression &&
      first.target.expression.syntacticEq second.target.expression do
    throwError "cell composition has different complete symbolic categories"
  let terms ← resolveTerms session reference do
    unless ← isDefEq (← session.readTerm first.source.value)
          (← session.readTerm second.source.value) <&&>
        isDefEq (← session.readTerm first.target.value)
          (← session.readTerm second.target.value) do
      liftM (m := TermElabM) <|
        throwError "cell composition has different complete native categories"
    unless ← isDefEq (← session.readTerm first.right)
        (← session.readTerm second.left) do
      liftM (m := TermElabM) <|
        throwError "cell composition has different complete intermediate functors"
    let left ← session.readTerm first.left
    let right ← session.readTerm second.right
    let transformation ← mkAppM ``CategoryTheory.CategoryStruct.comp
      #[← session.readTerm first.transformation,
        ← session.readTerm second.transformation]
    let expected ← mkAppM ``CategoryTheory.NatTrans #[left, right]
    unless ← isDefEq (← inferType transformation) expected do
      liftM (m := TermElabM) <|
        throwError "cell composition has different complete native endpoints"
    match first.isomorphism, second.isomorphism with
    | some firstIso, some secondIso =>
      let isomorphism ← mkAppM ``CategoryTheory.Iso.trans
        #[← session.readTerm firstIso, ← session.readTerm secondIso]
      let expected ← mkAppM ``CategoryTheory.Iso #[left, right]
      unless ← isDefEq (← inferType isomorphism) expected <&&>
          isDefEq (← mkAppM ``CategoryTheory.Iso.hom #[isomorphism]) transformation do
        liftM (m := TermElabM) <|
          throwError "the composite isomorphism does not witness its complete directed transformation"
      return #[transformation, isomorphism]
    | _, _ => return #[transformation]
  match terms with
  | #[transformation] =>
    return ⟨.vertical first.derivation second.derivation, first.source, first.target,
      transformation, first.left, second.right, none⟩
  | #[transformation, isomorphism] =>
    return ⟨.vertical first.derivation second.derivation, first.source, first.target,
      transformation, first.left, second.right, some isomorphism⟩
  | _ => throwError "cell composition returned an invalid expression family"



opaque SourceSession.horizontalCells (session : SourceSession) (reference : Syntax)
    (first second : SourceCell) : TermElabM SourceCell := do
  unless first.target.expression.syntacticEq second.source.expression do
    throwError "horizontal cell composition has different complete symbolic middle categories"
  let terms ← resolveTerms session reference do
    unless ← isDefEq (← session.readTerm first.target.value)
        (← session.readTerm second.source.value) do
      liftM (m := TermElabM) <|
        throwError "horizontal cell composition has different complete native middle categories"
    let left ← mkFunctorComp (← session.readTerm first.left)
      (← session.readTerm second.left)
    let right ← mkFunctorComp (← session.readTerm first.right)
      (← session.readTerm second.right)
    let transformation ← mkAppM ``CategoryTheory.NatTrans.hcomp
      #[← session.readTerm first.transformation,
        ← session.readTerm second.transformation]
    let expected ← mkAppM ``CategoryTheory.NatTrans #[left, right]
    unless ← isDefEq (← inferType transformation) expected do
      liftM (m := TermElabM) <|
        throwError "horizontal cell composition has different complete native endpoints"
    match first.isomorphism, second.isomorphism with
    | some firstIso, some secondIso =>
      let isomorphism ← mkAppM ``CategoryTheory.NatIso.hcomp
        #[← session.readTerm firstIso, ← session.readTerm secondIso]
      let expected ← mkAppM ``CategoryTheory.Iso #[left, right]
      unless ← isDefEq (← inferType isomorphism) expected <&&>
          isDefEq (← mkAppM ``CategoryTheory.Iso.hom #[isomorphism]) transformation do
        liftM (m := TermElabM) <|
          throwError "horizontal isomorphism does not witness its complete directed transformation"
      return #[transformation, left, right, isomorphism]
    | _, _ => return #[transformation, left, right]
  match terms with
  | #[transformation, left, right] =>
    return ⟨.horizontal first.derivation second.derivation, first.source, second.target,
      transformation, left, right, none⟩
  | #[transformation, left, right, isomorphism] =>
    return ⟨.horizontal first.derivation second.derivation, first.source, second.target,
      transformation, left, right, some isomorphism⟩
  | _ => throwError "horizontal cell composition returned an invalid expression family"



opaque SourceSession.inverseCell (session : SourceSession) (reference : Syntax)
    (cell : SourceCell) : TermElabM SourceCell := do
  let some original := cell.isomorphism | throwError "the source transformation has no inverse"
  let #[transformation, isomorphism, left, right] ← resolveTerms session reference do
    let isomorphism ← mkAppM ``CategoryTheory.Iso.symm #[← session.readTerm original]
    let left ← session.readTerm cell.right
    let right ← session.readTerm cell.left
    let expected ← mkAppM ``CategoryTheory.Iso #[left, right]
    unless ← isDefEq (← inferType isomorphism) expected do
      liftM (m := TermElabM) <|
        throwError "the inverse isomorphism has different complete native endpoints"
    return #[← mkAppM ``CategoryTheory.Iso.hom #[isomorphism], isomorphism, left, right]
    | throwError "source inverse formation returned an invalid expression family"
  return ⟨.inverse cell.derivation, cell.source, cell.target,
    transformation, left, right, some isomorphism⟩



opaque SourceSession.whiskerCell (session : SourceSession) (reference : Syntax)
    (side : WhiskerSide) (functor : SourceFunctor) (cell : SourceCell) : TermElabM SourceCell := do
  let (source, target, firstMiddle, secondMiddle) := match side with
    | .left => (functor.source, cell.target, functor.target, cell.source)
    | .right => (cell.source, functor.target, cell.target, functor.source)
  unless firstMiddle.expression.syntacticEq secondMiddle.expression do
    throwError "whiskering has different complete symbolic middle categories"
  let terms ← resolveTerms session reference do
    unless ← isDefEq (← session.readTerm firstMiddle.value)
        (← session.readTerm secondMiddle.value) do
      liftM (m := TermElabM) <|
        throwError "whiskering has different complete native middle categories"
    let functor ← session.readTerm functor.functor
    let compose (part : Expr) := match side with
      | .left => mkFunctorComp functor part
      | .right => mkFunctorComp part functor
    let arguments (part : Expr) := match side with
      | .left => #[functor, part]
      | .right => #[part, functor]
    let left ← compose (← session.readTerm cell.left)
    let right ← compose (← session.readTerm cell.right)
    let operation := match side with
      | .left => ``CategoryTheory.Functor.whiskerLeft
      | .right => ``CategoryTheory.Functor.whiskerRight
    let transformation ← mkAppM operation
      (arguments (← session.readTerm cell.transformation))
    let expected ← mkAppM ``CategoryTheory.NatTrans #[left, right]
    unless ← isDefEq (← inferType transformation) expected do
      liftM (m := TermElabM) <|
        throwError "whiskering has different complete native functor endpoints"
    match cell.isomorphism with
    | none => return #[transformation, left, right]
    | some original =>
      let operation := match side with
        | .left => ``CategoryTheory.Functor.isoWhiskerLeft
        | .right => ``CategoryTheory.Functor.isoWhiskerRight
      let isomorphism ← mkAppM operation (arguments (← session.readTerm original))
      let expected ← mkAppM ``CategoryTheory.Iso #[left, right]
      unless ← isDefEq (← inferType isomorphism) expected <&&>
          isDefEq (← mkAppM ``CategoryTheory.Iso.hom #[isomorphism]) transformation do
        liftM (m := TermElabM) <|
          throwError "the whiskered isomorphism does not witness its complete directed transformation"
      return #[transformation, left, right, isomorphism]
  match terms with
  | #[transformation, left, right] =>
    return ⟨.whisker side functor cell.derivation, source, target,
      transformation, left, right, none⟩
  | #[transformation, left, right, isomorphism] =>
    return ⟨.whisker side functor cell.derivation, source, target,
      transformation, left, right, some isomorphism⟩
  | _ => throwError "whiskering returned an invalid expression family"

private def checkConstructorComparison (source target left right isomorphism : Expr) :
    MetaM Unit := do
  let (leftSource, leftTarget) ← functorCategoryBundles left
  let (rightSource, rightTarget) ← functorCategoryBundles right
  unless ← isDefEq leftSource source <&&> isDefEq leftTarget target <&&>
      isDefEq rightSource source <&&> isDefEq rightTarget target do
    throwError "the constructor action has different complete native categories"
  let expected ← mkAppM ``CategoryTheory.Iso #[left, right]
  unless ← isDefEq (← inferType isomorphism) expected do
    throwError "the constructor comparison has different complete native functor endpoints"




opaque SourceSession.constructCell (session : SourceSession) (reference : Syntax)
    (id : ConstructorId) (cell : SourceCell) : TermElabM SourceCell := do
  let some constructor := (← semanticState).constructor? id
    | throwError "the source comparison constructor is absent"
  unless constructor.signature == #[.category] do
    throwError "the source constructor does not expose a unary category comparison interface"
  let some action := constructor.functorialAction
    | throwError "the source constructor has no declared functor action"
  let some comparison := constructor.comparisonAction
    | throwError "the source constructor has no declared comparison action"
  let some original := cell.isomorphism
    | throwError "the source constructor comparison interface requires a native isomorphism"
  discard <| checkedDeclaration constructor.semantics
  discard <| checkedDeclaration action
  discard <| checkedDeclaration comparison
  let source ← session.unaryCategory reference id cell.source
  let target ← session.unaryCategory reference id cell.target
  let #[transformation, left, right, isomorphism] ← resolveTerms session reference do
    let categories := #[← session.readTerm cell.source.value,
      ← session.readTerm cell.target.value]
    let left ← applyConstructorInterface action categories #[← session.readTerm cell.left]
    let right ← applyConstructorInterface action categories #[← session.readTerm cell.right]
    let isomorphism ← applyConstructorInterface comparison categories
      #[← session.readTerm original]
    let left ← SourceReadM.select (← sourceReferenceAt
      (.constructorInterface constructor .functorialAction) left left)
    let right ← SourceReadM.select (← sourceReferenceAt
      (.constructorInterface constructor .functorialAction) right right)
    let expected ← mkAppM ``CategoryTheory.Iso #[left, right]
    let isomorphism ← SourceReadM.select (← sourceReferenceAt
      (.constructorInterface constructor .comparisonAction) isomorphism isomorphism) (some expected)
    checkConstructorComparison (← session.readTerm source.value)
      (← session.readTerm target.value) left right isomorphism
    return #[← mkAppM ``CategoryTheory.Iso.hom #[isomorphism], left, right, isomorphism]
    | throwError "constructor comparison returned an invalid expression family"
  return ⟨.constructed constructor cell.derivation, source, target,
    transformation, left, right, some isomorphism⟩




opaque SourceSession.constructorCoherence (session : SourceSession) (reference : Syntax)
    (id : ConstructorId) (input : ConstructorCoherence) : TermElabM SourceCell := do
  let some constructor := (← semanticState).constructor? id
    | throwError "the source comparison constructor is absent"
  unless constructor.signature == #[.category] do
    throwError "the source constructor does not expose a unary category comparison interface"
  let some action := constructor.functorialAction
    | throwError "the source constructor has no declared functor action"
  let law ← match input with
    | .identity _ => match constructor.identityComparison with
      | some law => pure law
      | none => throwError "the source constructor has no declared identity comparison"
    | .composition _ _ => match constructor.compositionComparison with
      | some law => pure law
      | none => throwError "the source constructor has no declared composition comparison"
  let (domain, codomain) ← match input with
    | .identity category => pure (category, category)
    | .composition first second => do
      unless first.target.expression.syntacticEq second.source.expression do
        throwError "constructor composition has different complete symbolic middle categories"
      pure (first.source, second.target)
  discard <| checkedDeclaration constructor.semantics
  discard <| checkedDeclaration action
  discard <| checkedDeclaration law
  let source ← session.unaryCategory reference id domain
  let target ← session.unaryCategory reference id codomain
  let #[transformation, left, right, isomorphism] ← resolveTerms session reference do
    let (left, right, isomorphism) ← match input with
      | .identity category => do
        let category ← session.readTerm category.value
        let left ← applyConstructorInterface action #[category, category]
          #[← categoryIdentity category]
        let left ← SourceReadM.select (← sourceReferenceAt
          (.constructorInterface constructor .functorialAction) left left)
        let right ← categoryIdentity (← session.readTerm source.value)
        let isomorphism ← applyConstructorInterface law #[category] #[category]
        let expected ← mkAppM ``CategoryTheory.Iso #[left, right]
        let isomorphism ← SourceReadM.select (← sourceReferenceAt
          (.constructorInterface constructor .identityComparison) isomorphism isomorphism) (some expected)
        pure (left, right, isomorphism)
      | .composition first second => do
        let C ← session.readTerm first.source.value
        let D ← session.readTerm first.target.value
        let E ← session.readTerm second.target.value
        unless ← isDefEq D (← session.readTerm second.source.value) do
          liftM (m := TermElabM) <|
            throwError "constructor composition has different complete native middle categories"
        let F ← session.readTerm first.functor
        let G ← session.readTerm second.functor
        let left ← applyConstructorInterface action #[C, E] #[← mkFunctorComp F G]
        let left ← SourceReadM.select (← sourceReferenceAt
          (.constructorInterface constructor .functorialAction) left left)
        let first ← applyConstructorInterface action #[C, D] #[F]
        let second ← applyConstructorInterface action #[D, E] #[G]
        let first ← SourceReadM.select (← sourceReferenceAt
          (.constructorInterface constructor .functorialAction) first first)
        let second ← SourceReadM.select (← sourceReferenceAt
          (.constructorInterface constructor .functorialAction) second second)
        let right ← mkFunctorComp first second
        let isomorphism ← applyConstructorInterface law #[C, D, E] #[F, G]
        let expected ← mkAppM ``CategoryTheory.Iso #[left, right]
        let isomorphism ← SourceReadM.select (← sourceReferenceAt
          (.constructorInterface constructor .compositionComparison) isomorphism isomorphism) (some expected)
        pure (left, right, isomorphism)
    checkConstructorComparison (← session.readTerm source.value)
      (← session.readTerm target.value) left right isomorphism
    return #[← mkAppM ``CategoryTheory.Iso.hom #[isomorphism], left, right, isomorphism]
    | throwError "constructor coherence returned an invalid expression family"
  return ⟨.coherence constructor input, source, target,
    transformation, left, right, some isomorphism⟩


structure SourceCellComponent where
  private mk ::
  cell : SourceCell
  object : SourceTerm
  value : SourceTerm



opaque SourceSession.cellComponent (session : SourceSession) (reference : Syntax)
    (cell : SourceCell) (object : SourceTerm) : TermElabM SourceCellComponent := do
  let value ← session.elaborateScoped reference do
    let category ← session.readTerm cell.source.value
    let object ← session.readTerm object
    let carrier ← mkAppM ``CategoryTheory.Bundled.α #[category]
    unless ← isDefEq (← inferType object) carrier do
      liftM (m := TermElabM) <|
        throwError "the source cell object has a different complete native category"
    let transformation ← session.readTerm cell.transformation
    if let some original := (← SourceReadM.selection? transformation).bind (·.cellFamily) then
      let selected ← original.selectedComponent ⟨object,
        some ⟨.object, cell.source.expression, category, none, none⟩⟩
      selectMorphism selected (fun selected expected => SourceReadM.select selected expected)
        (some original.targetBundle)
    else
      mkAppM ``CategoryTheory.NatTrans.app #[transformation, object]
  return ⟨cell, object, value⟩

end CasCompiler
