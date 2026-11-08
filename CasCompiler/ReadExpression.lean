module

public import CasCompiler.SourceNumeral
public import CasCompiler.SourcePattern
public import CasCompiler.SourceCarrier
public import CasCompiler.SourceTuple
public import CasCompiler.SourceOperation
public import CasCompiler.SourceLimit
public import CasCompiler.SourceMember
public import CasCompiler.SourceLift
public import Lean.Elab.App

public section

namespace CasCompiler

open Lean Meta Elab Term

private def sourceAtomName? (source : Syntax) : Option String :=
  if source.isOfKind ``CasCatalogue.Language.casAtom ||
      source.isOfKind ``CasCatalogue.Language.casDomainAtom then
    -- Lean's alternative-token parser retains a token-kind node around its actual atom.
    some source[0][0].getAtomVal
  else none

-- Reuse Language.numeric's source rule: numeral-only syntax has no chosen set yet.
private partial def sourceNumeric (source : Syntax) : Bool :=
  !source.isIdent && !(source.isAtom &&
    (source.getAtomVal == "√" || source.getAtomVal == "|")) && source.getArgs.all sourceNumeric

-- Native application determines argument types before the original source is read once.
-- A final application uses the actual expressions, preserving lexical binding occurrences
-- even when expected-type unification has already assigned a provisional argument.
-- Reuse: Lean.Elab.App.elabAppArgs and Lean.Meta.mkFreshExprMVar at Lean 4.33.0.
partial def readExpression
    (categoryOf : FVarId → TermElabM (Option NativeSourceCategory))
    (source : TSyntax `cas_term) (expected : Option Expr)
    (qualification : Option String := none) : TermElabM NativeSourceJudgement :=
  withRef source do
  let application := fun (source : NativeSourceJudgement) (arguments : Array (TSyntax `cas_term))
      (expected : Option Expr) => do
    let function ← if arguments.isEmpty then pure source.value else sourceFunction source
    let holes ← arguments.mapM fun _ => mkFreshExprMVar none
    discard <| elabAppArgs function #[] (holes.map Arg.expr) expected false false
    let mut actual := #[]
    for argument in arguments, hole in holes do
      let type ← instantiateMVars (← inferType hole)
      let value ← readExpression categoryOf argument (some type)
      unless ← isDefEq hole value.value do
        throwErrorAt argument "the source argument does not match its dependent native type"
      actual := actual.push (Arg.expr value.value)
    elabAppArgs function #[] actual expected false false
  let elementOperation := fun (name : String) (operands : Array (TSyntax `cas_term))
      (numerals : Array (TSyntax `cas_term)) (known : Array (Option Expr))
      (domainHint : Option Expr) => do
    let mut retained : Array (Option Expr) := Array.replicate operands.size none
    let mut hints : Array Expr := #[]
    for operand in operands, index in [:operands.size] do
      if let some (some value) := known[index]? then
        retained := retained.set! index (some value)
        hints := hints.push (← inferType value)
        continue
      if let `(cas_term| $identifier:ident) := operand then
        if ((← getLCtx).findFromUserName? identifier.getId).isSome then
          let value ← readExpression categoryOf operand none
          retained := retained.set! index (some value.value)
          hints := hints.push (← inferType value.value)
    let contextual ← expected.mapM instantiateMVars
    let contextual := contextual.filter (! ·.headBeta.consumeMData.getAppFn.isMVar)
    let domain ← match domainHint.or contextual with
      | some type => pure type
      | none => do
        let mut domain := hints[0]?
        if domain.isNone then
          for operand in operands, index in [:operands.size] do
            if let `(cas_term| $_:num) := operand then continue
            let value ← readExpression categoryOf operand none
            domain := some (← inferType value.value)
            retained := retained.set! index (some value.value)
            hints := hints.push (← inferType value.value)
            break
        if let some selectedDomain := domain then pure selectedDomain
        else do
          let defaults := (← CasCatalogue.semanticState).objects.filter
            (·.notations.contains "literal.integral.domain")
          let #[entry] := defaults
            | CasCatalogue.throwSemanticAmbiguity "the source operation requires its scalar domain"
          discard <| checkedDeclaration entry.declaration
          mkConstWithFreshMVarLevels entry.declaration
    let originalOperand := retained
    let operationHints := if domainHint.isSome then #[domain] else hints
    let operation ← sourceOperation categoryOf name domain contextual operationHints operands.size
      (numerals.map fun numeral type => do
        return (← readExpression categoryOf numeral (some type)).value)
    let function ← sourceSetFunction operation.value
    let argument ← mkFreshExprMVar none
    discard <| elabAppArgs function #[] #[Arg.expr argument] none false false
    let cursor : IO.Ref Nat ← liftM (m := IO) (IO.mkRef 0)
    let readOperand : TSyntax `cas_term → Expr → TermElabM Expr := fun source type => do
      let index : Nat ← liftM (m := IO) cursor.get
      liftM (m := IO) (cursor.set (index + 1))
      let some transport := operation.inputTransports[index]?
        | throwError "the source operation lost its declared operand position"
      let read : Expr → TermElabM Expr := fun expected => do
        if let some (some value) := originalOperand[index]? then
          checkRegisteredDomains (← inferType value) expected
          unless ← isDefEq (← inferType value) expected do
            throwErrorAt source "the retained operand has a different declared domain"
          return value
        return (← readExpression categoryOf source (some expected)).value
      if transport then
        let some comparison := operation.comparison
          | throwError "the source operand lost its supplied comparison"
        let iso ← whnfR (← inferType comparison)
        let value ← read iso.getAppArgs[3]!
        let inverse ← mkAppM ``CategoryTheory.Iso.inv #[comparison]
        let inverse ← sourceSetFunction inverse
        elabAppArgs inverse #[] #[Arg.expr value] (some type) false false
      else if operation.inputDomains[index]?.getD false then read domain
      else read type
    let type ← instantiateMVars (← inferType argument)
    let value ← if operands.size == 1 then do
        let some operand := operands[0]?
          | throwError "the source operation requires its original operand"
        readOperand operand type
      else sourceTuple operands type readOperand
    let value ← elabAppArgs function #[] #[Arg.expr value] none false false
    let value ← if operation.outputTransport then do
        let some comparison := operation.comparison
          | throwError "the source result lost its supplied comparison"
        let forward ← mkAppM ``CategoryTheory.Iso.hom #[comparison]
        let forward ← sourceSetFunction forward
        elabAppArgs forward #[] #[Arg.expr value] expected false false
      else if operation.outputDomain then mkExpectedTypeHint value domain
      else pure value
    return (⟨value, none⟩ : NativeSourceJudgement)
  let action := fun (left right : TSyntax `cas_term) => do
    let rightExpected := if sourceNumeric right.raw then expected else none
    let value ← readExpression categoryOf right rightExpected
    elementOperation "•" #[left, right] #[] #[none, some value.value]
      (some (← inferType value.value))
  let juxtapose := fun (left right : TSyntax `cas_term) => do
    let rightExpected := if sourceNumeric right.raw then expected else none
    let rightValue ← readExpression categoryOf right rightExpected
    let leftValue ← if sourceNumeric left.raw then pure none
      else pure (some (← readExpression categoryOf left none))
    let name ← sourceJuxtapositionName categoryOf leftValue rightValue
    let owner ← if name == "•" then pure (some (← inferType rightValue.value)) else pure none
    elementOperation name #[left, right] #[] #[leftValue.map (·.value), some rightValue.value]
      owner
  let annotated := fun (body domain : TSyntax `cas_term) => do
    let domain ← readExpression categoryOf domain none
    discard <| getLevel domain.value
    if let some expected := expected then checkRegisteredDomains domain.value expected
    readExpression categoryOf body (some domain.value)
  let lambda := fun (pattern body : TSyntax `cas_term) => do
    let some expected := expected
      | throwError "a source lambda requires its independently declared function type"
    let type ← whnf expected
    if type.isAppOf ``TypeCat.Hom then
      -- Mathlib's set-map constructor wraps this exact native function. It supplies
      -- no structured-map laws; the complete declared Hom type fixes both endpoints.
      let constructor ← mkConstWithFreshMVarLevels ``TypeCat.ofHom
      let hole ← mkFreshExprMVar none
      discard <| elabAppArgs constructor #[] #[Arg.expr hole] (some expected) false false
      let function ← readExpression categoryOf source (some (← inferType hole))
      let value ← elabAppArgs constructor #[] #[Arg.expr function.value]
        (some expected) false false
      return ← sourceSetJudgement .morphism value
    let .forallE _ domain codomain binderInfo := type
      | CasCatalogue.throwUnsupportedSource
          "source lambda formation is not implemented for this declared map type"
    let value ← sourcePatternLambda pattern domain binderInfo fun parameter => do
      return (← readExpression categoryOf body (some (codomain.instantiate1 parameter))).value
    return ⟨value, none⟩
  let object := fun (name : String) (category : Option String)
      (arguments : Array (TSyntax `cas_term)) => do
    let (entry, categoryEntry) ← selectObject name category expected
    let (bundle, value) ← registeredExpressions (.inl entry) categoryEntry fun function expected =>
      application ⟨function, none⟩ arguments expected
    return (⟨value, some ⟨.object, categoryEntry.expression, bundle,
      ← objectCarrierSelection entry bundle value⟩⟩ : NativeSourceJudgement)
  let registered := fun (name : Ident) (arguments : Array (TSyntax `cas_term)) => do
    if let some declaration := (← getLCtx).findFromUserName? name.getId then
      let selected ← categoryOf declaration.fvarId
      let value ← application ⟨mkFVar declaration.fvarId, selected⟩ arguments expected
      return ⟨value, if arguments.isEmpty then selected else none⟩
    if name.getId == `id then
      let #[argument] := arguments
        | throwError "source identity requires one object"
      let object ← readExpression categoryOf argument none
      let object ← if object.category.isSome then pure object
        else sourceSetJudgement .object object.value
      let some category := object.category
        | throwError "source identity requires its complete selected category"
      unless category.role == .object do throwError "source identity requires an object"
      let carrier ← mkAppM ``CategoryTheory.Bundled.α #[category.bundle]
      let instanceValue ← mkAppM ``CategoryTheory.Bundled.str #[category.bundle]
      let structureValue ← mkAppOptM ``CategoryTheory.Category.toCategoryStruct
        #[some carrier, some instanceValue]
      let function ← mkAppOptM ``CategoryTheory.CategoryStruct.id
        #[some carrier, some structureValue]
      let value ← elabAppArgs function #[] #[Arg.expr object.value] expected false false
      return ⟨value, some { category with role := .morphism, carrier := none }⟩
    let (entry, categoryEntry) ← selectNamed
      (name.getId.toString (escape := false)) qualification expected
    let declaration := match entry with
      | .inl entry => entry.declaration
      | .inr entry => entry.declaration
    let parameterCount ← withoutModifyingState do
      let info ← checkedDeclaration declaration
      let (_, binders, _) ← forallMetaTelescopeReducing info.type
      pure (binders.filter (·.isExplicit)).size
    let (bundle, value) ← registeredExpressions entry categoryEntry fun function expected =>
      application ⟨function, none⟩ (arguments.take parameterCount) expected
    let role := match entry with
      | .inl _ => SourceCategoryRole.object
      | .inr _ => SourceCategoryRole.morphism
    let carrier ← match entry with
      | .inl object => objectCarrierSelection object bundle value
      | .inr _ => pure none
    let result : NativeSourceJudgement :=
      ⟨value, some ⟨role, categoryEntry.expression, bundle, carrier⟩⟩
    if parameterCount < arguments.size then
      return ⟨← application result (arguments.drop parameterCount) expected, none⟩
    return result
  let member := fun (receiver : TSyntax `cas_term) (name : String)
      (arguments : Array (TSyntax `cas_term)) => do
    let receiver ← readExpression categoryOf receiver none
    if let some value ← sourceLiftMember? receiver name then
      unless arguments.isEmpty do
        throwError "a selected lift projection takes no additional source arguments"
      return value
    let family ← sourceMemberFamily receiver name qualification
    if arguments.isEmpty then return family
    if arguments.size == 1 then
      return (⟨← application family arguments expected, none⟩ : NativeSourceJudgement)
    let function ← sourceFunction family
    let argument ← mkFreshExprMVar none
    discard <| elabAppArgs function #[] #[Arg.expr argument] expected false false
    let type ← instantiateMVars (← inferType argument)
    let argument ← sourceTuple arguments type fun source type => do
      return (← readExpression categoryOf source (some type)).value
    return (⟨← elabAppArgs function #[] #[Arg.expr argument] expected false false, none⟩ :
      NativeSourceJudgement)
  let readFunctorAction := fun (role : SourceCategoryRole) (receiver : TSyntax `cas_term)
      (id : Ident) (arguments : Array (TSyntax `cas_term)) => do
    let entry ← selectView (id.getId.toString (escape := false))
    let receiver ← readExpression categoryOf receiver none
    if let some category := receiver.category then
      unless category.role == role do
        throwError "the source functor action has a different object or morphism role"
    let selected ← viewExpressions entry
        (receiver.category.map fun category => (category.expression, category.bundle)) fun constant =>
      application ⟨constant, none⟩ arguments none
    let image ← match role with
      | .object => functorObject selected.functor receiver.value selected.targetBundle
      | .morphism => do
        let function ← mkAppM ``CategoryTheory.Functor.map #[selected.functor]
        -- AppBuilder protects pre-existing metavariables. Native source application must
        -- solve the selected declaration's levels at the actual arrow in this context.
        elabAppArgs function #[] #[Arg.expr receiver.value] none false false
    let (kind, id) := match selected.reference with
      | .inl id => (``CasCatalogue.EdgeRef.functor, id.raw)
      | .inr id => (``CasCatalogue.EdgeRef.classifierForget, id.raw)
    let edge := match selected.reference with
      | .inl id => CasCatalogue.EdgeRef.functor id
      | .inr id => CasCatalogue.EdgeRef.classifierForget id
    let carrier : Option NativeSourceCarrierSelection ← match receiver.category.bind (·.carrier) with
      | none => pure none
      | some carrier =>
        if role != .object || carrier.refs[0]? != some edge then pure none
        else do
          let some action := carrier.actions[0]?
            | throwError "the selected carrier prefix has no complete native edge application"
          let action ← instantiateMVars action
          let actual ← instantiateMVars selected.functor
          let agrees ← if action == actual then pure true else do
            if action.hasMVar || action.hasLevelMVar || actual.hasMVar || actual.hasLevelMVar then
              CasCatalogue.throwUnsupportedSource
                "carrier-prefix comparison requires its complete native view parameters"
            withoutModifyingState <| isDefEq action actual
          pure <| if agrees then
            some { carrier with refs := carrier.refs.drop 1, actions := carrier.actions.drop 1 }
          else none
    -- Keep the exact selected reference beside its actual native action for source inspection.
    -- Lean MData preserves these names through closure; native checking uses the retained body.
    return (⟨sourceReference kind id selected.declaration image,
      some ⟨role, selected.target, selected.targetBundle, carrier⟩⟩ :
      NativeSourceJudgement)
  let judgement ← if source.raw.getKind == ``CasCatalogue.Language.casCallWith then do
      let arguments := source.raw[4].getSepArgs.map fun argument =>
        (⟨argument⟩ : TSyntax `cas_term)
      member ⟨source.raw[0]⟩ (source.raw[2].getId.toString (escape := false)) arguments
    else if source.raw.isOfKind ``CasCatalogue.Language.casTimes then
      juxtapose ⟨source.raw[0]⟩ ⟨source.raw[2]⟩
    else if source.raw.isOfKind ``CasCatalogue.Language.casActed then
      juxtapose ⟨source.raw[0]⟩ (← `(cas_term| $(⟨source.raw[1]⟩):ident))
    else if let some name := sourceAtomName? source then object name qualification #[]
    else match source with
    | `(cas_term| lift($receiver:cas_term) along $id:ident($arguments:cas_term,*)
        with $input:cas_term using $evidence:cas_term) => do
      let state ← CasCatalogue.semanticState
      let #[row] := state.lifts.filter
        (·.id.raw == id.getId.toString (escape := false))
        | throwError "selected source lifting requires one registered lift"
      discard <| checkedDeclaration row.evidence
      if let some computation := row.computation then discard <| checkedDeclaration computation
      checkEdgeDeclarations state row.edge
      CasCatalogue.validateLift state row
      let receiver ← readExpression categoryOf receiver none
      let selected ← application ⟨← mkConstWithFreshMVarLevels row.evidence, none⟩
        arguments.getElems none
      let input ← readExpression categoryOf input none
      let `(cas_term| proof($proof:term)) := evidence
        | throwError "a selected lift requires explicit native monicity evidence"
      let proof ← elabTermEnsuringType proof none
      sourceSelectedLift row receiver input selected proof
    | `(cas_term| $left:cas_term × $right:cas_term) => do
      let left ← readExpression categoryOf left none qualification
      let right ← readExpression categoryOf right none qualification
      sourceBinaryLimit left right false
    | `(cas_term| $left:cas_term ⊔ $right:cas_term) => do
      let left ← readExpression categoryOf left none qualification
      let right ← readExpression categoryOf right none qualification
      sourceBinaryLimit left right true
    | `(cas_term| $left:cas_term + $right:cas_term) =>
      elementOperation "+" #[left, right] #[] #[] none
    | `(cas_term| $left:cas_term · $right:cas_term) =>
      elementOperation "·" #[left, right] #[] #[] none
    | `(cas_term| $left:cas_term • $right:cas_term) => action left right
    | `(cas_term| -$operand:cas_term) =>
      elementOperation "-" #[operand] #[] #[] none
    | `(cas_term| $base:cas_term ^ $power:cas_term) =>
      elementOperation "^" #[base] #[power] #[] none
    | `(cas_term| $name:ident ↦ $body:cas_term) => do
      lambda (← `(cas_term| $name:ident)) body
    | `(cas_term| ($first:cas_term, $rest:cas_term,*) ↦ $body:cas_term) => do
      lambda (← `(cas_term| ($first:cas_term, $rest:cas_term,*))) body
    | `(cas_term| $number:num in $domain:cas_term using ($evidence:cas_term,*)) => do
      let domain ← readExpression categoryOf domain none
      let some category := domain.category
        | throwError "source numeral evidence requires a selected domain object"
      unless category.role == .object do
        throwError "source numeral evidence requires a domain object"
      discard <| getLevel domain.value
      if let some expected := expected then
        checkRegisteredDomains domain.value expected
      let proofs ← evidence.getElems.mapM fun evidence => do
        let `(cas_term| proof($body:term)) := evidence
          | throwError "source numeral evidence requires the explicit proof wrapper"
        pure body
      pure ⟨← sourceNumeral categoryOf number.getNat domain.value proofs, none⟩
    | `(cas_term| $left:cas_term → $right:cas_term) => do
      let left ← sourceCarrier (← readExpression categoryOf left none)
      let right ← sourceCarrier (← readExpression categoryOf right none)
      let value ← mkAppM ``TypeCat.Hom #[left.value, right.value]
      sourceSetJudgement .object value
    | `(cas_term| view $receiver:cas_term along $functor:ident) =>
      readFunctorAction .object receiver functor #[]
    | `(cas_term| view $receiver:cas_term along $functor:ident($arguments:cas_term,*)) =>
      readFunctorAction .object receiver functor arguments.getElems
    | `(cas_term| map $receiver:cas_term along $functor:ident($arguments:cas_term,*)) =>
      readFunctorAction .morphism receiver functor arguments.getElems
    | `(cas_term| $left:cas_term ∘ $right:cas_term) => do
      let left ← readExpression categoryOf left none
      let right ← readExpression categoryOf right none
      let (left, right) ← sourceCommonCategory left right
      let some category := left.category <|> right.category
        | throwError "source composition requires its selected category"
      for selected in #[left.category, right.category] do
        if let some selected := selected then
          unless selected.role == .morphism do
            throwError "source composition requires morphisms"
          unless selected.expression.syntacticEq category.expression &&
              (← isDefEq selected.bundle category.bundle) do
            throwError "source composition has different complete selected categories"
      let carrier ← mkAppM ``CategoryTheory.Bundled.α #[category.bundle]
      let categoryInstance ← mkAppM ``CategoryTheory.Bundled.str #[category.bundle]
      let categoryStructure ← mkAppOptM ``CategoryTheory.Category.toCategoryStruct
        #[some carrier, some categoryInstance]
      let composition ← mkAppOptM ``CategoryTheory.CategoryStruct.comp
        #[some carrier, some categoryStructure]
      -- CategoryStruct.comp takes the earlier arrow first; source writes the later one first.
      let value ← elabAppArgs composition #[] #[Arg.expr right.value, Arg.expr left.value]
        expected false false
      pure ⟨value, some category⟩
    | `(cas_term| ($first:cas_term, $rest:cas_term,*)) => do
      let some expected := expected
        | throwError "a source tuple requires its independently declared domain"
      let value ← sourceTuple (#[first] ++ rest.getElems) expected fun component type => do
        return (← readExpression categoryOf component (some type)).value
      pure ⟨value, none⟩
    | `(cas_term| ($inner:cas_term)) =>
      readExpression categoryOf inner expected qualification
    | `(cas_term| $number:num) =>
      let some expected := expected
        | throwError "a source numeral requires its independently declared parameter type"
      pure ⟨← sourceNumeral categoryOf number.getNat expected, none⟩
    | `(cas_term| $name:ident) =>
      if let some declaration := (← getLCtx).findFromUserName? name.getId then
        pure ⟨mkFVar declaration.fvarId, ← categoryOf declaration.fvarId⟩
      else registered name #[]
    | `(cas_term| $name:ident($arguments:cas_term,*)) =>
      if ((← getLCtx).findFromUserName? name.getId).isSome then
        registered name arguments.getElems
      else if let .str receiver field := name.getId then do
        if !receiver.isAnonymous &&
            ((← getLCtx).findFromUserName? receiver).isSome then
          member (← `(cas_term| $(mkIdentFrom name receiver):ident)) field arguments.getElems
        else registered name arguments.getElems
      else registered name arguments.getElems
    | `(cas_term| $body:cas_term in $category:ident) => do
      if ((← getLCtx).findFromUserName? category.getId).isSome then
        annotated body (← `(cas_term| $category:ident))
      else
        readExpression categoryOf body expected (some (category.getId.toString (escape := false)))
    | `(cas_term| $body:cas_term in $domain:cas_term) =>
      annotated body domain
    | `(cas_term| ($function:cas_term)($arguments:cas_term,*)) => do
      let function ← readExpression categoryOf function none
      pure ⟨← application function arguments.getElems expected, none⟩
    | `(cas_term| $function:cas_term($arguments:cas_term,*)) => do
      let function ← readExpression categoryOf function none
      pure ⟨← application function arguments.getElems expected, none⟩
    | _ => do
      if source.raw.isOfKind ``CasCatalogue.Language.casMatrix then
        let some expected := expected
          | throwError "a source matrix requires its independently declared domain"
        let rows := source.raw[1].getSepArgs.map fun row =>
          row.getSepArgs.map fun cell => (⟨cell⟩ : TSyntax `cas_term)
        let value ← sourceMatrix rows expected fun component type => do
          return (← readExpression categoryOf component (some type)).value
        return ⟨value, none⟩
      CasCatalogue.throwUnsupportedSource
        m!"source translation is not implemented for expression {source}"
  if let some name := qualification then
    let required ← selectCategory (← CasCatalogue.semanticState) name
    let some selected := judgement.category
      | throwError "the retained source value has no selected category"
    unless selected.expression.syntacticEq required.expression do
      throwError "the retained source value has a different selected category"
  if let some expected := expected then
    -- A native type parameter consumes the actual selected object's carrier.
    -- Reuse the same checked source action as public function domains.
    let judgement ← if (← instantiateMVars expected).isSort &&
        judgement.category.any (·.role == .object) then
      sourceCarrier judgement
    else pure judgement
    checkRegisteredDomains (← inferType judgement.value) expected
    unless ← isDefEq (← inferType judgement.value) expected do
      throwError "the source expression does not have its independently declared parameter type"
    return judgement
  return judgement

end CasCompiler

