module

public import CasCompiler.SourceNumeral
public import CasCompiler.SourcePattern
public import CasCompiler.SourceCarrier
public import CasCompiler.SourceTuple
public import CasCompiler.SourceOperation
public import CasCompiler.SourceLimit
public import CasCompiler.SourceMember
public import CasCompiler.SourceMethod
public import CasCompiler.SourcePresentation
public import CasCompiler.SourceConstruction
public import CasCompiler.SourceLift
public import CasCompiler.SourceSubset
public import CasCompiler.SourceRing
public import CasCompiler.SourceAdmission
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

-- These forms determine their category and type from their own source inputs.
-- Other forms retain expected-type flow, including unqualified registered objects,
-- literals, tuples, lambdas and applications with implicit parameters.
private partial def sourcePrincipal (source : TSyntax `cas_term) : TermElabM Bool := do
  match source with
  | `(cas_term| ($inner:cas_term)) => sourcePrincipal inner
  | `(cas_term| $name:ident) =>
    return ((← getLCtx).findFromUserName? name.getId).isSome
  | `(cas_term| $_:cas_term in $_:cas_term)
  | `(cas_term| $_:cas_term → $_:cas_term)
  | `(cas_term| $_:cas_term × $_:cas_term)
  | `(cas_term| $_:cas_term ⊔ $_:cas_term)
  | `(cas_term| $_:cas_term ∘ $_:cas_term)
  | `(cas_term| |$_:cas_term|)
  | `(cas_term| view $_:cas_term along $_:ident)
  | `(cas_term| view $_:cas_term along $_:ident($_:cas_term,*))
  | `(cas_term| map $_:cas_term along $_:ident($_:cas_term,*)) => return true
  | `(cas_term| $name:ident($_:cas_term,*)) =>
    return name.getId == `id && ((← getLCtx).findFromUserName? name.getId).isNone
  | _ => return false

-- Native application determines argument types before the original source is read once.
-- A final application uses the actual expressions, preserving lexical binding occurrences
-- even when expected-type unification has already assigned a provisional argument.
-- Reuse: Lean.Elab.App.elabAppArgs and Lean.Meta.mkFreshExprMVar at Lean 4.33.0.
partial def readExpression
    (categoryOf : FVarId → TermElabM (Option NativeSourceCategory))
    (source : TSyntax `cas_term) (expected : Option Expr)
    (qualification : Option String := none)
    (expectedCategory : Option NativeSourceCategory := none) : TermElabM NativeSourceJudgement :=
  withRef source do
  let application := fun (source : NativeSourceJudgement) (arguments : Array (TSyntax `cas_term))
      (expected : Option Expr) => do
    -- An element with a registered application (a polynomial `p(a)`).
    if let #[argument] := arguments then
      if source.category.isNone then
        let type ← whnfR (← instantiateMVars (← inferType source.value))
        unless type.isForall || type.isAppOfArity ``Quiver.Hom 4 || type.isAppOf ``TypeCat.Hom do
          if let some value ← sourceObjectApplication? source.value (sourceNumeric argument.raw)
              fun expected => do return (← readExpression categoryOf argument expected).value then
            return value
    let function ← if arguments.isEmpty then pure source.value else sourceFunction source
    -- Several arguments of a map on a product are the components of one tuple (`gcd(84, 30)`).
    if arguments.size > 1 then
      let hole ← mkFreshExprMVar none
      let unary ← withoutModifyingState do
        discard <| elabAppArgs function #[] #[Arg.expr hole] none false false
        let type ← whnfR (← instantiateMVars (← inferType hole))
        let result ← whnfR (← inferType (mkApp function hole))
        return type.isAppOfArity ``Prod 2 && !result.isForall
      if unary then
        discard <| elabAppArgs function #[] #[Arg.expr hole] none false false
        let type ← instantiateMVars (← inferType hole)
        let tuple ← sourceTuple arguments type fun component type => do
          return (← readExpression categoryOf component (some type)).value
        return ← elabAppArgs function #[] #[Arg.expr tuple] expected false false
    let holes ← arguments.mapM fun _ => mkFreshExprMVar none
    discard <| elabAppArgs function #[] (holes.map Arg.expr) expected false false
    let mut actual := #[]
    for argument in arguments, hole in holes do
      let type ← instantiateMVars (← inferType hole)
      -- An object of another selected category is viewed along its structural route.
      let viewed : Option NativeSourceJudgement ← if sourceNumeric argument.raw then pure none else do
        let some category ← sourceObjectCategory? type | pure none
        let object ← readExpression categoryOf argument none
        let some selected := object.category | pure none
        if selected.role != .object || selected.expression.syntacticEq category.expression then
          pure none
        else
          -- Without a structural route the argument is read at the parameter's own category,
          -- where its name may select that category's row.
          let routes ← SourceRoutes.forOwner selected.expression category.expression
          let routed := (← routes.finiteRoutes).all (! ·.isEmpty)
          if routed then pure (some (← sourceStructuralView object category.expression))
          else pure none
      let value ← match viewed with
        | some value => pure value
        | none => readExpression categoryOf argument (some type)
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
    let inputContext := contextual.filter (! ·.headBeta.consumeMData.isSort)
    -- Actual typed operands determine the input domain before the expected result.
    -- Relations land in Ω; that result must not replace their selected operand owner.
    let domain ← match (domainHint.or hints[0]?).or inputContext with
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
    -- A registered action map `•` on exactly the pair of the operands' sets (a polynomial
    -- times a differential, `(6x + 1) dx`).
    if let some leftValue := leftValue then
      let pair ← mkAppM ``Prod #[← inferType leftValue.value, ← inferType rightValue.value]
      if let some action ← sourceMorphismFrom? "•" pair then
        let function ← sourceSetFunction action
        let argument ← mkAppM ``Prod.mk #[leftValue.value, rightValue.value]
        return ⟨← elabAppArgs function #[] #[Arg.expr argument] expected false false, none⟩
    let name ← sourceJuxtapositionName categoryOf leftValue rightValue
    let owner ← if name == "•" then pure (some (← inferType rightValue.value)) else pure none
    elementOperation name #[left, right] #[] #[leftValue.map (·.value), some rightValue.value]
      owner
  -- A value admitted into a registered subobject: read in the including set, then admitted
  -- with the domain's own evidence. A map read where its function is expected is that function.
  let admitted := fun (entry : CasCatalogue.ObjectEntry) (body : TSyntax `cas_term)
      (domain : Expr) => do
    sourceAdmission entry domain fun base => do
      if (← whnfR base).isForall then
        let value ← readExpression categoryOf body none
        let type ← whnfR (← inferType value.value)
        if type.isAppOfArity ``Quiver.Hom 4 || type.isAppOf ``TypeCat.Hom then
          return ← sourceSetFunction value.value
      return (← readExpression categoryOf body (some base)).value
  let annotated := fun (body domain : TSyntax `cas_term) => do
    let domain ← sourceCarrier (← readExpression categoryOf domain none)
    discard <| getLevel domain.value
    if let some entry ← sourceAdmissionDomain? domain.value then
      let identifier := body.raw.isIdent && ((← getLCtx).findFromUserName? body.raw.getId).isSome
      let typed ← if identifier then do
          let value ← readExpression categoryOf body none
          isDefEq (← inferType value.value) domain.value
        else pure false
      unless typed do
        let value ← admitted entry body domain.value
        return (⟨← mkExpectedTypeHint value domain.value, none⟩ : NativeSourceJudgement)
    -- A relation's annotation selects its operand structure, not its truth-value result.
    -- Reuse the same whole-family operation preparation as other element operations.
    match body with
    | `(cas_term| $left:cas_term ≤ $right:cas_term) =>
      return ← elementOperation "≤" #[left, right] #[] #[] (some domain.value)
    | `(cas_term| $left:cas_term < $right:cas_term) =>
      return ← elementOperation "<" #[left, right] #[] #[] (some domain.value)
    | _ => pure ()
    if let some expected := expected then checkRegisteredDomains domain.value expected
    readExpression categoryOf body (some domain.value)
  let relation := fun (name : String) (left right : TSyntax `cas_term) => do
    -- The public precedence grammar places a trailing domain on the right operand.
    -- Its actual selected structure types both operands through the registered map.
    match right with
    | `(cas_term| $operand:cas_term in $domain:cas_term) =>
      let domain ← sourceCarrier (← readExpression categoryOf domain none)
      elementOperation name #[left, operand] #[] #[] (some domain.value)
    | _ => elementOperation name #[left, right] #[] #[] none
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
      | do
        -- `x ↦ e` in `R[x]`: the element `e` with `x` the ring's registered generator.
        let `(cas_term| $name:ident) := pattern
          | CasCatalogue.throwUnsupportedSource
              "source lambda formation is not implemented for this declared map type"
        let some generator ← sourceGeneratorAt? expected none
          | CasCatalogue.throwUnsupportedSource
              "source lambda formation is not implemented for this declared map type"
        return ← withLetDecl name.getId expected generator fun bound => do
          let body ← readExpression categoryOf body (some expected)
          return (⟨← mkLetFVars #[bound] body.value, none⟩ : NativeSourceJudgement)
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
    let spelling := name.getId.toString (escape := false)
    let (spelling, arguments) ← do
      let state ← CasCatalogue.semanticState
      let some (base, number) := CasCatalogue.Language.subscripted? spelling
        | pure (spelling, arguments)
      if state.objects.any (·.name == spelling) || state.morphisms.any (·.name == spelling) ||
          !state.objects.any (·.name == base) then
        pure (spelling, arguments)
      else
        -- The documented leading parameter enters the same dependent application once.
        -- Exact lexical and registered spellings have already retained their own identity.
        let literal : TSyntax `num := ⟨Syntax.mkNumLit (toString number)⟩
        let leading ← `(cas_term| $literal:num)
        pure (base, #[leading] ++ arguments)
    let selected ← selectNamed spelling qualification expected
    match selected with
    | .construction entry => do
      let some receiver := arguments.back?
        | throwError "a source construction requires its actual receiver"
      let receiver ← readExpression categoryOf receiver none
      sourceConstruction entry receiver
        ((arguments.pop).map fun parameter type => do
          return (← readExpression categoryOf parameter (some type)).value)
    | .registered entry categoryEntry => do
      let declaration := match entry with
        | .inl entry => entry.declaration
        | .inr entry => entry.declaration
      let parameterCount ← withoutModifyingState do
        let info ← checkedDeclaration declaration
        let (_, binders, _) ← forallMetaTelescopeReducing info.type
        pure (binders.filter (·.isExplicit)).size
      -- `d(f)`: a named map applied to one element whose set fixes its declaration parameters,
      -- rather than one source argument per parameter (`rev(3, 2)`).
      if let (.inr row, #[argument]) := (entry, arguments) then
        if parameterCount > 0 && !sourceNumeric argument.raw then
          let element ← readExpression categoryOf argument none
          let type ← instantiateMVars (← inferType element.value)
          let parameterType ← withoutModifyingState do
            let info ← checkedDeclaration declaration
            let (parameters, binders, _) ← forallMetaTelescopeReducing info.type
            let some (first, _) := (parameters.zip binders).find? (·.2.isExplicit)
              | throwError "the named map lost its declaration parameter"
            instantiateMVars (← inferType first)
          unless ← withoutModifyingState (isDefEq type parameterType) do
            let some morphism ← sourceMorphismFrom? row.name type
              | throwError "the named map {row.name} does not leave the set of its argument"
            let function ← sourceSetFunction morphism
            return ⟨← elabAppArgs function #[] #[Arg.expr element.value] expected false false, none⟩
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
      -- A named global element `1 ⟶ X` (`i`, `π`) read where an element of a set is expected
      -- is its value at the terminal point.
      if role == .morphism && parameterCount == arguments.size then
        if let some expected := expected then
          let expected ← instantiateMVars expected
          let type ← whnfR (← inferType value)
          if !expected.isSort && type.isAppOfArity ``Quiver.Hom 4 &&
              !(← whnfR expected).isAppOfArity ``Quiver.Hom 4 then
            let source := type.getAppArgs[2]!
            if (← synthInstance? (← mkAppM ``Unique #[source])).isSome then
              return ⟨← sourcePointValue value (some expected), none⟩
      if parameterCount < arguments.size then
        return ⟨← application result (arguments.drop parameterCount) expected, none⟩
      return result
  let member := fun (receiver : TSyntax `cas_term) (name : String)
      (arguments : Array (TSyntax `cas_term)) => do
    let readArguments : Option (Expr → TermElabM Expr) := if arguments.isEmpty then none
      else some fun type => do
        if let #[argument] := arguments then
          return (← readExpression categoryOf argument (some type)).value
        sourceTuple arguments type fun source type => do
          return (← readExpression categoryOf source (some type)).value
    -- A numeral receiver is read at the declared source of the registered method.
    if sourceNumeric receiver.raw then
      let read := fun (type : Expr) => do
        return (← readExpression categoryOf receiver (some type)).value
      let some value ← sourceElementMember? name none read readArguments
        | throwError "no registered morphism {name} accepts this numeral"
      return (⟨value, none⟩ : NativeSourceJudgement)
    let receiver ← readExpression categoryOf receiver none
    if let some value ← sourceLiftMember? receiver name then
      unless arguments.isEmpty do
        throwError "a selected lift projection takes no additional source arguments"
      return value
    -- A method of objects on a subset is its extent's method (`Fs.cardinality()`).
    let object ← match ← sourceExtent? receiver with
      | some extent => pure extent
      | none => pure receiver
    let method ← sourceMethod object name
    let family ← sourceMemberFamily object name qualification
    let family ← match method, family with
      | some _, some _ =>
        CasCatalogue.throwSemanticAmbiguity
          "a method and a member family both accept this selected receiver"
      | some method, none => pure method
      | none, some family => pure family
      | none, none => do
        let some value ← sourceElementMember? name (some receiver) (fun _ => pure receiver.value)
            readArguments
          | throwError "no declared member family accepts this complete selected receiver"
        return (⟨value, none⟩ : NativeSourceJudgement)
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
    match entry with
    | .construction entry =>
      sourceConstruction entry receiver (arguments.map fun parameter type => do
          return (← readExpression categoryOf parameter (some type)).value)
    | .registered entry => do
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
      let carrier : Option NativeSourceCarrierSelection ←
          match receiver.category.bind (·.carrier) with
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
      -- Keep the selected reference beside its actual action for source inspection.
      return (⟨sourceReference kind id selected.declaration image,
        some ⟨role, selected.target, selected.targetBundle, carrier⟩⟩ : NativeSourceJudgement)
  -- `x ∈ A` for a subset `A`: the registered membership of A's power object.
  let membership := fun (element container : TSyntax `cas_term) => do
    let container ← readExpression categoryOf container none
    let some power ← sourcePowerObject? (← instantiateMVars (← inferType container.value))
      | do
        -- Membership in an object is the element's reading in that object, settled when the
        -- statement is read (`-3 ∈ ℤ`, `p ∈ ℤ[x]`).
        let domain ← sourceCarrier container
        discard <| getLevel domain.value
        return ← readExpression categoryOf element (some domain.value)
    let element ← readExpression categoryOf element (some power.base)
    return (⟨← sourceMembership power element.value container.value, none⟩ :
      NativeSourceJudgement)
  -- A bound variable ranges over the carrier of its declared domain object.
  let boundIn := fun (bound : Ident) (domain : TSyntax `cas_term)
      (body : Expr → Expr → TermElabM NativeSourceJudgement) => do
    let domain ← sourceCarrier (← readExpression categoryOf domain none)
    withLocalDeclD bound.getId domain.value fun parameter => body domain.value parameter
  let scaled := fun (factor : TSyntax `cas_term) (power : Syntax) => do
    let factor ← match power.find? (·.isAtom) |>.map (·.getAtomVal) with
      | some "²" => `(cas_term| $factor:cas_term ^ 2)
      | some "³" => `(cas_term| $factor:cas_term ^ 3)
      | _ => pure factor
    return factor
  -- The object whose registered notation is `notation`, at the source arguments.
  let notationObject := fun (form : String) (arguments : Array (TSyntax `cas_term)) => do
    let state ← CasCatalogue.semanticState
    let rows := state.objects.filter (·.notations.contains form)
    let #[entry] := rows
      | if rows.isEmpty then return none
        else CasCatalogue.throwSemanticAmbiguity s!"several objects declare the notation {form}"
    let #[categoryEntry] := state.categories.filter (·.id == entry.category)
      | throwError "the notation object requires one complete category"
    let (bundle, value) ← registeredExpressions (.inl entry) categoryEntry fun function expected =>
      application ⟨function, none⟩ arguments expected
    return some (⟨value, some ⟨.object, categoryEntry.expression, bundle,
      ← objectCarrierSelection entry bundle value⟩⟩ : NativeSourceJudgement)
  -- `Xⁿ` of an object is its `n`-tuples `Vec(X, n)`, and `(ℤ/n)^k` the object of the notation
  -- `(ℤ/)^`. An element base is an element power. Only a base that names an object is read here.
  let objectPower := fun (base power : TSyntax `cas_term) => do
    let `(cas_term| $_:num) := power | return none
    if let `(cas_term| ($inner:cas_term)) := base then
      if let `(cas_term| $atom:cas_term / $modulus:cas_term) := inner then
        if let some name := sourceAtomName? atom then
          if let some object ← notationObject s!"({name}/)^" #[modulus, power] then
            return some object
    let named := base.raw.isOfKind ``CasCatalogue.Language.casAtom || base.raw.isIdent ||
      (match base with
        | `(cas_term| $_:ident($_:cas_term,*)) => true
        | `(cas_term| ($_:cas_term)) => true
        | _ => false)
    unless named do return none
    let object ← readExpression categoryOf base none
    unless object.category.any (·.role == .object) do return none
    return some (← registered (mkIdentFrom source `Vec) #[base, power])
  -- A principal operand fixes its own type; the other operand is read at that type.
  let equationOperands := fun (left right : TSyntax `cas_term) => do
    let leftPrincipal ← sourcePrincipal left
    let rightPrincipal ← sourcePrincipal right
    let (left, right) ← if !leftPrincipal && rightPrincipal then do
      -- An annotated operand `x in D` gives the other operand D's carrier with its selected
      -- source object, not only the native type of x (`2 + 3 = 0 in ℤ/5`).
      let domain ← match right with
        | `(cas_term| $_:cas_term in $domain:cas_term) => do
          if domain.raw.isIdent then pure none
          else pure (some (← sourceCarrier (← readExpression categoryOf domain none)).value)
        | _ => pure none
      let right ← readExpression categoryOf right none
      let leftType ← match domain with
        | some domain => pure domain
        | none => inferType right.value
      let left ← readExpression categoryOf left (some leftType) none right.category
      pure (left, right)
    else do
      let left ← readExpression categoryOf left none
      let type ← inferType left.value
      let right ← readExpression categoryOf right
        (if rightPrincipal then none else some type) none
        (if rightPrincipal then none else left.category)
      pure (left, right)
    let (left, right) ← sourceCommonCategory left right
    checkRegisteredDomains (← inferType left.value) (← inferType right.value)
    return (left, right)
  -- The registered object whose name the language derives from the name `N` of the object
  -- `base = N(…)` reads (`N∖0`, `Spec N`), at the same explicit parameters.
  let relatedObject := fun (base : TSyntax `cas_term) (derived : String → String) => do
    let base ← readExpression categoryOf base none
    let state ← CasCatalogue.semanticState
    -- A definition names the object its value is.
    let base := { base with value := ← zetaReduce (← instantiateMVars base.value) }
    let head := base.value.consumeMData.getAppFn
    let some entry := state.objects.find? fun entry => head.isConstOf entry.declaration
      | throwError "the derived object is formed of a registered object"
    let rows := state.objects.filter (·.name == derived entry.name)
    let #[target] := rows
      | CasCatalogue.throwUnsupportedSource s!"no registered object {derived entry.name}"
    let #[category] := state.categories.filter (·.id == target.category)
      | throwError "the derived object requires one complete category"
    let arguments ← sourceExplicitArguments (← instantiateMVars base.value.consumeMData)
    let (bundle, value) ← registeredExpressions (.inl target) category fun function expected =>
      elabAppArgs function #[] (arguments.map Arg.expr) expected false false
    return (⟨value, some ⟨.object, category.expression, bundle,
      ← objectCarrierSelection target bundle value⟩⟩ : NativeSourceJudgement)
  -- A subset used as an object denotes its extent.
  let asObject := fun (judgement : NativeSourceJudgement) => do
    return (← sourceExtent? judgement).getD judgement
  let judgement ← if source.raw.getKind == ``CasCatalogue.Language.casCallWith then do
      let arguments := source.raw[4].getSepArgs.map fun argument =>
        (⟨argument⟩ : TSyntax `cas_term)
      member ⟨source.raw[0]⟩ (source.raw[2].getId.toString (escape := false)) arguments
    else if source.raw.isOfKind ``CasCatalogue.Language.casTimes then
      juxtapose ⟨source.raw[0]⟩ ⟨source.raw[2]⟩
    else if source.raw.isOfKind ``CasCatalogue.Language.casActed then
      juxtapose ⟨source.raw[0]⟩ (← `(cas_term| $(⟨source.raw[1]⟩):ident))
    else if source.raw.isOfKind ``CasCatalogue.Language.casScaled then do
      -- `2n`, `3x²`: the numeral times the variable (public language contract).
      let factor ← scaled (← `(cas_term| $(⟨source.raw[1]⟩):ident)) source.raw[2]
      readExpression categoryOf (← `(cas_term| $(⟨source.raw[0]⟩):num · $factor:cas_term))
        expected qualification expectedCategory
    else if source.raw.isOfKind ``CasCatalogue.Language.casScaledRoot then do
      -- `2√2`: the numeral times the square root.
      let factor ← `(cas_term| √$(⟨source.raw[2]⟩):cas_term)
      readExpression categoryOf (← `(cas_term| $(⟨source.raw[0]⟩):num · $factor:cas_term))
        expected qualification expectedCategory
    else if source.raw.isOfKind ``CasCatalogue.Language.casCoefficient then do
      -- `(a)x²`: the parenthesized coefficient times the variable.
      let factor ← scaled (← `(cas_term| $(⟨source.raw[3]⟩):ident)) source.raw[4]
      let coefficient : TSyntax `cas_term := ⟨source.raw[1]⟩
      readExpression categoryOf (← `(cas_term| ($coefficient:cas_term) · $factor:cas_term))
        expected qualification expectedCategory
    else if source.raw.isOfKind ``CasCatalogue.Language.casDefinite then do
      -- `∫_{a}^{b} e dt`: the registered binder `∫` at the bounds, binding `t`.
      let some bound := sourceDifferentialOf? source.raw[6].getId
        | throwError "a definite integral ends with the differential of its variable"
      let bounds : Array (TSyntax `cas_term) := #[⟨source.raw[1]⟩, ⟨source.raw[3]⟩]
      let value ← sourceBinder "∫" (bounds.map fun bound type => do
          return (← readExpression categoryOf bound (some type)).value)
        bound fun _ => do return (← readExpression categoryOf ⟨source.raw[5]⟩ none).value
      pure ⟨value, none⟩
    else if source.raw.isOfKind ``CasCatalogue.Language.casLimit then do
      -- `lim_{t → a} e`: the registered binder `lim` at the point `a`.
      let point : TSyntax `cas_term := ⟨source.raw[3]⟩
      let value ← sourceBinder "lim" #[fun type => do
          return (← readExpression categoryOf point (some type)).value]
        source.raw[1].getId fun _ => do
          return (← readExpression categoryOf ⟨source.raw[5]⟩ none).value
      pure ⟨value, none⟩
    else if source.raw.isOfKind ``CasCatalogue.Language.casBig then do
      -- `∑_{t ∈ A} e`, `∏_{t ∈ A} e`: the registered binder at the index set `A`.
      let token := (source.raw[0].find? (·.isAtom)).map (·.getAtomVal) |>.getD "∑"
      let index : TSyntax `cas_term := ⟨source.raw[4]⟩
      let value ← sourceBinder token #[fun type => do
          return (← readExpression categoryOf index (some type)).value]
        source.raw[2].getId fun _ => do
          return (← readExpression categoryOf ⟨source.raw[6]⟩ none).value
      pure ⟨value, none⟩
    else if source.raw.isOfKind ``CasCatalogue.Language.casInfinity then
      registered (mkIdentFrom source (.mkSimple "∞")) #[]
    else if source.raw.isOfKind ``CasCatalogue.Language.casIntegral then
      -- `∫ ω`: the registered primitives of the differential `ω`.
      registered (mkIdentFrom source (.mkSimple "∫")) #[⟨source.raw[1]⟩]
    else if source.raw.isOfKind ``CasCatalogue.Language.casProgression then do
      -- `{a₀, a₁, …, ...}`: the progression `{a₀ + d·k | k ∈ ℕ}` its numerals begin, with
      -- `d = a₁ - a₀` constant (public language contract).
      let numerals ← source.raw[1].getSepArgs.mapM fun numeral => do
        let `(cas_term| $value:num) := (⟨numeral⟩ : TSyntax `cas_term)
          | throwError "a progression `…, ...` is of numerals"
        pure value.getNat
      let (some first, some second) := (numerals[0]?, numerals[1]?)
        | throwError "a progression `…, ...` begins with two numerals"
      unless first ≤ second do throwError "a progression `…, ...` in ℕ increases"
      let difference := second - first
      unless (numerals.toList.zip numerals.toList.tail).all fun (x, y) => y = x + difference do
        CasCatalogue.throwStratum .invalid
          m!"{numerals.toList}, ... is not an arithmetic progression"
      let first : TSyntax `num := ⟨Syntax.mkNumLit (toString first)⟩
      let difference : TSyntax `num := ⟨Syntax.mkNumLit (toString difference)⟩
      readExpression categoryOf
        (← `(cas_term| {$first:num + $difference:num · index | index ∈ ℕ}))
        expected qualification expectedCategory
    else if source.raw.isOfKind ``CasCatalogue.Language.casMultiples then do
      -- `2ℕ`: the multiples `{2·n | n ∈ ℕ}` of the numeral in the named set.
      let factor : TSyntax `num := ⟨source.raw[0]⟩
      let set : TSyntax `cas_term := ⟨mkNode ``CasCatalogue.Language.casAtom #[source.raw[1]]⟩
      readExpression categoryOf (← `(cas_term| {$factor:num · index | index ∈ $set:cas_term}))
        expected qualification expectedCategory
    else if source.raw.isOfKind ``CasCatalogue.Language.casUnits then
      -- `Xˣ`: the registered units of `X`.
      registered (mkIdentFrom source `Units) #[⟨source.raw[0]⟩]
    else if source.raw.isOfKind ``CasCatalogue.Language.casFiniteSubsets then
      registered (mkIdentFrom source (.mkSimple "𝒫_fin")) #[⟨source.raw[2]⟩]
    else if source.raw.isOfKind ``CasCatalogue.Language.casNonzero then do
      -- `X ∖ 0` for `X = N(…)`: the registered object `N∖0` at the same parameters.
      unless source.raw[2].isNatLit? == some 0 do
        throwError "`X ∖ n` is written for n = 0 only, the nonzero elements"
      relatedObject ⟨source.raw[0]⟩ fun name => s!"{name}∖0"
    else if source.raw.isOfKind ``CasCatalogue.Language.casSpec then
      -- `Spec A` for `A = N(…)`: the registered object `Spec N` at the same parameters.
      relatedObject ⟨source.raw[1]⟩ fun name => s!"Spec {name}"
    else if source.raw.isOfKind ``CasCatalogue.Language.casRing then
      -- `R[x]`: the polynomials `Poly(R)`; the variable `x` names its generator.
      registered (mkIdentFrom source `Poly) #[⟨source.raw[0]⟩]
    else if source.raw.isOfKind ``CasCatalogue.Language.casMvRing then do
      -- `R[x, y]`, `R[x_0, …, x_9]`: `MvPoly(n, R)` in its `n` listed variables.
      let names ← match sourceRingVariableNames source.raw with
        | .ok names => pure names
        | .error message => throwError message
      let count : TSyntax `cas_term ← `(cas_term| $(⟨Syntax.mkNumLit (toString names.size)⟩):num)
      registered (mkIdentFrom source `MvPoly) #[count, ⟨source.raw[0]⟩]
    else if source.raw.isOfKind ``CasCatalogue.Language.casSeries then
      -- `R[[t]]`: the formal power series `PowerSeries(R)`.
      registered (mkIdentFrom source `PowerSeries) #[⟨source.raw[0]⟩]
    else if let some name := sourceAtomName? source then object name qualification #[]
    else match source with
    | `(cas_term| presentation($name:ident($arguments:cas_term,*))) =>
      sourcePresentation name.getId.toString false fun declaration =>
        application ⟨declaration, none⟩ arguments.getElems none
    | `(cas_term| inverse_presentation($name:ident($arguments:cas_term,*))) =>
      sourcePresentation name.getId.toString true fun declaration =>
        application ⟨declaration, none⟩ arguments.getElems none
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
      let left ← asObject (← readExpression categoryOf left none qualification)
      let right ← asObject (← readExpression categoryOf right none qualification)
      sourceBinaryLimit left right false
    | `(cas_term| $left:cas_term ⊔ $right:cas_term) => do
      let left ← asObject (← readExpression categoryOf left none qualification)
      let right ← asObject (← readExpression categoryOf right none qualification)
      sourceBinaryLimit left right true
    | `(cas_term| $left:cas_term + $right:cas_term) =>
      elementOperation "+" #[left, right] #[] #[] none
    | `(cas_term| $left:cas_term - $right:cas_term) => do
      -- `x - y` is `x + -y` in the selected structure (public language contract).
      -- The expansion is read once through the same registered addition and negation.
      return ← readExpression categoryOf (← `(cas_term| $left:cas_term + (-$right:cas_term)))
        expected qualification expectedCategory
    | `(cas_term| $left:cas_term ∪ $right:cas_term) =>
      elementOperation "∪" #[left, right] #[] #[] none
    | `(cas_term| $left:cas_term ∩ $right:cas_term) =>
      elementOperation "∩" #[left, right] #[] #[] none
    | `(cas_term| $left:cas_term \ $right:cas_term) =>
      elementOperation "\\" #[left, right] #[] #[] none
    | `(cas_term| $left:cas_term △ $right:cas_term) =>
      elementOperation "△" #[left, right] #[] #[] none
    | `(cas_term| $left:cas_term ⊆ $right:cas_term) => relation "⊆" left right
    | `(cas_term| $element:cas_term ∈ $container:cas_term) => membership element container
    | `(cas_term| $element:cas_term ∉ $container:cas_term) => do
      return ⟨mkNot (← membership element container).value, none⟩
    | `(cas_term| $base:cas_term²) => do
      if let some object ← objectPower base (← `(cas_term| 2)) then return object
      readExpression categoryOf (← `(cas_term| $base:cas_term ^ 2)) expected qualification
        expectedCategory
    | `(cas_term| $base:cas_term³) => do
      if let some object ← objectPower base (← `(cas_term| 3)) then return object
      readExpression categoryOf (← `(cas_term| $base:cas_term ^ 3)) expected qualification
        expectedCategory
    | `(cas_term| √$operand:cas_term) =>
      -- `√x` is `sqrt(x)` (public language contract).
      registered (mkIdentFrom source `sqrt) #[operand]
    | `(cas_term| 𝒫($operand:cas_term)) =>
      registered (mkIdentFrom source (.mkSimple "𝒫")) #[operand]
    | `(cas_term| {$elements:cas_term,*}) => do
      let some expected := expected
        | throwError "a source set literal requires its declared power object"
      -- A literal in an admitted subobject of a power object (`𝒫_fin(X)`) is admitted there.
      if let some entry ← sourceAdmissionDomain? (← instantiateMVars expected) then
        return ⟨← admitted entry source expected, none⟩
      let some power ← sourcePowerObject? (← instantiateMVars expected)
        | throwError "a source set literal requires a subset of a registered power object"
      -- Elements are read in the registered form of the base set (`Poly(ℤ)` for `Polynomial ℤ`).
      let base ← sourceRegisteredForm power.base
      let elements ← elements.getElems.mapM fun element => do
        return (← readExpression categoryOf element (some base)).value
      return ⟨← sourceSubsetLiteral power elements expected, none⟩
    | `(cas_term| {$bound:ident ∈ $domain:cas_term | $body:cas_term}) => do
      -- Over a subset `A ⊆ X`: `{t ∈ X | t ∈ A and P}`, through `A`'s power object.
      let subset ← readExpression categoryOf domain none
      if let some power ← sourcePowerObject? (← instantiateMVars (← inferType subset.value)) then
        return ← withLocalDeclD bound.getId power.base fun parameter => do
          let predicate ← readExpression categoryOf body (some (mkSort .zero))
          let member ← sourceMembership power parameter subset.value
          let predicate ← mkLambdaFVars #[parameter] (mkAnd member predicate.value)
          return (⟨← sourceComprehension power predicate expected, none⟩ : NativeSourceJudgement)
      boundIn bound domain fun base parameter => do
        let predicate ← readExpression categoryOf body (some (mkSort .zero))
        let predicate ← mkLambdaFVars #[parameter] predicate.value
        let power ← sourcePowerObjectAt base
        return (⟨← sourceComprehension power predicate expected, none⟩ : NativeSourceJudgement)
    | `(cas_term| {$body:cas_term | $bound:ident ∈ $domain:cas_term}) =>
      boundIn bound domain fun base parameter => do
        let value ← readExpression categoryOf body none
        let target ← instantiateMVars (← inferType value.value)
        if target.containsFVar parameter.fvarId! then
          throwError "the source image has a codomain that depends on its bound variable"
        let function ← mkLambdaFVars #[parameter] value.value
        let power ← sourcePowerObjectAt target
        return (⟨← sourceImage power base function expected, none⟩ : NativeSourceJudgement)
    | `(cas_term| {$pairs:cas_pair,*} : $source:cas_term → $target:cas_term) => do
      -- The map with this graph, through the registered graph literal of the endpoints'
      -- category. Totality and distinct arguments are decided by the kernel on the literal.
      let domain ← readExpression categoryOf source none
      let codomain ← readExpression categoryOf target none
      let (domain, codomain) ← sourceCommonCategory domain codomain
      let some category := domain.category
        | throwError "a graph literal requires its selected category"
      unless category.role == .object && codomain.category.any (·.role == .object) do
        throwError "a graph literal maps between objects"
      let state ← CasCatalogue.semanticState
      let rows := state.graphLiterals.filter fun row => state.categories.any fun entry =>
        entry.id == row.category && entry.expression.syntacticEq category.expression
      let #[row] := rows
        | CasCatalogue.throwUnsupportedSource "the selected category has no registered graph literal"
      let sourceCarrierType := (← sourceCarrier domain).value
      let targetCarrierType := (← sourceCarrier codomain).value
      let pairType ← mkAppM ``Prod #[sourceCarrierType, targetCarrierType]
      let mut elements := #[]
      for pair in pairs.getElems do
        let `(cas_pair| $argument:cas_term ↦ $result:cas_term) := pair
          | throwError "a graph literal lists pairs `x ↦ y`"
        let argument ← readExpression categoryOf argument (some sourceCarrierType)
        let result ← readExpression categoryOf result (some targetCarrierType)
        elements := elements.push (← mkAppOptM ``Prod.mk
          #[some sourceCarrierType, some targetCarrierType, some argument.value, some result.value])
      let graph ← mkListLit pairType elements.toList
      discard <| checkedDeclaration row.denotation
      let constant ← mkConstWithFreshMVarLevels row.denotation
      let (arguments, infos, type) ← forallMetaTelescopeReducing (← inferType constant)
      let type ← whnfR type
      unless type.isAppOfArity ``Quiver.Hom 4 do
        throwError "the registered graph literal does not denote a map"
      unless ← isDefEq type.getAppArgs[2]! domain.value <&&>
          isDefEq type.getAppArgs[3]! codomain.value do
        throwError "the registered graph literal has different endpoints"
      let explicit := (List.range arguments.size).toArray.filter (infos[·]!.isExplicit)
      let some first := explicit[0]? | throwError "the graph literal takes no graph"
      unless ← isDefEq arguments[first]! graph do
        throwError "the graph literal does not accept this list of pairs"
      for argument in arguments, info in infos do
        if info.isInstImplicit && (← instantiateMVars argument).isMVar then
          let some instanceValue ← synthInstance? (← inferType argument)
            | throwError "the graph literal lacks its declared decidable equality"
          discard <| isDefEq argument instanceValue
      for index in explicit.drop 1 do
        let obligation ← instantiateMVars (← inferType arguments[index]!)
        let some proof ← CasCatalogue.Decide.decisionProof obligation
          | CasCatalogue.throwStratum .invalid m!"the graph does not list each element once: {obligation}"
        discard <| isDefEq arguments[index]! proof
      let value ← instantiateMVars (mkAppN constant arguments)
      return ⟨sourceReference ``CasCatalogue.GraphLiteralEntry row.id.raw row.denotation value,
        some { category with role := .morphism, carrier := none }⟩
    | `(cas_term| $left:cas_term = $right:cas_term) => do
      -- Within a term, `=` is the equality predicate of the operands' common domain.
      let (left, right) ← equationOperands left right
      return ⟨← mkEq left.value right.value, none⟩
    | `(cas_term| $left:cas_term ≤ $right:cas_term) => relation "≤" left right
    | `(cas_term| $left:cas_term < $right:cas_term) => relation "<" left right
    | `(cas_term| $receiver.$method:ident()) =>
      member receiver method.getId.toString #[]
    | `(cas_term| |$receiver:cas_term|) => do
      let receiver ← asObject (← readExpression categoryOf receiver none)
      unless receiver.category.any (·.role == .object) do
        CasCatalogue.throwUnsupportedSource
          "source absolute-value formation requires its declared operation family"
      let some value ← sourceMethod receiver "cardinality"
        | throwError "the selected source object has no declared cardinality method"
      pure value
    | `(cas_term| $left:cas_term · $right:cas_term) =>
      elementOperation "·" #[left, right] #[] #[] none
    | `(cas_term| $left:cas_term • $right:cas_term) => action left right
    | `(cas_term| -$operand:cas_term) =>
      elementOperation "-" #[operand] #[] #[] none
    | `(cas_term| 2 ^ $power:cas_term) => do
      -- `2^X` of an object is its power set; of an element, the element power.
      if power.raw.isOfKind ``CasCatalogue.Language.casAtom || power.raw.isIdent then
        let object ← readExpression categoryOf power none
        if object.category.any (·.role == .object) then
          return ← registered (mkIdentFrom source (.mkSimple "𝒫")) #[power]
      elementOperation "^" #[← `(cas_term| 2)] #[power] #[] none
    | `(cas_term| $base:cas_term ^ $power:cas_term) => do
      if let some object ← objectPower base power then return object
      elementOperation "^" #[base] #[power] #[] none
    | `(cas_term| $left:cas_term / $right:cas_term) => do
      -- `d/dx`: the registered derivative of the ring whose variable `x` is.
      let identifier := fun (term : TSyntax `cas_term) => match term with
        | `(cas_term| $name:ident) => some name.getId
        | _ => none
      if identifier left == some `d then
        if let some generator := (identifier right).bind sourceDifferentialOf? then
          if let some declaration := (← getLCtx).findFromUserName? generator then
            let some morphism ← sourceMorphismFrom? "derivative" declaration.type
              | throwError "the ring of {generator} has no registered derivative"
            return ⟨morphism, none⟩
      -- `ℤ/n`: the object whose registered notation is the atom followed by `/`.
      let some atom := sourceAtomName? left
        | CasCatalogue.throwUnsupportedSource "source division is not implemented"
      let some object ← notationObject s!"{atom}/" #[right]
        | CasCatalogue.throwUnsupportedSource "source division is not implemented"
      return object
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
      readExpression categoryOf inner expected qualification expectedCategory
    | `(cas_term| ℵ₀) => do
      let some expected := expected
        | throwError "a named object literal requires its selected category"
      let some category := expectedCategory
        | throwError "a named object literal requires its selected category"
      let some value ← sourceObjectNamedLiteral `«ℵ₀» category expected
        | throwError "the selected category has no registered named literal form"
      return value
    | `(cas_term| $number:num) => do
      let some expected := expected
        | throwError "a source numeral requires its independently declared parameter type"
      if let some entry ← sourceAdmissionDomain? (← instantiateMVars expected) then
        return ⟨← admitted entry source expected, none⟩
      if let some category := expectedCategory then
        if let some value ← sourceObjectNumeral number.getNat category expected then return value
      pure ⟨← sourceNumeral categoryOf number.getNat expected, none⟩
    | `(cas_term| $name:ident) =>
      if let some declaration := (← getLCtx).findFromUserName? name.getId then
        pure ⟨mkFVar declaration.fvarId, ← categoryOf declaration.fvarId⟩
      else if let some generator ← (sourceDifferentialOf? name.getId).filterM fun generator =>
          return ((← getLCtx).findFromUserName? generator).isSome then
        -- `dv` for a bound variable `v` is its differential `d(v)` (public language contract).
        readExpression categoryOf
          (← `(cas_term| $(mkIdentFrom name `d):ident($(mkIdentFrom name generator):ident)))
          expected qualification
          expectedCategory
      else if name.getId == `false then pure ⟨mkConst ``False, none⟩
      else if name.getId == `true then pure ⟨mkConst ``True, none⟩
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
    | `(cas_term| $body:cas_term in $category:ident / $base:cas_term) => do
      -- `X in C/Y`: X read in the registered category family C at its base parameter Y.
      let state ← CasCatalogue.semanticState
      let name := category.getId.toString (escape := false)
      -- The family registered as `C/` (`Schemes/`, beside `Schemes`), else `C` itself.
      let some entry := (state.categories.find? (·.name == name ++ "/")).orElse fun _ =>
          state.categories.find? (·.name == name)
        | annotated body (← `(cas_term| $category:ident / $base:cas_term))
      let name := entry.name
      discard <| checkedDeclaration entry.declaration
      let family ← mkConstWithFreshMVarLevels entry.declaration
      let (parameters, _, _) ← forallMetaTelescopeReducing (← inferType family)
      let some parameter := parameters.back?
        | throwError "the category {name} has no base parameter"
      let base ← readExpression categoryOf base (some (← instantiateMVars (← inferType parameter)))
      unless ← isDefEq parameter base.value do
        throwError "the base is not an object of the base category of {name}"
      -- An object already selected elsewhere is in C through C's registered refinement of its
      -- object family, at the same parameters (`ℂ[x₀, …]` as a ℂ-algebra).
      let object ← readExpression categoryOf body none
      let judgement ← if object.category.any (·.expression.syntacticEq entry.expression) then
          pure object
        else do
          let value ← zetaReduce (← instantiateMVars object.value)
          let some original := state.objects.find? fun row =>
              value.consumeMData.getAppFn.isConstOf row.declaration
            | throwError "the value does not name a registered object"
          let rows := state.objects.filter fun row =>
            row.category == entry.id && (row.refines.any (·.base == original.id) ||
              original.refines.any (·.base == row.id))
          let #[refinement] := rows
            | CasCatalogue.throwStratum .invalid m!"{original.name} has no registered object in {name}"
          let arguments ← sourceExplicitArguments value.consumeMData
          let (bundle, refined) ← registeredExpressions (.inl refinement) entry
            fun function expected =>
              elabAppArgs function #[] (arguments.map Arg.expr) expected false false
          pure (⟨refined, some ⟨.object, entry.expression, bundle, none⟩⟩ : NativeSourceJudgement)
      let some selected := judgement.category
        | throwError "the source value has no selected category"
      unless ← isDefEq (mkAppN family parameters) selected.bundle do
        CasCatalogue.throwStratum .invalid m!"the value is not an object of {name} over this base"
      return judgement
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
          | CasCatalogue.throwUnsupportedSource "source matrix default-domain interpretation is not implemented"
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
    let judgement ← if (← instantiateMVars expected).isSort then
      if judgement.category.any (·.role == .object) then sourceCarrier judgement
      else match ← sourceExtent? judgement with
        | some extent => sourceCarrier extent
        | none => pure judgement
    else pure judgement
    checkRegisteredDomains (← inferType judgement.value) expected
    unless ← isDefEq (← inferType judgement.value) expected do
      throwError "the source expression does not have its independently declared parameter type"
    return judgement
  return judgement

/-- Read a whole source term. Each variable of a ring `R[v]` that the term writes and uses free is
bound to that ring's registered generator for this term only.
Source: the public language contract, "`R[x]`: the polynomials over `R`, whose generator `x`
names". A variable named by two different written rings is ambiguous. -/
partial def withRingVariables
    (categoryOf : FVarId → TermElabM (Option NativeSourceCategory))
    (recorded : Array (Name × Expr × Option Nat))
    (source : TSyntax `cas_term) (read : TermElabM NativeSourceJudgement) :
    TermElabM NativeSourceJudgement := do
  let mut written : Array (Name × Syntax × Option Nat) := #[]
  for (name, ring, index) in sourceRingVariables source.raw do
    unless sourceUses name source.raw && !sourceBinds name source.raw do continue
    if let some (_, other, _) := written.find? (·.1 == name) then
      unless other.reprint == ring.reprint do
        CasCatalogue.throwSemanticAmbiguity m!"{name} is the variable of several rings"
      continue
    written := written.push (name, ring, index)
  -- The rings of the definitions the term uses supply the variables it does not write.
  let mut inherited : Array (Name × Expr × Option Nat) := #[]
  for (name, carrier, index) in recorded do
    unless sourceUses name source.raw && !sourceBinds name source.raw do continue
    if written.any (·.1 == name) then continue
    if let some (_, other, _) := inherited.find? (·.1 == name) then
      unless other == carrier do
        CasCatalogue.throwSemanticAmbiguity m!"{name} is the variable of several rings"
      continue
    inherited := inherited.push (name, carrier, index)
  let mut bindings : Array (Name × Sum Syntax Expr × Option Nat) := #[]
  for (name, ring, index) in written do bindings := bindings.push (name, .inl ring, index)
  for (name, carrier, index) in inherited do bindings := bindings.push (name, .inr carrier, index)
  bind bindings.toList
where
  bind : List (Name × Sum Syntax Expr × Option Nat) → TermElabM NativeSourceJudgement
    | [] => read
    | (name, ring, index) :: rest => do
      if ((← getLCtx).findFromUserName? name).isSome then return ← bind rest
      let carrier ← match ring with
        | .inl ring => pure (← sourceCarrier (← readExpression categoryOf ⟨ring⟩ none)).value
        | .inr carrier => pure carrier
      let some generator ← sourceGeneratorAt? carrier index
        | throwError "the ring of {name} has no registered generator"
      withLetDecl name carrier generator fun bound => do
        let judgement ← bind rest
        return { judgement with value := ← mkLetFVars #[bound] judgement.value }

/-- Read a whole source term with its written rings' variables (`withRingVariables`). -/
def readSourceTerm (categoryOf : FVarId → TermElabM (Option NativeSourceCategory))
    (recorded : Array (Name × Expr × Option Nat))
    (source : TSyntax `cas_term) (expected : Option Expr) : TermElabM NativeSourceJudgement :=
  withRingVariables categoryOf recorded source (readExpression categoryOf source expected)

/-- `a = b` in a question: native equality of the operands at their common domain, as in
SourceEquality and the public claimEqual contract. Formation supplies no proof. -/
def sourceEquation (categoryOf : FVarId → TermElabM (Option NativeSourceCategory))
    (left right : TSyntax `cas_term) : TermElabM Expr := do
  let equation ← `(cas_term| $left:cas_term = $right:cas_term)
  return (← readExpression categoryOf equation (some (mkSort .zero))).value

end CasCompiler

