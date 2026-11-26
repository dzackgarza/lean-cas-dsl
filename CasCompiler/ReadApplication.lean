module

public import CasCompiler.ReadContext
public import CasCompiler.ReadDispatch
public import CasCompiler.SourceRing
public import CasCompiler.SourceTuple
public import CasCompiler.SourceSubset
public import CasCompiler.SourceObjectAlias
public import CasCompiler.SourceOperation
import CasCompiler.SourceCarrier

public section

namespace CasCompiler

open Lean Meta Elab Term

namespace SourceReader

def mapEnds :
    Expr → SourceReadM (Option (Expr × Expr)) :=
  fun (arrow : Expr) => do
    let inferred ← liftM (m := MetaM) <| instantiateMVars (← inferType arrow)
    let type ← if inferred.isAppOfArity ``Quiver.Hom 4 then pure inferred else whnfR inferred
    if type.isAppOfArity ``Quiver.Hom 4 then
      let endpoint := fun value => do
        if let some selected ← SourceReadM.selection? value then
          if let some endpoint := selected.endpoint then return endpoint.value
        declaredEndpoint value
      return some (← endpoint type.getAppArgs[2]!, ← endpoint type.getAppArgs[3]!)
    if type.isAppOfArity ``TypeCat.Hom 2 then return some (type.getAppArgs[0]!, type.getAppArgs[1]!)
    return none

-- Only an unresolved bare object spelling can acquire a registered refinement for a
-- declaration parameter. A retained binding or an explicit qualification already selected
-- its complete source object and must use that object's own outgoing routes.
private partial def bareObjectName? (source : TSyntax `cas_term) :
    SourceReadM (Option String) := do
  if let some name := sourceAtomName? source then return some name
  match source with
  | `(cas_term| ($inner:cas_term)) => bareObjectName? inner
  | `(cas_term| $name:ident) =>
    if ((← liftM (m := MetaM) getLCtx).findFromUserName? name.getId).isSome then return none
    return some (name.getId.toString (escape := false))
  | _ => return none

private def applicationApplicableCore (context : ReadContext)
    (preRead : Option NativeSourceJudgement := none) :
    NativeSourceJudgement → Array (TSyntax `cas_term) → Option Expr →
      SourceReadM (Except MessageData Expr) :=
  let readExpression := @ReadContext.readExpression context
  let readArgument := @ReadContext.readExpressionApplicable context
  let categoryOf := context.categoryOf
  fun (source : NativeSourceJudgement) (arguments : Array (TSyntax `cas_term))
      (expected : Option Expr) => do
    let readOriginal := fun index argument => do
      if index == 0 then
        if let some original := preRead then return original
      readExpression categoryOf argument none
    let readAt := fun index argument type => do
      if index == 0 then
        if let some original := preRead then
          return ← checkReadJudgementApplicable
            { context with
              source := argument
              expected := type
              qualification := none
              expectedCategory := none } original
      readArgument categoryOf argument type
    let source ← if source.category.any (·.role == .morphism) then do
      let selected := (← SourceReadM.selection? source.value).getD { value := source.value }
      let value ← SourceReadM.select { selected with value := source.value, category := source.category }
      pure { source with value }
    else pure source
    -- A map applied to its whole domain is the map's image (`m2(ℕ)`), through the registered
    -- image of the power object of its target (PowerObjectEntry.image).
    if let #[argument] := arguments then
      if argument.raw.isOfKind ``CasCatalogue.Language.casAtom then
        if let some (domain, codomain) ← mapEnds source.value then
          let object ← readOriginal 0 argument
          if object.category.any (·.role == .object) then
            if ← isDefEq object.value domain then
              let target ← sourcePowerObjectAt codomain
              return .ok (← sourceImageOf target domain source.value expected)
    -- An element with a registered application (a polynomial `p(a)`).
    if let #[argument] := arguments then
      if source.category.isNone then
        let type ← whnfR (← liftM (m := MetaM) <| instantiateMVars (← inferType source.value))
        unless type.isForall || type.isAppOfArity ``Quiver.Hom 4 || type.isAppOf ``TypeCat.Hom do
          if let some value ← sourceObjectApplication? source.value (sourceNumeric argument.raw)
              (fun expected => do
                match ← readAt 0 argument expected with
                | .ok value => return value.value
                | .error message => liftM (m := TermElabM) <| throwError message) then
            return .ok value
    let function ← if arguments.isEmpty then pure source.value else sourceFunction source
    -- Several arguments of a map on a product are the components of one tuple (`gcd(84, 30)`).
    if arguments.size > 1 then
      let hole ← mkFreshExprMVar none
      let unary ← withoutModifyingState do
        discard <| elabAppArgs function #[] #[Arg.expr hole] none false false
        let type ← whnfR (← declaredEndpoint (← inferType hole))
        let result ← whnfR (← declaredEndpoint (← inferType (mkApp function hole)))
        return type.isAppOfArity ``Prod 2 && !result.isForall
      if unary then
        discard <| elabAppArgs function #[] #[Arg.expr hole] none false false
        let type ← declaredEndpoint (← inferType hole)
        let tuple ← sourceTuple arguments type fun component type => do
          return (← readExpression categoryOf component (some type)).value
        return .ok (← elabAppArgs function #[] #[Arg.expr tuple] expected false false)
    -- A named spelling for the actual declared source of a Sets arrow is checked at the
    -- entire native family before its parameters are applied. This can guide its point's
    -- existing literal reader without choosing another runtime object by carrier equality.
    let namedDomain ← if arguments.size == 1 && source.category.any (fun category =>
        category.role == .morphism &&
          category.expression.syntacticEq (.atom CasCatalogue.CategoryId.sets)) then do
        let type ← whnfR (← inferType source.value)
        if type.isAppOfArity ``Quiver.Hom 4 then
          let endpoint ← declaredEndpoint type.getAppArgs[2]!
          let selected := (← SourceReadM.selection? endpoint).getD { value := endpoint }
          let named ← sourceNamedObjectAlias CasCatalogue.CategoryId.sets selected
          pure (some (← SourceReadM.select named))
        else pure none
      else pure none
    let applied ← elabSourceApplicationApplicableScoped function (arguments.map (·.raw)) expected
      (sourceInstance := some SourceReadM.tryInstance) fun index type => do
      let some argument := arguments[index]?
        | liftM (m := TermElabM) <| throwError "the source application lost an original argument"
      let formalType := type
      let type ← match namedDomain with
        | some domain =>
          let scope ← get
          let agrees ← scope.context.withOriginalSources #[type, domain] fun original =>
            isDefEq original[0]! original[1]!
          unless agrees do
            liftM (m := TermElabM) <| throwError "the Sets point application changed its actual declared source"
          pure domain
        | none => pure type
      -- Domain atoms contain no identifier token, so the numeral-only syntax predicate
      -- alone does not distinguish them from literals. Keep their registered spelling.
      let bareName ← bareObjectName? argument
      -- An object of another selected category is viewed along its structural route.
      let viewed : Option NativeSourceJudgement ← if sourceNumeric argument.raw && bareName.isNone then pure none else do
        let some category ← sourceObjectCategory? type | pure none
        let object ← readOriginal index argument
        let some selected := object.category | pure none
        if selected.role != .object || selected.expression.syntacticEq category.expression then
          pure none
        else
          -- Without a structural route the argument is read at the parameter's own category,
          -- where its name may select that category's row.
          let routes ← SourceRoutes.forOwner selected.expression category.expression
          let routed := (← routes.finiteRoutes).all (! ·.isEmpty)
          -- The surface name of the applied family, for a declared preferred route.
          let state ← CasCatalogue.semanticState
          let head := function.consumeMData.getAppFn.constName?
          let name := head.bind fun head =>
            (state.objects.find? (·.declaration == head)).map (·.name) <|>
            (state.morphisms.find? (·.declaration == head)).map (·.name)
          if routed then pure (some (← sourceStructuralView object category.expression name))
          else if !selected.expression.syntacticEq (.atom CasCatalogue.CategoryId.sets) then
            pure none
          else match bareName with
            | none => pure none
            | some spelling =>
              -- A row already declared in the parameter category keeps ordinary expected-type
              -- selection. Otherwise its exact named base may supply a declared carrier prefix.
              if state.objects.any (fun entry =>
                  entry.name == spelling && entry.category == category.id) then pure none
              else sourceNamedConstantParameter? object.value category.expression
      let value ← match viewed with
        | some value => pure (.ok value)
        | none => readAt index argument (some type)
      let value ← match value with
        | .ok value => pure value
        | .error message => return .error message
      let value ← match ← checkReadJudgementApplicable
          { context with
            source := argument
            expected := some formalType
            qualification := none
            expectedCategory := none } value with
        | .ok value => pure value
        | .error message => return .error message
      let parameter ← match value.category with
        | some category =>
          if category.role == .object then annotateSourceObject category value.value
          else pure value.value
        | none => pure value.value
      return .ok parameter
    let (result, actual) ← match applied with
      | .ok value => pure value
      | .error message => return .error message
    if let #[argument] := actual then
      if source.category.any (·.role == .morphism) then
        if let some original := (← SourceReadM.selection? argument).bind (·.pointOrigin) then
          -- Retain the ordinary native composition of the already selected point and
          -- carrier map. A later application keeps this point's same original domain.
          let mapped ← sourceCarrier source
          let some category := mapped.category
            | liftM (m := TermElabM) <| throwError "the point action lost its selected carrier category"
          let carrier ← mkAppM ``CategoryTheory.Bundled.α #[category.bundle]
          let categoryInstance ← mkAppM ``CategoryTheory.Bundled.str #[category.bundle]
          let categoryStructure ← mkAppOptM ``CategoryTheory.Category.toCategoryStruct
            #[some carrier, some categoryInstance]
          let composition ← mkAppOptM ``CategoryTheory.CategoryStruct.comp
            #[some carrier, some categoryStructure]
          let point ← elabAppArgs composition #[] #[Arg.expr original.point, Arg.expr mapped.value]
            none false false
          return .ok (← SourceReadM.select (← retainSourcePoint point { value := result }))
    return .ok result

/-- Ordinary application keeps its original positional operand reader. -/
def applicationApplicable (context : ReadContext) (source : NativeSourceJudgement)
    (arguments : Array (TSyntax `cas_term)) (expected : Option Expr) :
    SourceReadM (Except MessageData Expr) :=
  applicationApplicableCore context none source arguments expected

def application (context : ReadContext)
    (source : NativeSourceJudgement) (arguments : Array (TSyntax `cas_term))
    (expected : Option Expr) : SourceReadM Expr := do
  match ← applicationApplicable context source arguments expected with
  | .ok value => pure value
  | .error message => liftM (m := TermElabM) <| throwError message

-- A call of an already selected native map has its domain from that receiver. This
-- extends principal reading through nested actual calls without selecting an overloaded
-- declaration from an expected endpoint or turning an interpretation failure into a rule.
private partial def principalApplication (context : ReadContext)
    (source : TSyntax `cas_term) : SourceReadM Bool := do
  if ← sourcePrincipal source then return true
  match source with
  | `(cas_term| ($inner:cas_term)) => principalApplication context inner
  | `(cas_term| $_:cas_term in $_:cas_term using ($_:cas_term,*)) => return true
  | `(cas_term| $name:ident($arguments:cas_term,*)) =>
    if arguments.getElems.isEmpty then return false
    let function ← liftM (m := TermElabM) `(cas_term| $name:ident)
    unless ← principalApplication context function do return false
    SourceReadM.inspect do
      let receiver ← context.readExpression context.categoryOf function none
      return receiver.category.any (·.role == .morphism)
  | `(cas_term| ($function:cas_term)($arguments:cas_term,*))
  | `(cas_term| $function:cas_term($arguments:cas_term,*)) =>
    if arguments.getElems.isEmpty then return false
    unless ← principalApplication context function do return false
    SourceReadM.inspect do
      let receiver ← context.readExpression context.categoryOf function none
      return receiver.category.any (·.role == .morphism)
  | _ => return false

/-- Both native application and whole-point composition complete against the same public
reader contract before unique selection. Original operands are read once by their positions. -/
def applicationResultCompleting (context : ReadContext) (source : NativeSourceJudgement)
    (arguments : Array (TSyntax `cas_term)) (expected : Option Expr)
    (complete : ReadCompletion) :
    SourceReadM (Except MessageData NativeSourceJudgement) := do
  let supplied ← if let #[argument] := arguments then do
    if source.category.any (·.role == .morphism) && (← principalApplication context argument) then
      let point ← context.readExpression context.categoryOf argument none
      pure (some point)
    else pure none
  else pure none
  let generalized := supplied.any (fun point => point.category.any (·.role == .morphism))
  let ordinary := do
    let formed ← applicationApplicableCore context supplied source arguments
      (if generalized then none else expected)
    match formed with
    | .ok value => complete ⟨value, if arguments.isEmpty then source.category else none⟩
    | .error message => pure (.error message)
  unless generalized do return ← ordinary
  let some point := supplied
    | liftM (m := TermElabM) <| throwError "the generalized application lost its original operand"
  let composed := do
    let mapped ← sourceCarrier source
    let supplied ← sourceCarrier point
    let some category := mapped.category
      | liftM (m := TermElabM) <| throwError "generalized application lost its selected carrier category"
    let some suppliedCategory := supplied.category
      | liftM (m := TermElabM) <| throwError "the generalized point lost its selected carrier category"
    unless category.role == .morphism && suppliedCategory.role == .morphism &&
        category.expression.syntacticEq suppliedCategory.expression &&
        (← isDefEq category.bundle suppliedCategory.bundle) do
      return .error m!"generalized application has different complete carrier categories"
    let some (_, pointTarget) ← mapEnds supplied.value
      | liftM (m := TermElabM) <| throwError "the supplied generalized point lost its native endpoints"
    let some (mapSource, _) ← mapEnds mapped.value
      | liftM (m := TermElabM) <| throwError "the selected map lost its native endpoints"
    match ← registeredSourceDomainsApplicable pointTarget mapSource with
    | .error message => return .error message
    | .ok () => pure ()
    let scope ← get
    let agrees ← scope.context.withOriginalSources #[pointTarget, mapSource] fun original =>
      isDefEq original[0]! original[1]!
    unless agrees do
      return .error m!"the generalized point does not have the selected map's source"
    let pointType ← liftM (m := MetaM) <| instantiateMVars (← inferType supplied.value)
    let mapType ← liftM (m := MetaM) <| instantiateMVars (← inferType mapped.value)
    let stated ← if pointType.isAppOfArity ``Quiver.Hom 4 &&
        mapType.isAppOfArity ``Quiver.Hom 4 then
      pure (mkAppN pointType.getAppFn (pointType.getAppArgs.set! 3 mapType.getAppArgs[2]!))
    else do
      let pointType ← whnfR pointType
      let mapType ← whnfR mapType
      unless pointType.isAppOfArity ``TypeCat.Hom 2 &&
          mapType.isAppOfArity ``TypeCat.Hom 2 do
        liftM (m := TermElabM) <| throwError "the generalized application lost its complete native Hom types"
      pure (mkAppN pointType.getAppFn (pointType.getAppArgs.set! 1 mapType.getAppArgs[0]!))
    let pointSelection := (← SourceReadM.selection? supplied.value).getD {
      value := supplied.value, category := supplied.category }
    let pointValue ← SourceReadM.select { pointSelection with value := supplied.value } (some stated)
    let carrier ← mkAppM ``CategoryTheory.Bundled.α #[category.bundle]
    let instanceValue ← mkAppM ``CategoryTheory.Bundled.str #[category.bundle]
    let structureValue ← mkAppOptM ``CategoryTheory.Category.toCategoryStruct
      #[some carrier, some instanceValue]
    let composition ← mkAppOptM ``CategoryTheory.CategoryStruct.comp
      #[some carrier, some structureValue]
    let value ← elabAppArgs composition #[]
      #[Arg.expr pointValue, Arg.expr mapped.value] none false false
    let value ← SourceReadM.select { value, category := some category }
    complete ⟨value, some category⟩
  SourceReadM.chooseApplicable #[ordinary, composed]
    m!"no application of the selected source accepts its original operand"
    m!"the selected source admits distinct completed ordinary and generalized applications"

/-- Compatibility callers still receive the actual provided expected-type completion.
Qualification belongs to the assembled reader and is not replayed by this wrapper. -/
def applicationResultApplicable (context : ReadContext) (source : NativeSourceJudgement)
    (arguments : Array (TSyntax `cas_term)) (expected : Option Expr) :
    SourceReadM (Except MessageData NativeSourceJudgement) :=
  applicationResultCompleting context source arguments expected
    (checkReadJudgementApplicable { context with expected, qualification := none })

/-- Required application preserves actual operand and native construction failures. -/
def applicationResult (context : ReadContext) (source : NativeSourceJudgement)
    (arguments : Array (TSyntax `cas_term)) (expected : Option Expr) :
    SourceReadM NativeSourceJudgement := do
  match ← applicationResultApplicable context source arguments expected with
  | .ok value => pure value
  | .error message => liftM (m := TermElabM) <| throwError message

end SourceReader

end CasCompiler
