module

public import CasCompiler.ReadContext
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
    Expr → TermElabM (Option (Expr × Expr)) :=
  fun (arrow : Expr) => do
    let type ← whnfR (← instantiateMVars (← inferType arrow))
    if type.isAppOfArity ``Quiver.Hom 4 then
      return some (← declaredEndpoint type.getAppArgs[2]!, ← declaredEndpoint type.getAppArgs[3]!)
    if type.isAppOfArity ``TypeCat.Hom 2 then return some (type.getAppArgs[0]!, type.getAppArgs[1]!)
    return none

-- Only an unresolved bare object spelling can acquire a registered refinement for a
-- declaration parameter. A retained binding or an explicit qualification already selected
-- its complete source object and must use that object's own outgoing routes.
private partial def bareObjectName? (source : TSyntax `cas_term) :
    TermElabM (Option String) := do
  if let some name := sourceAtomName? source then return some name
  match source with
  | `(cas_term| ($inner:cas_term)) => bareObjectName? inner
  | `(cas_term| $name:ident) =>
    if ((← getLCtx).findFromUserName? name.getId).isSome then return none
    return some (name.getId.toString (escape := false))
  | _ => return none

def application (context : ReadContext) :
    NativeSourceJudgement → Array (TSyntax `cas_term) → Option Expr → TermElabM Expr :=
  let readExpression := @ReadContext.readExpression context
  let categoryOf := context.categoryOf
  fun (source : NativeSourceJudgement) (arguments : Array (TSyntax `cas_term))
      (expected : Option Expr) => do
    -- A map applied to its whole domain is the map's image (`m2(ℕ)`), through the registered
    -- image of the power object of its target (PowerObjectEntry.image).
    if let #[argument] := arguments then
      if argument.raw.isOfKind ``CasCatalogue.Language.casAtom then
        if let some (domain, codomain) ← mapEnds source.value then
          let object ← readExpression categoryOf argument none
          if object.category.any (·.role == .object) then
            if ← isDefEq object.value domain then
              let target ← sourcePowerObjectAt codomain
              return ← sourceImageOf target domain source.value expected
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
        let type ← whnfR (← declaredEndpoint (← inferType hole))
        let result ← whnfR (← declaredEndpoint (← inferType (mkApp function hole)))
        return type.isAppOfArity ``Prod 2 && !result.isForall
      if unary then
        discard <| elabAppArgs function #[] #[Arg.expr hole] none false false
        let type ← declaredEndpoint (← inferType hole)
        let tuple ← sourceTuple arguments type fun component type => do
          return (← readExpression categoryOf component (some type)).value
        return ← elabAppArgs function #[] #[Arg.expr tuple] expected false false
    -- A named spelling for the actual declared source of a Sets arrow is checked at the
    -- entire native family before its parameters are applied. This can guide its point's
    -- existing literal reader without choosing another runtime object by carrier equality.
    let namedDomain ← if arguments.size == 1 && source.category.any (fun category =>
        category.role == .morphism &&
          category.expression.syntacticEq (.atom CasCatalogue.CategoryId.sets)) then do
        let type ← whnfR (← inferType source.value)
        if type.isAppOfArity ``Quiver.Hom 4 then
          pure (some (← sourceNamedObjectAlias CasCatalogue.CategoryId.sets
            (← declaredEndpoint type.getAppArgs[2]!)))
        else pure none
      else pure none
    let (result, actual) ← elabSourceApplication function (arguments.map (·.raw)) expected fun index type => do
      let some argument := arguments[index]?
        | throwError "the source application lost an original argument"
      let type ← match namedDomain with
        | some domain =>
          unless ← isDefEq type domain do
            throwError "the Sets point application changed its actual declared source"
          pure domain
        | none => pure type
      -- Domain atoms contain no identifier token, so the numeral-only syntax predicate
      -- alone does not distinguish them from literals. Keep their registered spelling.
      let bareName ← bareObjectName? argument
      -- An object of another selected category is viewed along its structural route.
      let viewed : Option NativeSourceJudgement ← if sourceNumeric argument.raw && bareName.isNone then pure none else do
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
        | some value => pure value
        | none => readExpression categoryOf argument (some type)
      let parameter ← match value.category with
        | some category =>
          if category.role == .object then annotateSourceObject category value.value
          else pure value.value
        | none => pure value.value
      return parameter
    if let #[argument] := actual then
      if source.category.any (·.role == .morphism) then
        if let some original ← sourcePointOrigin? argument then
          -- Retain the ordinary native composition of the already selected point and
          -- carrier map. A later application keeps this point's same original domain.
          let mapped ← sourceCarrier source
          let some category := mapped.category
            | throwError "the point action lost its selected carrier category"
          let carrier ← mkAppM ``CategoryTheory.Bundled.α #[category.bundle]
          let categoryInstance ← mkAppM ``CategoryTheory.Bundled.str #[category.bundle]
          let categoryStructure ← mkAppOptM ``CategoryTheory.Category.toCategoryStruct
            #[some carrier, some categoryInstance]
          let composition ← mkAppOptM ``CategoryTheory.CategoryStruct.comp
            #[some carrier, some categoryStructure]
          let point ← elabAppArgs composition #[] #[Arg.expr original.point, Arg.expr mapped.value]
            none false false
          return ← retainSourcePoint point result
    return result

-- A call of an already selected native map has its domain from that receiver. This
-- extends principal reading through nested actual calls without selecting an overloaded
-- declaration from an expected endpoint or turning an interpretation failure into a rule.
private partial def principalApplication (context : ReadContext)
    (source : TSyntax `cas_term) : TermElabM Bool := do
  if ← sourcePrincipal source then return true
  match source with
  | `(cas_term| ($inner:cas_term)) => principalApplication context inner
  | `(cas_term| $_:cas_term in $_:cas_term using ($_:cas_term,*)) => return true
  | `(cas_term| $name:ident($arguments:cas_term,*)) =>
    if arguments.getElems.isEmpty then return false
    let function ← `(cas_term| $name:ident)
    unless ← principalApplication context function do return false
    withoutModifyingState do
      let receiver ← context.readExpression context.categoryOf function none
      return receiver.category.any (·.role == .morphism)
  | `(cas_term| ($function:cas_term)($arguments:cas_term,*))
  | `(cas_term| $function:cas_term($arguments:cas_term,*)) =>
    if arguments.getElems.isEmpty then return false
    unless ← principalApplication context function do return false
    withoutModifyingState do
      let receiver ← context.readExpression context.categoryOf function none
      return receiver.category.any (·.role == .morphism)
  | _ => return false

/-- Apply an actual selected map to its supplied value or whole generalized point.
Principal source maps retain their original category and complete arrow before native
composition. A map-valued parameter still uses ordinary application at its declared type.
Reuse: sourceCarrier's checked whole-family actions and CategoryStruct.comp, the same
native operation used by explicit source composition. No endpoint selects another map. -/
def applicationResult (context : ReadContext) (source : NativeSourceJudgement)
    (arguments : Array (TSyntax `cas_term)) (expected : Option Expr) :
    TermElabM NativeSourceJudgement := do
  if let #[argument] := arguments then
    if source.category.any (·.role == .morphism) && (← principalApplication context argument) then
      let point ← context.readExpression context.categoryOf argument none
      if point.category.any (·.role == .morphism) then
        let function ← sourceFunction source
        let .forallE _ domain _ _ ← whnfR (← inferType function)
          | throwError "the selected map lost its actual carrier-function domain"
        let ordinary ← withoutModifyingState do
          if ← isDefEq (← inferType point.value) domain then return true
          if (← whnfR domain).isForall then
            return ← isDefEq (← inferType (← sourceFunction point)) domain
          return false
        unless ordinary do
          let mapped ← sourceCarrier source
          let supplied ← sourceCarrier point
          let some category := mapped.category
            | throwError "generalized application lost its selected carrier category"
          let some suppliedCategory := supplied.category
            | throwError "the generalized point lost its selected carrier category"
          unless category.role == .morphism && suppliedCategory.role == .morphism &&
              category.expression.syntacticEq suppliedCategory.expression &&
              (← isDefEq category.bundle suppliedCategory.bundle) do
            throwError "generalized application has different complete carrier categories"
          let some (_, pointTarget) ← mapEnds supplied.value
            | throwError "the supplied generalized point lost its native endpoints"
          let some (mapSource, _) ← mapEnds mapped.value
            | throwError "the selected map lost its native endpoints"
          checkRegisteredDomains pointTarget mapSource
          let carrier ← mkAppM ``CategoryTheory.Bundled.α #[category.bundle]
          let instanceValue ← mkAppM ``CategoryTheory.Bundled.str #[category.bundle]
          let structureValue ← mkAppOptM ``CategoryTheory.Category.toCategoryStruct
            #[some carrier, some instanceValue]
          let composition ← mkAppOptM ``CategoryTheory.CategoryStruct.comp
            #[some carrier, some structureValue]
          let value ← elabAppArgs composition #[]
            #[Arg.expr supplied.value, Arg.expr mapped.value] expected false false
          return ⟨value, some category⟩
  let value ← application context source arguments expected
  return ⟨value, if arguments.isEmpty then source.category else none⟩

end SourceReader

end CasCompiler
