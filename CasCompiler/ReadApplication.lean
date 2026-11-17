module

public import CasCompiler.ReadContext
public import CasCompiler.SourceRing
public import CasCompiler.SourceTuple
public import CasCompiler.SourceSubset

public section

namespace CasCompiler

open Lean Meta Elab Term

namespace SourceReader

def mapEnds :
    Expr → TermElabM (Option (Expr × Expr)) :=
  fun (arrow : Expr) => do
    let type ← whnfR (← instantiateMVars (← inferType arrow))
    if type.isAppOfArity ``Quiver.Hom 4 then return some (type.getAppArgs[2]!, type.getAppArgs[3]!)
    if type.isAppOfArity ``TypeCat.Hom 2 then return some (type.getAppArgs[0]!, type.getAppArgs[1]!)
    return none

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
          -- The surface name of the applied family, for a declared preferred route.
          let state ← CasCatalogue.semanticState
          let head := function.consumeMData.getAppFn.constName?
          let name := head.bind fun head =>
            (state.objects.find? (·.declaration == head)).map (·.name) <|>
            (state.morphisms.find? (·.declaration == head)).map (·.name)
          if routed then pure (some (← sourceStructuralView object category.expression name))
          else pure none
      let value ← match viewed with
        | some value => pure value
        | none => readExpression categoryOf argument (some type)
      unless ← isDefEq hole value.value do
        throwErrorAt argument "the source argument does not match its dependent native type"
      actual := actual.push (Arg.expr value.value)
    elabAppArgs function #[] actual expected false false

end SourceReader

end CasCompiler
