module

public import CasCompiler.Surface
public import CasCatalogue.Decide

public section

namespace CasCompiler

open Lean Meta Elab Term CasCatalogue

/-- The value of a global element `1 ⟶ X` at the terminal source's point, as source numerals
read their registered point declarations. -/
def sourcePointValue (element : Expr) (expected : Option Expr) : TermElabM Expr := do
  let type ← whnfR (← inferType element)
  unless type.isAppOfArity ``Quiver.Hom 4 do
    throwError "a registered distinguished element is not a native point map"
  let point ← mkAppOptM ``default #[some type.getAppArgs[2]!, none]
  let function ← sourceSetFunction element
  elabAppArgs function #[] #[Arg.expr point] expected false false

/-- The registered generator `∀ params, 1 ⟶ obj params` of the object whose carrier is `type`,
at its point: the variable `x` of `R[x]`. The parameters are those that reducible unification
of the declared family with `type` determines (as for operation refinements).
Source: Registry.Entry.ObjectEntry.generator. Several applicable objects are ambiguous. -/
def sourceGeneratorAt? (type : Expr) (index : Option Nat) : TermElabM (Option Expr) := do
  let state ← semanticState
  let mut found := #[]
  for entry in state.objects do
    let some generator := entry.generator | continue
    discard <| checkedDeclaration generator
    let family ← mkConstWithFreshMVarLevels generator
    let (parameters, infos, result) ← forallMetaTelescopeReducing (← inferType family)
    -- An indexed family of generators (`xᵢ`) is selected by its index; a single generator by
    -- a bare variable.
    let explicit := (parameters.zip infos).filter (·.2.isExplicit)
    let indexed ← match explicit.back? with
      | some (last, _) => pure ((← whnfR (← inferType last)).isAppOf ``Fin)
      | none => pure false
    unless indexed == index.isSome do continue
    let result ← whnfR result
    unless result.isAppOfArity ``Quiver.Hom 4 do continue
    let applicable ← withoutModifyingState do
      unless ← withReducible (isDefEq result.getAppArgs[3]! type) do return false
      for argument in parameters, info in infos do
        if info.isInstImplicit && (← instantiateMVars argument).isMVar then
          let some instanceValue ← synthInstance? (← inferType argument) | return false
          unless ← isDefEq argument instanceValue do return false
      -- The index of an indexed generator is the variable's own position, assigned below.
      let determined := if indexed then parameters.pop else parameters
      let arguments ← determined.mapM instantiateMVars
      return !arguments.any (fun argument => argument.hasMVar || argument.hasLevelMVar)
    unless applicable do continue
    discard <| withReducible (isDefEq result.getAppArgs[3]! type)
    for argument in parameters, info in infos do
      if info.isInstImplicit && (← instantiateMVars argument).isMVar then
        let some instanceValue ← synthInstance? (← inferType argument)
          | throwError "the registered generator lost its instance"
        discard <| isDefEq argument instanceValue
    if let some index := index then
      let some (slot, _) := explicit.back? | continue
      let bound ← instantiateMVars (← whnfR (← inferType slot)).appArg!
      let proposition ← mkAppM ``LT.lt #[mkNatLit index, bound]
      let some proof ← CasCatalogue.Decide.decisionProof proposition
        | throwError "the ring has no variable of index {index}"
      discard <| isDefEq slot (← mkAppM ``Fin.mk #[mkNatLit index, proof])
    let element ← instantiateMVars (mkAppN family parameters)
    found := found.push (entry, element)
  match found with
  | #[] => return none
  | #[(entry, element)] =>
    let value ← sourcePointValue element (some type)
    return some (sourceReference ``ObjectEntry.generator entry.id.raw (entry.generator.getD .anonymous) value)
  | _ => throwSemanticAmbiguity "several registered objects have a generator at this carrier"

/-- `x_3` as `("x_", 3)`. -/
def sourceIndexed? (name : Name) : Option (String × Nat) :=
  let chars := name.toString.toList
  let digits := (chars.reverse.takeWhile Char.isDigit).reverse
  if digits.isEmpty || digits.length == chars.length then none
  else some (String.ofList (chars.take (chars.length - digits.length)),
    (String.ofList digits).toNat!)

/-- The variables `x, y` or `x_0, x_1, ..., x_9` of `R[…]`, in order: `...` runs through the
indices between its neighbours, which share their prefix (public language contract). -/
def sourceRingVariableNames (stx : Syntax) : Except String (Array Name) := do
  let items := #[stx[2]] ++ stx[4].getSepArgs.map (·[0])
  let mut names : Array Name := #[]
  let mut index := 0
  while index < items.size do
    let item := items[index]!
    if item.isIdent then
      names := names.push item.getId
    else
      let (some before, some after) := (names.back?, items[index + 1]?)
        | throw "`...` stands between variables"
      let (some (stem, first), some (stem', last)) :=
          (sourceIndexed? before, sourceIndexed? after.getId)
        | throw "`...` stands between indexed variables `x_i, ..., x_k`"
      unless stem == stem' && first < last do
        throw "`...` runs up between variables of one prefix"
      for middle in [first + 1:last] do names := names.push (.mkSimple s!"{stem}{middle}")
    index := index + 1
  return names

/-- The variables that the rings `R[v]`, `R[v₀, …]` and series `R[[v]]` written in `stx` name,
with the ring syntax and, in several variables, the variable's index.
Source: the public language contract, "`R[x]`: the polynomials over `R` in `x`". -/
partial def sourceRingVariables (stx : Syntax) : Array (Name × Syntax × Option Nat) :=
  let own : Array (Name × Syntax × Option Nat) :=
    if stx.isOfKind ``CasCatalogue.Language.casRing then #[(stx[2].getId, stx, none)]
    else if stx.isOfKind ``CasCatalogue.Language.casSeries then #[(stx[3].getId, stx, none)]
    else if stx.isOfKind ``CasCatalogue.Language.casMvRing then
      match sourceRingVariableNames stx with
      | .ok names => names.mapIdx fun index name => (name, stx, some index)
      | .error _ => #[]
    else #[]
  stx.getArgs.foldl (fun found argument => found ++ sourceRingVariables argument) own

/-- The variable `v` whose differential the identifier `dv` names. -/
def sourceDifferentialOf? (name : Name) : Option Name :=
  match name with
  | .str .anonymous text =>
    if text.startsWith "d" && text.length > 1 then some (.mkSimple (text.drop 1).toString) else none
  | _ => none

/-- Whether `name` occurs as an identifier of `stx` outside the variable slot of a ring, or as
its differential `dv`. -/
partial def sourceUses (name : Name) (stx : Syntax) : Bool :=
  if stx.isIdent then stx.getId == name || sourceDifferentialOf? stx.getId == some name
  else if stx.isOfKind ``CasCatalogue.Language.casRing ||
      stx.isOfKind ``CasCatalogue.Language.casSeries ||
      stx.isOfKind ``CasCatalogue.Language.casMvRing then sourceUses name stx[0]
  else stx.getArgs.any (sourceUses name)

/-- Whether a binder of `stx` binds `name`: a map `name ↦ e`, a comprehension, an image, a
big operator, a limit or a definite integral. -/
partial def sourceBinds (name : Name) (stx : Syntax) : Bool :=
  let binder :=
    if stx.isOfKind ``CasCatalogue.Language.casBig then stx[2].getId == name
    else if stx.isOfKind ``CasCatalogue.Language.casLimit then stx[1].getId == name
    else match stx.getArgs.toList with
      | [identifier, arrow, _] => identifier.isIdent && identifier.getId == name &&
          arrow.isAtom && arrow.getAtomVal.trim == "↦"
      | [left, first, second, third, fourth, _, right] =>
        let atom := fun (node : Syntax) (value : String) =>
          node.isAtom && node.getAtomVal.trim == value
        atom left "{" && atom right "}" &&
          ((first.isIdent && first.getId == name && atom second "∈") ||
            (atom second "|" && third.isIdent && third.getId == name && atom fourth "∈"))
      | _ => false
  binder || stx.getArgs.any (sourceBinds name)

/-- The registered objects of the object type `type` of a parameter (`A : Under R`), at the
declaration parameters that unification determines, for which `fits` holds once the parameter
is that object. -/
private def registeredObjectsAt (type : Expr) (fits : Expr → TermElabM Bool) :
    TermElabM (Array Expr) := do
  let mut found := #[]
  for entry in (← semanticState).objects do
    discard <| checkedDeclaration entry.declaration
    let family ← mkConstWithFreshMVarLevels entry.declaration
    let (parameters, _, objectType) ← forallMetaTelescopeReducing (← inferType family)
    let object := mkAppN family parameters
    let applicable ← withoutModifyingState do
      unless ← isDefEq objectType type do return false
      unless ← fits object do return false
      return !(← instantiateMVars object).hasMVar
    if applicable then
      discard <| isDefEq objectType type
      discard <| fits object
      found := found.push (← instantiateMVars object)
  return found

/-- `p(a)` for an element `p` of an object with a registered application
`∀ params A, obj params × A ⟶ B` (a polynomial's evaluation `R[x] × A → A` at an `R`-algebra
`A`). An argument in the coefficient ring `R` itself is evaluated in `Under.mk (𝟙 R)`, the
algebra that lean-categories states is own-ring evaluation (`Polynomials.evaluation_own`); any
other argument in the unique registered `R`-algebra whose carrier is its set.
Source: ObjectEntry.application. `read` reads the argument, at the coefficient set when given. -/
def sourceObjectApplication? (value : Expr) (numeral : Bool)
    (read : Option Expr → TermElabM Expr) : TermElabM (Option Expr) := do
  let type ← instantiateMVars (← inferType value)
  let state ← semanticState
  let mut applications := #[]
  for entry in state.objects do
    let some application := entry.application | continue
    discard <| checkedDeclaration entry.declaration
    let family ← mkConstWithFreshMVarLevels entry.declaration
    let (parameters, _, _) ← forallMetaTelescopeReducing (← inferType family)
    if ← withoutModifyingState (withReducible (isDefEq (mkAppN family parameters) type)) then
      applications := applications.push (entry, application)
  let some (entry, application) := applications[0]? | return none
  unless applications.size == 1 do
    throwSemanticAmbiguity "several registered applications act on this element"
  discard <| checkedDeclaration application
  let constant ← mkConstWithFreshMVarLevels application
  let (parameters, _, arrow) ← forallMetaTelescopeReducing (← inferType constant)
  let arrow ← whnfR arrow
  unless arrow.isAppOfArity ``Quiver.Hom 4 do
    throwError "the application of {entry.name} is not a native map"
  let pair ← whnfR arrow.getAppArgs[2]!
  unless pair.isAppOfArity ``Prod 2 do
    throwError "the application of {entry.name} does not act on a pair"
  unless ← withReducible (isDefEq pair.getAppArgs[0]! type) do
    throwError "the application of {entry.name} does not act on this element"
  let some algebra := parameters.back?
    | throwError "the application of {entry.name} has no argument object"
  let algebraType ← instantiateMVars (← inferType algebra)
  unless algebraType.isAppOf ``CategoryTheory.Under do
    throwUnsupportedSource m!"the application of {entry.name} acts at an unread argument object"
  let ring := algebraType.appArg!
  let own ← mkAppM ``CategoryTheory.Under.mk #[← mkAppM ``CategoryTheory.CategoryStruct.id #[ring]]
  -- The set the application reads its argument in, once the argument object is `object`.
  let argumentSet := fun (object : Expr) => do
    unless ← isDefEq algebra object do return none
    return some (← instantiateMVars pair.getAppArgs[1]!)
  let ownCarrier ← withoutModifyingState do
    let some carrier ← argumentSet own | throwError "the own-ring algebra does not fit"
    return carrier
  -- A numeral is an element of the coefficient set, the source of the object's registered
  -- constants `R ↪ R[x]` (ObjectEntry.constants). It is read by the numeral rules at that set's
  -- native type, where the declared literal selectors (ℤ, ℚ) recognize it.
  let coefficients ← match entry.constants with
    | none => pure ownCarrier
    | some constants => do
      discard <| checkedDeclaration constants
      let family ← mkConstWithFreshMVarLevels constants
      let (_, _, inclusion) ← forallMetaTelescopeReducing (← inferType family)
      let inclusion ← whnfR inclusion
      unless inclusion.isAppOfArity ``Quiver.Hom 4 &&
          (← withReducible (isDefEq inclusion.getAppArgs[3]! type)) do
        throwError "the constants of {entry.name} do not land in this element's set"
      instantiateMVars inclusion.getAppArgs[2]!
  let argument ← if numeral then read (some (← whnf coefficients)) else read none
  let argumentType ← instantiateMVars (← inferType argument)
  let candidates ← if ← isDefEq argumentType ownCarrier then pure #[own]
    else registeredObjectsAt algebraType fun object => do
      let some carrier ← argumentSet object | return false
      isDefEq carrier argumentType
  let selected ← match candidates with
    | #[object] => pure object
    | #[] => throwUnsupportedSource m!"no registered coefficient algebra acts on this argument"
    | _ => throwSemanticAmbiguity "several registered algebras act on the argument's set"
  unless ← isDefEq algebra selected do
    throwError "the selected argument object does not fit the application of {entry.name}"
  let applied ← instantiateMVars (mkAppN constant parameters)
  if applied.hasMVar || applied.hasLevelMVar then
    throwError "the application of {entry.name} is not determined"
  let function ← sourceSetFunction (sourceReference ``ObjectEntry.application entry.id.raw
    application applied)
  let result ← elabAppArgs function #[] #[Arg.expr (← mkAppM ``Prod.mk #[value, argument])]
    none false false
  -- The value lies in the argument's own set, as the reader formed it.
  mkExpectedTypeHint result argumentType

end CasCompiler
