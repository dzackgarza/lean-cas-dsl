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

/-- Whether `name` occurs as an identifier of `stx` outside the variable slot of a ring. -/
partial def sourceUses (name : Name) (stx : Syntax) : Bool :=
  if stx.isIdent then stx.getId == name
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

end CasCompiler
