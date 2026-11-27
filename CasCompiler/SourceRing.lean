module

public import CasCompiler.Surface
public import CasCompiler.SourcePointOrigin
public import CasCompiler.PointFamily
public import CasCompiler.Syntax
public import CasCatalogue.Decide

public section

namespace CasCompiler

open Lean Meta Elab Term CasCatalogue



def sourcePointValueSelection (element : Expr) (expected : Option Expr) :
    TermElabM (SourceSelection Expr) := do
  let type ← whnfR (← inferType element)
  unless type.isAppOfArity ``Quiver.Hom 4 do
    throwError "a registered distinguished element is not a native point map"


  let point ← mkAppOptM ``default #[some (← declaredEndpoint type.getAppArgs[2]!), none]
  let function ← sourceSetFunction element
  let value ← elabAppArgs function #[] #[Arg.expr point] expected false false
  let value ← if expected.isSome then pure value
    else mkExpectedTypeHint value (← declaredEndpoint type.getAppArgs[3]!)
  retainSourcePoint element { value }


def sourcePointValue (element : Expr) (expected : Option Expr) : SourceReadM Expr := do
  SourceReadM.select (← sourcePointValueSelection element expected)






def sourceGeneratorAt? (type : Expr) (index : Option Nat) : SourceReadM (Option Expr) := do
  let state ← semanticState
  let (nativeType, selected) ← registeredSourceDomain type
  if selected.isEmpty && (← SourceReadM.selection? type).isSome then return none
  let entries := if selected.isEmpty then state.objects else selected
  let mut found := #[]
  for entry in entries do
    let some generator := entry.generator | continue
    discard <| checkedDeclaration generator
    let family ← mkConstWithFreshMVarLevels generator
    let (parameters, infos, result) ← forallMetaTelescopeReducing (← inferType family)


    let explicit := (parameters.zip infos).filter (·.2.isExplicit)
    let indexed ← match explicit.back? with
      | some (last, _) => pure ((← whnfR (← inferType last)).isAppOf ``Fin)
      | none => pure false
    unless indexed == index.isSome do continue
    let result ← whnfR result
    unless result.isAppOfArity ``Quiver.Hom 4 do continue
    let namedTarget := nativeType.getAppFn.isConstOf entry.declaration &&
      result.getAppArgs[3]!.headBeta.consumeMData.getAppFn.isConstOf entry.declaration
    let applicable ← liftM (m := MetaM) <| withoutModifyingState do
      if namedTarget then
        unless (← alignSourceArguments? entry.declaration parameters
            result.getAppArgs[3]! nativeType).isSome do return false
      unless ← withReducible (isDefEq result.getAppArgs[3]! nativeType) do return false
      for argument in parameters, info in infos do
        if info.isInstImplicit && (← instantiateMVars argument).isMVar then
          let some instanceValue ← synthInstance? (← inferType argument) | return false
          unless ← isDefEq argument instanceValue do return false

      let determined := if indexed then parameters.pop else parameters
      let arguments ← determined.mapM instantiateMVars
      return !arguments.any (fun argument => argument.hasMVar || argument.hasLevelMVar)
    unless applicable do continue


    let retained ← if namedTarget then do
        let some retained ← alignSourceArguments? entry.declaration parameters
            result.getAppArgs[3]! nativeType
          | liftM (m := TermElabM) <| throwError "the registered generator lost its original object parameters"
        pure retained
      else pure (Array.replicate parameters.size none)
    discard <| liftM (m := MetaM) <| withReducible (isDefEq result.getAppArgs[3]! nativeType)
    for argument in parameters, info in infos do
      if info.isInstImplicit && (← liftM (m := MetaM) <| instantiateMVars argument).isMVar then
        let some instanceValue ← synthInstance? (← inferType argument)
          | liftM (m := TermElabM) <| throwError "the registered generator lost its instance"
        discard <| isDefEq argument instanceValue
    if let some index := index then
      let some (slot, _) := explicit.back? | continue
      let bound ← liftM (m := MetaM) <| instantiateMVars (← whnfR (← inferType slot)).appArg!
      let proposition ← mkAppM ``LT.lt #[mkNatLit index, bound]
      let some proof ← CasCatalogue.Decide.decisionProof proposition
        | liftM (m := TermElabM) <| throwError "the ring has no variable of index {index}"
      discard <| isDefEq slot (← mkAppM ``Fin.mk #[mkNatLit index, proof])
    let mut arguments ← liftM (m := MetaM) <| parameters.mapM instantiateMVars
    for original in retained, position in [:retained.size] do
      if let some original := original then
        arguments := arguments.set! position (← liftM (m := MetaM) <| instantiateMVars original)
    let element ← liftM (m := MetaM) <| instantiateMVars (mkAppN family arguments)
    found := found.push (entry, element)
  match found with
  | #[] => return none
  | #[(entry, element)] =>
    let selected ← sourcePointValueSelection element none
    let selected ← retainSourceApplication { selected with reference := some (.generator entry) }
      element
    return some (← SourceReadM.select selected (some type))
  | _ => liftM (m := TermElabM) <| throwSemanticAmbiguity "several registered objects have a generator at this carrier"


def sourceIndexed? (name : Name) : Option (String × Nat) :=
  let chars := name.toString.toList
  let digits := (chars.reverse.takeWhile Char.isDigit).reverse
  if digits.isEmpty || digits.length == chars.length then none
  else some (String.ofList (chars.take (chars.length - digits.length)),
    (String.ofList digits).toNat!)



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


def sourceDifferentialOf? (name : Name) : Option Name :=
  match name with
  | .str .anonymous text =>
    if text.startsWith "d" && text.length > 1 then some (.mkSimple (text.drop 1).toString) else none
  | _ => none



partial def sourceUses (name : Name) (stx : Syntax) : Bool :=
  if stx.isIdent then stx.getId == name || sourceDifferentialOf? stx.getId == some name
  else if stx.isOfKind ``CasCatalogue.Language.casRing ||
      stx.isOfKind ``CasCatalogue.Language.casSeries ||
      stx.isOfKind ``CasCatalogue.Language.casMvRing then sourceUses name stx[0]
  else stx.getArgs.any (sourceUses name)



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







private def objectApplication? (value : Expr) :
    SourceReadM (Option (ObjectEntry × Name)) := do
  let (_, owners) ← registeredSourceDomain (← inferType value)
  let applications := owners.filterMap fun entry =>
    entry.application.map fun application => (entry, application)
  let some found := applications[0]? | return none
  unless applications.size == 1 do
    liftM (m := TermElabM) <| throwSemanticAmbiguity "several registered applications act on this element"
  return some found




def sourceDirectApplicationApplicable? (value : Expr)
    (read : Expr → SourceReadM (Except MessageData Expr)) :
    SourceReadM (Except MessageData (Option Expr)) := do
  let some (entry, application) ← objectApplication? value | return .ok none
  discard <| checkedDeclaration application
  let (type, _) ← registeredSourceDomain (← liftM (m := MetaM) <| instantiateMVars (← inferType value))
  let selectedValue := (← SourceReadM.selection? value).getD { value }
  let value ← SourceReadM.select { selectedValue with value } (some type)
  let constant ← mkConstWithFreshMVarLevels application
  let (parameters, _, arrow) ← forallMetaTelescopeReducing (← inferType constant)
  let arrow ← whnfR arrow
  unless arrow.isAppOfArity ``Quiver.Hom 4 do
    liftM (m := TermElabM) <| throwError "the application of {entry.name} is not a native map"
  let pair ← whnfR arrow.getAppArgs[2]!
  unless pair.isAppOfArity ``Prod 2 do
    liftM (m := TermElabM) <| throwError "the application of {entry.name} does not act on a pair"
  unless ← liftM (m := MetaM) <| withReducible (isDefEq pair.getAppArgs[0]! type) do
    liftM (m := TermElabM) <| throwError "the application of {entry.name} does not act on this element"
  let some last := parameters.back? | return .ok none
  if (← liftM (m := MetaM) <| instantiateMVars (← inferType last)).isAppOf ``CategoryTheory.Under then return .ok none
  let argumentSet ← liftM (m := MetaM) <| instantiateMVars pair.getAppArgs[1]!
  if argumentSet.hasMVar then
    liftM (m := TermElabM) <| throwUnsupportedSource m!"the application of {entry.name} acts at an unread argument object"
  let argument ← match ← read argumentSet with
    | .ok value => pure value
    | .error message => return .error message
  unless ← isDefEq (← inferType argument) argumentSet do
    return .error m!"the application argument has another declared native type"
  let applied ← liftM (m := MetaM) <| instantiateMVars (mkAppN constant parameters)
  if applied.hasMVar || applied.hasLevelMVar then
    liftM (m := TermElabM) <| throwError "the application of {entry.name} is not determined"
  let family ← PointFamily.forApplication entry
  let arrow ← SourceReadM.select (← family.selected applied.getAppFn.constLevels!
    applied.getAppArgs applied)
  let function ← sourceSetFunction arrow
  let first := (← SourceReadM.selection? value).getD { value }
  let second := (← SourceReadM.selection? argument).getD { value := argument }
  let pair ← SourceReadM.select (← sourcePairPoint (fun selected => SourceReadM.select selected)
    { first with value } { second with value := argument })
  return .ok (some (← elabAppArgs function #[] #[Arg.expr pair]
    none false false))


def sourceDirectApplication? (value : Expr) (read : Expr → SourceReadM Expr) :
    SourceReadM (Option Expr) := do
  match ← sourceDirectApplicationApplicable? value (fun type => do return .ok (← read type)) with
  | .ok value => pure value
  | .error message => liftM (m := TermElabM) <| throwError message

def sourceObjectApplication? (value : Expr) (numeral : Bool)
    (read : Option Expr → SourceReadM Expr) : SourceReadM (Option Expr) := do
  if let some applied ← sourceDirectApplication? value fun set => read (some set) then
    return some applied
  let (type, _) ← registeredSourceDomain (← liftM (m := MetaM) <| instantiateMVars (← inferType value))
  let selectedValue := (← SourceReadM.selection? value).getD { value }
  let value ← SourceReadM.select { selectedValue with value } (some type)
  let some (entry, application) ← objectApplication? value | return none
  discard <| checkedDeclaration application
  let constant ← mkConstWithFreshMVarLevels application
  let (parameters, _, arrow) ← forallMetaTelescopeReducing (← inferType constant)
  let arrow ← whnfR arrow
  unless arrow.isAppOfArity ``Quiver.Hom 4 do
    liftM (m := TermElabM) <| throwError "the application of {entry.name} is not a native map"
  let pair ← whnfR arrow.getAppArgs[2]!
  unless pair.isAppOfArity ``Prod 2 do
    liftM (m := TermElabM) <| throwError "the application of {entry.name} does not act on a pair"
  unless ← liftM (m := MetaM) <| withReducible (isDefEq pair.getAppArgs[0]! type) do
    liftM (m := TermElabM) <| throwError "the application of {entry.name} does not act on this element"
  let some algebra := parameters.back?
    | liftM (m := TermElabM) <| throwError "the application of {entry.name} has no argument object"
  let algebraType ← liftM (m := MetaM) <| instantiateMVars (← inferType algebra)
  unless algebraType.isAppOf ``CategoryTheory.Under do
    liftM (m := TermElabM) <| throwUnsupportedSource m!"the application of {entry.name} acts at an unread argument object"
  let ring := algebraType.appArg!
  let own ← mkAppM ``CategoryTheory.Under.mk #[← mkAppM ``CategoryTheory.CategoryStruct.id #[ring]]

  let argumentSet : Expr → MetaM (Option Expr) := fun object => do
    unless ← isDefEq algebra object do return none
    return some (← instantiateMVars pair.getAppArgs[1]!)
  let ownCarrier ← liftM (m := MetaM) <| withoutModifyingState do
    let some carrier ← argumentSet own | throwError "the own-ring algebra does not fit"
    return carrier



  let coefficients ← match entry.constants with
    | none => pure ownCarrier
    | some constants => do
      discard <| checkedDeclaration constants
      let family ← mkConstWithFreshMVarLevels constants
      let (_, _, inclusion) ← forallMetaTelescopeReducing (← inferType family)
      let inclusion ← whnfR inclusion
      unless inclusion.isAppOfArity ``Quiver.Hom 4 &&
          (← liftM (m := MetaM) <| withReducible (isDefEq inclusion.getAppArgs[3]! type)) do
        liftM (m := TermElabM) <| throwError "the constants of {entry.name} do not land in this element's set"
      liftM (m := MetaM) <| instantiateMVars inclusion.getAppArgs[2]!
  let argument ← if numeral then read (some (← whnf coefficients)) else read none
  let originalArgumentType ← liftM (m := MetaM) <| instantiateMVars (← inferType argument)
  let (argumentType, _) ← registeredSourceDomain originalArgumentType
  let selectedArgument := (← SourceReadM.selection? argument).getD { value := argument }
  let argument ← SourceReadM.select { selectedArgument with value := argument } (some argumentType)
  let candidates ← if ← isDefEq argumentType ownCarrier then pure #[own]
    else registeredObjectsAt algebraType fun object => do
      let some carrier ← argumentSet object | return false
      isDefEq carrier argumentType
  let selected ← match candidates with
    | #[object] => pure object
    | #[] => liftM (m := TermElabM) <| throwUnsupportedSource m!"no registered coefficient algebra acts on this argument"
    | _ => liftM (m := TermElabM) <| throwSemanticAmbiguity "several registered algebras act on the argument's set"
  unless ← isDefEq algebra selected do
    liftM (m := TermElabM) <| throwError "the selected argument object does not fit the application of {entry.name}"
  let applied ← liftM (m := MetaM) <| instantiateMVars (mkAppN constant parameters)
  if applied.hasMVar || applied.hasLevelMVar then
    liftM (m := TermElabM) <| throwError "the application of {entry.name} is not determined"
  let family ← PointFamily.forApplication entry
  let arrow ← SourceReadM.select (← family.selected applied.getAppFn.constLevels!
    applied.getAppArgs applied)
  let function ← sourceSetFunction arrow
  let first := (← SourceReadM.selection? value).getD { value }
  let second := (← SourceReadM.selection? argument).getD { value := argument }
  let pair ← SourceReadM.select (← sourcePairPoint (fun selected => SourceReadM.select selected)
    { first with value } { second with value := argument })
  let result ← elabAppArgs function #[] #[Arg.expr pair]
    none false false

  return some (← SourceReadM.select { value := result } (some originalArgumentType))

end CasCompiler
