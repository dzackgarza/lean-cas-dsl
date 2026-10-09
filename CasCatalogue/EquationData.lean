/- Copyright (c) 2026 Dzack Garza. Released under Apache 2.0 license. -/
module
public import Lean.Meta
public import Lean.Compiler.NoncomputableAttr
public import CasCatalogue.Decide

@[expose] public section
open Lean Meta

namespace CasCatalogue.EquationData

/-- Reduce a fully supplied class operation through its original dictionary. Only the
projection is reduced; the resulting operation body remains available to equation metadata. -/
def selectedProjection? (value : Expr) : MetaM (Option Expr) := do
  if (← whnf (← inferType value)).isForall then return none
  let head := value.getAppFn
  let projected ← match head with
    | .const name _ =>
        let some info ← getProjectionFnInfo? name | return none
        unless info.fromClass do return none
        let some dictionary := value.getAppArgs[info.numParams]? | return none
        unless (← isClass? (← inferType dictionary)).isSome do return none
        let some unfolded ← unfoldDefinition? value (ignoreTransparency := true)
          | return none
        let some field ← withTransparency .all <| reduceProj? unfolded.getAppFn
          | return none
        pure (mkAppN field unfolded.getAppArgs).headBeta
    | .proj _ _ dictionary =>
        unless (← isClass? (← inferType dictionary)).isSome do return none
        let some field ← withTransparency .all <| reduceProj? head | return none
        pure (mkAppN field value.getAppArgs).headBeta
    | _ => return none
  if projected == value then return none
  return some projected

/-- Expose enclosing definition bodies without unfolding an operator whose provider supplies
equations. Every change here is definitional; theorem rewriting remains proof-producing. -/
def exposeDefinitions (value : Expr) : MetaM Expr := do
  unless value.eq?.isSome do return value
  let mut current := value
  for _ in [:32] do
    let expose (data : Expr) := Meta.transform data (pre := fun term => do
      if term.isSort || (← isProof term) || (← isType term) ||
          (← isClass? (← inferType term)).isSome then return .done term
      if let some name := term.getAppFn.constName? then
        if (← getReducibilityStatus name) == .irreducible &&
            (← getEqnsFor? name).isSome then return .continue
      if let some projected ← selectedProjection? term then
        return .continue (some projected)
      let beta := term.headBeta
      if beta != term then return .continue (some beta)
      if let .letE _ _ value body _ := term then
        return .continue (some (body.instantiate1 value))
      if let some unfolded ← unfoldDefinition? term (ignoreTransparency := true) then
        return .continue (some unfolded)
      if let some projected ← withTransparency .all <| reduceProj? term.getAppFn then
        return .continue (some (mkAppN projected term.getAppArgs))
      if let some reduced ← withReducible <| reduceRecMatcher? term then
        return .continue (some reduced)
      return .continue)
    let some (type, currentLeft, currentRight) := current.eq? | return current
    let next := mkApp3 current.getAppFn type (← expose currentLeft) (← expose currentRight)
    if next == current then break
    current := next
  return current

/-- Discover unfolding equations only from irreducible operators in actual data terms.
Types and proofs are preserved. Equation names come from Lean's declaration metadata. -/
def operators (condition : Expr) : MetaM (Array Name) := do
  let some (_, left, right) := condition.eq? | return #[]
  let collect : StateRefT (Array Name) MetaM Unit := do
    for value in #[left, right] do
      discard <| Meta.transform value (pre := fun term => do
        if term.isSort || (← isProof term) || (← isType term) ||
          (← isClass? (← inferType term)).isSome then return .done term
        if let some name := term.getAppFn.constName? then
          if (← getReducibilityStatus name) == .irreducible &&
              (← getEqnsFor? name).isSome && !(← get).contains name then
            modify (·.push name)
        return .continue)
  let (_, names) ← collect.run #[]
  return names

/-- One instantiated provider equation, matched only at its actual left-hand side. -/
def equationAt (value : Expr) (equation : Name) : MetaM (Option (Expr × Expr)) :=
  withoutModifyingState do
    let equationProof ← mkConstWithFreshMVarLevels equation
    let (arguments, _, conclusion) ← forallMetaTelescope (← inferType equationProof)
    let some (_, left, right) := conclusion.eq? | return none
    unless left.getAppFn.constName? == value.getAppFn.constName? do return none
    unless ← withTransparency .all <| isDefEq left value do return none
    let proof ← instantiateMVars (mkAppN equationProof arguments)
    let right ← instantiateMVars right
    if proof.hasMVar || proof.hasLevelMVar || right.hasMVar || right.hasLevelMVar then
      return none
    return some (right, proof)

/-- Rebuild a complete application after one argument equality. Later dependent arguments
are transported from their actual original values, including proof and instance packages.
The result carrier must remain the original carrier. -/
def transportArgument (value : Expr) (index : Nat) (replacement equality : Expr) :
    MetaM (Option (Expr × Expr)) := do
  let arguments := value.getAppArgs
  let some selected := arguments[index]? | return none
  let originalType ← inferType value
  withLocalDeclD `selectedData (← inferType selected) fun boundValue => do
   let equalityType ← mkEq selected boundValue
   withLocalDeclD `selectedEquality equalityType fun boundEquality => do
    let mut rebuilt := mkApp (mkAppN value.getAppFn (arguments.extract 0 index)) boundValue
    for later in [(index + 1):arguments.size] do
      let .forallE _ domain _ _ ← whnf (← inferType rebuilt) | return none
      let originalArgument := arguments[later]!
      let sameType ← withoutModifyingState <| withTransparency .all <|
        isDefEq (← inferType originalArgument) domain
      let argument ← if sameType then pure originalArgument else do
        let motive ← mkLambdaFVars #[boundValue, boundEquality] domain
        mkEqRec motive originalArgument boundEquality
      rebuilt := mkApp rebuilt argument
    unless ← withoutModifyingState <| withTransparency .all <|
        isDefEq (← inferType rebuilt) originalType do return none
    let template ← mkLambdaFVars #[boundValue, boundEquality] rebuilt
    let motive ← mkLambdaFVars #[boundValue, boundEquality] (← mkEq value rebuilt)
    let proof ← mkEqRec motive (← mkEqRefl value) equality
    return some ((mkAppN template #[replacement, equality]).headBeta, proof)

/-- Check the actual synthesized logical algorithm's data constants using Lean's computability
metadata. Proofs and type parameters do not participate; opaque/axiomatic data is rejected. -/
def computationalDecision (value : Expr) : MetaM Bool := do
  let collect : StateRefT Bool MetaM Unit := do
    discard <| Meta.transform value (pre := fun term => do
      if term.isSort || (← isProof term) || (← isType term) then return .done term
      if term.isFVar && (← isClass? (← inferType term)).isSome then
        set false
        return .done term
      if let some name := term.getAppFn.constName? then
        if Lean.isNoncomputable (← getEnv) name then set false
        match (← getEnv).find? name with
        | some (.axiomInfo _) | some (.opaqueInfo _) => set false
        | _ => pure ()
      return .continue)
  return (← collect.run true).2

/-- Normalize a data recursor on its exact selected `Decidable` argument using either a
checked closed predicate proof or an independently synthesized computable algorithm for the
same predicate. Subsingleton equality retains the original evidence; no algebra instance changes. -/
def decisionRecursorAt (value : Expr)
    (solvePredicate : Expr → MetaM (Option Expr)) : MetaM (Option (Expr × Expr)) := do
  let some name := value.getAppFn.constName? | return none
  let some (.recInfo recursor) := (← getEnv).find? name | return none
  let index := recursor.getMajorIdx
  let some selected := value.getAppArgs[index]? | return none
  let type ← withTransparency .default <| whnf (← inferType selected)
  unless type.isAppOf ``Decidable do return none
  let predicate := type.getAppArgs[0]!
  if predicate.hasMVar || predicate.hasLevelMVar || predicate.hasLooseBVars then
    return none
  let selectedHead ← withTransparency .default <| whnf selected
  if selectedHead.isAppOf ``Decidable.isTrue || selectedHead.isAppOf ``Decidable.isFalse then
    return none
  let mut replacement : Option Expr := none
  if !predicate.hasFVar then
    if let some proof ← solvePredicate predicate then
      replacement := some (← mkAppM ``Decidable.isTrue #[proof])
    else if let some proof ← solvePredicate (mkNot predicate) then
      replacement := some (← mkAppM ``Decidable.isFalse #[proof])
  if replacement.isNone then
    if let some candidate := (← withTransparency .all <| trySynthInstance type).toOption then
      let candidate ← instantiateMVars candidate
      if !candidate.hasMVar && !candidate.hasLevelMVar &&
          (← computationalDecision candidate) &&
          !(← withoutModifyingState <| withTransparency .all <| isDefEq candidate selected) then
        replacement := some candidate
  let some chosenReplacement := replacement | return none
  let equality ← mkAppM ``Subsingleton.elim #[selected, chosenReplacement]
  transportArgument value index chosenReplacement equality

/-- Rewrite actual data subterms by provider equations, retaining structural congruence.
The depth bound limits traversal; dependent evidence is transported from its full original data. -/
partial def rewriteData (value : Expr) (equations : Array Name) (fuel : Nat)
    (solvePredicate : Expr → MetaM (Option Expr)) :
    MetaM (Expr × Expr) := do
  if fuel == 0 || value.isSort || (← isProof value) || (← isType value) ||
      (← isClass? (← inferType value)).isSome then
    return (value, ← mkEqRefl value)
  if let some result ← decisionRecursorAt value solvePredicate then return result
  for equation in equations do
    if let some result ← equationAt value equation then return result
  match value with
  | .app _ _ =>
      let mut current := value
      let mut transport ← mkEqRefl value
      for index in [:value.getAppNumArgs] do
        let argument := current.getAppArgs[index]!
        let (replacement, equality) ← rewriteData argument equations (fuel - 1) solvePredicate
        if replacement == argument then continue
        if let some (rebuilt, step) ← transportArgument current index replacement equality then
          transport ← mkEqTrans transport step
          current := rebuilt
      return (current, transport)
  | .lam name domain body info =>
      withLocalDecl name info domain fun boundValue => do
        let (newBody, bodyProof) ← rewriteData (body.instantiate1 boundValue) equations (fuel - 1) solvePredicate
        let newValue ← mkLambdaFVars #[boundValue] newBody
        let pointwise ← mkLambdaFVars #[boundValue] bodyProof
        return (newValue, ← mkAppM ``funext #[pointwise])
  | .proj structureName index structureValue =>
      let (newStructure, structureProof) ← rewriteData structureValue equations (fuel - 1) solvePredicate
      if newStructure == structureValue then return (value, ← mkEqRefl value)
      withLocalDeclD `data (← inferType structureValue) fun boundValue => do
        let projection ← mkLambdaFVars #[boundValue] (.proj structureName index boundValue)
        unless (← whnf (← inferType projection)).isArrow do
          return (value, ← mkEqRefl value)
        return (.proj structureName index newStructure, ← mkCongrArg projection structureProof)
  | .mdata metadata body =>
      let (newBody, proof) ← rewriteData body equations (fuel - 1) solvePredicate
      return (.mdata metadata newBody, proof)
  | _ => return (value, ← mkEqRefl value)

/-- Rewrite the two equality operands and assemble the proposition equality directly. -/
def unfoldEquations (condition : Expr) (equations : Array Name)
    (solvePredicate : Expr → MetaM (Option Expr)) :
    MetaM (Expr × Expr) := do
  let some (type, left, right) := condition.eq? | return (condition, ← mkEqRefl condition)
  let (newLeft, leftProof) ← rewriteData left equations 64 solvePredicate
  let (newRight, rightProof) ← rewriteData right equations 64 solvePredicate
  let eqLeft := mkApp condition.getAppFn type
  let leftFunctionProof ← mkCongrArg eqLeft leftProof
  let first ← mkCongrFun leftFunctionProof right
  let second ← mkCongrArg (mkApp eqLeft newLeft) rightProof
  return (← mkEq newLeft newRight, ← mkEqTrans first second)

/-- Prove a closed typed equality using existing declaration unfolding equations and a
structural solver. Eight bounded rounds expose opaque data operations; each equation proof
is retained in the transport back to the exact original proposition. No quotient normal-form
assumption or theorem-name selection participates. Failure to prove equality decides nothing. -/
partial def proveAux (condition : Expr) (solveNormalized : Expr → MetaM (Option Expr))
    (predicateFuel : Nat) :
    MetaM (Option Expr) := do
  if predicateFuel == 0 then return none
  let original ← instantiateMVars condition
  if original.hasMVar || original.hasLevelMVar || original.hasFVar || original.hasLooseBVars then
    return none
  let negative := original.isAppOf ``Not
  let equation := if negative then original.getAppArgs[0]! else original
  unless equation.eq?.isSome do return none
  let solvePredicate := fun predicate => do
    if let some proof ← Decide.decisionProof predicate then return some proof
    proveAux predicate Decide.decisionProof (predicateFuel - 1)
  let mut current ← exposeDefinitions equation
  let exposedTarget := if negative then mkNot current else current
  if current != equation then
    if let some proof ← solveNormalized exposedTarget then
      let proof ← instantiateMVars (mkExpectedPropHint proof original)
      if !proof.hasMVar && !proof.hasLevelMVar && !proof.hasFVar &&
          !proof.hasLooseBVars && (← Decide.kernelAccepts original proof) then
        return some proof
  let mut transport := mkExpectedPropHint (← mkEqRefl current) (← mkEq equation current)
  let mut changed := false
  for _ in [:8] do
    let mut roundChanged := false
    let (decided, decisionStep) ← unfoldEquations current #[] solvePredicate
    if decided != current then
      transport ← withTransparency .all <| mkEqTrans transport decisionStep
      current := decided
      roundChanged := true
      changed := true
    let names ← operators current
    for name in names.extract 0 (min names.size 8) do
      let some equations ← getEqnsFor? name | continue
      let (rewritten, step) ← unfoldEquations current equations solvePredicate
      if rewritten == current then continue
      transport ← withTransparency .all <| mkEqTrans transport step
      current := rewritten
      roundChanged := true
      changed := true
    unless roundChanged do break
    current ← exposeDefinitions current
    transport := mkExpectedPropHint transport (← mkEq equation current)
  unless changed do return none
  let target := if negative then mkNot current else current
  let finalTransport ← if negative then mkCongrArg (mkConst ``Not) transport else pure transport
  let some proof ← solveNormalized target | return none
  let proof := mkExpectedPropHint proof target
  let proof ← withTransparency .all <| mkEqMPR finalTransport proof
  let proof ← instantiateMVars (mkExpectedPropHint proof original)
  unless ← Decide.kernelAccepts original proof do return none
  return some proof

/-- Bounded declaration-data equality reconstruction at its full original proposition. -/
def prove (condition : Expr) (solveNormalized : Expr → MetaM (Option Expr)) :
    MetaM (Option Expr) := proveAux condition solveNormalized 8

end CasCatalogue.EquationData
