module

public import CasCompiler.Surface

public section

namespace CasCompiler

open Lean Meta Elab Term CasCatalogue

private inductive NumeralContext where
  | direct
  | selected (value : Expr)
  | refinement (entry : ObjectEntry)

private def numeralProof (proposition : Expr) : MetaM (Option Expr) := do
  if proposition.isAppOfArity ``Eq 3 then
    let arguments := proposition.getAppArgs
    if ← withoutModifyingState <| isDefEq arguments[1]! arguments[2]! then
      return some (← mkEqRefl arguments[1]!)
  let decision ← mkDecide proposition
  unless (← withAtLeastTransparency .default <| whnf decision).isConstOf ``Bool.true do
    return none
  return some (← mkDecideProof proposition)

-- Resolve only proof and instance fields, in declaration order. All mathematical data
-- parameters must already come from the actual domain, literal or selected structure.
private def completePointParameters (arguments : Array Expr) (binders : Array BinderInfo)
    (proofs : Array Term) (start : Nat) : TermElabM (Option Nat) := do
  let mut proofIndex := start
  for argument in arguments, binder in binders do
    unless (← instantiateMVars argument).hasMVar do continue
    let type ← instantiateMVars (← inferType argument)
    if binder.isInstImplicit then
      unless ← isDefEq argument (← synthInstance type) do return none
    else if ← isProp type then
      let proof ← if proofs.isEmpty then do
          let some proof ← numeralProof type | return none
          pure proof
        else do
          let some evidence := proofs[proofIndex]?
            | throwError "the source numeral requires explicit evidence for its domain obligation"
          proofIndex := proofIndex + 1
          elabTermEnsuringType evidence (some type)
      unless ← isDefEq argument proof do return none
    else throwSemanticAmbiguity "the source numeral requires an actual declaration parameter"
  return some proofIndex

/-- Form only the source's actual point map, with its actual refinement comparison.
Reuse: NumeralEntry's last natural parameter and explicit proof obligations;
ObjectRefinement's checked shared telescope and directed identification. -/
private def numeralCandidate (row : NumeralEntry) (context : NumeralContext)
    (number : Nat) (expected : Expr) (proofs : Array Term) : TermElabM (Option Expr) := do
  let (object, comparison, proofIndex) ← match context with
    | .direct => pure (none, none, 0)
    | .selected value => pure (some value, none, 0)
    | .refinement entry => do
      let some refinement := entry.refines
        | throwError "a source numeral refinement has no declared comparison"
      discard <| checkedDeclaration entry.declaration
      discard <| checkedDeclaration refinement.identification
      let declaration ← mkConstWithFreshMVarLevels entry.declaration
      let (parameters, binders, _) ← forallMetaTelescopeReducing (← inferType declaration)
      let comparison ← applyObjectParameters entry.id.raw refinement.identification parameters
      let type ← whnfR (← inferType comparison)
      unless type.isAppOfArity ``CategoryTheory.Iso 4 do
        throwError "a source numeral refinement requires its complete native isomorphism"
      unless ← isDefEq type.getAppArgs[3]! expected do return none
      let some proofIndex ← completePointParameters parameters binders proofs 0 | return none
      pure (some (mkAppN declaration parameters), some comparison, proofIndex)
  let declaration ← mkConstWithFreshMVarLevels row.declaration
  let (arguments, binders, type) ← forallMetaTelescopeReducing (← inferType declaration)
  unless type.isAppOfArity ``Quiver.Hom 4 do
    throwError "a registered numeral requires its complete native point signature"
  let explicit := (List.range arguments.size).toArray.filter (binders[·]!.isExplicit)
  let some literal ← explicit.reverse.findM? fun index =>
      return (← inferType arguments[index]!).isConstOf ``Nat
    | throwError "a registered numeral has no declared natural parameter"
  if let some object := object then
    let some first := explicit[0]?
      | throwError "a registered numeral has no declared structural object parameter"
    unless ← isDefEq arguments[first]! object do return none
  unless ← isDefEq arguments[literal]! (mkNatLit number) do return none
  let target := type.getAppArgs[3]!
  let destination ← match comparison with
    | none => pure expected
    | some comparison => do
      let type ← whnfR (← inferType comparison)
      pure type.getAppArgs[2]!
  if row.over.isNone then
    let source ← sourceDomain expected
    let target ← sourceDomain target
    unless source.getAppFn.constName?.isSome &&
        source.getAppFn.constName? == target.getAppFn.constName? do return none
  unless ← isDefEq target destination do return none
  for index in explicit.filter (· > literal) do
    let proposition ← instantiateMVars (← inferType arguments[index]!)
    unless ← isProp proposition do
      throwError "a registered numeral's trailing obligations must be propositions"
  let some proofIndex ← completePointParameters arguments binders proofs proofIndex | return none
  unless proofIndex == proofs.size do
    throwError "the source numeral has evidence beyond its declared domain obligations"
  let point ← instantiateMVars (mkAppN declaration arguments)
  if point.hasMVar || point.hasLevelMVar then
    throwError "the registered source numeral is not determined at its complete boundary"
  let point ← match comparison with
    | none => pure point
    | some comparison => do
      let comparison ← instantiateMVars comparison
      let type ← whnfR (← inferType comparison)
      let hom ← mkAppM ``CategoryTheory.Iso.hom #[comparison]
      let categoryStructure ← mkAppOptM ``CategoryTheory.Category.toCategoryStruct
        #[some type.getAppArgs[0]!, some type.getAppArgs[1]!]
      let composition ← mkAppOptM ``CategoryTheory.CategoryStruct.comp
        #[some type.getAppArgs[0]!, some categoryStructure]
      elabAppArgs composition #[] #[Arg.expr point, Arg.expr hom] none false false
  let type ← inferType point
  unless type.isAppOfArity ``Quiver.Hom 4 do
    throwError "the admitted numeral is not a native point map"
  let source := type.getAppArgs[2]!
  let terminalPoint ← mkAppOptM ``default #[some source, none]
  return some (← elabAppArgs point #[] #[Arg.expr terminalPoint] (some expected) false false)

/-- Read a numeral from its independent point declarations, not a host OfNat instance.
Nat parameters use the kernel's natural literal. Point domains retain their original source
object identity; refinements require the actual registered object and directed comparison.
Source: Registry.Entry.NumeralEntry and ObjectRefinement, LC-15; #66 source intake contract. -/
opaque sourceNumeral (categoryOf : FVarId → TermElabM (Option NativeSourceCategory))
    (number : Nat) (expected : Expr) (proofs : Array Term := #[]) : TermElabM Expr := do
  if expected.headBeta.isConstOf ``Nat then
    unless proofs.isEmpty do throwError "a natural parameter literal has no domain obligations"
    return mkNatLit number
  let state ← semanticState
  let domain ← sourceDomain expected
  let bases := state.objects.filter fun entry =>
    entry.refines.isNone && domain.getAppFn.constName? == some entry.declaration
  let mut candidates : Array (NumeralEntry × NumeralContext) := #[]
  for row in state.numerals do
    discard <| checkedDeclaration row.declaration
    match row.over with
    | none => candidates := candidates.push (row, .direct)
    | some owner =>
      let #[category] := state.categories.filter (·.id == owner)
        | throwError "the source numeral requires one registered structural category"
      if bases.isEmpty then
        for declaration in ← getLCtx do
          unless expected.containsFVar declaration.fvarId do continue
          if let some selected ← categoryOf declaration.fvarId then
            if selected.role == .object && selected.expression.syntacticEq category.expression then
              discard <| checkedDeclaration category.declaration
              let family ← mkConstWithFreshMVarLevels category.declaration
              let (parameters, _, _) ← forallMetaTelescopeReducing (← inferType family)
              unless ← isDefEq selected.bundle (mkAppN family parameters) do
                throwError "the source numeral has a different complete structural category"
              candidates := candidates.push (row, .selected (mkFVar declaration.fvarId))
      for entry in state.objects.filter (·.category == owner) do
        if bases.isEmpty then
          if let some value := expected.find? fun value =>
              value.getAppFn.constName? == some entry.declaration then
            candidates := candidates.push (row, .selected value)
        if let some refinement := entry.refines then
          if bases.any (·.id == refinement.base) then
            candidates := candidates.push (row, .refinement entry)
  let hasSelectedStructure := candidates.any fun (_, context) =>
    match context with
    | .selected _ => true
    | _ => false
  if bases.isEmpty && !hasSelectedStructure then
    let defaults := state.objects.filter (·.notations.contains "literal.integral.domain")
    if defaults.size > 1 then
      throwSemanticAmbiguity "the source numeral has several integral-domain selectors"
    for base in defaults do
      let info ← getConstInfo base.declaration
      if let some body := info.value? then
        -- Native annotations can expose the selector's exact authored mathematical head.
        if body.headBeta.getAppFn.constName?.isSome &&
            body.headBeta.getAppFn.constName? == domain.getAppFn.constName? then
          discard <| checkedDeclaration base.declaration
          for row in state.numerals do
            if let some owner := row.over then
              for entry in state.objects.filter (·.category == owner) do
                if entry.refines.any (·.base == base.id) then
                  candidates := candidates.push (row, .refinement entry)
  let mut admitted := #[]
  for (row, context) in candidates do
    let applicable ← withoutModifyingState do
      return (← numeralCandidate row context number expected proofs).isSome
    if applicable then
      admitted := admitted.push (row, context)
  let #[(row, context)] := admitted
    | if admitted.isEmpty then
        throwError "no declared source point numeral was admitted in the supplied domain"
      else throwSemanticAmbiguity "several declared source point numerals apply in this domain"
  let some value ← numeralCandidate row context number expected proofs
    | throwError "the selected source numeral changed its admitted boundary"
  return value

end CasCompiler
