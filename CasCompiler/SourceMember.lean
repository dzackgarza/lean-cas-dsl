module

public import CasCompiler.Surface
public import CasCompiler.SourceTypeOrigin
public import CasCompiler.SourceMemberChoice
public import Lean.Meta.Structure
public import Lean.Meta.Sym.SymM

public section

namespace CasCompiler

open Lean Meta Elab Term CasCatalogue

-- Reuse Language.bindSelectedReceiver's native structure telescope. All fields remain
-- metavariables until the complete receiver type determines them; no instance is chosen.
private def bindReceiver (row : MorphismEntry) (receiver : Expr) (slot : Nat) :
    MetaM (Option Expr) := do
  discard <| checkedDeclaration row.declaration
  let declaration ← mkConstWithFreshMVarLevels row.declaration
  let (parameters, binders, _) ← forallMetaTelescopeReducing (← inferType declaration)
  let some parameter := parameters[slot]? | return none
  unless binders[slot]!.isExplicit do return none
  withConfig (fun config => { config with zetaDelta := false }) do
    unless ← expandSourceStructures (parameters.take slot) do return none
    unless ← isDefEq (← inferType parameter) (← inferType receiver) <&&>
        isDefEq parameter receiver do return none
    return some (← instantiateMVars (mkAppN declaration parameters))

/-- Prepare every registered family indexed by the actual selected receiver.
Reuse: Language.invariantOf's unique typed receiver rule, native declaration telescopes,
Lean.Meta.etaStructReduce and the registered morphism boundary check. -/
opaque sourceMemberFamilyChoices (receiver : NativeSourceJudgement) (name : String)
    (qualification : Option String := none) :
    TermElabM (Array (SourceMemberChoice (MorphismEntry × Nat))) := do
  let original ← saveState
  try
    prepare original
  finally
    original.restore
where
  prepare (originalState : Lean.Elab.Term.SavedState) :
       TermElabM (Array (SourceMemberChoice (MorphismEntry × Nat))) := do
    let some selected := receiver.category
      | return #[]
    let state ← semanticState
    let qualified ← qualification.mapM (selectCategory state)
    let mut candidates : Array (SourceMemberChoice (MorphismEntry × Nat)) := #[]
    for row in state.morphisms do
      unless row.name == name && qualified.all (·.id == row.category) do continue
      discard <| checkedDeclaration row.declaration
      let info ← getConstInfo row.declaration
      let binders ← withoutModifyingState do
        let (_, binders, _) ← forallMetaTelescopeReducing info.type
        return binders
      for slot in [:binders.size] do
        unless binders[slot]!.isExplicit do continue
        originalState.restore
        let some original ← bindReceiver row receiver.value slot | continue
        let original ← instantiateMVars original
        if original.hasMVar || original.hasLevelMVar then
          throwUnsupportedSource "the selected member requires its complete declaration parameters"
        -- Contract only native structure eta terms back to their original projected owners.
        -- Lean.Meta.Structure.etaStructReduce requires the same actual owner in every field.
        let parameters ← original.getAppArgs.mapM fun parameter => do
          let parameter ← instantiateMVars parameter
          let some constructor ← isConstructorApp? parameter | return parameter
          unless isStructure (← getEnv) constructor.induct do return parameter
          let fields ← parameter.getAppArgs.mapM fun field =>
            withConfig (fun config => { config with zetaDelta := false }) <| withReducible (whnf field)
          let parameter ← Sym.foldProjs (mkAppN parameter.getAppFn fields)
          etaStructReduce parameter (fun _ => true)
        let #[category] := state.categories.filter (·.id == row.category)
          | throwError "the member family requires one complete result category"
        let (bundle, value) ← registeredExpressions (.inr row) category fun function _ => do
          unless ← isDefEq function original.getAppFn do
            throwError "the member family changed its whole source declaration"
          return mkAppN function parameters
        let value ← instantiateMVars value
        let proof ← mkExpectedTypeHint (← mkEqRefl original) (← mkEq original value)
        checkWithKernel proof
        let value ← withLetDecl (← mkFreshUserName `memberParameterAgreement) (← inferType proof) proof
          fun binding => mkLetFVars #[binding] value
            (usedLetOnly := false) (generalizeNondepLet := false)
        -- Keep the receiver's full chosen category beside the application as native data.
        let value ← withLetDecl (← mkFreshUserName `memberReceiverCategory)
          (← inferType selected.bundle) selected.bundle fun binding => mkLetFVars #[binding] value
            (usedLetOnly := false) (generalizeNondepLet := false)
        candidates := candidates.push {
          path := ⟨receiver, none⟩
          evidence := (row, slot)
          judgement := ⟨value, some ⟨.morphism, category.expression, bundle, none, none⟩⟩
          nativeState := ← saveState }
    return candidates

opaque sourceMemberFamily (receiver : NativeSourceJudgement) (name : String)
    (qualification : Option String := none) : TermElabM (Option NativeSourceJudgement) := do
  let choices ← sourceMemberFamilyChoices receiver name qualification
  if choices.isEmpty then return none
  let paths := choices.map (·.path)
  let preferred : Option (Array (Nat × Route)) ←
    sourceMemberPreference name (paths.filterMap (·.receiver.category)) paths
  let surviving := match preferred with
    | none => choices
    | some selected => selected.filterMap fun (selection : Nat × Route) => choices[selection.1]?
  let #[chosen] := surviving
    | throwSemanticAmbiguity "several declared member parameters accept this selected receiver"
  chosen.nativeState.restore
  return some (retainMemberPreference chosen.judgement (preferred.bind fun selected =>
    selected[0]?.map fun (selection : Nat × Route) => selection.2))

/-- A registered morphism named `name` at fresh declaration parameters, with its source set. -/
def morphismAtSource (row : MorphismEntry) :
    TermElabM (Expr × Expr × Array (Expr × BinderInfo)) := do
  discard <| checkedDeclaration row.declaration
  let declaration ← mkConstWithFreshMVarLevels row.declaration
  let (parameters, infos, _) ← forallMetaTelescopeReducing (← inferType declaration)
  let morphism := mkAppN declaration parameters
  let type ← whnfR (← inferType morphism)
  unless type.isAppOfArity ``Quiver.Hom 4 do
    throwError "the registered morphism {row.id.raw} is not a native map"
  return (morphism, type.getAppArgs[2]!, parameters.zip infos)

/-- Synthesize the declared instances of a morphism once its source fixed the parameters. -/
def synthesizeDeclared (parameters : Array (Expr × BinderInfo)) : TermElabM Bool := do
  for (parameter, info) in parameters do
    if info.isInstImplicit && (← instantiateMVars parameter).isMVar then
      let some instanceValue ← synthInstance? (← instantiateMVars (← inferType parameter))
        | return false
      unless ← isDefEq parameter instanceValue do return false
  return true

private structure MemberSourceObject where
  entry : Option ObjectEntry
  value : Expr
  category : NativeSourceCategory

/-- Inspect only the original registered domain and its explicit object parameters.
Owner envelopes are consumed through their checked codec; their proof, comparison and
carrier fields are never searched for another possible source object. -/
private partial def memberSourceObjects (value : Expr) : TermElabM (Array MemberSourceObject) := do
  let retained ← match ← sourceTypeOrigin? value with
    | some origin => pure (some (origin.category, origin.object))
    | none => sourceObjectOrigin? value
  let original := retained.map (·.2) |>.getD value
  let (declared, entries) ← registeredDomain original
  let entry ← match entries with
    | #[] => pure none
    | #[entry] => pure (some entry)
    | _ => throwSemanticAmbiguity "the member parameter requires its selected source object"
  if retained.isNone && entry.isNone then return #[]
  let category ← match retained with
    | some (category, _) => pure category
    | none => do
      let some entry := entry
        | throwError "the member parameter lost its already selected source row"
      let #[category] := (← semanticState).categories.filter (·.id == entry.category)
        | throwError "the member parameter requires its complete registered category"
      discard <| checkedDeclaration category.declaration
      let family ← mkConstWithFreshMVarLevels category.declaration
      let (parameters, _, _) ← forallMetaTelescopeReducing (← inferType family)
      let bundle := mkAppN family parameters
      unless ← isDefEq (← inferType original)
          (← mkAppM ``CategoryTheory.Bundled.α #[bundle]) do
        throwError "the member parameter changed its complete registered category"
      let bundle ← instantiateMVars bundle
      let bundle := sourceReference ``NamedCategoryEntry category.id.raw category.declaration bundle
      pure ⟨.object, category.expression, bundle,
        ← objectCarrierSelection entry bundle original, none⟩
  let mut found : Array MemberSourceObject := #[⟨entry, original, category⟩]
  -- A selected structured owner supplies only its own structure. In particular its
  -- underlying named carrier cannot be promoted to another registered structure.
  unless category.role == .object && category.expression.syntacticEq (.atom CategoryId.sets) do
    return found
  if entry.isNone then return found
  let info ← getFunInfoNArgs declared.getAppFn declared.getAppNumArgs
  for argument in declared.getAppArgs, parameter in info.paramInfo do
    if parameter.isExplicit && !(← isProof argument) then
      found := found ++ (← memberSourceObjects argument)
  return found

/-- Specialize an authored refinement at the original named base's complete arguments.
The comparison keeps that actual base occurrence and complete category in its native type. -/
private def memberRefinement? (base : MemberSourceObject) (entry : ObjectEntry)
    (expected : Expr) : TermElabM (Option Expr) := do
  let some original := base.entry | return none
  let some refinement := entry.refines | return none
  unless refinement.base == original.id &&
      base.category.expression.syntacticEq (.atom CategoryId.sets) do return none
  discard <| checkedDeclaration entry.declaration
  discard <| checkedDeclaration refinement.identification
  let declaration ← mkConstWithFreshMVarLevels entry.declaration
  let (parameters, _, result) ← forallMetaTelescopeReducing (← inferType declaration)
  unless ← isDefEq result expected do return none
  let comparison ← applyObjectParameters entry.id.raw refinement.identification parameters
  let type ← whnfR (← inferType comparison)
  unless type.isAppOfArity ``CategoryTheory.Iso 4 do
    throwError "the member refinement requires its complete registered comparison"
  let some supplied ← alignSourceArguments? original.declaration parameters type.getAppArgs[3]!
      (← sourceDomain base.value) | return none
  let arguments ← (parameters.zip supplied).mapM fun (parameter, supplied) => do
    match supplied with
    | some actual =>
      unless ← isDefEq parameter actual do
        throwError "the member refinement changed an original source parameter"
      pure actual
    | none => instantiateMVars parameter
  let #[category] := (← semanticState).categories.filter (·.id == entry.category)
    | throwError "the member refinement requires its complete registered category"
  let (bundle, object) ← registeredExpressions (.inl entry) category fun function _ =>
    pure (mkAppN function arguments)
  let some carrier ← objectCarrierSelection entry bundle object
    | throwError "the member refinement lost its registered carrier comparison"
  let #[comparison] := carrier.comparisons
    | throwError "the member refinement changed its original comparison family"
  let type ← whnfR (← inferType comparison)
  unless type.isAppOfArity ``CategoryTheory.Iso 4 do
    throwError "the member refinement lost its native comparison type"
  let targetType ← mkAppM ``CategoryTheory.Bundled.α #[base.category.bundle]
  let targetStructure ← mkAppM ``CategoryTheory.Bundled.str #[base.category.bundle]
  let target ← annotateSourceObject base.category base.value
  let expected ← mkAppOptM ``CategoryTheory.Iso
    #[some targetType, some targetStructure, some type.getAppArgs[2]!, some target]
  unless ← isDefEq type expected do return none
  let comparison ← mkExpectedTypeHint comparison expected
  let carrier := { carrier with comparisons := #[comparison] }
  return some (← annotateSourceObject
    ⟨.object, category.expression, bundle, some carrier, none⟩ object)

/-- The registered morphism named `name` whose source is the set `type`, at the declaration
parameters that reducible unification determines (`d/dx` on `ℚ[x]`). -/
def sourceMorphismFrom? (name : String) (type : Expr)
    (selected : Option MorphismEntry := none) : TermElabM (Option Expr) := do
  let rows ← match selected with
    | some row => do
      unless row.name == name do throwError "the selected morphism has another source name"
      pure #[row]
    | none => do pure ((← semanticState).morphisms.filter (·.name == name))
  let mut found := #[]
  for row in rows do
    let (morphism, source, parameters) ← morphismAtSource row
    let applicable ← withoutModifyingState do
      unless ← withReducible (isDefEq source type) do return false
      unless ← synthesizeDeclared parameters do return false
      return !(← instantiateMVars morphism).hasMVar
    unless applicable do continue
    discard <| withReducible (isDefEq source type)
    discard <| synthesizeDeclared parameters
    found := found.push (sourceReference ``MorphismEntry row.id.raw row.declaration
      (← instantiateMVars morphism))
  if found.isEmpty then
    -- The actual declared domain may retain an original object parameter (the scalar of
    -- the vectors supplied to span). Only that selected object, or an authored refinement
    -- of its exact named base, can supply an otherwise undetermined member parameter.
    let state ← semanticState
    let objects ← memberSourceObjects type
    for row in rows do
      let declaration ← checkedDeclaration row.declaration
      let count ← forallTelescopeReducing declaration.type
        fun parameters _ => pure parameters.size
      for object in objects do
        let refinements := state.objects.filter fun entry =>
          object.entry.any fun base => entry.refines.any (·.base == base.id)
        let choices : Array (Option ObjectEntry) := #[none] ++ refinements.map some
        for choice in choices do
          for slot in [:count] do
            let applied ← withoutModifyingState do
              let (morphism, source, parameters) ← morphismAtSource row
              let some (parameter, info) := parameters[slot]? | return none
              unless info.isExplicit do return none
              let expected ← inferType parameter
              let value ← match choice with
                | some refinement => memberRefinement? object refinement expected
                | none => do
                  unless ← isDefEq (← inferType object.value) expected do return none
                  pure (some (← annotateSourceObject object.category object.value))
              let some value := value | return none
              unless ← isDefEq parameter value do return none
              unless ← isDefEq source type do return none
              unless ← synthesizeDeclared parameters do return none
              let morphism ← instantiateMVars morphism
              -- Native unification may erase inert metadata. Rebuild this declared slot
              -- from the actual checked owner, rather than a reduced carrier assignment.
              let morphism := mkAppN morphism.getAppFn
                (morphism.getAppArgs.set! slot (← instantiateMVars value))
              if morphism.hasMVar || morphism.hasLevelMVar then return none
              -- Preserve the actual source domain and every original comparison in the
              -- parameter. Native conversion checks this complete instantiated boundary.
              let arrow ← whnfR (← inferType morphism)
              let target := arrow.getAppArgs[3]!
              let target ← if ← isDefEq target type then pure type else pure target
              let args := arrow.getAppArgs
              let morphism := sourceReference ``MorphismEntry row.id.raw row.declaration morphism
              let applied ← mkExpectedTypeHint morphism
                (mkAppN arrow.getAppFn #[args[0]!, args[1]!, type, target])
              return some (sourceDerivedReference ``MorphismEntry row.id.raw row.declaration applied)
            if let some applied := applied then
              -- Repeated occurrences of the exact same original parameter give the same
              -- expression. Equal carriers or different retained origins are not merged.
              unless found.contains applied do found := found.push applied
  match found with
  | #[] => return none
  | #[morphism] => return some morphism
  | _ => throwSemanticAmbiguity s!"several registered morphisms {name} leave this set"

/-- `x.m()` for an element `x`: the registered morphism `m` whose source is the set `x` lies in,
applied to `x`. Its declaration parameters are those that reducible unification of its source
with the element's type determines. `read` reads the receiver at a candidate's source when the
receiver has no type of its own (a numeral). Source: the original reader's method call on an
element; Registry.Entry.MorphismEntry. Several applicable morphisms are ambiguous. -/
def sourceElementMemberChoices (name : String) (receiver : Option NativeSourceJudgement)
    (read : Expr → TermElabM (Except MessageData Expr))
    (arguments : Option (Expr → TermElabM (Except MessageData Expr))) :
    TermElabM (Array (SourceMemberChoice MorphismEntry) × Array MessageData) := do
  let original ← saveState
  try
    prepare original
  finally
    original.restore
where
  prepare (originalState : Lean.Elab.Term.SavedState) :
       TermElabM (Array (SourceMemberChoice MorphismEntry) × Array MessageData) := do
    -- A receiver already selected as a categorical object or morphism cannot
    -- enter the element candidate branch below. Reject that shape before
    -- opening any unrelated registered map telescope.
    if receiver.any (fun receiver => receiver.category.isSome) then return (#[], #[])
    let state ← semanticState
    let mut found : Array (SourceMemberChoice MorphismEntry) := #[]
    let mut mismatches : Array MessageData := #[]
    for row in state.morphisms do
      unless row.name == name do continue
      originalState.restore
      let (morphism, whole, parameters) ← morphismAtSource row
      -- With further arguments the source is the pair of the receiver's set and theirs.
      let source ← match arguments with
        | none => pure whole
        | some _ => do
          let pair ← whnfR whole
          unless pair.isAppOfArity ``Prod 2 do continue
          pure pair.getAppArgs[0]!
      let element ← match receiver with
        | some receiver => do
          unless receiver.category.isNone do continue
          let type ← instantiateMVars (← inferType receiver.value)
          unless ← withReducible (isDefEq source type) do continue
          unless ← synthesizeDeclared parameters do continue
          if (← instantiateMVars morphism).hasMVar then continue
          pure receiver.value
        | none => do
          unless ← synthesizeDeclared parameters do continue
          let source ← instantiateMVars source
          if source.hasMVar || source.hasLevelMVar then continue
          match ← read source with
          | .ok element => pure element
          | .error message =>
            mismatches := mismatches.push (← addMessageContext message)
            continue
      let morphism ← instantiateMVars morphism
      let function ← sourceSetFunction (sourceReference ``MorphismEntry row.id.raw row.declaration
        morphism)
      let argument ← match arguments with
        | none => pure element
        | some read => do
          let pair ← whnfR (← instantiateMVars ((← whnfR (← inferType morphism)).getAppArgs[2]!))
          match ← read pair.getAppArgs[1]! with
          | .ok value => mkAppM ``Prod.mk #[element, value]
          | .error message =>
            mismatches := mismatches.push (← addMessageContext message)
            continue
      let value ← elabAppArgs function #[] #[Arg.expr argument] none false false
      found := found.push {
        path := ⟨receiver.getD ⟨element, none⟩, none⟩
        evidence := row
        judgement := ⟨value, none⟩
        nativeState := ← saveState }
    return (found, mismatches)

def sourceElementMember? (name : String) (receiver : Option NativeSourceJudgement)
    (read : Expr → TermElabM Expr) (arguments : Option (Expr → TermElabM Expr)) :
    TermElabM (Option Expr) := do
  let (found, mismatches) ← sourceElementMemberChoices name receiver
    (fun type => do return .ok (← read type))
    (arguments.map fun read type => do return .ok (← read type))
  match found with
  | #[] =>
    if let some message := mismatches[0]? then throwError message
    return none
  | #[chosen] =>
    chosen.nativeState.restore
    return some chosen.judgement.value
  | _ => throwSemanticAmbiguity s!"several registered morphisms {name} accept this element"

end CasCompiler
