module

public import CasCompiler.Surface
public import CasCompiler.SourceTypeOrigin
public import CasCompiler.SourceMemberChoice
public import CasCompiler.SourceProof
public import Lean.Meta.Structure
public import Lean.Meta.Sym.SymM

public section

namespace CasCompiler

open Lean Meta Elab Term CasCatalogue



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
    return some (← liftM (m := MetaM) <| instantiateMVars (mkAppN declaration parameters))



opaque sourceMemberFamilyChoices (receiver : NativeSourceJudgement) (name : String)
    (qualification : Option String := none) :
    SourceReadM (Array (SourceMemberChoice (MorphismEntry × Nat))) := do
  let some selected := receiver.category | return #[]
  let state ← semanticState
  let qualified ← liftM (m := TermElabM) <| qualification.mapM (selectCategory state)
  let mut candidates : Array (MorphismEntry × Nat) := #[]
  for row in state.morphisms do
    unless row.name == name && qualified.all (·.id == row.category) do continue
    discard <| checkedDeclaration row.declaration
    let info ← liftM (m := MetaM) <| getConstInfo row.declaration
    let binders ← liftM (m := MetaM) <| withoutModifyingState do
      let (_, binders, _) ← forallMetaTelescopeReducing info.type
      return binders
    for slot in [:binders.size] do
      unless binders[slot]!.isExplicit do continue
      candidates := candidates.push (row, slot)
  return (← SourceMemberChoice.collectApplicable <| candidates.map fun (row, slot) => do
    let some original ← bindReceiver row receiver.value slot | return .ok none
    let original ← liftM (m := MetaM) <| instantiateMVars original
    if original.hasMVar || original.hasLevelMVar then
      liftM (m := TermElabM) <|
        throwUnsupportedSource "the selected member requires its complete declaration parameters"
    let parameters ← liftM (m := MetaM) <| original.getAppArgs.mapM fun parameter => do
      let parameter ← liftM (m := MetaM) <| instantiateMVars parameter
      let some constructor ← isConstructorApp? parameter | return parameter
      unless isStructure (← liftM (m := MetaM) getEnv) constructor.induct do return parameter
      let fields ← parameter.getAppArgs.mapM fun field =>
        withConfig (fun config => { config with zetaDelta := false }) <| withReducible (whnf field)
      let parameter ← Sym.foldProjs (mkAppN parameter.getAppFn fields)
      etaStructReduce parameter (fun _ => true)
    let #[category] := state.categories.filter (·.id == row.category)
      | liftM (m := TermElabM) <| throwError "the member family requires one complete result category"
    let (bundle, value) ← registeredExpressions (.inr row) category fun function _ => do
      unless ← isDefEq function original.getAppFn do
        liftM (m := TermElabM) <| throwError "the member family changed its whole source declaration"
      return mkAppN function parameters
    let original ← SourceReadM.select { value := original } (some (← inferType value))
    let proof ← SourceReadM.prove (← mkEq original value) fun proposition _ => do
      let proposition ← whnfR proposition
      unless proposition.isAppOfArity ``Eq 3 do
        throwError "the member family lost its original parameter agreement"
      mkExpectedTypeHint (← mkEqRefl proposition.getAppArgs[1]!) proposition
    let body ← liftM (m := MetaM) <| withLetDecl (← mkFreshUserName `memberParameterAgreement) (← inferType proof) proof
      fun binding => mkLetFVars #[binding] value
        (usedLetOnly := false) (generalizeNondepLet := false)
    let body ← liftM (m := MetaM) <| withLetDecl (← mkFreshUserName `memberReceiverCategory)
      (← inferType selected.bundle) selected.bundle fun binding => mkLetFVars #[binding] body
        (usedLetOnly := false) (generalizeNondepLet := false)
    let retained := (← SourceReadM.selection? value).getD { value }
    let category : NativeSourceCategory := ⟨.morphism, category.expression, bundle, none, none⟩
    let value ← SourceReadM.select { retained with value := body, category := some category }
    return .ok (some (← SourceMemberChoice.capture ⟨receiver, none⟩
      (row, slot) ⟨value, some category⟩))).1

opaque sourceMemberFamily (receiver : NativeSourceJudgement) (name : String)
    (qualification : Option String := none) : SourceReadM (Option NativeSourceJudgement) := do
  let choices ← sourceMemberFamilyChoices receiver name qualification
  if choices.isEmpty then return none
  let paths := choices.map (·.path)
  let preferred ← sourceMemberPreference name (paths.filterMap (·.receiver.category)) paths
  let surviving := match preferred with
    | none => choices
    | some selected => selected.filterMap fun (selection : Nat × Route) => choices[selection.1]?
  let #[chosen] := surviving
    | liftM (m := TermElabM) <|
      throwSemanticAmbiguity "several declared member parameters accept this selected receiver"
  chosen.withScope do
    return some (← retainMemberPreference chosen.judgement (preferred.bind fun selected =>
      selected[0]?.map fun (selection : Nat × Route) => selection.2))


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


def synthesizeDeclared (parameters : Array (Expr × BinderInfo)) : TermElabM Bool := do
  for (parameter, info) in parameters do
    if info.isInstImplicit && (← liftM (m := MetaM) <| instantiateMVars parameter).isMVar then
      let some instanceValue ← synthInstance? (← liftM (m := MetaM) <| instantiateMVars (← inferType parameter))
        | return false
      unless ← isDefEq parameter instanceValue do return false
  return true

private structure MemberSourceObject where
  entry : Option ObjectEntry
  value : Expr
  category : NativeSourceCategory




private partial def memberSourceObjects (value : Expr) : SourceReadM (Array MemberSourceObject) := do
  let retained ← match ← sourceTypeOrigin? value with
    | some origin => pure (some (origin.category, origin.object))
    | none => sourceObjectOrigin? value
  let original := retained.map (·.2) |>.getD value
  let (declared, entries) ← registeredSourceDomain original
  let entry ← match entries with
    | #[] => pure none
    | #[entry] => pure (some entry)
    | _ => liftM (m := TermElabM) <| throwSemanticAmbiguity "the member parameter requires its selected source object"
  if retained.isNone && entry.isNone then return #[]
  let category ← match retained with
    | some (category, _) => pure category
    | none => do
      let some entry := entry
        | liftM (m := TermElabM) <| throwError "the member parameter lost its already selected source row"
      let #[category] := (← semanticState).categories.filter (·.id == entry.category)
        | liftM (m := TermElabM) <| throwError "the member parameter requires its complete registered category"
      discard <| checkedDeclaration category.declaration
      let family ← mkConstWithFreshMVarLevels category.declaration
      let (parameters, _, _) ← forallMetaTelescopeReducing (← inferType family)
      let bundle := mkAppN family parameters
      unless ← isDefEq (← inferType original)
          (← mkAppM ``CategoryTheory.Bundled.α #[bundle]) do
        liftM (m := TermElabM) <| throwError "the member parameter changed its complete registered category"
      let bundle ← liftM (m := MetaM) <| instantiateMVars bundle
      discard <| SourceReadM.select (← sourceReferenceAt (.category category) bundle bundle)
      pure ⟨.object, category.expression, bundle,
        ← objectCarrierSelection entry bundle original, none⟩
  let mut found : Array MemberSourceObject := #[⟨entry, original, category⟩]


  unless category.role == .object && category.expression.syntacticEq (.atom CategoryId.sets) do
    return found
  if entry.isNone then return found
  let info ← getFunInfoNArgs declared.getAppFn declared.getAppNumArgs
  for argument in declared.getAppArgs, parameter in info.paramInfo do
    if parameter.isExplicit && !(← isProof argument) then
      found := found ++ (← memberSourceObjects argument)
  return found



private def memberRefinement? (base : MemberSourceObject) (entry : ObjectEntry)
    (expected : Expr) : SourceReadM (Option Expr) := do
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
    liftM (m := TermElabM) <| throwError "the member refinement requires its complete registered comparison"
  let some supplied ← alignSourceArguments? original.declaration parameters type.getAppArgs[3]!
      (← registeredSourceDomain base.value).1 | return none
  let arguments ← (parameters.zip supplied).mapM fun (parameter, supplied) => do
    match supplied with
    | some actual =>
      unless ← isDefEq parameter actual do
        liftM (m := TermElabM) <| throwError "the member refinement changed an original source parameter"
      pure actual
    | none => liftM (m := MetaM) <| instantiateMVars parameter
  let #[category] := (← semanticState).categories.filter (·.id == entry.category)
    | liftM (m := TermElabM) <| throwError "the member refinement requires its complete registered category"
  let (bundle, object) ← registeredExpressions (.inl entry) category fun function _ =>
    pure (mkAppN function arguments)
  let some carrier ← objectCarrierSelection entry bundle object
    | liftM (m := TermElabM) <| throwError "the member refinement lost its registered carrier comparison"
  let #[comparison] := carrier.comparisons
    | liftM (m := TermElabM) <| throwError "the member refinement changed its original comparison family"
  let type ← whnfR (← inferType comparison)
  unless type.isAppOfArity ``CategoryTheory.Iso 4 do
    liftM (m := TermElabM) <| throwError "the member refinement lost its native comparison type"
  let targetType ← mkAppM ``CategoryTheory.Bundled.α #[base.category.bundle]
  let targetStructure ← mkAppM ``CategoryTheory.Bundled.str #[base.category.bundle]
  let target ← annotateSourceObject base.category base.value
  let expected ← mkAppOptM ``CategoryTheory.Iso
    #[some targetType, some targetStructure, some type.getAppArgs[2]!, some target]
  unless ← (← get).context.withOriginalSources #[type, expected]
      (fun values => isDefEq values[0]! values[1]!) do return none
  let selected := (← SourceReadM.selection? comparison).getD { value := comparison }
  let comparison ← SourceReadM.select { selected with value := comparison } (some expected)
  let carrier := { carrier with comparisons := #[comparison] }
  return some (← annotateSourceObject
    ⟨.object, category.expression, bundle, some carrier, none⟩ object)




def sourceMorphismFrom? (name : String) (type : Expr)
    (selected : Option MorphismEntry := none) : SourceReadM (Option Expr) := do
  let rows ← match selected with
    | some row => do
      unless row.name == name do
        liftM (m := TermElabM) <| throwError "the selected morphism has another source name"
      pure #[row]
    | none => pure ((← semanticState).morphisms.filter (·.name == name))
  let (originalType, _) ← registeredSourceDomain type
  let mut found : Array (MorphismEntry × Expr × Expr) := #[]
  for row in rows do
    let (morphism, source, parameters) ← morphismAtSource row
    let applicable ← liftM (m := TermElabM) <| withoutModifyingState do
      unless ← withReducible (isDefEq source originalType) do return false
      unless ← synthesizeDeclared parameters do return false
      let morphism ← liftM (m := MetaM) <| instantiateMVars morphism
      return !morphism.hasMVar && !morphism.hasLevelMVar
    unless applicable do continue
    discard <| liftM (m := MetaM) <| withReducible (isDefEq source originalType)
    discard <| synthesizeDeclared parameters
    let morphism ← liftM (m := MetaM) <| instantiateMVars morphism
    found := found.push (row, morphism, ← inferType morphism)
  if found.isEmpty then
    let state ← semanticState
    let objects ← memberSourceObjects type
    for row in rows do
      let #[category] := state.categories.filter (·.id == row.category)
        | liftM (m := TermElabM) <| throwError "the selected member requires its complete category"
      let declaration ← checkedDeclaration row.declaration
      let count ← liftM (m := MetaM) <| forallTelescopeReducing declaration.type fun parameters _ => pure parameters.size
      for object in objects do
        let refinements := state.objects.filter fun entry =>
          object.entry.any fun base => entry.refines.any (·.base == base.id)
        let choices : Array (Option ObjectEntry) := #[none] ++ refinements.map some
        for choice in choices do
          for slot in [:count] do
            let prepare : SourceReadM (Option (Expr × Expr)) := do
              let previous ← liftM (m := MetaM) getMCtx
              let (morphism, source, parameters) ← morphismAtSource row
              let owned := (← liftM (m := MetaM) getMCtx).decls.foldl (fun result identity _ =>
                if previous.decls.contains identity then result else result.push identity) #[]
              let some (parameter, info) := parameters[slot]? | return none
              unless info.isExplicit do return none
              let expected ← inferType parameter
              let value ← match choice with
                | some refinement => memberRefinement? object refinement expected
                | none => do
                  unless ← isDefEq (← inferType object.value) expected do return none
                  let retained ← SourceReadM.selection? object.value
                  let same := retained.any fun source =>
                    SourceSelection.exactlyMatches Expr.equal source
                      { source with category := some object.category }
                  if same then pure (some object.value)
                  else pure (some (← annotateSourceObject object.category object.value))
              let some value := value | return none
              extendSourceApplicationScope owned
              unless ← isDefEq parameter value do return none
              unless ← isDefEq source originalType do return none
              unless ← synthesizeDeclared parameters do return none
              let morphism ← liftM (m := MetaM) <| instantiateMVars morphism
              let morphism := mkAppN morphism.getAppFn
                (morphism.getAppArgs.set! slot (← liftM (m := MetaM) <| instantiateMVars value))
              if morphism.hasMVar || morphism.hasLevelMVar then return none
              let arrow ← inferType morphism
              let arrow ← if arrow.isAppOfArity ``Quiver.Hom 4 then pure arrow else whnfR arrow
              unless arrow.isAppOfArity ``Quiver.Hom 4 do
                liftM (m := TermElabM) <| throwError "the selected member lost its native map type"
              let target := arrow.getAppArgs[3]!
              let target ← if ← isDefEq target originalType then pure type else pure target
              let args := arrow.getAppArgs
              let expected := mkAppN arrow.getAppFn #[args[0]!, args[1]!, type, target]
              return some (morphism, expected)
            unless ← SourceReadM.inspect (return (← prepare).isSome) do continue
            let some (morphism, expected) ← prepare | continue
            let duplicate := found.any fun (original, value, target) =>
              SourceSelection.exactlyMatches Expr.equal
                (sourceReference (.named (.registered (.inr original) category)) value)
                (sourceReference (.named (.registered (.inr row) category)) morphism) &&
                target.equal expected
            unless duplicate do found := found.push (row, morphism, expected)
  match found with
  | #[] => return none
  | #[(row, morphism, expected)] =>
    let #[category] := (← semanticState).categories.filter (·.id == row.category)
      | liftM (m := TermElabM) <| throwError "the selected member requires its complete category"
    let (_, value) ← registeredExpressions (.inr row) category (fun _ _ => pure morphism)
    let some retained ← SourceReadM.selection? value
      | liftM (m := TermElabM) <| throwError "the selected member lost its original source row"
    return some (← SourceReadM.select { retained with value := value } (some expected))
  | _ => liftM (m := TermElabM) <|
    throwSemanticAmbiguity s!"several registered morphisms {name} leave this set"



def sourceElementMemberChoices (name : String) (receiver : Option NativeSourceJudgement)
    (read : Expr → SourceReadM (Except MessageData Expr))
    (arguments : Option (Expr → SourceReadM (Except MessageData Expr))) :
    SourceReadM (Array (SourceMemberChoice MorphismEntry) × Array MessageData) := do
  if receiver.any (fun receiver => receiver.category.isSome) then return (#[], #[])
  let state ← semanticState
  SourceMemberChoice.collectApplicable <|
    (state.morphisms.filter (·.name == name)).map fun row => do
      let previous ← liftM (m := MetaM) getMCtx
      let (morphism, whole, parameters) ← morphismAtSource row
      let owned := (← liftM (m := MetaM) getMCtx).decls.foldl (fun result identity _ =>
        if previous.decls.contains identity then result else result.push identity) #[]
      let source ← match arguments with
        | none => pure (some whole)
        | some _ => do
          let pair ← whnfR whole
          if pair.isAppOfArity ``Prod 2 then pure (some pair.getAppArgs[0]!) else pure none
      let some source := source | return .ok none
      let elementResult : Except MessageData (Option Expr) ← match receiver with
        | some receiver => do
          let (type, _) ← registeredSourceDomain (← inferType receiver.value)
          unless ← liftM (m := MetaM) <| withReducible (isDefEq source type) do return .ok none
          unless ← synthesizeDeclared parameters do return .ok none
          if (← liftM (m := MetaM) <| instantiateMVars morphism).hasMVar then return .ok none
          pure (.ok (some receiver.value))
        | none => do
          unless ← synthesizeDeclared parameters do return .ok none
          let source ← liftM (m := MetaM) <| instantiateMVars source
          if source.hasMVar || source.hasLevelMVar then return .ok none
          match ← read source with
          | .ok element => pure (.ok (some element))
          | .error message => return .error message
      let element ← match elementResult with
        | .ok (some element) => pure element
        | .ok none => return .ok none
        | .error message => return .error message
      extendSourceApplicationScope owned
      let morphism ← liftM (m := MetaM) <| instantiateMVars morphism
      let #[category] := state.categories.filter (·.id == row.category)
        | liftM (m := TermElabM) <| throwError "the element member lost its complete registered category"
      let (_, selected) ← registeredExpressions (.inr row) category (fun _ _ => pure morphism)
      let function ← sourceSetFunction selected
      let argumentResult : Except MessageData Expr ← match arguments with
        | none => pure (.ok element)
        | some read => do
          let pair ← whnfR (← liftM (m := MetaM) <| instantiateMVars whole)
          match ← read pair.getAppArgs[1]! with
          | .ok value => pure (.ok (← mkAppM ``Prod.mk #[element, value]))
          | .error message => pure (.error message)
      let argument ← match argumentResult with
        | .ok value => pure value
        | .error message => return .error message
      let applied ← elabSourceApplicationApplicableScoped function #[Syntax.missing] none
        fun _ expected => do
          if ← isDefEq (← inferType argument) expected then return .ok argument
          let retained := (← SourceReadM.selection? argument).getD { value := argument }
          return .ok (← SourceReadM.select { retained with value := argument } (some expected))
      let value ← match applied with
        | .ok (value, _) => pure value
        | .error message => return .error message
      return .ok (some (← SourceMemberChoice.capture
        ⟨receiver.getD ⟨element, none⟩, none⟩ row ⟨value, none⟩))

def sourceElementMember? (name : String) (receiver : Option NativeSourceJudgement)
    (read : Expr → SourceReadM Expr) (arguments : Option (Expr → SourceReadM Expr)) :
    SourceReadM (Option Expr) := do
  let (found, mismatches) ← sourceElementMemberChoices name receiver
    (fun type => do return .ok (← read type))
    (arguments.map fun read type => do return .ok (← read type))
  match found with
  | #[] =>
    if let some message := mismatches[0]? then liftM (m := TermElabM) <| throwError message
    return none
  | #[chosen] => chosen.withScope (pure (some chosen.judgement.value))
  | _ => liftM (m := TermElabM) <|
    throwSemanticAmbiguity s!"several registered morphisms {name} accept this element"

end CasCompiler
