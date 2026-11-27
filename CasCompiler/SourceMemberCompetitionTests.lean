module

import CasCompiler.Read
import CasCompiler.SourceTestSupport
import CasCompiler.ReadMember
import CasCompiler.ReadDispatch
import CasCompiler.SourcePropertyQualification
import LeanCategories.Catalogue
public meta import Lean.Elab.Command
meta import CasCompiler.Read
meta import CasCompiler.SourceTestSupport
meta import CasCompiler.ReadMember
meta import CasCompiler.ReadDispatch
meta import CasCompiler.SourcePropertyQualification
meta import LeanCategories.Catalogue

namespace CasCompiler.SourceMemberCompetitionTests

open Lean Meta Elab Term CasCatalogue

private def sourceTerm (text : String) : TermElabM (TSyntax `cas_term) := do
  let .ok source := Parser.runParserCategory (← liftM (m := CoreM) getEnv) `cas_term text
    | liftM (m := MetaM) <| throwError "the member competition control did not parse"
  return ⟨source⟩

private def readMember (context : ReadContext) (receiver : TSyntax `cas_term)
    (name : String) (arguments : Array (TSyntax `cas_term)) :
    SourceReadM NativeSourceJudgement := do
  match ← SourceReader.memberCompleting context (checkReadJudgementApplicable context)
      receiver name arguments with
  | .ok value => pure value
  | .error message => liftM (m := MetaM) <| throwError message

private def memberContext (source : TSyntax `cas_term) (reads : IO.Ref Nat)
    (project : NativeSourceJudgement → String → Array (TSyntax `cas_term) →
      SourceReadM (Option NativeSourceJudgement)) : ReadContext := {
  categoryOf := fun _ => pure none
  source
  expected := none
  qualification := none
  expectedCategory := none
  project
  read := fun categoryOf source expected qualification expectedCategory => do
    liftM (m := IO) <| reads.modify (· + 1)
    readExpressionApplicable categoryOf source expected qualification expectedCategory
}





run_cmd Lean.Elab.Command.liftTermElabM do
  let identities ← liftM (m := IO) CasRuntime.IdentitySupply.new
  let session ← SourceSession.empty identities
  discard <| session.elaborateJudgementsScoped Syntax.missing do
    let source ← sourceTerm "Fin(3).is_finite()"
    let receiver ← sourceTerm "Fin(3)"
    let reads ← liftM (m := IO) <| IO.mkRef (0 : Nat)
    let projects ← liftM (m := IO) <| IO.mkRef (0 : Nat)
    let declarations ← liftM (m := IO) <| IO.mkRef (#[] : Array Name)
    let context := memberContext source reads fun _ name arguments => do
      unless name == "is_finite" && arguments.isEmpty do
        liftM (m := MetaM) <| throwError "the competing projection lost its original member call"
      liftM (m := IO) <| projects.modify (· + 1)
      let name ← mkAuxDeclName `competingMemberProjection
      addDecl (.defnDecl {
        name
        levelParams := []
        type := mkConst ``Nat
        value := mkNatLit 0
        hints := .abbrev
        safety := .safe })
      liftM (m := IO) <| declarations.modify (·.push name)
      return some ⟨mkConst name, none⟩
    let failure : Option Exception ← try
      discard <| readMember context receiver "is_finite" #[]
      pure none
    catch error => pure (some error)
    let some failure := failure
      | liftM (m := MetaM) <| throwError "a projection displaced a simultaneously applicable property"
    unless CasCatalogue.Exception.isSemanticAmbiguity failure do throw failure
    unless (← liftM (m := IO) reads.get) == 1 && (← liftM (m := IO) projects.get) == 1 do
      liftM (m := MetaM) <| throwError "member competition reread its receiver or replayed a selected projection"
    for name in ← liftM (m := IO) declarations.get do
      if ((← liftM (m := CoreM) getEnv).setExporting false).contains name then
        liftM (m := MetaM) <| throwError "an ambiguous member retained a speculative native declaration"



    let selectedReceiver ← readExpression (fun _ => pure none) receiver none
    liftM (m := IO) <| reads.set 0
    liftM (m := IO) <| projects.set 0
    liftM (m := IO) <| declarations.set #[]
    discard <| SourceReadM.inspect do
      let candidates ← SourceReader.memberChoicesAtReceiver context selectedReceiver "is_finite" #[] none
      unless candidates.choices.size == 2 do
        liftM (m := MetaM) <| throwError "the formed-receiver entrance lost a competing native reading"
      let failure : Option Exception ← try
        discard <| SourceReader.completeMemberChoices context (checkReadJudgementApplicable context)
          "is_finite" #[] candidates.considered candidates.choices candidates.mismatches
        pure none
      catch error => pure (some error)
      let some failure := failure
        | liftM (m := MetaM) <| throwError "discovery selected an ambiguous member"
      unless CasCatalogue.Exception.isSemanticAmbiguity failure do throw failure
      unless (← liftM (m := IO) reads.get) == 0 && (← liftM (m := IO) projects.get) == 1 do
        liftM (m := MetaM) <| throwError "discovery reread the receiver or replayed a candidate"
      return true



    liftM (m := IO) <| reads.set 0
    liftM (m := IO) <| projects.set 0
    liftM (m := IO) <| declarations.set #[]
    let result ← readMember { context with expected := some (mkSort .zero) }
      receiver "is_finite" #[]
    let #[classifier] := (← semanticState).classifiers.filter (·.id == ClassifierId.setsFinite)
      | liftM (m := MetaM) <| throwError "the original finiteness classifier is absent or ambiguous"
    let finite ← mkAppM ``CasCatalogue.Foundation.Objects.fin #[mkNatLit 3]
    let expected ← elabAppArgs (← mkConstWithFreshMVarLevels ``CasCatalogue.Classifier.Holds)
      #[] #[Arg.expr (← classifierInstance classifier), Arg.expr finite] none false false
    SourceTest.checkOriginal #[result.value, expected] fun native => do
      unless ← isDefEq native[0]! native[1]! do
        liftM (m := MetaM) <| throwError "the surviving member changed its independently declared property"
    checkWithKernel result.value
    unless (← liftM (m := IO) reads.get) == 1 && (← liftM (m := IO) projects.get) == 1 do
      liftM (m := MetaM) <| throwError "member result checking reread source or replayed a candidate"
    for name in ← liftM (m := IO) declarations.get do
      if ((← liftM (m := CoreM) getEnv).setExporting false).contains name then
        liftM (m := MetaM) <| throwError "a native-domain mismatch retained a rejected projection declaration"
    pure #[]



run_cmd Lean.Elab.Command.liftTermElabM do
  let identities ← liftM (m := IO) CasRuntime.IdentitySupply.new
  let session ← SourceSession.empty identities
  discard <| session.elaborateJudgementsScoped Syntax.missing do
    let source ← sourceTerm "Fin(3).retained_native_projection()"
    let receiver ← sourceTerm "Fin(3)"
    let reads ← liftM (m := IO) <| IO.mkRef (0 : Nat)
    let projects ← liftM (m := IO) <| IO.mkRef (0 : Nat)
    let introduced ← liftM (m := IO) <| IO.mkRef (none : Option Name)
    let context := memberContext source reads fun _ name arguments => do
      unless name == "retained_native_projection" && arguments.isEmpty do
        liftM (m := MetaM) <| throwError "the retained projection changed its original member call"
      liftM (m := IO) <| projects.modify (· + 1)
      let name ← mkAuxDeclName `retainedMemberProjection
      addDecl (.defnDecl {
        name
        levelParams := []
        type := mkConst ``Nat
        value := mkNatLit 7
        hints := .abbrev
        safety := .safe })
      liftM (m := IO) <| introduced.set (some name)
      return some ⟨mkConst name, none⟩
    let result ← readMember context receiver "retained_native_projection" #[]
    let some name ← liftM (m := IO) introduced.get
      | liftM (m := MetaM) <| throwError "the selected projection callback was not executed"
    unless (← liftM (m := IO) reads.get) == 1 && (← liftM (m := IO) projects.get) == 1 && result.value == Lean.mkConst name do
      liftM (m := MetaM) <| throwError "member selection replaced or replayed the original checked native result"
    unless ((← liftM (m := CoreM) getEnv).setExporting false).contains name do
      liftM (m := MetaM) <| throwError "member selection discarded its original checked native environment"
    checkWithKernel result.value
    pure #[]



run_cmd Lean.Elab.Command.liftTermElabM do
  let identities ← liftM (m := IO) CasRuntime.IdentitySupply.new
  let session ← SourceSession.empty identities
  discard <| session.elaborateJudgementsScoped Syntax.missing do
    let source ← sourceTerm "Fin(3).is_finite()"
    let receiver ← sourceTerm "Fin(3)"
    let reads ← liftM (m := IO) <| IO.mkRef (0 : Nat)
    let introduced ← liftM (m := IO) <| IO.mkRef (none : Option Name)
    let originalFailure ← liftM (m := IO) <|
      registerInternalExceptionId `CasCompiler.tests.originalMemberStateFailure
    let context := memberContext source reads fun _ _ _ => do
      let name ← mkAuxDeclName `failedMemberProjection
      addDecl (.defnDecl {
        name
        levelParams := []
        type := mkConst ``Nat
        value := mkNatLit 1
        hints := .abbrev
        safety := .safe })
      liftM (m := IO) <| introduced.set (some name)
      throw (Exception.internal originalFailure)
    let failure : Option Exception ← try
      discard <| readMember context receiver "is_finite" #[]
      pure none
    catch error => pure (some error)
    let some (.internal actual _) := failure
      | liftM (m := MetaM) <| throwError "a failed member callback lost its original native exception"
    unless actual == originalFailure do
      liftM (m := MetaM) <| throwError "a failed member callback was relabelled or retried"
    let some name ← liftM (m := IO) introduced.get
      | liftM (m := MetaM) <| throwError "the failed member control never reached its actual callback"
    if ((← liftM (m := CoreM) getEnv).setExporting false).contains name then
      liftM (m := MetaM) <| throwError "a failed member callback retained its speculative native declaration"
    pure #[]

private def preference? (value : Expr) : SourceReadM (Option (Array EdgeRef)) := do
  return (← SourceReadM.selection? value).bind (·.preferredRoute)




run_cmd Lean.Elab.Command.liftTermElabM do
  let identities ← liftM (m := IO) CasRuntime.IdentitySupply.new
  let session ← SourceSession.empty identities
  discard <| session.elaborateJudgementsScoped Syntax.missing do
    let source ← sourceTerm "Fin(3)"
    let reads ← liftM (m := IO) <| IO.mkRef (0 : Nat)
    let fallbackCalls ← liftM (m := IO) <| IO.mkRef (0 : Nat)
    let context := memberContext source reads fun _ _ _ => pure none
    let failing : ReadCompletingRule := fun context complete => do
      let value ← context.readExpression context.categoryOf context.source none
      discard <| complete value
      throwReadRuleMismatch
    let fallback : ReadCompletingRule := fun _ complete => do
      liftM (m := IO) <| fallbackCalls.modify (· + 1)
      complete ⟨mkNatLit 0, none⟩
    let failure : Option Exception ← try
      discard <| readWithCompletingRules #[failing, fallback] context
      pure none
    catch error => pure (some error)
    let some (.internal id _) := failure
      | liftM (m := MetaM) <| throwError "a completed rule's original internal exception was relabelled or swallowed"
    unless id == readRuleMismatch && (← liftM (m := IO) fallbackCalls.get) == 0 do
      liftM (m := MetaM) <| throwError "a completed rule's failure reopened source interpretation"
    let unmatched : ReadCompletingRule := fun _ _ => throwReadRuleMismatch
    let .ok _ ← readWithCompletingRules #[unmatched, fallback] context
      | liftM (m := MetaM) <| throwError "ordinary unmatched syntax stopped trying its next rule"
    unless (← liftM (m := IO) fallbackCalls.get) == 1 do
      liftM (m := MetaM) <| throwError "the unmatched syntax control did not reach its ordinary next rule"
    pure #[]

private def selectedMethod? (value : Expr) : SourceReadM (Option MethodEntry) := do
  let some selected ← SourceReadM.selection? value | return none
  let some application := selected.application | return none
  let .routedMethod family := application.family | return none
  return some family.entry




run_cmd Lean.Elab.Command.liftTermElabM do
  let previous := preferredRoutesExtension.getState (← liftM (m := CoreM) getEnv)
  try
    let identities ← liftM (m := IO) CasRuntime.IdentitySupply.new
    let session ← SourceSession.empty identities
    discard <| session.elaborateJudgementsScoped Syntax.missing do
      setPreferredRoutes #[]
      let source ← sourceTerm "(ℚ in Rings).cardinality()"
      let receiver ← sourceTerm "ℚ in Rings"
      let state ← semanticState
      let rings ← selectCategory state "Rings"
      let query ← SourceRoutes.forMethod rings.expression "cardinality"
      let some routes ← query.finiteRoutes
        | liftM (m := MetaM) <| throwError "the actual cardinality control requires its finite registered routes"
      let distinct := routes.foldl (fun found route =>
        if found.any (·.refs == route.refs) then found else found.push route) (#[] : Array Route)
      let some chosen := distinct.find? (! ·.refs.isEmpty)
        | liftM (m := MetaM) <| throwError "the original ring cardinality has no inherited route"
      let #[method] := state.methods.filter fun entry =>
        entry.name == "cardinality" && entry.owner.syntacticEq chosen.target
        | liftM (m := MetaM) <| throwError "the actual cardinality route does not have one method binding"
      let labels := chosen.refs.map (·.label)
      let reads ← liftM (m := IO) <| IO.mkRef (0 : Nat)
      let calls ← liftM (m := IO) <| IO.mkRef (0 : Nat)
      let introduced ← liftM (m := IO) <| IO.mkRef (none : Option Name)
      let context := memberContext source reads fun _ name arguments => do
        unless name == "cardinality" && arguments.isEmpty do
          liftM (m := MetaM) <| throwError "the competing projection changed its actual source call"
        liftM (m := IO) <| calls.modify (· + 1)
        let name ← mkAuxDeclName `preferredMemberProjection
        addDecl (.defnDecl {
          name
          levelParams := []
          type := mkConst ``Nat
          value := mkNatLit 9
          hints := .abbrev
          safety := .safe })
        liftM (m := IO) <| introduced.set (some name)
        return some ⟨mkConst name, none⟩

      setPreferredRoutes #[{ receiver := rings.id.raw, name := "cardinality", route := labels }]
      let result ← readMember context receiver "cardinality" #[]
      unless (← selectedMethod? result.value).any (fun original => reprStr original == reprStr method) &&
          (← preference? result.value) == some chosen.refs do
        liftM (m := MetaM) <| throwError "a direct projection displaced the actually preferred inherited method"
      checkWithKernel result.value
      unless (← liftM (m := IO) reads.get) == 1 && (← liftM (m := IO) calls.get) == 1 do
        liftM (m := MetaM) <| throwError "preferred member selection replayed its receiver or a candidate"
      let some rejected ← liftM (m := IO) introduced.get
        | liftM (m := MetaM) <| throwError "the competing projection was not considered"
      if ((← liftM (m := CoreM) getEnv).setExporting false).contains rejected then
        liftM (m := MetaM) <| throwError "the preferred method retained a rejected projection declaration"



      liftM (m := IO) <| reads.set 0
      liftM (m := IO) <| calls.set 0
      liftM (m := IO) <| introduced.set none
      setPreferredRoutes #[{ receiver := rings.id.raw, name := "cardinality", route := #[] }]
      let direct ← readMember context receiver "cardinality" #[]
      let some retained ← liftM (m := IO) introduced.get
        | liftM (m := MetaM) <| throwError "the direct preferred member was not formed"
      let scope ← get
      unless (← SourceTest.originatesAt scope.context scope.selections direct.value (Lean.mkConst retained)) &&
          (← preference? direct.value) == some #[] &&
          (← liftM (m := IO) reads.get) == 1 && (← liftM (m := IO) calls.get) == 1 do
        liftM (m := MetaM) <| throwError "member selection did not retain its original direct native result"
      checkWithKernel direct.value



      setPreferredRoutes #[{ receiver := rings.id.raw, name := "cardinality", route := labels }]
      let failure : Option Exception ← try
        discard <| readMember { context with expected := some (mkConst ``Nat) }
          receiver "cardinality" #[]
        pure none
      catch error => pure (some error)
      let some failure := failure
        | liftM (m := MetaM) <| throwError "a non-surviving preferred member route was silently replaced"
      unless CasCatalogue.Exception.stratum? failure == some .invalid do throw failure



      let sets ← selectCategory state "Sets"
      setPreferredRoutes #[{ receiver := sets.id.raw, name := "is_finite", route := #[] }]
      let propertySource ← sourceTerm "Fin(3).is_finite()"
      let propertyReceiver ← sourceTerm "Fin(3)"
      let propertyContext := memberContext propertySource reads fun _ _ _ =>
        pure (some ⟨mkNatLit 0, none⟩)
      let conflict : Option Exception ← try
        discard <| readMember propertyContext propertyReceiver "is_finite" #[]
        pure none
      catch error => pure (some error)
      let some conflict := conflict
        | liftM (m := MetaM) <| throwError "a preferred empty route invented agreement between member kinds"
      unless CasCatalogue.Exception.isSemanticAmbiguity conflict do throw conflict
      pure #[]
  finally
    setPreferredRoutes previous




run_cmd Lean.Elab.Command.liftTermElabM do
  let identities ← liftM (m := IO) CasRuntime.IdentitySupply.new
  let session ← SourceSession.empty identities
  discard <| session.elaborateJudgementsScoped Syntax.missing do
    let source ← sourceTerm "Fin(3).is_finite()"
    let receiver ← sourceTerm "Fin(3)"
    let #[required] := (← semanticState).categories.filter fun entry =>
      entry.expression.syntacticEq (.classifierTotal ClassifierId.setsFinite)
      | liftM (m := MetaM) <| throwError "the qualification control lost its independent finite-object category"
    let reads ← liftM (m := IO) <| IO.mkRef (0 : Nat)
    let completed ← liftM (m := IO) <| IO.mkRef (0 : Nat)
    let original ← liftM (m := IO) <| IO.mkRef (none : Option NativeSourceJudgement)
    let context := memberContext source reads (fun receiver _ _ => do
        liftM (m := IO) <| original.set (some receiver)
        return some receiver)
    let context := { context with qualification := some required.name }
    let result ← SourceReader.memberCompleting context (fun value => do
        liftM (m := IO) <| completed.modify (· + 1)
        checkReadJudgementApplicable context value) receiver "is_finite" #[]
    let .ok result := result
      | liftM (m := MetaM) <| throwError "a qualifier's explicit category mismatch displaced an applicable member"
    unless (← liftM (m := IO) completed.get) == 2 && (← liftM (m := IO) reads.get) == 1 do
      liftM (m := MetaM) <| throwError "member qualification replayed its receiver or completed a candidate twice"
    let some selected := result.category
      | liftM (m := MetaM) <| throwError "the qualified member lost its complete selected category"
    let some carrier := selected.carrier
      | liftM (m := MetaM) <| throwError "the qualified member lost its checked property inclusion"
    let some original ← liftM (m := IO) original.get
      | liftM (m := MetaM) <| throwError "the qualification control lost its original source receiver"
    let some originalCategory := original.category
      | liftM (m := MetaM) <| throwError "the original finite object lost its source category"
    let some forget := carrier.actions[0]?
      | liftM (m := MetaM) <| throwError "the qualified member lost its actual forgetful action"
    unless selected.expression.syntacticEq required.expression &&
        carrier.refs[0]? == some (.classifierForget ClassifierId.setsFinite) do
      liftM (m := MetaM) <| throwError "member qualification changed the original selected classifier"
    let mapped ← functorObject forget result.value originalCategory.bundle
    SourceTest.checkOriginal #[mapped, original.value] fun native => do
      unless ← isDefEq native[0]! native[1]! do
        liftM (m := MetaM) <| throwError "member qualification changed the original object"
    checkWithKernel result.value



    let source ← sourceTerm "ℕ.is_finite()"
    let receiver ← sourceTerm "ℕ"
    let context := memberContext source reads (fun receiver _ _ => pure (some receiver))
    let context := { context with qualification := some required.name }
    let failure : Option Exception ← try
      discard <| readMember context receiver "is_finite" #[]
      pure none
    catch error => pure (some error)
    let some failure := failure
      | liftM (m := MetaM) <| throwError "member qualification accepted an unestablished original property"
    unless CasCatalogue.Exception.stratum? failure == some .invalid do throw failure
    pure #[]



run_cmd Lean.Elab.Command.liftTermElabM do
  let identities ← liftM (m := IO) CasRuntime.IdentitySupply.new
  let session ← SourceSession.empty identities
  discard <| session.elaborateJudgementsScoped Syntax.missing do
    let first ← readExpression (fun _ => pure none) (← sourceTerm "Fin(2) × Fin(3)") none
    let firstChoice ← SourceMemberChoice.capture ⟨first, none⟩ () first
    checkSourceMemberSelections #[firstChoice, firstChoice]
    let second ← readExpression (fun _ => pure none) (← sourceTerm "Fin(3) × Fin(2)") none
    let secondChoice ← SourceMemberChoice.capture ⟨second, none⟩ () second
    let some left := first.category
      | liftM (m := MetaM) <| throwError "the first independent construction lost its category"
    let some right := second.category
      | liftM (m := MetaM) <| throwError "the second independent construction lost its category"
    unless left.expression.syntacticEq right.expression &&
        (← isDefEq left.bundle right.bundle) do
      liftM (m := MetaM) <| throwError "the selected-diagram control did not share the same complete category"
    let failure : Option Exception ← try
      checkSourceMemberSelections #[firstChoice, secondChoice]
      pure none
    catch error => pure (some error)
    let some failure := failure
      | liftM (m := MetaM) <| throwError "member agreement compared only the carrier and discarded a selected diagram"
    unless CasCatalogue.Exception.isSemanticAmbiguity failure do throw failure
    pure #[]

end CasCompiler.SourceMemberCompetitionTests
