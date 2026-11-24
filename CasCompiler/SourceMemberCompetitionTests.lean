module

import CasCompiler.Read
import CasCompiler.ReadMember
import CasCompiler.ReadDispatch
import CasCompiler.SourcePropertyQualification
import LeanCategories.Catalogue
public meta import Lean.Elab.Command
meta import CasCompiler.Read
meta import CasCompiler.ReadMember
meta import CasCompiler.ReadDispatch
meta import CasCompiler.SourcePropertyQualification
meta import LeanCategories.Catalogue

namespace CasCompiler.SourceMemberCompetitionTests

open Lean Meta Elab Term CasCatalogue

private def sourceTerm (text : String) : TermElabM (TSyntax `cas_term) := do
  let .ok source := Parser.runParserCategory (← getEnv) `cas_term text
    | throwError "the member competition control did not parse"
  return ⟨source⟩

private def readMember (context : ReadContext) (receiver : TSyntax `cas_term)
    (name : String) (arguments : Array (TSyntax `cas_term)) :
    TermElabM NativeSourceJudgement := do
  match ← SourceReader.memberCompleting context (checkReadJudgementApplicable context)
      receiver name arguments with
  | .ok value => pure value
  | .error message => throwError message

private def memberContext (source : TSyntax `cas_term) (reads : IO.Ref Nat)
    (project : NativeSourceJudgement → String → Array (TSyntax `cas_term) →
      TermElabM (Option NativeSourceJudgement)) : ReadContext := {
  categoryOf := fun _ => pure none
  source
  expected := none
  qualification := none
  expectedCategory := none
  project
  read := fun categoryOf source expected qualification expectedCategory => do
    reads.modify (· + 1)
    readExpressionApplicable categoryOf source expected qualification expectedCategory
}

-- This controls the actual reader's projection callback; it adds no mathematical registry
-- row. The property is the independently registered Fin(3).is_finite() reading. Both kinds
-- must compete, even when the earlier projection callback returns a well-typed value.
-- Original public method/property/image/projection tests remain separate and unchanged.
run_cmd Lean.Elab.Command.liftTermElabM do
  let source ← sourceTerm "Fin(3).is_finite()"
  let receiver ← sourceTerm "Fin(3)"
  let reads ← liftM (m := IO) <| IO.mkRef (0 : Nat)
  let projects ← liftM (m := IO) <| IO.mkRef (0 : Nat)
  let declarations ← liftM (m := IO) <| IO.mkRef (#[] : Array Name)
  let context := memberContext source reads fun _ name arguments => do
    unless name == "is_finite" && arguments.isEmpty do
      throwError "the competing projection lost its original member call"
    projects.modify (· + 1)
    let name ← mkAuxDeclName `competingMemberProjection
    addDecl (.defnDecl {
      name
      levelParams := []
      type := mkConst ``Nat
      value := mkNatLit 0
      hints := .abbrev
      safety := .safe })
    declarations.modify (·.push name)
    return some ⟨mkConst name, none⟩
  let failure : Option Exception ← try
    discard <| readMember context receiver "is_finite" #[]
    pure none
  catch error => pure (some error)
  let some failure := failure
    | throwError "a projection displaced a simultaneously applicable property"
  unless CasCatalogue.Exception.isSemanticAmbiguity failure do throw failure
  unless (← reads.get) == 1 && (← projects.get) == 1 do
    throwError "member competition reread its receiver or replayed a selected projection"
  for name in ← declarations.get do
    if ((← getEnv).setExporting false).contains name then
      throwError "an ambiguous member retained a speculative native declaration"

  -- Discovery receives the actual selected native receiver and the same
  -- competing candidates, rather than running the source reader a second time.
  let selectedReceiver ← readExpression (fun _ => pure none) receiver none
  reads.set 0
  projects.set 0
  declarations.set #[]
  let saved ← saveState
  try
    let candidates ← SourceReader.memberChoicesAtReceiver context selectedReceiver "is_finite" #[] none
    unless candidates.choices.size == 2 do
      throwError "the formed-receiver entrance lost a competing native reading"
    let failure : Option Exception ← try
      discard <| SourceReader.completeMemberChoices context (checkReadJudgementApplicable context)
        "is_finite" #[] candidates.considered candidates.choices candidates.mismatches
      pure none
    catch error => pure (some error)
    let some failure := failure
      | throwError "discovery selected an ambiguous member"
    unless CasCatalogue.Exception.isSemanticAmbiguity failure do throw failure
    unless (← reads.get) == 0 && (← projects.get) == 1 do
      throwError "discovery reread the receiver or replayed a candidate"
  finally saved.restore

  -- The final expected-type check is applied to each result. Its explicit mismatch can
  -- decline the Nat-valued projection, while the original property remains a proposition.
  reads.set 0
  projects.set 0
  declarations.set #[]
  let result ← readMember { context with expected := some (mkSort .zero) }
    receiver "is_finite" #[]
  let #[classifier] := (← semanticState).classifiers.filter (·.id == ClassifierId.setsFinite)
    | throwError "the original finiteness classifier is absent or ambiguous"
  let finite ← mkAppM ``CasCatalogue.Foundation.Objects.fin #[mkNatLit 3]
  let expected ← elabAppArgs (← mkConstWithFreshMVarLevels ``CasCatalogue.Classifier.Holds)
    #[] #[Arg.expr (← classifierInstance classifier), Arg.expr finite] none false false
  unless ← isDefEq result.value expected do
    throwError "the surviving member changed its independently declared property"
  checkWithKernel result.value
  unless (← reads.get) == 1 && (← projects.get) == 1 do
    throwError "member result checking reread source or replayed a candidate"
  for name in ← declarations.get do
    if ((← getEnv).setExporting false).contains name then
      throwError "a native-domain mismatch retained a rejected projection declaration"

-- A unique kind retains the exact checked native state from its one callback invocation.
-- The ordinary native alias makes a replay or a discarded selected environment observable.
run_cmd Lean.Elab.Command.liftTermElabM do
  let source ← sourceTerm "Fin(3).retained_native_projection()"
  let receiver ← sourceTerm "Fin(3)"
  let reads ← liftM (m := IO) <| IO.mkRef (0 : Nat)
  let projects ← liftM (m := IO) <| IO.mkRef (0 : Nat)
  let introduced ← liftM (m := IO) <| IO.mkRef (none : Option Name)
  let context := memberContext source reads fun _ name arguments => do
    unless name == "retained_native_projection" && arguments.isEmpty do
      throwError "the retained projection changed its original member call"
    projects.modify (· + 1)
    let name ← mkAuxDeclName `retainedMemberProjection
    addDecl (.defnDecl {
      name
      levelParams := []
      type := mkConst ``Nat
      value := mkNatLit 7
      hints := .abbrev
      safety := .safe })
    introduced.set (some name)
    return some ⟨mkConst name, none⟩
  let result ← readMember context receiver "retained_native_projection" #[]
  let some name ← introduced.get
    | throwError "the selected projection callback was not executed"
  unless (← reads.get) == 1 && (← projects.get) == 1 && result.value == Lean.mkConst name do
    throwError "member selection replaced or replayed the original checked native result"
  unless ((← getEnv).setExporting false).contains name do
    throwError "member selection discarded its original checked native environment"
  checkWithKernel result.value

-- An exception is not absence. A property that would otherwise apply cannot rescue a
-- failed projection callback, and the failed callback's native declaration is rolled back.
run_cmd Lean.Elab.Command.liftTermElabM do
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
    introduced.set (some name)
    throw (Exception.internal originalFailure)
  let failure : Option Exception ← try
    discard <| readMember context receiver "is_finite" #[]
    pure none
  catch error => pure (some error)
  let some (.internal actual _) := failure
    | throwError "a failed member callback lost its original native exception"
  unless actual == originalFailure do
    throwError "a failed member callback was relabelled or retried"
  let some name ← introduced.get
    | throwError "the failed member control never reached its actual callback"
  if ((← getEnv).setExporting false).contains name then
    throwError "a failed member callback retained its speculative native declaration"

private partial def preference? : Expr → Option String
  | .mdata data body =>
    if data.contains `CasCompiler.source.preferredRoute then
      some (data.getString `CasCompiler.source.preferredRoute)
    else preference? body
  | .letE _ _ value body _ => preference? (body.instantiate1 value)
  | _ => none

-- The completion continuation belongs to the already matched rule. Even an internal
-- exception with the dispatcher's private mismatch identifier cannot reopen syntax search
-- after that boundary. No result from the fallback may replace the failed interpretation.
run_cmd Lean.Elab.Command.liftTermElabM do
  let source ← sourceTerm "Fin(3)"
  let reads ← liftM (m := IO) <| IO.mkRef (0 : Nat)
  let fallbackCalls ← liftM (m := IO) <| IO.mkRef (0 : Nat)
  let context := memberContext source reads fun _ _ _ => pure none
  let failing : ReadCompletingRule := fun context complete => do
    let value ← context.readExpression context.categoryOf context.source none
    discard <| complete value
    throwReadRuleMismatch
  let fallback : ReadCompletingRule := fun _ complete => do
    fallbackCalls.modify (· + 1)
    complete ⟨mkNatLit 0, none⟩
  let failure : Option Exception ← try
    discard <| readWithCompletingRules #[failing, fallback] context
    pure none
  catch error => pure (some error)
  let some (.internal id _) := failure
    | throwError "a completed rule's original internal exception was relabelled or swallowed"
  unless id == readRuleMismatch && (← fallbackCalls.get) == 0 do
    throwError "a completed rule's failure reopened source interpretation"
  let unmatched : ReadCompletingRule := fun _ _ => throwReadRuleMismatch
  let .ok _ ← readWithCompletingRules #[unmatched, fallback] context
    | throwError "ordinary unmatched syntax stopped trying its next rule"
  unless (← fallbackCalls.get) == 1 do
    throwError "the unmatched syntax control did not reach its ordinary next rule"

private partial def selectedMethod? : Expr → Option String
  | .mdata data body =>
    if data.getName `CasCompiler.source.kind == ``RoutedMethodFamily then
      some (data.getString `CasCompiler.source.id)
    else selectedMethod? body
  | .letE _ _ value body _ => selectedMethod? (body.instantiate1 value)
  | _ => none

-- A preference is checked after all actual kinds and their native result domains survive.
-- The method and its nonempty structural route come from the independent registry. The
-- callback controls the existing projection entrance and supplies no registry row or law.
run_cmd Lean.Elab.Command.liftTermElabM do
  let previous := preferredRoutesExtension.getState (← getEnv)
  try
    setPreferredRoutes #[]
    let source ← sourceTerm "(ℚ in Rings).cardinality()"
    let receiver ← sourceTerm "ℚ in Rings"
    let state ← semanticState
    let rings ← selectCategory state "Rings"
    let query ← SourceRoutes.forMethod rings.expression "cardinality"
    let some routes ← query.finiteRoutes
      | throwError "the actual cardinality control requires its finite registered routes"
    let distinct := routes.foldl (fun found route =>
      if found.any (·.refs == route.refs) then found else found.push route) (#[] : Array Route)
    let some chosen := distinct.find? (! ·.refs.isEmpty)
      | throwError "the original ring cardinality has no inherited route"
    let #[method] := state.methods.filter fun entry =>
      entry.name == "cardinality" && entry.owner.syntacticEq chosen.target
      | throwError "the actual cardinality route does not have one method binding"
    let labels := chosen.refs.map (·.label)
    let reads ← liftM (m := IO) <| IO.mkRef (0 : Nat)
    let calls ← liftM (m := IO) <| IO.mkRef (0 : Nat)
    let introduced ← liftM (m := IO) <| IO.mkRef (none : Option Name)
    let context := memberContext source reads fun _ name arguments => do
      unless name == "cardinality" && arguments.isEmpty do
        throwError "the competing projection changed its actual source call"
      calls.modify (· + 1)
      let name ← mkAuxDeclName `preferredMemberProjection
      addDecl (.defnDecl {
        name
        levelParams := []
        type := mkConst ``Nat
        value := mkNatLit 9
        hints := .abbrev
        safety := .safe })
      introduced.set (some name)
      return some ⟨mkConst name, none⟩

    setPreferredRoutes #[{ receiver := rings.id.raw, name := "cardinality", route := labels }]
    let result ← readMember context receiver "cardinality" #[]
    unless selectedMethod? result.value == some method.id.raw &&
        preference? result.value == some (reprStr labels) do
      throwError "a direct projection displaced the actually preferred inherited method"
    checkWithKernel result.value
    unless (← reads.get) == 1 && (← calls.get) == 1 do
      throwError "preferred member selection replayed its receiver or a candidate"
    let some rejected ← introduced.get
      | throwError "the competing projection was not considered"
    if ((← getEnv).setExporting false).contains rejected then
      throwError "the preferred method retained a rejected projection declaration"

    -- The direct projection has the actual empty path at its already selected receiver.
    -- It competes with the inherited methods even though they use a different kind.
    reads.set 0
    calls.set 0
    introduced.set none
    setPreferredRoutes #[{ receiver := rings.id.raw, name := "cardinality", route := #[] }]
    let direct ← readMember context receiver "cardinality" #[]
    let some retained ← introduced.get
      | throwError "the direct preferred member was not formed"
    unless direct.value.consumeMData == Lean.mkConst retained &&
        preference? direct.value == some (reprStr (#[] : Array String)) &&
        (← reads.get) == 1 && (← calls.get) == 1 do
      throwError "member selection did not retain its original direct native result"
    checkWithKernel direct.value

    -- The inherited method's result is not a Nat. A preference for its rejected route is
    -- invalid; the Nat-valued projection cannot rescue or relabel that declared choice.
    setPreferredRoutes #[{ receiver := rings.id.raw, name := "cardinality", route := labels }]
    let failure : Option Exception ← try
      discard <| readMember { context with expected := some (mkConst ``Nat) }
        receiver "cardinality" #[]
      pure none
    catch error => pure (some error)
    let some failure := failure
      | throwError "a non-surviving preferred member route was silently replaced"
    unless CasCatalogue.Exception.stratum? failure == some .invalid do throw failure

    -- A preference selects a route, never a member kind. On Sets the real property and
    -- the controlled direct projection have the same empty route and remain ambiguous.
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
      | throwError "a preferred empty route invented agreement between member kinds"
    unless CasCatalogue.Exception.isSemanticAmbiguity conflict do throw conflict
  finally
    setPreferredRoutes previous

-- Qualification is the same once-per-candidate completion as expected native typing.
-- The real property has no selected object category and declines only that own mismatch;
-- the actual finite object returned by the projection is refined by its existing proof.
run_cmd Lean.Elab.Command.liftTermElabM do
  let source ← sourceTerm "Fin(3).is_finite()"
  let receiver ← sourceTerm "Fin(3)"
  let #[required] := (← semanticState).categories.filter fun entry =>
    entry.expression.syntacticEq (.classifierTotal ClassifierId.setsFinite)
    | throwError "the qualification control lost its independent finite-object category"
  let reads ← liftM (m := IO) <| IO.mkRef (0 : Nat)
  let completed ← liftM (m := IO) <| IO.mkRef (0 : Nat)
  let original ← liftM (m := IO) <| IO.mkRef (none : Option NativeSourceJudgement)
  let context := memberContext source reads (fun receiver _ _ => do
      original.set (some receiver)
      return some receiver)
  let context := { context with qualification := some required.name }
  let result ← SourceReader.memberCompleting context (fun value => do
      completed.modify (· + 1)
      checkReadJudgementApplicable context value) receiver "is_finite" #[]
  let .ok result := result
    | throwError "a qualifier's explicit category mismatch displaced an applicable member"
  unless (← completed.get) == 2 && (← reads.get) == 1 do
    throwError "member qualification replayed its receiver or completed a candidate twice"
  let some selected := result.category
    | throwError "the qualified member lost its complete selected category"
  let some carrier := selected.carrier
    | throwError "the qualified member lost its checked property inclusion"
  let some original ← original.get
    | throwError "the qualification control lost its original source receiver"
  let some originalCategory := original.category
    | throwError "the original finite object lost its source category"
  let some forget := carrier.actions[0]?
    | throwError "the qualified member lost its actual forgetful action"
  unless selected.expression.syntacticEq required.expression &&
      carrier.refs[0]? == some (.classifierForget ClassifierId.setsFinite) &&
      (← isDefEq (← functorObject forget result.value originalCategory.bundle)
        original.value) do
    throwError "member qualification changed the original object or selected classifier"
  checkWithKernel result.value

  -- A failed chosen proof remains an actual error. No competing property can turn an
  -- arbitrary infinite object into a finite one or treat that proof failure as absence.
  let source ← sourceTerm "ℕ.is_finite()"
  let receiver ← sourceTerm "ℕ"
  let context := memberContext source reads (fun receiver _ _ => pure (some receiver))
  let context := { context with qualification := some required.name }
  let failure : Option Exception ← try
    discard <| readMember context receiver "is_finite" #[]
    pure none
  catch error => pure (some error)
  let some failure := failure
    | throwError "member qualification accepted an unestablished original property"
  unless CasCatalogue.Exception.stratum? failure == some .invalid do throw failure

-- Two actual source constructions can share the complete Sets bundle while retaining
-- different chosen diagrams. Whole-family coalescing must not discard that selected data.
run_cmd Lean.Elab.Command.liftTermElabM do
  let first ← readExpression (fun _ => pure none) (← sourceTerm "Fin(2) × Fin(3)") none
  let firstState ← saveState
  let firstChoice : SourceMemberChoice Unit :=
    ⟨⟨first, none⟩, (), first, firstState⟩
  checkSourceMemberSelections #[firstChoice, firstChoice]
  let second ← readExpression (fun _ => pure none) (← sourceTerm "Fin(3) × Fin(2)") none
  let secondChoice : SourceMemberChoice Unit :=
    ⟨⟨second, none⟩, (), second, ← saveState⟩
  let some left := first.category
    | throwError "the first independent construction lost its category"
  let some right := second.category
    | throwError "the second independent construction lost its category"
  unless left.expression.syntacticEq right.expression &&
      (← isDefEq left.bundle right.bundle) do
    throwError "the selected-diagram control did not share the same complete category"
  let failure : Option Exception ← try
    checkSourceMemberSelections #[firstChoice, secondChoice]
    pure none
  catch error => pure (some error)
  let some failure := failure
    | throwError "member agreement compared only the carrier and discarded a selected diagram"
  unless CasCatalogue.Exception.isSemanticAmbiguity failure do throw failure

end CasCompiler.SourceMemberCompetitionTests
