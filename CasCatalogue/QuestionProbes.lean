module

import CasCatalogue.Realize
import LeanCategories.Catalogue.Semantics
meta import CasCatalogue.Realize
meta import LeanCategories.Catalogue.Semantics

open Lean Elab Command Term
open CasCatalogue CasCatalogue.Language CasCatalogue.Realize

/- Reader mechanics only: these probes do not admit mathematical assertions or meanings. -/
run_cmd liftTermElabM do
  let ask (text : String) : TermElabM TypedQuestion := do
    let .ok parsed :=  Parser.runParserCategory (← getEnv) `cas_stmt text
      | throwError "probe did not parse: {text}"
    interpret {} parsed
  let member ← ask "assert -3 ∈ ℤ"
  let typed ← ask "assert -3 in ℤ"
  unless member.identity.1 != typed.identity.1 do
    throwError "membership and typing collapsed"
  let inclusion ← ask "assert ℤ ⊆ ℚ"
  let conjunction ← ask "assert ℤ ⊆ ℚ and ℤ ⊆ ℚ"
  unless inclusion.identity.1 != conjunction.identity.1 do
    throwError "conjunction collapsed to its operand"
  let negated ← ask "assert -3 ∉ ℤ"
  unless member.identity.1 != negated.identity.1 do
    throwError "negation collapsed to membership"
  let parameterA ← ask "assert 0 ∈ ℤ/3"
  let parameterB ← ask "assert 0 ∈ ℤ/5"
  unless parameterA.identity.1 != parameterB.identity.1 do
    throwError "distinct family parameters collapsed"
  let plainFinite ← ask "assert Fin(3) in Sets"
  let structuredFinite ← ask "assert Fin(3) in FiniteSets"
  unless plainFinite.identity.1 != structuredFinite.identity.1 do
    throwError "the reader erased the selected finite-set structure"
  let ordinaryCard ← ask "assert |Fin(3)| = 3"
  let liftedCard ← ask "assert |Fin(3) in FiniteSets| = 3"
  unless ordinaryCard.identity.1 != liftedCard.identity.1 do
    throwError "the reader erased the selected structural route to cardinality"
  -- Structural mechanical probes use formal declarations as inert identity data; these
  -- do not state or accept mathematical propositions about those declarations.
  let operand := Lean.mkNatLit 0
  let first : Question := .judgement "in" #[operand] #[] #[``Nat]
  let second : Question := .judgement "in" #[operand] #[] #[``Int]
  let routed : Question := .judgement "in" #[operand] #[``Nat.succ] #[``Nat]
  let (firstIdentity, _) ← claimQuestion (.judged first (Lean.mkConst ``True) (some true) "probe")
  let (secondIdentity, _) ← claimQuestion (.judged second (Lean.mkConst ``True) (some true) "probe")
  let (routedIdentity, _) ← claimQuestion (.judged routed (Lean.mkConst ``True) (some true) "probe")
  unless firstIdentity != secondIdentity && firstIdentity != routedIdentity do
    throwError "formal selected identity or structural route was erased"
  let lambdaA := Expr.lam `a (Lean.mkConst ``Nat) (.bvar 0) .default
  let lambdaB := Expr.lam `b (Lean.mkConst ``Nat) (.bvar 0) .default
  unless canonicalTerm lambdaA == canonicalTerm lambdaB do
    throwError "bound-variable spelling prevented representation-preserving comparison"
  let failed ← ask "assert 2 + 3 = 6"
  let harness ← Harness.empty
  let .ok parsed :=  Parser.runParserCategory (← getEnv) `cas_stmt "assert 2 + 3 = 6"
    | throwError "failure probe did not parse"
  let (outcome, _, retained) ← runAsking harness {} parsed
  unless outcome.kind == "wrong" && retained == some failed.identity do
    throwError "a refuted assertion changed its question or reported semantic invalidity"

run_cmd liftTermElabM do
  for (stratum, expected) in #[(Stratum.invalid, InterpretationFailureKind.invalid),
      (.semanticAmbiguity, .ambiguous), (.noImplementation, .internal),
      (.ambiguousRealization, .internal), (.unavailable, .internal), (.malformed, .internal)] do
    let failed : TermElabM Unit := throwStratum stratum "stage-classification probe"
    let actual ← tryCatchRuntimeEx (failed *> pure InterpretationFailureKind.internal)
      fun error => pure (Exception.interpretationKind error)
    unless actual == expected do
      throwError "the interpretation boundary accepted a failure belonging to another stage"
  let legacy : TermElabM Unit := throwSemanticAmbiguity "legacy reader ambiguity"
  let legacyKind ← tryCatchRuntimeEx (legacy *> pure InterpretationFailureKind.internal)
    fun error => pure (Exception.interpretationKind error)
  unless legacyKind == .ambiguous do
    throwError "the reader's original ambiguity tag was lost"
  let internal : TermElabM Unit := throwError "unclassified interpreter failure"
  let internalKind ← tryCatchRuntimeEx (internal *> pure InterpretationFailureKind.invalid)
    fun error => pure (Exception.interpretationKind error)
  unless internalKind == .internal do
    throwError "an unclassified exception was promoted to mathematical invalidity"
  let simulated : TermElabM ExecutionOutcome :=
    throwStratum .invalid "a computational exception cannot judge mathematical validity"
  let outcome ← tryCatchRuntimeEx simulated executionFailure
  unless outcome matches .internal _ do
    throwError "execution accepted a semantic-invalidity constructor"
  let malformed : TermElabM ExecutionOutcome := throwStratum .malformed "bad reply"
  let outcome ← tryCatchRuntimeEx malformed executionFailure
  unless outcome matches .malformed _ do
    throwError "execution erased the decoder's malformed-output stratum"

-- Typed constructor mechanics retain the canonical registered commutative coefficient object.
run_cmd liftTermElabM do
  let state ← registryState
  let sets ← categoryNamed state "Sets"
  let some commutative := state.categories.find? (·.id == CategoryId.commutativeRings)
    | throwError "constructor probe has no registered parameter category"
  let some constructor := state.objects.find? fun entry =>
      entry.name == "PowerSeries" && entry.category == sets.id
    | throwError "constructor probe has no registered family"
  let selected ← (object state "ℝ" #[] (some commutative)).run {}
  let .object coefficient _ (some (selectedEntry, _)) _ _ := selected
    | throwError "constructor probe lost its registered coefficient origin"
  let trace ← Trace.new
  let series ← (object state constructor.name #[selected] (some sets)).run { trace := some trace }
  let .object seriesHandle _ (some (_, #[stored])) _ _ := series
    | throwError "typed constructor probe lost its parameters"
  unless stored.declarations == selected.declarations do
    throwError "typed constructor erased its selected parameter category"
  let exact ← (typedParamTerms constructor.declaration #[selected]).run { trace := some trace }
  let exactTerm ← elabTermAndSynthesize exact[0]! none
  unless ← Lean.Meta.isDefEq exactTerm coefficient do
    throwError "an already typed selected parameter was replaced"
  let recovered ← (recognize state seriesHandle sets).run {}
  let .object _ _ (some (_, #[.object _ parameterCategory (some (parameterEntry, _)) _ _])) _ _ := recovered
    | throwError "structured constructor parameter lost its registered origin"
  unless parameterCategory.id == commutative.id && parameterEntry.id == selectedEntry.id do
    throwError "structured constructor recognition changed the coefficient category or origin"

-- Selected routes survive; identical complete incoming structures retain both presentations.
run_cmd liftTermElabM do
  let state ← registryState
  let sets ← categoryNamed state "Sets"
  let rings ← categoryNamed state "Rings"
  let trace ← Trace.new
  let plain ← (object state "ℂ" #[] (some sets)).run { trace := some trace }
  let selected ← (object state "ℂ" #[] (some rings)).run { trace := some trace }
  let .object _ _ (some (selectedEntry, _)) _ _ := selected
    | throwError "structural parameter probe lost its selected origin"
  let some sum := state.morphisms.find? (·.name == "∑")
    | throwError "structural parameter probe has no registered family"
  let domain ← (object state "Fin" #[.nat 2] (some sets)).run {}
  discard <| (typedParamTerms sum.declaration #[domain, selected]).run { trace := some trace }
  let transported := (← trace.get).toArray.any fun (_, node) => match node with
    | .retainedRoute sourceCategory targetCategory route applications receiver =>
        sourceCategory == rings.id && targetCategory != rings.id && !route.isEmpty &&
          applications.size == route.size && receiver.getAppFn.constName? == some selectedEntry.declaration
    | _ => false
  unless transported do
    throwError "structural parameter route or exact source provenance was erased"
  let plainTrace ← Trace.new
  let terms ← (typedParamTerms sum.declaration #[domain, plain]).run { trace := some plainTrace }
  let actual ← elabTermAndSynthesize terms[1]! none
  let some (.parameterEquivalence expected representative sources) ← plainTrace.node? actual
    | throwError "identical complete incoming structures lost their source presentations"
  unless sources.size ≥ 2 do
    throwError "incoming structure equivalence did not retain both registered origins"
  let originIds := sources.map (·.source)
  unless originIds.toList.eraseDups.length == sources.size do
    throwError "incoming structure equivalence duplicated a registered origin"
  unless ← Lean.Meta.isDefEq actual representative do
    throwError "the retained equivalent parameter is not the actual application parameter"
  for source in sources do
    unless !source.route.isEmpty && !source.carrierRoute.isEmpty &&
        !source.identifications.isEmpty do
      throwError "incoming full-structure equality erased a declared refinement route"
    unless ← Lean.Meta.isDefEq (← Lean.Meta.inferType source.image) expected do
      throwError "a source presentation has the wrong complete structured type"
    let equation ← Lean.Meta.mkEq source.image representative
    unless ← Lean.Meta.isTypeCorrect source.identity <&&>
        Lean.Meta.isDefEq (← Lean.Meta.inferType source.identity) equation do
      throwError "a full structured source equality is not kernel typed"
  let .object plainHandle .. := plain | unreachable!
  let anonymous := Value.object plainHandle sets none none none
  let rejected ← try
    discard <| (typedParamTerms sum.declaration #[domain, anonymous]).run {}
    pure false
  catch error => pure ((CasCatalogue.Exception.stratum? error) == some .invalid)
  unless rejected do
    throwError "carrier coincidence supplied an unregistered parameter structure"

run_cmd liftTermElabM do
  let parameterVar ← Lean.Meta.mkFreshExprMVar (some (Lean.mkConst ``Nat))
  let unified ← (parameterTrial (Lean.Meta.isDefEq parameterVar (Lean.mkNatLit 3))).run {}
  unless unified && (← instantiateMVars parameterVar) == parameterVar do
    throwError "a speculative parameter assignment escaped its trial"
  let invalid ← (parameterCompatible (throwStratum .invalid "inapplicable trial")).run {}
  unless !invalid do throwError "an inapplicable trial was retained"
  let ambiguity ← try
    discard <| (parameterCompatible (throwSemanticAmbiguity "nested ambiguity")).run {}
    pure false
  catch error => pure (CasCatalogue.Exception.isSemanticAmbiguity error)
  unless ambiguity do throwError "a nested parameter ambiguity became inapplicability"
  let internal ← try
    discard <| (parameterCompatible (throwError "unexpected interpreter failure")).run {}
    pure false
  catch error => pure (CasCatalogue.Exception.stratum? error).isNone
  unless internal do throwError "an interpreter exception became inapplicability"

-- A partially applied object family is a function, never an admitted object value.
run_cmd liftTermElabM do
  let state ← registryState
  let rejected ← try
    discard <| (object state "Fin" #[] none).run {}
    pure false
  catch error => pure ((CasCatalogue.Exception.stratum? error) == some .invalid)
  unless rejected do
    throwError "an unresolved object-family parameter was admitted as object data"

/- A failed declaration remains in scope; later occurrences cannot become free variables. -/
run_cmd liftTermElabM do
  let harness ← Harness.empty
  let .ok binding := Parser.runParserCategory (← getEnv) `cas_stmt "let F := Fin(3,4)"
    | throwError "failed-binding probe did not parse"
  let (_, scope, bindingQuestion) ← runAsking harness {} binding
  unless scope.contains `F && bindingQuestion.isNone do
    throwError "a failed binding was dropped from the declared scope"
  let .ok assertion := Parser.runParserCategory (← getEnv) `cas_stmt "assert |F| = 3"
    | throwError "failed-binding use did not parse"
  let (_, _, question) ← runAsking harness scope assertion
  unless question.isNone do
    throwError "a failed fixed binding became an interpreted free-variable question"

/- Reading an admitted point and preparing its fixed execution remains distinct
from finding a missing implementation. No mathematical answer is supplied here.
Registered evidence artifacts stay inside this complete observation. -/
run_cmd withoutModifyingEnv <| liftTermElabM do
  let harness ← Harness.empty
  let harness := { harness with computationOnly := true }
  let .ok parsed := Parser.runParserCategory (← getEnv) `cas_stmt
      "assert (360).multiplicity(2) = 3"
    | throwError "admitted-point request did not parse"
  let (outcome, _, question) ← runAsking harness {} parsed
  unless outcome.kind == "gap" && question.isSome do
    throwError "a missing computation lost the admitted point's fixed question: {outcome.kind}: {outcome.detail}"
  let prepared ← interpret {} parsed
  for changeCategory in #[true, false] do
    let mut changed := false
    let altered := prepared.trace.fold (fun records term node =>
      let replacement := match node with
        | .admittedPoint id category parameters original originalCategory source target =>
            Node.admittedPoint id category parameters original
              (if changeCategory then CategoryId.groups else originalCategory)
              source (if changeCategory then target else source)
        | _ => node
      records.insert term replacement) ({} : Std.HashMap Lean.Expr Node)
    for (_, node) in prepared.trace.toArray do
      if node matches .admittedPoint .. then changed := true
    unless changed do throwError "the admitted-point probe did not reach an admission"
    let rejected ← tryCatchRuntimeEx
      (evaluate harness { prepared with trace := altered }) executionFailure
    unless rejected matches .internal _ do
      throwError "execution accepted an altered admitted-point category or endpoint"

/- The whole prepared binder request, including its operation snapshot, must be
read within the ordinary command budget. No mathematical answer is evaluated.
Registered evidence may generate equation lemmas while observing the request;
keep those artifacts in the observation environment, not this kernel module. -/
run_cmd withoutModifyingEnv <| liftTermElabM do
  let .ok binding := Parser.runParserCategory (← getEnv) `cas_stmt
      "let r(x) := x³ - 2x + 1 in ℚ[x]"
    | throwError "binder snapshot fixture did not parse"
  let some (name, value) ← letBinding? binding
    | throwError "binder snapshot fixture was not bound"
  let scope : Language.Scope := ({} : Language.Scope).insert name value
  let .ok parsed := Parser.runParserCategory (← getEnv) `cas_stmt
      "assert ∑_{a ∈ ((map r to ℂ[x]) in ℂ[x] ∖ 0).roots()} a = 0"
    | throwError "binder snapshot request did not parse"
  discard <| interpret scope parsed

/- Complete registered readings stay inside the ordinary preparation budget.
These observations compare no mathematical answer with an implementation. -/
run_cmd withoutModifyingEnv <| liftTermElabM do
  let bind (scope : Language.Scope) (text : String) : TermElabM Language.Scope := do
    let .ok parsed := Parser.runParserCategory (← getEnv) `cas_stmt text
      | throwError "differential binding did not parse"
    let some (name, value) ← letBinding? parsed
      | throwError "differential operand was not bound"
    return scope.insert name value
  let scope ← bind {} "let f := x ↦ 3x² + x + 1 in ℚ[x]"
  let scope ← bind scope "let F := x³ + (1/2)x² + x in ℚ[x]"
  let .ok parsed := Parser.runParserCategory (← getEnv) `cas_stmt "assert d(F) = f dx"
    | throwError "differential request did not parse"
  discard <| interpret scope parsed

run_cmd withoutModifyingEnv <| liftTermElabM do
  let bind (scope : Language.Scope) (text : String) : TermElabM Language.Scope := do
    let .ok parsed := Parser.runParserCategory (← getEnv) `cas_stmt text
      | throwError "span binding did not parse"
    let some (name, value) ← letBinding? parsed
      | throwError "span operand was not bound"
    return scope.insert name value
  let scope ← bind {} "let u₁ := (1, 0, 1) in ℚ³"
  let scope ← bind scope "let u₂ := (0, 1, 1) in ℚ³"
  let scope ← bind scope "let W := span({u₁, u₂})"
  let .ok parsed := Parser.runParserCategory (← getEnv) `cas_stmt "assert W.dim() = 2"
    | throwError "span request did not parse"
  discard <| interpret scope parsed
