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
  let .object coefficient _ (some (selectedEntry, _)) := selected
    | throwError "constructor probe lost its registered coefficient origin"
  let trace ← Trace.new
  let series ← (object state constructor.name #[selected] (some sets)).run { trace := some trace }
  let .object seriesHandle _ (some (_, #[stored])) := series
    | throwError "typed constructor probe lost its parameters"
  unless stored.declarations == selected.declarations do
    throwError "typed constructor erased its selected parameter category"
  let exact ← (typedParamTerms constructor.declaration #[selected]).run { trace := some trace }
  let exactTerm ← elabTermAndSynthesize exact[0]! none
  unless ← Lean.Meta.isDefEq exactTerm coefficient do
    throwError "an already typed selected parameter was replaced"
  let recovered ← (recognize state seriesHandle sets).run {}
  let .object _ _ (some (_, #[.object _ parameterCategory (some (parameterEntry, _))])) := recovered
    | throwError "structured constructor parameter lost its registered origin"
  unless parameterCategory.id == commutative.id && parameterEntry.id == selectedEntry.id do
    throwError "structured constructor recognition changed the coefficient category or origin"

-- An explicitly selected structure supplies its own routes; competing named sources stay ambiguous.
run_cmd liftTermElabM do
  let state ← registryState
  let sets ← categoryNamed state "Sets"
  let rings ← categoryNamed state "Rings"
  let trace ← Trace.new
  let plain ← (object state "ℂ" #[] (some sets)).run { trace := some trace }
  let selected ← (object state "ℂ" #[] (some rings)).run { trace := some trace }
  let .object _ _ (some (selectedEntry, _)) := selected
    | throwError "structural parameter probe lost its selected origin"
  let some sum := state.morphisms.find? (·.name == "∑")
    | throwError "structural parameter probe has no registered family"
  let domain ← (object state "Fin" #[.nat 2] (some sets)).run {}
  discard <| (typedParamTerms sum.declaration #[domain, selected]).run { trace := some trace }
  let transported := (← trace.get).toArray.any fun (_, node) => match node with
    | .parameterTransport source sourceCategory targetCategory route _ =>
        source == selectedEntry.id && sourceCategory == rings.id &&
          targetCategory != rings.id && !route.isEmpty
    | _ => false
  unless transported do
    throwError "structural parameter route or exact source provenance was erased"
  let competing ← try
    discard <| (typedParamTerms sum.declaration #[domain, plain]).run {}
    pure false
  catch error => pure ((CasCatalogue.Exception.stratum? error) == some .semanticAmbiguity)
  unless competing do
    throwError "competing registered parameter origins were merged by carrier coincidence"
  let .object plainHandle .. := plain | unreachable!
  let anonymous := Value.object plainHandle sets none
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
    discard <| (parameterCompatible (throwStratum .semanticAmbiguity "nested ambiguity")).run {}
    pure false
  catch error => pure ((CasCatalogue.Exception.stratum? error) == some .semanticAmbiguity)
  unless ambiguity do throwError "a nested parameter ambiguity became inapplicability"
  let internal ← try
    discard <| (parameterCompatible (throwError "unexpected interpreter failure")).run {}
    pure false
  catch error => pure (CasCatalogue.Exception.stratum? error).isNone
  unless internal do throwError "an interpreter exception became inapplicability"
