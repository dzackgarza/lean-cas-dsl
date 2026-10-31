module

import CasCatalogue.Trace
meta import CasCatalogue.Trace

/- Engineering controls for producer proof boundaries and exact local validation reuse.
Original ProofIdentityProbes and ProducerOccurrenceProbes are unchanged. -/

open Lean Meta Elab Command Term CasCatalogue

private def requireClosureFailure (expected : String) (action : TermElabM Unit) :
    TermElabM Unit := do
  let failure ← try
      action
      pure none
    catch error => pure (some (← error.toMessageData.toString))
  unless failure == some expected do
    throwError "producer proof-boundary control expected {expected}, got {failure}"

private def copiedOrdinal (value : Expr) (raw : Bool := false) : TermElabM Expr := do
  let some anchor := Trace.producerAnchor? value
    | throwError "the control requires an original complete producer anchor"
  let ordinal := if raw then mkRawNatLit (anchor.occurrence + 1) else toExpr anchor.occurrence
  return mkAppN value.getAppFn (value.getAppArgs.set! 0 ordinal)

/- A checked private proof constant whose producer occurs only in its type. This
is a reflexive engineering expression, not a registered mathematical assertion. -/
private def proofWithAbsentProducer :
    Trace.producerResult 0 "engineering.producer.unrecorded_proof_type" (0 : Nat) =
    Trace.producerResult 0 "engineering.producer.unrecorded_proof_type" (0 : Nat) := rfl

/- Only a checked implementation of the same original proposition may contain the
OfNat copy. The producer's original key, selected record and proposition stay exact. -/
run_cmd liftTermElabM <| withoutErrToSorry <| withCurrHeartbeats do
  let trace ← Trace.new
  let zero := mkRawNatLit 0
  let node := Node.functor ⟨"engineering.producer.proof_boundary"⟩ #[] zero
  let original ← Trace.recordProduced (some trace) zero node
  let copied ← copiedOrdinal original
  let absentRaw ← copiedOrdinal original true
  unless original != copied && (Trace.producerAnchor? copied).isNone &&
      (Trace.producerAnchor? absentRaw).isSome do
    throwError "the proof control did not separate raw addresses from numeral copies"
  let proposition ← mkEq original original
  let implementation ← mkEqRefl copied
  let checked ← mkExpectedTypeHint implementation proposition
  unless (← isTypeCorrect checked) && (← inferType checked) == proposition &&
      (checked.find? (·.equal copied)).isSome &&
      (proposition.find? (·.equal copied)).isNone do
    throwError "the proof copy is not confined to checked evidence at the original target"
  let entries := (← trace.get).toArray
  Trace.checkProducedEntries entries #[checked]
  let missing := "a selected producer reference is outside its complete trace"
  for data in #[copied, absentRaw, mkApp (mkConst ``Nat.succ) copied] do
    unless ← isTypeCorrect data do throwError "a negative data control is ill-typed"
    requireClosureFailure missing (Trace.checkProducedEntries entries #[data])
  let dataType := mkApp (mkConst ``Fin) copied
  unless ← isTypeCorrect dataType do throwError "the negative data-type control is ill-typed"
  requireClosureFailure missing (Trace.checkProducedEntries entries #[dataType])
  -- Unit has a unique value but is Type-valued data, not a Prop-valued proof.
  let uniqueWitness ← mkAppM ``Trace.producerArgument #[copied, mkConst ``Unit.unit]
  unless (← isTypeCorrect uniqueWitness) && !(← isProof uniqueWitness) do
    throwError "the unique-witness control is not Type-valued data"
  requireClosureFailure missing (Trace.checkProducedEntries entries #[uniqueWitness])
  for missingReference in #[copied, absentRaw] do
    let changedProposition ← mkEq missingReference missingReference
    let changedProof ← mkEqRefl missingReference
    for value in #[changedProposition, changedProof] do
      unless ← isTypeCorrect value do throwError "a negative proposition control is ill-typed"
      requireClosureFailure missing (Trace.checkProducedEntries entries #[value])
  -- Every retained node is still checked, including one absent from the roots.
  let retained := Node.functor ⟨"engineering.producer.retained_field"⟩ #[copied] zero
  requireClosureFailure missing
    (Trace.checkProducedEntries (entries.push (checked, retained)) #[original])
  -- isProof can classify this unchecked application, but it must not hide its body.
  let invalid := mkApp2 (mkConst ``id [.zero]) (mkConst ``True) zero
  unless (← isProof invalid) && !(← isTypeCorrect invalid) do
    throwError "the unchecked proof control is not proof-looking ill-typed syntax"
  requireClosureFailure "a producer proof boundary contains an ill-typed proof"
    (Trace.checkProducedEntries entries #[invalid])
  let constant := Lean.mkConst ``proofWithAbsentProducer
  let constantType ← inferType constant
  unless (← isProof constant) && (← isTypeCorrect constant) &&
      (constant.find? (·.isAppOfArity ``Trace.producerResult 4)).isNone &&
      (constantType.find? (·.isAppOfArity ``Trace.producerResult 4)).isSome do
    throwError "the proof-constant control did not hide its producer solely in its type"
  requireClosureFailure missing (Trace.checkProducedEntries entries #[constant])
  withLocalDeclD `h proposition fun h =>
    Trace.checkProducedEntries entries #[h]
  withLocalDeclD `h constantType fun h => do
    unless (← isProof h) && (h.find? (·.isAppOfArity ``Trace.producerResult 4)).isNone do
      throwError "the local-proof control is not a bare proof variable"
    requireClosureFailure missing (Trace.checkProducedEntries entries #[h])

/- A producer whose result itself is a proof still needs its original exact record.
Metadata and additional application arguments must not hide that producer address. -/
run_cmd liftTermElabM <| withoutErrToSorry <| withCurrHeartbeats do
  let trace ← Trace.new
  let zero := mkRawNatLit 0
  let node := Node.functor ⟨"engineering.producer.proof_result"⟩ #[] zero
  let proof ← mkEqRefl zero
  let original ← Trace.recordProduced (some trace) proof node
  let copied ← copiedOrdinal original
  let function ← instantiateMVars
    (← elabTermAndSynthesize (← `(fun (_ : Nat) => True.intro)) none)
  let callable ← Trace.recordProduced (some trace) function node
  let copiedCallable ← copiedOrdinal callable
  let entries := (← trace.get).toArray
  let metadataApplication := mkApp (mkMData {} callable) zero
  let missingMetadataApplication := mkApp (mkMData {} copiedCallable) zero
  unless !(missingMetadataApplication.getAppFn.isConstOf ``Trace.producerResult) &&
      (← isProof missingMetadataApplication) && (← isTypeCorrect missingMetadataApplication) do
    throwError "the combined metadata/application control lost its checked proof spine"
  Trace.checkProducedEntries entries
    #[original, mkApp callable zero, metadataApplication]
  for missing in #[copied, mkMData {} copied, mkApp copiedCallable zero,
      missingMetadataApplication] do
    unless (← isProof missing) && (← isTypeCorrect missing) do
      throwError "the missing proof producer is not a type-correct proof"
    requireClosureFailure "a selected producer reference is outside its complete trace"
      (Trace.checkProducedEntries entries #[missing])
  let changed := Node.construction ⟨"engineering.producer.changed_proof_record"⟩ #[] zero
  requireClosureFailure "the producer anchor changed its complete selected record"
    (Trace.checkProducedEntries #[(original, changed)] #[original])

/- Open binders only for type inspection. Repeated raw bodies occur under different
let values, and dependent proof propositions retain the original binder reference. -/
run_cmd liftTermElabM <| withoutErrToSorry <| withCurrHeartbeats do
  let trace ← Trace.new
  let zero := mkRawNatLit 0
  let original ← Trace.recordProduced (some trace) zero
    (.functor ⟨"engineering.producer.dependent_proof"⟩ #[] zero)
  let copied ← copiedOrdinal original
  let body (n : Expr) : TermElabM Expr := do
    let actual := mkApp2 (mkConst ``Nat.add) original n
    let internal := mkApp2 (mkConst ``Nat.add) copied n
    let proposition ← mkEq actual actual
    let proof ← mkExpectedTypeHint (← mkEqRefl internal) proposition
    mkAppM ``Trace.producerArgument #[proof, mkApp (mkConst ``Nat.succ) n]
  let dependent ← withLocalDeclD `n (mkConst ``Nat) fun n => do
    mkLambdaFVars #[n] (← body n)
  let letBody (value : Nat) : TermElabM Expr :=
    withLetDecl `n (mkConst ``Nat) (mkRawNatLit value) fun n => do
      mkLetFVars #[n] (← body n)
  let first ← letBody 7
  let second ← letBody 11
  let .letE _ _ firstValue firstBody _ := first
    | throwError "the contextual producer control lost its first let binder"
  let .letE _ _ secondValue secondBody _ := second
    | throwError "the contextual producer control lost its second let binder"
  unless firstValue != secondValue && firstBody == secondBody do
    throwError "the contextual control does not reuse raw syntax under distinct lets"
  for value in #[dependent, first, second] do
    unless ← isTypeCorrect value do throwError "a dependent producer control is ill-typed"
  let entries := (← trace.get).toArray
  Trace.checkProducedEntries entries #[dependent, first, second]
  Trace.checkProducedEntries entries #[second, first, dependent]
  let bad ← withLocalDeclD `n (mkConst ``Nat) fun n => do
    let actual := mkApp2 (mkConst ``Nat.add) copied n
    let proof ← mkEqRefl actual
    let value ← mkAppM ``Trace.producerArgument #[proof, mkApp (mkConst ``Nat.succ) n]
    mkLambdaFVars #[n] value
  unless ← isTypeCorrect bad do throwError "the dependent negative control is ill-typed"
  requireClosureFailure "a selected producer reference is outside its complete trace"
    (Trace.checkProducedEntries entries #[dependent, bad])

/- Inference/abstraction does not license let reduction or an open body's reuse as
an exact trace address. The prepared trace contains closed original producer keys. -/
run_cmd liftTermElabM <| withoutErrToSorry <| withCurrHeartbeats do
  let trace ← Trace.new
  let zero := mkRawNatLit 0
  let formal := Expr.letE `n (mkConst ``Nat) zero (mkBVar 0) false
  let original ← Trace.recordProduced (some trace) formal
    (.functor ⟨"engineering.producer.retained_let"⟩ #[] formal)
  let proposition ← mkEq original original
  let proof ← mkExpectedTypeHint (← mkEqRefl zero) proposition
  unless (← isTypeCorrect proof) && (← inferType proof) == proposition do
    throwError "the checked let-valued producer lost its exact original proposition"
  let entries := (← trace.get).toArray
  Trace.checkProducedEntries entries #[proof]
  let rewritten := original.replace fun term => if term.equal formal then some zero else none
  unless rewritten != original && (← isTypeCorrect rewritten) do
    throwError "the let-substitution control did not change a complete typed producer key"
  let rewrittenProof ← mkEqRefl rewritten
  requireClosureFailure "a selected producer reference is outside its complete trace"
    (Trace.checkProducedEntries entries #[rewrittenProof])
  let (raw, rawNode, closed) ← withLocalDeclD `n (mkConst ``Nat) fun n => do
    let localTrace ← Trace.new
    let node := Node.functor ⟨"engineering.producer.open_body"⟩ #[n] n
    let opened ← Trace.recordProduced (some localTrace) n node
    let raw := opened.abstract #[n]
    let rawNode ← node.mapTermsM fun term => pure (term.abstract #[n])
    return (raw, rawNode, ← mkLambdaFVars #[n] opened)
  unless raw.hasLooseBVars && !closed.hasLooseBVars && (← isTypeCorrect closed) &&
      !(← isTypeCorrect raw) do
    throwError "the open-key control did not separate a well-typed lambda from its raw body"
  requireClosureFailure "the producer anchor is outside its original complete type"
    (Trace.checkProducedEntries #[(raw, rawNode)] #[closed])

/- The trace dictionary uses Expr.eqv; successful validation reuse must instead
retain exact raw syntax and exact ordered fields. Both single records below are
valid, but an alpha-equivalent reference against the other record must reject. -/
run_cmd liftTermElabM <| withoutErrToSorry <| withCurrHeartbeats do
  let zero := mkRawNatLit 0
  let type := Lean.mkConst ``Nat
  let lambdaA := Expr.lam `x type (mkBVar 0) .default
  let lambdaB := Expr.lam `y type (mkBVar 0) .default
  unless lambdaA == lambdaB && !lambdaA.equal lambdaB do
    throwError "the exact-record control did not distinguish Expr.eqv from Expr.equal"
  let nodeA := Node.functor ⟨"engineering.producer.exact_cached_record"⟩ #[lambdaA] zero
  let nodeB := Node.functor ⟨"engineering.producer.exact_cached_record"⟩ #[lambdaB] zero
  let trace ← Trace.new
  let recorded ← Trace.recordProduced (some trace) zero nodeB
  let reference := recorded.replace fun term =>
    if term.equal lambdaB then some lambdaA else none
  unless recorded == reference && !recorded.equal reference && nodeA == nodeB &&
      (← isTypeCorrect recorded) && (← isTypeCorrect reference) do
    throwError "the exact-record control lost its closed alpha-equivalent producers"
  let table := Std.HashMap.ofArray #[(recorded, nodeB)]
  unless (table[reference]?).isSome do
    throwError "the alpha-equivalent reference does not exercise the actual trace lookup"
  Trace.checkProducerRecord reference nodeA
  Trace.checkProducerRecord recorded nodeB
  let expected := "the producer anchor changed an ordered typed field"
  requireClosureFailure expected
    (Trace.checkProducedEntries #[(recorded, nodeB)] #[reference])
  -- Each original association must still be authenticated, even if insertion
  -- selects a different alpha-equivalent representative for the complete map.
  for entries in #[#[(reference, nodeA), (recorded, nodeB)],
      #[(recorded, nodeB), (reference, nodeA)],
      #[(recorded, nodeA), (recorded, nodeB)]] do
    requireClosureFailure expected
      (Trace.checkProducedEntries entries)
