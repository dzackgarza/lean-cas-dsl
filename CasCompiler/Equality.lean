module

public import CasCompiler.Resolve

public section

namespace CasCompiler

open Lean Meta Elab Term

/-- Actual source equality atoms and the licensed generic logical inference steps. -/
inductive SourceEqualityDerivation where
  | hypothesis (binding : BindingId)
  | operationConversion (evidence : SourceOperationAgreement)
  | operationRefinement (evidence : SourceOperationRefinement)
  | symmetry (original : SourceEqualityDerivation)
  | transitivity (first second : SourceEqualityDerivation)
  | congruence (function : SourceTerm) (original : SourceEqualityDerivation)

/-- A checked equality retains its complete terms, proposition, proof and source derivation. -/
structure SourceEquality where
  private mk ::
  derivation : SourceEqualityDerivation
  left : SourceTerm
  right : SourceTerm
  proposition : SourceTerm
  proof : SourceTerm

/-- Retain an already checked whole-family conversion without changing its original scope. -/
opaque SourceOperationAgreement.asEquality (evidence : SourceOperationAgreement) : SourceEquality :=
  ⟨.operationConversion evidence, evidence.left.term, evidence.right.term,
    evidence.proposition, evidence.proof⟩

/-- Retain the actual registered source restriction equality and both whole family terms. -/
opaque SourceOperationRefinement.asEquality (evidence : SourceOperationRefinement) :
    SourceEquality :=
  ⟨.operationRefinement evidence, evidence.original.term, evidence.term,
    evidence.proposition, evidence.proof⟩

private def equalityExpressions (left right proof : Expr) : MetaM (Array Expr) := do
  unless ← isDefEq (← inferType left) (← inferType right) do
    throwError "the source equality has different complete native endpoint types"
  let proposition ← mkEq left right
  unless ← isDefEq (← inferType proof) proposition do
    throwError "the source equality proof has a different complete native proposition"
  checkWithKernel (← mkExpectedTypeHint proof proposition)
  return #[left, right, proposition, proof]

/-- Use an actual equality hypothesis from the complete source context, by stable binding ID.
Reuse: ContextTelescope's formal roles and native local proof typing; the hypothesis stays rigid. -/
opaque SourceSession.equalityAssumption (session : SourceSession) (reference : Syntax)
    (binding : BindingId) : TermElabM SourceEquality := do
  let #[left, right, proposition, proof] ← session.elaborateMany reference fun context => do
      let some original := context.bindings.find? (·.id == binding)
        | throwError "the source equality hypothesis is outside the complete current context"
      unless original.role == .hypothesis do
        throwError "source equality assumption requires an actual formal hypothesis"
      let type ← whnfR (← inferType original.expression)
      unless type.isAppOfArity ``Eq 3 do
        throwError "the source hypothesis is not a native equality proposition"
      let #[_, left, right] := type.getAppArgs
        | throwError "the source hypothesis has an invalid native equality interface"
      equalityExpressions left right original.expression
    | throwError "source equality assumption returned an invalid evidence family"
  return ⟨.hypothesis binding, left, right, proposition, proof⟩

/-- Apply native equality symmetry in the full current source context.
Reuse: Lean Eq.symm, exact expected-type checking and synchronous kernel checking. -/
opaque SourceSession.equalitySymmetry (session : SourceSession) (reference : Syntax)
    (evidence : SourceEquality) : TermElabM SourceEquality := do
  let #[left, right, proposition, proof] ← session.elaborateMany reference fun context => do
      let left ← evidence.right.source.inContext context
      let right ← evidence.left.source.inContext context
      let proof ← mkAppM ``Eq.symm #[← evidence.proof.source.inContext context]
      equalityExpressions left right proof
    | throwError "source equality symmetry returned an invalid evidence family"
  return ⟨.symmetry evidence.derivation, left, right, proposition, proof⟩

/-- Compose checked equalities only at the same complete native intermediate term.
Reuse: Lean Eq.trans; source terms remain rigid under stable-ID context transport. -/
opaque SourceSession.equalityTransitivity (session : SourceSession) (reference : Syntax)
    (first second : SourceEquality) : TermElabM SourceEquality := do
  let #[left, right, proposition, proof] ← session.elaborateMany reference fun context => do
      let middle ← first.right.source.inContext context
      let other ← second.left.source.inContext context
      unless ← isDefEq (← inferType middle) (← inferType other) <&&> isDefEq middle other do
        throwError "source equality transitivity has different complete native intermediate terms"
      let left ← first.left.source.inContext context
      let right ← second.right.source.inContext context
      let proof ← mkAppM ``Eq.trans
        #[← first.proof.source.inContext context, ← second.proof.source.inContext context]
      equalityExpressions left right proof
    | throwError "source equality transitivity returned an invalid evidence family"
  return ⟨.transitivity first.derivation second.derivation, left, right, proposition, proof⟩

/-- Apply nondependent congruence with the actual retained source function.
Reuse: Lean congrArg and exact native checking; the resulting goal retains that whole function. -/
opaque SourceSession.equalityCongruence (session : SourceSession) (reference : Syntax)
    (function : SourceTerm) (evidence : SourceEquality) : TermElabM SourceEquality := do
  let #[left, right, proposition, proof] ← session.elaborateMany reference fun context => do
      let function ← function.source.inContext context
      let left := mkApp function (← evidence.left.source.inContext context)
      let right := mkApp function (← evidence.right.source.inContext context)
      let proof ← mkAppM ``congrArg #[function, ← evidence.proof.source.inContext context]
      equalityExpressions left right proof
    | throwError "source equality congruence returned an invalid evidence family"
  return ⟨.congruence function evidence.derivation, left, right, proposition, proof⟩

/-- A native dependent transport retains the exact motive, source value and equality derivation. -/
structure SourceSubstitution where
  private mk ::
  equality : SourceEquality
  motive : SourceTerm
  input : SourceTerm
  value : SourceTerm

/-- Transport the actual source value along the licensed equality at its complete dependent type.
Reuse: Lean congrArg and Eq.mp; no object, value or dependent index is chosen by conversion. -/
opaque SourceSession.equalitySubstitution (session : SourceSession) (reference : Syntax)
    (motive : SourceTerm) (equality : SourceEquality) (input : SourceTerm) :
    TermElabM SourceSubstitution := do
  let typeEquality ← session.equalityCongruence reference motive equality
  let value ← session.elaborate reference fun context => do
    let source ← typeEquality.left.source.inContext context
    let target ← typeEquality.right.source.inContext context
    discard <| getLevel source
    discard <| getLevel target
    let original ← input.source.inContext context
    unless ← isDefEq (← inferType original) source do
      throwError "equality substitution has a different complete native source value type"
    let value ← mkAppM ``Eq.mp #[← typeEquality.proof.source.inContext context, original]
    unless ← isDefEq (← inferType value) target do
      throwError "equality substitution has a different complete native target value type"
    checkWithKernel (← mkExpectedTypeHint value target)
    return value
  return ⟨equality, motive, input, value⟩

end CasCompiler
