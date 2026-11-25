module

public import CasCompiler.LimitInterface
public import Mathlib.CategoryTheory.Limits.Creates

public section

namespace CasCompiler

open Lean Meta CasCatalogue

/-- The complete fixed creation chosen at the original source boundary. The target cone and
its universal data are separate original inputs. In particular, neither a Cone value nor an
existence proposition supplies the target mediator. Every term travels in the same full source
context; these are retained source fields, not mathematical inhabitants reconstructed from JSON. -/
structure LimitCreationInterface (term : Type) where
  lift : LiftId
  declaration : Name
  edge : EdgeRef
  evidence : term
  createsLimit : term
  functor : term
  diagram : term
  targetCone : term
  targetUniversal : term
  standardization : term
  standardizedCone : term
  standardizedUniversal : term
  /-- Fixed source-derived action on the original target cone and universal data.
  The diagram transport stays inside this action; it is never evaluated by the kernel. -/
  requestFamily : term
  result : term

abbrev NativeLimitCreationInterface := LimitCreationInterface Expr

/-- Preserve the exact ordered native fields through closure and substitution. -/
def LimitCreationInterface.mapM [Monad m] (original : LimitCreationInterface α)
    (f : α → m β) : m (LimitCreationInterface β) := do
  return {
    lift := original.lift
    declaration := original.declaration
    edge := original.edge
    evidence := ← f original.evidence
    createsLimit := ← f original.createsLimit
    functor := ← f original.functor
    diagram := ← f original.diagram
    targetCone := ← f original.targetCone
    targetUniversal := ← f original.targetUniversal
    standardization := ← f original.standardization
    standardizedCone := ← f original.standardizedCone
    standardizedUniversal := ← f original.standardizedUniversal
    requestFamily := ← f original.requestFamily
    result := ← f original.result }

/-- The typed owner envelope stores all eleven native fields in this declared order. -/
def LimitCreationInterface.terms (original : LimitCreationInterface α) : Array α :=
  #[original.evidence, original.createsLimit, original.functor, original.diagram,
    original.targetCone, original.targetUniversal, original.standardization,
    original.standardizedCone, original.standardizedUniversal, original.requestFamily,
    original.result]

/-- Decode only the exact typed field table of the original owner envelope. -/
def LimitCreationInterface.ofTerms (lift : LiftId) (declaration : Name) (edge : EdgeRef)
    (terms : Array α) : Except String (LimitCreationInterface α) := do
  let #[evidence, createsLimit, functor, diagram, targetCone, targetUniversal,
      standardization, standardizedCone, standardizedUniversal, requestFamily, result] := terms
    | throw "the selected creation lost its complete original typed interface"
  return {
    lift := lift, declaration := declaration, edge := edge
    evidence := evidence, createsLimit := createsLimit, functor := functor, diagram := diagram
    targetCone := targetCone, targetUniversal := targetUniversal
    standardization := standardization, standardizedCone := standardizedCone
    standardizedUniversal := standardizedUniversal, requestFamily := requestFamily
    result := result }

end CasCompiler
