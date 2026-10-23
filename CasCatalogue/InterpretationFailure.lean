/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CasContract.Failure

@[expose] public section

open Lean

namespace CasCatalogue

/-- Several semantic readings remain. The reader owns this failure; it is independent of
the contract's backend failure strata. -/
def throwSemanticAmbiguity {m : Type → Type} {α : Type} [Monad m] [MonadError m]
    (message : MessageData) : m α :=
  throwError (MessageData.tagged `CasCatalogue.throwSemanticAmbiguity
    m!"ambiguous statement: {message}")

/-- Recognize the reader's ambiguity through Lean's preserved message context. -/
def Exception.isSemanticAmbiguity (error : Exception) : Bool :=
  error.toMessageData.hasTag (· == `CasCatalogue.throwSemanticAmbiguity) ||
    Exception.stratum? error == some .semanticAmbiguity

/-- Only interpretation can reject a mathematical reading. Computational failures
cannot be emitted before a complete question exists; seeing one in the reader is
an internal failure of the interpretation path, not a missing leaf or bad reply. -/
inductive InterpretationFailureKind
  | invalid
  | ambiguous
  | internal
  deriving DecidableEq, Repr, Inhabited

/-- Classify an exception at the interpretation boundary, without consulting any
backend or interpreting a message string. Both the original reader tag and the
published semantic-ambiguity stratum retain their meaning. -/
def Exception.interpretationKind (error : Exception) : InterpretationFailureKind :=
  if Exception.isSemanticAmbiguity error then .ambiguous
  else if Exception.stratum? error == some .invalid then .invalid
  else .internal

end CasCatalogue
