/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Lean.Exception

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
  error.toMessageData.hasTag (· == `CasCatalogue.throwSemanticAmbiguity)

end CasCatalogue
