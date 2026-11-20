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

/-- A source form whose translation is unfinished, distinct from invalid mathematics.
Reuse: Lean's tagged MessageData, as for semantic ambiguity above. -/
def throwUnsupportedSource {m : Type → Type} {α : Type} [Monad m] [MonadError m]
    (message : MessageData) : m α :=
  throwError (MessageData.tagged `CasCatalogue.throwUnsupportedSource message)

def Exception.isUnsupportedSource (error : Exception) : Bool :=
  error.toMessageData.hasTag (· == `CasCatalogue.throwUnsupportedSource)

/-- The tag of the failure "the source uses the name `name`, and no registration and no binding
declares it". A session uses it to tell a name whose own definition did not read. -/
def unknownSourceNameTag (name : String) : Name :=
  .str `CasCatalogue.unknownSourceName name

/-- Whether the failure is the unknown source name `name`. -/
def Exception.isUnknownSourceName (error : Exception) (name : String) : Bool :=
  error.toMessageData.hasTag (· == unknownSourceNameTag name)

end CasCatalogue
