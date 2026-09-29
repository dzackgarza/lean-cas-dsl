/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CasCatalogue.Leaf
public import CasLeaves.Foundation.Cardinality
public meta import CasCatalogue.Leaf
public meta import CasLeaves.Foundation.Cardinality

@[expose] public section

/-!
# Cardinalities of free modules computed by Sage

This leaf's program (`CasLeaves/Modules/SageCardinality/sage_cardinality.py`, owned by the leaf)
answers the registered semantic operation `meth.cardinality` on the free modules `(ℤ/n)^k`
realized by `rz.modules.zmod_free`; the answer is decoded into a cardinal handle, the method's
semantic result type, or rejected. The answer is the backend's assertion (CC-TRUST): the decoder
checks its shape, not its truth.
-/

open Lean
open CasCatalogue.Foundation.Cardinality

namespace CasCatalogue.Modules.SageCardinality

/-- Decode Sage's cardinal. -/
def decodeCardinality (j : Json) : Except String CardinalHandle := do
  match ← j.getObjValAs? String "cardinal" with
  | "aleph0" => pure .aleph0
  | "finite" => return .finite (← j.getObjValAs? Nat "n")
  | other => throw s!"not a cardinal: {other}"

/-- The command running the leaf's program: `CAS_SAGE_PYTHON` (default `.venv/bin/python`). -/
def sageCommand : IO String := return (← IO.getEnv "CAS_SAGE_PYTHON").getD ".venv/bin/python"

def connectSage (state : RegistryState) : IO (Except Backend.PortError Backend.Conn) := do
  Backend.connect state "sage" (← sageCommand)
    #["CasLeaves/Modules/SageCardinality/sage_cardinality.py"]

/-- The cardinality of `(ℤ/n)^k`, computed by Sage and decoded; a rejected answer is malformed. -/
def sageCardinality (c : Backend.Conn) (n k : ℕ) : IO (Except Backend.PortError CardinalHandle) :=
  Backend.callDecoded c "meth.cardinality" (Json.mkObj [("n", toJson n), ("k", toJson k)])
    decodeCardinality

/-- The cardinality of `(ℤ/n)^k` by a fresh connection to the leaf's program. -/
def sageCardinalityOf (n k : ℕ) (state : RegistryState) :
    IO (Except Backend.PortError CardinalHandle) := do
  match ← connectSage state with
  | .error e => return .error e
  | .ok c =>
      let answer ← sageCardinality c n k
      Backend.stop c
      return answer

end CasCatalogue.Modules.SageCardinality

namespace CasCatalogue

register_leaf
  { backend := "sage"
    contributions := [
  .backendOperation
  { id := ⟨"bop.sage.modules.cardinality"⟩, backend := "sage", operation := "meth.cardinality"
    decoder := `CasCatalogue.Modules.SageCardinality.decodeCardinality }] }

end CasCatalogue
