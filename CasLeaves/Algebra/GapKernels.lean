/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CasCatalogue.Leaf
public import CasCatalogue.Semantics.Limits.Registration
public import CasLeaves.Algebra.KernelDecode
public meta import CasCatalogue.Leaf
public meta import CasCatalogue.Semantics.Limits.Registration

@[expose] public section

/-!
# Kernels of groups computed by GAP

The leaf's backend program (`CasLeaves/Algebra/GapKernels/gap_kernels.py`, owned by this leaf)
answers the registered semantic operation
`lim.groups.kernel`: GAP computes the kernel of a homomorphism of group tables, and the answer is
decoded by `decodeKernel` into a subgroup of the source with its inclusion (checked: group laws,
injective homomorphism, exactly the kernel), or rejected. The leaf declares the operation for the
backend `gap`; nothing else about groups, subgroups or kernels is the backend's.
-/

open Lean
open CasCatalogue.Algebra.Actions CasCatalogue.Algebra.Subgroups CasCatalogue.Algebra.KernelDecode

namespace CasCatalogue.Algebra.GapKernels

/-- The multiplication table of a group table, as JSON rows. -/
def encodeTable (t : GroupTable) : Json :=
  Json.mkObj [("size", toJson t.size), ("mul", Json.arr <| (List.finRange t.size).toArray.map
    fun a => Json.arr <| (List.finRange t.size).toArray.map fun b => toJson (t.mul a b).val)]

/-- A homomorphism of group tables, as the adapter reads it. -/
def encodeHom (f : HomHandle) : Json :=
  Json.mkObj [("source", encodeTable f.source), ("target", encodeTable f.target),
    ("map", Json.arr <| (List.finRange f.source.size).toArray.map fun a => toJson (f.map a).val)]

/-- The command running the leaf's program: `CAS_GAP_PYTHON` (default `.venv/bin/python`) running the adapter, with
the given flags. -/
def gapCommand : IO String := return (← IO.getEnv "CAS_GAP_PYTHON").getD ".venv/bin/python"

/-- Connect to the GAP adapter, checking its announced operations against the registry. -/
def connectGap (state : RegistryState) (flags : Array String := #[]) :
    IO (Except Backend.PortError Backend.Conn) := do
  Backend.connect state "gap" (← gapCommand) (#["CasLeaves/Algebra/GapKernels/gap_kernels.py"] ++ flags)

/-- The kernel of `f`, computed by GAP and decoded; a rejected answer is malformed. -/
def gapKernel (c : Backend.Conn) (f : HomHandle) : IO (Except Backend.PortError SubgroupHandle) :=
  Backend.callDecoded c kernelOperation (encodeHom f) fun encoded =>
    decodeKernel f { operation := kernelOperation, encoded }

end CasCatalogue.Algebra.GapKernels

namespace CasCatalogue

register_leaf
  { backend := "gap"
    contributions := [
  .backendOperation
  { id := ⟨"bop.gap.groups.kernel"⟩, backend := "gap", operation := "lim.groups.kernel"
    decoder := `CasCatalogue.Algebra.KernelDecode.decodeKernel }] }

end CasCatalogue
