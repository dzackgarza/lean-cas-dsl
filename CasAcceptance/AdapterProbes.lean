/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CasContract.Adapter
public import CasAcceptance.UnivProbes
public import CasLeaves.Algebra.KernelDecode
public import CasLeaves.Algebra.RingTables
public meta import CasContract.Adapter
public meta import CasAcceptance.UnivProbes
public meta import CasLeaves.Algebra.KernelDecode
public meta import CasLeaves.Algebra.RingTables

@[expose] public section

/-!
# Kernel decoding (CC-DECODE)

A backend's kernel of `sign : S₃ → ℤ/2` decodes into the semantic subgroup `A₃ ↪ S₃`, equal to the
Lean-native kernel; kernels of the trivial and identity maps round-trip likewise. A result without
its inclusion, a result that misses kernel elements, and a result for another operation are
rejected. (The refusals of `register_leaf` are tested with the contract, in
`CasContract.Probes.LeafBoundary`; no leaf is registered in this repository.)
-/

open Lean Meta Elab Term Command
open CasCatalogue.Algebra.Actions CasCatalogue.Algebra.Subgroups CasCatalogue.Algebra.KernelDecode
open CasCatalogue.PropsProbes

namespace CasCatalogue.AdapterProbes

/-- `ℤ/2`. -/
abbrev z2 : GroupTable :=
  { size := 2, mul := fun a b => a + b, assoc := by decide, one := 0, one_mul := by decide
    mul_one := by decide, inv := fun a => a, inv_mul := by decide }

/-- The sign on the indices of `S₃ = D₃`. -/
def signMap (x : Fin 6) : Fin 2 := if x.val < 3 then 0 else 1

/-- The sign of `S₃ = D₃`: rotations `↦ 0`, reflections `↦ 1`. -/
def sign : HomHandle :=
  { source := s3, target := z2, map := signMap, map_mul := by decide }

/-- The trivial map `S₃ → ℤ/2`, and the identity of `S₃`. -/
def trivialMap : HomHandle :=
  { source := s3, target := z2, map := fun _ => (0 : Fin 2), map_mul := by decide }
def identityMap : HomHandle :=
  { source := s3, target := s3, map := id, map_mul := by decide }

/-- The elements of a subgroup, as indices in its ambient group. -/
def members (h : SubgroupHandle) : List ℕ :=
  ((List.finRange h.source.size).map fun a => (h.map a).val).mergeSort (fun a b => decide (a ≤ b))

/-- Decode what a backend sends for the native kernel. -/
def roundTrip (f : HomHandle) : Option (List ℕ) :=
  (nativeKernel f).bind fun k => (decodeKernel f (encodeKernel k)).toOption.map members

#guard (nativeKernel sign).map members == some [0, 1, 2]
#guard roundTrip sign == (nativeKernel sign).map members
#guard roundTrip trivialMap == some [0, 1, 2, 3, 4, 5]
#guard roundTrip identityMap == some [0]

/-- The backend's answer with its inclusion dropped. -/
def withoutInclusion (f : HomHandle) : Option BackendResult :=
  (nativeKernel f).map fun k =>
    let r := encodeKernel k
    { r with encoded := Json.mkObj [("subgroup", (r.encoded.getObjValD "subgroup"))] }

/-- The trivial subgroup, claimed as the kernel of the sign. -/
def tooSmall : Option BackendResult := (nativeKernel identityMap).map encodeKernel

def rejection (f : HomHandle) (r : Option BackendResult) : Option String :=
  r.bind fun r => match decodeKernel f r with
    | .error message => some message
    | .ok _ => none

/-- Whether a rejection message mentions `s`. -/
def mentions (s : String) (m : String) : Bool := decide ((m.splitOn s).length > 1)

/-- The sign's kernel, reported as the image. -/
def misnamed : Option BackendResult :=
  (nativeKernel sign).map fun k => { encodeKernel k with operation := "op.groups.image" }

#guard (rejection sign (withoutInclusion sign)).map (mentions "defining arrow") == some true
#guard (rejection sign tooSmall).map (mentions "misses kernel") == some true
#guard (rejection sign misnamed).map (mentions "not lim.groups.kernel") == some true

end CasCatalogue.AdapterProbes
