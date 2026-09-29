/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CasCatalogue.Adapter
public import CasAcceptance.UnivProbes
public import CasLeaves.Algebra.KernelDecode
public import CasLeaves.Algebra.RingTables
public meta import CasCatalogue.Adapter
public meta import CasAcceptance.UnivProbes
public meta import CasLeaves.Algebra.KernelDecode
public meta import CasLeaves.Algebra.RingTables

@[expose] public section

/-!
# Acceptance for `cc-adapter` (CC-ADAPTER, CC-DECODE)

* A backend leaf registers its permitted contributions with `register_leaf`; each of the ten
  forbidden contributions of spec §5 is rejected with a diagnostic naming the rule, and a contract
  containing one registers nothing. A permitted contribution that does not typecheck against the
  semantic universe (a realizer of an unregistered category) is rejected too.
* A backend's kernel of `sign : S₃ → ℤ/2` decodes into the semantic subgroup `A₃ ↪ S₃`, equal to
  the Lean-native kernel; kernels of the trivial and identity maps round-trip likewise. A result
  without its inclusion, a result that misses kernel elements, and a result for another operation
  are rejected.
-/

open Lean Meta Elab Term Command
open CasCatalogue.Algebra.Actions CasCatalogue.Algebra.Subgroups CasCatalogue.Algebra.KernelDecode
open CasCatalogue.PropsProbes

namespace CasCatalogue.AdapterProbes

/- A backend leaf realizing rings, by its own name for the table denotation. -/
register_leaf
  { backend := "probe-sage"
    contributions := [.realizer
      { id := ⟨"rz.probe.sage_rings"⟩, category := ⟨"cat.rings"⟩, backend := "probe-sage"
        denotation := `CasCatalogue.Algebra.RingTables.ringTableDenotation }] }

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
#guard (rejection sign misnamed).map (mentions "not op.groups.kernel") == some true

run_cmd liftTermElabM do
  let expectRule (contribution : LeafContribution) (rule : String) : MetaM Unit := do
    let contract : LeafContract := { backend := "probe-sage", contributions := [contribution] }
    try
      discard <| contract.check
      throwError "a forbidden contribution was accepted: {rule}"
    catch err =>
      let message ← err.toMessageData.toString
      unless (message.splitOn rule).length > 1 do
        throwError "the rejection does not name the rule '{rule}': {message}"
  let state ← registryState
  let some groups := state.categories.find? (·.id.raw == "cat.groups")
    | throwError "cat.groups is not registered"
  expectRule (.category { groups with id := ⟨"cat.probe.sage_group_class"⟩ })
    "cannot invent a public category"
  let order : MethodEntry :=
    { id := ⟨"meth.probe.order"⟩, name := "order", owner := groups.expression,
      functor := FunctorId.groupsMonoid, shape := .object }
  expectRule (.method order)
    "cannot attach a method"
  let isAbelian : PropertyEntry :=
    { id := ⟨"prop.probe.is_abelian"⟩, name := "IsAbelian",
      classifier := ClassifierId.magmasCommutative }
  expectRule (.property isAbelian)
    "cannot attach a method"
  let abelian : ClassifierEntry :=
    { id := ⟨"clf.probe.abelian"⟩, declaration := `x, host := groups.expression,
      realization := `x }
  expectRule (.subcategory abelian)
    "cannot declare a superclass or subcategory relation"
  let some groupsMonoid := state.functor? FunctorId.groupsMonoid
    | throwError "fun.groups.monoid is not registered"
  expectRule (.forgetfulRoute { groupsMonoid with id := ⟨"fun.probe.groups_to_sets"⟩ })
    "cannot create an implicit forgetful route"
  let some comparison := state.cells.find? (·.invertible)
    | throwError "no comparison is registered"
  expectRule (.identification comparison)
    "cannot decide that two presentations are the same"
  expectRule (.coercion groups.expression Foundation.Sets) "cannot add public coercions"
  expectRule (.refineObject `CasCatalogue.PropsProbes.z3 ClassifierId.magmasCommutative)
    "cannot refine an object's semantic type after construction"
  expectRule (.resultClass "SageKernelSubgroup") "cannot expose backend-specific result classes"
  let some lift := state.lifts[0]? | throwError "no lift is registered"
  expectRule (.genericSemantics lift) "cannot define generic subgroup, kernel or image"
  -- A permitted contribution must still typecheck against the semantic universe.
  let orphanRealizer : RealizerEntry :=
    { id := ⟨"rz.probe.orphan"⟩, category := ⟨"cat.probe.unregistered"⟩,
      backend := "probe-sage",
      denotation := `CasCatalogue.Algebra.RingTables.ringTableDenotation }
  let orphan : LeafContract :=
    { backend := "probe-sage", contributions := [.realizer orphanRealizer] }
  if (← try discard orphan.check; pure true catch _ => pure false) then
    throwError "a realizer of an unregistered category was accepted"
  -- A contract with one forbidden contribution registers nothing.
  let before := (← registryState).realizers.size
  let mixedRealizer : RealizerEntry :=
    { id := ⟨"rz.probe.mixed"⟩, category := ⟨"cat.rings"⟩, backend := "probe-sage",
      denotation := `CasCatalogue.Algebra.RingTables.ringTableDenotation }
  let mixed : LeafContract :=
    { backend := "probe-sage", contributions := [.realizer mixedRealizer, .resultClass "SageRing"] }
  try registerLeaf mixed catch _ => pure ()
  unless (← registryState).realizers.size == before do
    throwError "a rejected contract registered part of itself"
  -- The permitted leaf above is registered.
  unless (← registryState).realizers.any (·.id.raw == "rz.probe.sage_rings") do
    throwError "the permitted leaf contribution was not registered"

/- The command itself fails to elaborate on a forbidden contribution, naming the rule. -/
/--
error: leaf probe-sage: §5: a backend leaf cannot expose backend-specific result classes
(SageKernelSubgroup); results decode into the operation's semantic result type
-/
#guard_msgs (whitespace := lax) in
register_leaf { backend := "probe-sage", contributions := [.resultClass "SageKernelSubgroup"] }

end CasCatalogue.AdapterProbes
