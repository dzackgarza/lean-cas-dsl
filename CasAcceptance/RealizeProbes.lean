/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CasAcceptance.Standard
public import CasCatalogue.ResolveSyntax
public import CasCatalogue.Memo
public meta import CasAcceptance.Standard
public meta import CasCatalogue.ResolveSyntax
public meta import CasCatalogue.Memo

@[expose] public section

/-!
# Acceptance for `cc-realize` (CC-SEP, CC-ROUTE, CC-TRUST, CC-MEMO, CC-CARRIER)

* CC-TRUST / CC-ROUTE: the one semantic `cardinality` of a formed module is realized four ways —
  composed Lean-native actions (compiled: Lean-checked), the same reduced by the kernel (kernel
  theorem), a certifying backend (certificate-checked) and a fused backend (trusted assertion).
  The values agree and the statuses are distinguished; the audit reports one owner.
* CC-SEP: a receiver's category is the category of a registered realizer of it; with the realizer
  rows removed the same receiver is rejected.
* CC-MEMO: applying the cardinality action through a memo table of explicit applications returns
  the same values as without it.
* CC-CARRIER: `𝔽₃[x]/(x²+1)` and `𝔽₃[y]/(y²+y+2)` are distinct objects; their equality is not
  decided true; the registered isomorphism transports elements (and respects multiplication); in
  the other direction, where none is registered, transport reports the absence.
-/

open Lean Meta Elab Term Command
open CasCatalogue.Modules.Bilinear.Valued.Actions CasCatalogue.Foundation.Actions
open CasCatalogue.Foundation.Cardinality CasCatalogue.Algebra.RingTables

namespace CasCatalogue.RealizeProbes

/-- The zero form, and the `A₂` form. -/
def zeroForm : GramHandle := ⟨0, !![]⟩
def a2Form : GramHandle := ⟨2, !![2, -1; -1, 2]⟩

#audit cardinality in "cat.bilin_module"

def viaActions := run% cardinality (zeroForm) in "cat.bilin_module"
def viaKernel := run% cardinality (zeroForm) in "cat.bilin_module" proved
def viaCertified :=
  run% cardinality (zeroForm) in "cat.bilin_module" using "impl.bilin_module.cardinality.certified"
def viaFused :=
  run% cardinality (zeroForm) in "cat.bilin_module" using "impl.bilin_module.cardinality.fused"

/- One value, four epistemic statuses. -/
#guard [viaActions, viaKernel, viaCertified, viaFused].map (·.value) ==
  List.replicate 4 ⟨CardinalHandle.finite 1⟩
#guard [viaActions, viaKernel, viaCertified, viaFused].map (·.trust) ==
  [.leanChecked, .kernelTheorem, .certificateChecked, .trustedAssertion]
#guard (run% cardinality (a2Form) in "cat.bilin_module").value ==
  (run% cardinality (a2Form) in "cat.bilin_module" using
    "impl.bilin_module.cardinality.fused").value

/- CC-MEMO: the same values with and without the memo table. -/
def handles : List SetHandle := [.intPow 0, .intPow 3, .finite 5, .intPow 3, .finite 5]

def cardinalities (memo : Option (MemoTable SetHandle CardinalHandle)) : IO (List CardinalHandle) :=
  handles.mapM (memoApply memo "fun.sets.cardinality" cardinalityOf)

run_cmd liftTermElabM do
  let table ← MemoTable.new SetHandle CardinalHandle
  let first ← cardinalities (some table)
  let again ← cardinalities (some table)
  let plain ← cardinalities none
  unless first == plain && again == plain do
    throwError "memoization changed a value"
  unless (← table.get).size == 3 do
    throwError "the memo table is not keyed by explicit application"

/- CC-CARRIER: two presentations of `𝔽₉`, distinct objects with different multiplications. -/
#guard (f9a.mul 3 3).val == 2 && (f9b.mul 3 3).val == 7

/-- No procedure decides equality of ring objects; distinct presentations are never identified. -/
def decideSamePresentation (a b : RingTable) :
    Decision (ringTableDenotation.obj a = ringTableDenotation.obj b) := .undecided

#guard (decideSamePresentation f9a f9b).answer != some true

/- The registered isomorphism transports `x` to `y + 2` and respects multiplication. -/
#guard (transport% (3) from f9a to f9b : Fin 9).val == 5
#guard (List.finRange 9).all fun a => (List.finRange 9).all fun b =>
  (transport% (f9a.mul a b) from f9a to f9b : Fin 9) ==
    f9b.mul (transport% (a) from f9a to f9b) (transport% (b) from f9a to f9b)

run_cmd liftTermElabM do
  -- No isomorphism is registered from the second presentation to the first.
  let term ← `(transport% (3) from f9b to f9a)
  match ← try (some <$> Term.withoutErrToSorry (elabTerm term none)) catch err => do
      let message ← err.toMessageData.toString
      unless (message.splitOn "no registered isomorphism").length > 1 do
        throwError "unexpected failure: {message}"
      pure none with
  | some _ => throwError "a transport without a registered isomorphism succeeded"
  | none => pure ()
  -- CC-SEP: the receiver's category comes from a registered realizer, not from its handle.
  let state ← registryState
  let routeAction ← composeAction state none (.functor FunctorId.bilinModuleForget)
  checkRealizer state ⟨"cat.bilin_module"⟩ routeAction
  let unrealized := { state with realizers := #[] }
  if (← try checkRealizer unrealized ⟨"cat.bilin_module"⟩ routeAction; pure true
      catch _ => pure false) then
    throwError "a receiver was accepted without a registered realizer"
  -- CC-ROUTE: one owner, several realizations of the same composite.
  -- (Multisets own a different `cardinality`, counting multiplicity; no route reaches it from
  -- formed modules.)
  let some bilin := state.categories.find? (·.id.raw == "cat.bilin_module")
    | throwError "cat.bilin_module is not registered"
  let reachable := (state.methods.filter (·.name == "cardinality")).filter fun m =>
    !(state.routes bilin.expression m.owner).isEmpty
  unless reachable.map (·.id.raw) == #["meth.cardinality"] do
    throwError "cardinality has more than one owner on formed modules"
  unless (state.implementations.filter (·.method.raw == "meth.cardinality")).size == 2 do
    throwError "the two backend realizations are not both registered"

end CasCatalogue.RealizeProbes
