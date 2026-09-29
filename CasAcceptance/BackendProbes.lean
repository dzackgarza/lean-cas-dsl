/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CasAcceptance.AdapterProbes
public meta import CasAcceptance.AdapterProbes

@[expose] public section

/-!
# Acceptance for `cc-backends` (CC-ADAPTER, CC-DECODE, CC-TRUST)

Where GAP is installed (`CAS_GAP_PYTHON`, default `.venv/bin/python` with `passagemath-gap`):

* the GAP adapter announces exactly the registered operation declared for it
  (`lim.groups.kernel`), and GAP's kernels of `sign : S₃ → ℤ/2`, of the trivial map and of the
  identity decode into the subgroups `A₃`, `S₃` and `1`, each with its inclusion, equal to the
  Lean-native kernels;
* a hostile adapter is rejected: one announcing its own subgroup operation is refused at connection
  (not a registered operation), one forgetting the inclusion and one answering the whole group as
  the kernel are rejected by the decoder;
* a leaf declaring a backend operation that is not a registered semantic operation, or one without
  a decoder, is rejected at its contract;
* the registry, the user-visible surface, is the same before and after.

Where GAP is not installed the connection reports it unavailable, and nothing is exercised.
-/

open Lean Meta Elab Term Command
open CasCatalogue.Algebra.KernelDecode CasCatalogue.Algebra.GapKernels CasCatalogue.AdapterProbes

namespace CasCatalogue.BackendProbes

run_cmd liftTermElabM do
  let state ← registryState
  let before ← checkedRegistryManifest
  match ← connectGap state with
  | .error (.unavailable backend reason) =>
      logInfo m!"{backend} is not installed here ({reason}); cc-backends is not exercised"
  | .error e => throwError e.render
  | .ok c =>
      unless c.ready.capabilities == #["lim.groups.kernel"] do
        throwError "GAP announces {c.ready.capabilities}"
      for (f, expected) in [(sign, [0, 1, 2]), (trivialMap, [0, 1, 2, 3, 4, 5]),
          (identityMap, [0])] do
        match ← gapKernel c f with
        | .ok k =>
            unless members k == expected && (nativeKernel f).map members == some expected do
              throwError "GAP's kernel {members k} is not {expected}"
        | .error e => throwError "GAP's kernel was rejected: {e}"
      Backend.stop c
      -- A backend's own subgroup notion is not a registered operation: refused at connection.
      match ← connectGap state #["--hostile=capability"] with
      | .error (.contract message) =>
          unless mentions "op.groups.orthogonal_subgroup" message do throwError message
      | .error e => throwError "unexpected: {e.render}"
      | .ok c => Backend.stop c; throwError "an undeclared operation was accepted"
      -- Wrong answers are rejected by the decoder.
      for (flag, reason) in [("--hostile=forget-inclusion", "defining arrow"),
          ("--hostile=whole-group", "not contained in the kernel")] do
        let .ok c ← connectGap state #[flag] | throwError "cannot start the adapter with {flag}"
        match ← gapKernel c sign with
        | .error message => unless mentions reason message do throwError message
        | .ok _ => throwError "the answer of {flag} was accepted"
        Backend.stop c
  -- A leaf declaring a backend operation that is not a registered semantic operation (an
  -- isotropic-subgroup operation on generic groups) is rejected at its contract.
  let isotropic : LeafContract :=
    { backend := "gap", contributions := [.backendOperation
        { id := ⟨"bop.probe.isotropic"⟩, backend := "gap", operation := "op.groups.isotropic"
          decoder := `CasCatalogue.Algebra.KernelDecode.decodeKernel }] }
  if (← try discard isotropic.check; pure true catch _ => pure false) then
    throwError "an operation that is not registered was declared for a backend"
  let notADecoder : LeafContract :=
    { backend := "gap", contributions := [.backendOperation
        { id := ⟨"bop.probe.not_a_decoder"⟩, backend := "gap", operation := "lim.groups.kernel"
          decoder := `CasCatalogue.Algebra.GapKernels.encodeHom }] }
  if (← try discard notADecoder.check; pure true catch _ => pure false) then
    throwError "a backend operation without a decoder was accepted"
  unless (← checkedRegistryManifest) == before do
    throwError "a backend changed the registry"

end CasCatalogue.BackendProbes
