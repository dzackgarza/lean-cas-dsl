/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CasAcceptance.AdapterProbes
public import CasLeaves.Modules.SageCardinality
public meta import CasAcceptance.AdapterProbes
public meta import CasLeaves.Modules.SageCardinality

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

Where Sage is installed (`CAS_SAGE_PYTHON`, default `.venv/bin/python` with
`passagemath-modules`), the Sage cardinality leaf's program answers `meth.cardinality` on `(ℤ/n)^k`,
and the decoded cardinals equal the Lean-native ones (`cardinalityOf`).

Where an engine is not installed the connection reports it unavailable, and nothing is exercised
for it.
-/

open Lean Meta Elab Term Command
open CasCatalogue.Algebra.KernelDecode CasCatalogue.Algebra.GapKernels CasCatalogue.AdapterProbes
open CasCatalogue.Modules.SageCardinality CasCatalogue.Foundation.Cardinality
open CasCatalogue.Foundation.Actions

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
        | .error e => throwError "GAP's kernel was rejected: {e.render}"
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
        | .error e =>
            unless e.stratum == .malformed && mentions reason e.render do throwError e.render
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

run_cmd liftTermElabM do
  match ← connectSage (← registryState) with
  | .error (.unavailable backend reason) =>
      logInfo m!"{backend} is not installed here ({reason}); the Sage leaf is not exercised"
  | .error e => throwError e.render
  | .ok c =>
      unless c.ready.capabilities == #["meth.cardinality"] do
        throwError "Sage announces {c.ready.capabilities}"
      for (n, k) in [(4, 3), (0, 2), (5, 0), (0, 0), (7, 1)] do
        match ← sageCardinality c n k with
        | .ok card =>
            unless card == cardinalityOf (.zmodPow n k) do
              throwError "Sage's cardinality of (ℤ/{n})^{k} is {repr card}"
        | .error e => throwError "Sage's answer was rejected: {e.render}"
      Backend.stop c

end CasCatalogue.BackendProbes
