/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CasAcceptance.Standard
public meta import CasAcceptance.Standard

@[expose] public section

/-!
# Acceptance for `cc-leaf-boundary` (CC-ADAPTER, CC-IMMEDIATE, CC-SEP)

* Every imported leaf module (`CasLeaves.*`) has only permitted direct imports — the leaf API
  `CasCatalogue.Leaf`, other leaves, Mathlib, `lean-categories` — and wrote only permitted rows
  (realizers, actions, implementations, deciders, isomorphisms); no module outside the core, its
  probes and the leaves wrote any row (`leafBoundaryViolations`).
* A module of the leaf library that imports a core-internal module cannot register: its first
  `register_leaf` fails naming the import. Simulated here by elaborating a row as the module
  `CasLeaves.Probe` with this probe's imports (which include core internals).
* `normalized_registry` fails in any module outside `lean-categories`, whatever it registers: in
  a leaf, the notebook, the core and its probes.
* The leaf write path refuses semantic rows even from a leaf with clean imports.
-/

open Lean Meta Elab Command

namespace CasCatalogue.LeafBoundaryProbes

run_cmd liftTermElabM do
  let violations := leafBoundaryViolations (← getEnv)
  unless violations.isEmpty do
    throwError "leaf boundary violations: {violations.toList}"
  let leaves := (← getEnv).header.moduleNames.filter (leafRoot.isPrefixOf ·)
  unless leaves.size ≥ 10 do
    throwError "the standard universe imports only {leaves.size} leaf modules"

#guard leafImportViolations #[`CasCatalogue.Leaf, `CasLeaves.Algebra.Actions,
  `Mathlib.Algebra.Group.Defs, `LeanCategories.Foundation.Mathlib] == #[]
-- A leaf of another package (root `Ext`) has only its intake contract: not this repository's
-- litmus leaves, not the acceptance suite.
#guard leafImportViolations #[`CasCatalogue.Leaf, `Ext.Engine, `LeanCategories.Catalogue.Syntax,
  `CasLeaves.Foundation.FiniteSets, `CasAcceptance.Standard] `Ext ==
    #[`CasLeaves.Foundation.FiniteSets, `CasAcceptance.Standard]
#guard leafImportViolations #[`CasCatalogue.Leaf, `CasCatalogue.Registry.Extension,
  `CasCatalogue.Resolve] == #[`CasCatalogue.Registry.Extension, `CasCatalogue.Resolve]

/-- A realizer row of an already-registered category, and a semantic row. -/
def realizerRow : RegistryEntry := .realizer
  { id := ⟨"rz.probe.leaf_boundary"⟩, category := ⟨"cat.magmas"⟩, backend := "probe"
    denotation := `CasCatalogue.Algebra.Actions.magmaDenotation }
def categoryRow : RegistryEntry := .category
  { id := ⟨"cat.probe.leaf_boundary"⟩, declaration := `LeanCategories.Algebra.Magmas
    expression := .atom ⟨"cat.probe.leaf_boundary"⟩
    realization := `CasCatalogue.Algebra.CatalogueRegistration.magmasRealization }

/-- Run `action` as though elaborating the module `module`; succeed iff it throws an error
containing `fragment`. -/
def rejectsAs (module : Name) (fragment : String) (action : MetaM Unit) : MetaM Bool := do
  let env ← getEnv
  try
    withEnv (env.setMainModule module) action
    return false
  catch e =>
    return ((← e.toMessageData.toString).splitOn fragment).length > 1

run_cmd liftTermElabM do
  unless ← rejectsAs `CasLeaves.Probe "imports core-internal modules"
      (addLeafRegistryEntryChecked realizerRow) do
    throwError "a leaf importing core internals registered a row"
  -- Semantic rows are written only in `lean-categories`: a leaf, the notebook, the core and its
  -- probes are all refused.
  for module in [`CasLeaves.Probe, `Notebook.Session, `CasCatalogue.Probe, `CasAcceptance.Probe] do
    unless ← rejectsAs module "is not a `lean-categories` module"
        (addRegistryEntryChecked categoryRow) do
      throwError "a semantic row was written in {module}"
  unless ← rejectsAs `CasAcceptance.Probe "contributes only realizers"
      (addLeafRegistryEntryChecked categoryRow) do
    throwError "the leaf write path accepted a semantic row"

end CasCatalogue.LeafBoundaryProbes
