/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CasAcceptance.Standard
public meta import CasAcceptance.Standard

@[expose] public section

/-!
# Acceptance for `cc-sem-upstream` and `cc-sem-derive`: the semantics are `lean-categories`'

* Every semantic row visible here was written by a `lean-categories` module
  (`LeanCategories.Catalogue.*`), and none by this repository.
* The registry's semantic part is exactly `lean-categories`' semantic registry: the same rows, in
  the same order.
* The standard universe's semantic rows are all there (at least the categories, functors and
  methods the probes use).

That a module of this repository cannot write a semantic row is `LeafBoundaryProbes`'.
-/

open Lean Meta Elab Command

namespace CasCatalogue.SemanticProjectionProbes

run_cmd liftTermElabM do
  let env ← getEnv
  let mut count := 0
  for (module, rows) in semanticRowsByModule env do
    unless rows.isEmpty do
      unless (`LeanCategories.Catalogue).isPrefixOf module do
        throwError "{module} wrote the semantic rows {rows.toList.map (·.stableId)}"
      count := count + rows.size
  let state ← registryState
  let upstream ← semanticState
  unless state.toSemanticState.entries.map (·.stableId) == upstream.entries.map (·.stableId) do
    throwError "the registry's semantics differ from lean-categories' semantic registry"
  unless count == upstream.entries.length do
    throwError "{upstream.entries.length} semantic rows, {count} of them written upstream"
  for id in ["cat.sets", "cat.finite_sets", "cat.bilin_module", "cat.bil_wform", "cat.lattice",
      "cat.torsion_free_modules"] do
    unless state.categories.any (·.id.raw == id) do
      throwError "the semantic category {id} is missing"
  unless count ≥ 200 do
    throwError "only {count} semantic rows"

end CasCatalogue.SemanticProjectionProbes
