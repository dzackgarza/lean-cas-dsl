/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CasAcceptance.Standard
public import CasCatalogue.ResolveSyntax
public import CasAcceptance.LatticeActionProbes
public meta import CasAcceptance.Standard
public meta import CasCatalogue.ResolveSyntax
public meta import CasAcceptance.LatticeActionProbes

@[expose] public section

/-!
# Acceptance for `cc-closure` (CC-CLOSURE)

A category registered in `lean-categories` with nothing declared for it: torsion-free `R`-modules
(`cat.torsion_free_modules`), one property classifier on `Mod_R` (so one structural functor, its
forgetful functor into the module fibration), and its total category. It declares no operation.
Its generated surface (`#methods`) then contains:

* `cardinality` (through `Mod_R → ∫ Mod → Sets`) and `rank` (on `Mod_R`), resolved;
* on its morphisms, `kernel`, reached along the derived edge `Arr(forget)`: the result must return
  to the leaf, and since no lift of subobjects is registered for it the surface reports the missing
  lift (CC-LIFT) rather than a module kernel posing as a torsion-free one. The mathematics that
  would supply it — torsion-freeness passes to submodules — is to be stated as a lift upstream.

The surface is computed from the registry at query time; no per-leaf method list exists. The same
mechanism gives lattices `rank`, computed through the composed actions.
-/

open CategoryTheory Lean Meta Elab Term Command
open LeanCategories CasCatalogue.Lattices.Valued.ActionProbes CasCatalogue.Foundation.Cardinality

namespace CasCatalogue.ClosureProbes

#methods "cat.torsion_free_modules"
#methods "cat.lattice"

/- Lattices inherit `rank`, computed through the composed actions: `rank A₂ = 2`, `rank E₈ = 8`. -/
#guard method% rank (a2) in "cat.lattice" == ⟨CardinalHandle.finite 2⟩
#guard method% rank (e8) in "cat.lattice" == ⟨CardinalHandle.finite 8⟩

run_cmd liftTermElabM do
  let state ← registryState
  let some leaf := state.categories.find? (·.id.raw == "cat.torsion_free_modules")
    | throwError "the leaf is not registered"
  let rows := state.closure leaf.expression
  for name in ["cardinality", "rank"] do
    unless rows.any fun row => row.name == name && row.resolved do
      throwError "the leaf does not inherit {name}"
  let some arrows := state.arrowsOf? leaf.expression | throwError "no arrow constructor"
  let morphismRows := state.closure arrows
  unless morphismRows.any fun row =>
      row.name == "kernel" && !row.resolved && (row.status.splitOn "no lift").length > 1 do
    throwError "the leaf's kernel is not reported with its missing lift"
  -- Nothing was declared for the leaf: no method, property, action or lift mentions it.
  if state.methods.any (·.owner.syntacticEq leaf.expression) then
    throwError "a method is declared on the leaf"

end CasCatalogue.ClosureProbes
