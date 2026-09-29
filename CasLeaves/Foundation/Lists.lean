/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CasCatalogue.Leaf
public import CasCatalogue.Semantics.Foundation.Lists
public import CasLeaves.Foundation.Actions
public meta import CasCatalogue.Leaf
public meta import CasCatalogue.Semantics.Foundation.Lists

@[expose] public section

/-!
# The list functor on presented sets

`L = List` on presented sets: `X ↦ List X`, presented by `SetHandle.list`. The realization of sets
is induced, so the action is the lift of `L` (`RealizedAction.induced`), and the registered cells
of `L` (unit, join, reversal) are realized on it by the core as preimages.
-/

open CategoryTheory
open CasCatalogue.Foundation.Actions CasCatalogue.Foundation.Lists

namespace CasCatalogue.Foundation.ListActions

/-- `L` on presented sets. -/
def listAction : RealizedAction listDeclaration.{0} setDenotation setDenotation :=
  RealizedAction.induced _ SetHandle.list fun _ => rfl

end CasCatalogue.Foundation.ListActions

namespace CasCatalogue

register_leaf
  { backend := "lean"
    contributions := [
  .action
  { id := ⟨"act.sets.list.presented"⟩, edge := .functor FunctorId.setsList
    realization := `CasCatalogue.Foundation.ListActions.listAction }] }

end CasCatalogue
