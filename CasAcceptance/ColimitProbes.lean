/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CasAcceptance.Standard
public import CasCatalogue.ResolveSyntax
public meta import CasAcceptance.Standard
public meta import CasCatalogue.ResolveSyntax

@[expose] public section

/-!
# Acceptance for `cc-colimits` (CC-UNIV)

The registered coproduct `colim.sets.coproduct` of presented finite sets `Fin 2 ⊔ Fin 3`: the apex
presented by the leaf as `Fin 5`, the coprojections and the descent of a competing cocone into
`Fin 4` computed by the core (`realizedColimitCocone`, the dual of `realizedLimitCone`), and the
descent factors the cocone and is unique.
-/

open CategoryTheory Limits Lean Meta Elab Command
open CasCatalogue.Foundation.Actions CasCatalogue.Foundation.Coproducts

namespace CasCatalogue.ColimitProbes

def finHom {a b : ℕ} (h : Fin a → Fin b) : @Quiver.Hom SetHandles _ (.finite a) (.finite b) :=
  InducedCategory.homMk (TypeCat.ofHom h)

abbrev D : Discrete WalkingPair ⥤ SetHandles :=
  pair (SetHandle.finite 2 : SetHandles) (SetHandle.finite 3)

noncomputable def L : ColimitCocone (D ⋙ setDenotation) :=
  colimitCoconeOfIso (diagramIsoPair _) (Limits.Registration.setsCoproduct _ _)

def apex := finiteCoproduct 2 3

noncomputable def P : ColimitCocone D :=
  realizedColimitCocone setDenotationFullyFaithful L apex.1 apex.2

#guard (exec% P.cocone.pt : SetHandle) == .finite 5
#guard (List.finRange 2).map (fun i => (show Fin 5 from
  (exec% (P.cocone.ι.app ⟨.left⟩)).hom i)) == [0, 1]
#guard (List.finRange 3).map (fun i => (show Fin 5 from
  (exec% (P.cocone.ι.app ⟨.right⟩)).hom i)) == [2, 3, 4]

/-- A competing cocone into `Fin 4`. -/
def f : Fin 2 → Fin 4 := ![0, 3]
def g : Fin 3 → Fin 4 := ![1, 2, 1]

noncomputable def s : Cocone D := BinaryCofan.mk (P := (SetHandle.finite 4 : SetHandles))
  (finHom f) (finHom g)

noncomputable def descent : @Quiver.Hom SetHandles _ P.cocone.pt (.finite 4) :=
  P.isColimit.desc s

#guard (List.finRange 5).map (fun i => (show Fin 4 from (exec% descent).hom i)) ==
  [0, 3, 1, 2, 1]

theorem descent_fac (j : Discrete WalkingPair) : P.cocone.ι.app j ≫ descent = s.ι.app j :=
  P.isColimit.fac s j

theorem descent_unique (m : @Quiver.Hom SetHandles _ P.cocone.pt (.finite 4))
    (h : ∀ j, P.cocone.ι.app j ≫ m = s.ι.app j) : m = descent :=
  P.isColimit.uniq s m h

run_cmd liftTermElabM do
  let state ← registryState
  for (id, category) in [("colim.sets.coproduct", "cat.sets"),
      ("colim.bil_w_form.cokernel", "cat.bil_wform")] do
    let some l := state.limits.find? (·.id.raw == id) | throwError "{id} is not registered"
    unless l.colimit && l.category.raw == category do throwError "{id} is misregistered"
  -- A colimit presentation is not a limit: declaring the coproduct a limit is rejected.
  let some l := state.limits.find? (·.id.raw == "colim.sets.coproduct") | unreachable!
  let asLimit : LimitEntry := { l with id := ⟨"lim.probe.coproduct"⟩, colimit := false }
  if (← try validateRegistryEntryDeclaration (.limit asLimit); pure true
      catch _ => pure false) then
    throwError "a colimit cocone family was accepted as a limit"

end CasCatalogue.ColimitProbes
