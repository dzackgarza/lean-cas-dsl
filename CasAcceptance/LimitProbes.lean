/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CasAcceptance.Standard
public import CasAcceptance.AdapterProbes
public import CasAcceptance.PropsProbes
public meta import CasAcceptance.AdapterProbes
public meta import CasAcceptance.PropsProbes
public import CasCatalogue.ResolveSyntax
public import Mathlib.CategoryTheory.Limits.Shapes.Opposites.Pullbacks
public meta import CasAcceptance.Standard
public meta import CasCatalogue.ResolveSyntax

@[expose] public section

/-!
# Acceptance for `cc-limits` (CC-UNIV, CC-CALC)

* A pullback in the registered category `Sets`: the registered presentation `lim.sets.pullback`
  (Mathlib's explicit pullback), its apex presented by the leaf `limr.sets.pullback.finite`, and
  the core's realized limit cone of the diagram of handles (`realizedLimitCone`): apex, legs,
  and the mediator of a competing cone, which factors it and is unique (Mathlib's `IsLimit`).
* The pushout in `Setsᵒᵖ`, obtained through `Op` (`PullbackCone.isLimitEquivIsColimitOp`): its
  descent from the opposite of the competing cone is the opposite of the mediator.
* A kernel in the registered category `Grp` (`lim.groups.kernel`, apex presented by
  `limr.groups.kernel.table`): the kernel of the sign `S₃ → ℤ/2` is returned with its inclusion,
  the alternating group `A₃ ↪ S₃`, and a competing fork factors through it.
-/

open CategoryTheory Limits Lean Meta Elab Term Command
open CasCatalogue.Foundation.Actions CasCatalogue.Foundation.Pullbacks
open CasCatalogue.Algebra.Actions CasCatalogue.Algebra.Kernels CasCatalogue.Algebra.Subgroups

namespace CasCatalogue.LimitProbes

/-! ### A pullback of finite sets -/

def f : Fin 3 → Fin 2 := ![0, 1, 1]
def g : Fin 2 → Fin 2 := ![1, 0]

/-- A morphism of presented finite sets. -/
def finHom {a b : ℕ} (h : Fin a → Fin b) : @Quiver.Hom SetHandles _ (.finite a) (.finite b) :=
  InducedCategory.homMk (TypeCat.ofHom h)

/-- The diagram of handles `Fin 3 → Fin 2 ← Fin 2`. -/
abbrev D : WalkingCospan ⥤ SetHandles := cospan (finHom f) (finHom g)

/-- The registered presentation, on the diagram's denotation. -/
noncomputable def L : LimitCone (D ⋙ setDenotation) :=
  limitConeOfIso (diagramIsoCospan _) (Limits.Registration.setsPullback _ _)

/-- The apex, presented by the leaf. -/
def apex := finitePullback 3 2 2 f g

/-- The pullback, as a limit cone of handles. -/
noncomputable def P : LimitCone D :=
  realizedLimitCone setDenotationFullyFaithful L apex.1 apex.2

/- The apex is the presented set of the three pairs `(0, 1), (1, 0), (2, 0)`, and the legs are
their projections. -/
#guard (exec% P.cone.pt : SetHandle) == .finite 3
#guard (List.finRange 3).map (fun i => (show Fin 3 from
  (exec% (P.cone.π.app WalkingCospan.left)).hom i)) == [0, 1, 2]
#guard (List.finRange 3).map (fun i => (show Fin 2 from
  (exec% (P.cone.π.app WalkingCospan.right)).hom i)) == [1, 0, 0]

/-- A competing cone: the one-point set, sent to `(2, 0)`. -/
def u : Fin 1 → Fin 3 := ![2]
def v : Fin 1 → Fin 2 := ![0]

def s : PullbackCone (finHom f) (finHom g) :=
  PullbackCone.mk (finHom u) (finHom v) <| by
    apply InducedCategory.hom_ext; apply TypeCat.Hom.ext; apply TypeCat.Fun.ext
    funext x; fin_cases x; rfl

/-- Its mediator into the pullback. -/
noncomputable def mediator : @Quiver.Hom SetHandles _ (.finite 1) P.cone.pt := P.isLimit.lift s

#guard (show Fin 3 from (exec% mediator).hom 0) == 2

/-- The mediator factors the competing cone. -/
theorem mediator_fst : mediator ≫ P.cone.π.app WalkingCospan.left = finHom u :=
  P.isLimit.fac s WalkingCospan.left

theorem mediator_snd : mediator ≫ P.cone.π.app WalkingCospan.right = finHom v :=
  P.isLimit.fac s WalkingCospan.right

/-- It is the only map that does. -/
theorem mediator_unique (m : @Quiver.Hom SetHandles _ (.finite 1) P.cone.pt)
    (h₁ : m ≫ P.cone.π.app WalkingCospan.left = finHom u)
    (h₂ : m ≫ P.cone.π.app WalkingCospan.right = finHom v) : m = mediator :=
  PullbackCone.IsLimit.hom_ext (t := (P.cone : PullbackCone _ _)) P.isLimit
    (h₁.trans mediator_fst.symm) (h₂.trans mediator_snd.symm)

/-! ### The pushout in the opposite category -/

/-- The opposite of the pullback is a pushout in `SetHandlesᵒᵖ`. -/
noncomputable def pushoutIsColimit : IsColimit (PullbackCone.op (P.cone : PullbackCone _ _)) :=
  PullbackCone.isLimitEquivIsColimitOp _ P.isLimit

/-- Its descent from the opposite of the competing cone is the opposite of the mediator. -/
theorem pushout_desc : (pushoutIsColimit.desc (PullbackCone.op s)).unop = mediator := rfl

#guard (show Fin 3 from (exec% (pushoutIsColimit.desc (PullbackCone.op s)).unop).hom (0 : Fin 1)) == 2

/-! ### A kernel of groups -/

/-- `S₃`, rotations first: `0, 1, 2` are `1, r, r²`, then the reflections. -/
def s3 : GroupTable := CasCatalogue.PropsProbes.s3
/-- `ℤ/2`. -/
def z2 : GroupTable := CasCatalogue.AdapterProbes.z2

/-- The sign `S₃ → ℤ/2`, as a morphism handle of group tables. -/
def sign : @Quiver.Hom GroupTables _ s3 z2 :=
  InducedCategory.homMk (GrpCat.ofHom CasCatalogue.AdapterProbes.sign.hom)

/-- The trivial homomorphism. -/
def trivial : @Quiver.Hom GroupTables _ s3 z2 := InducedCategory.homMk 1

abbrev K : WalkingParallelPair ⥤ GroupTables := parallelPair sign trivial

noncomputable def kernelCone : LimitCone K :=
  let kernel := tableKernel s3 z2 sign
  realizedLimitCone groupDenotationFullyFaithful
    (limitConeOfIso (diagramIsoParallelPair _) (Limits.Registration.groupsKernel _))
    kernel.1 kernel.2

/-- The kernel is returned with its inclusion. -/
noncomputable def inclusion : kernelCone.cone.pt ⟶ s3 := kernelCone.cone.π.app .zero

#guard (exec% kernelCone.cone.pt : GroupTable).size == 3
#guard ((List.finRange 3).map fun i => (show Fin 6 from (exec% inclusion).hom i).val) ==
  [0, 1, 2]

theorem inclusion_mono : Mono inclusion :=
  (Fork.IsLimit.mono kernelCone.isLimit)

/- The presentations used are the registered ones. -/
run_cmd liftTermElabM do
  let state ← registryState
  let expect (limit realization declaration realizationName : String) : MetaM Unit := do
    let some l := state.limits.find? (·.id.raw == limit) | throwError "{limit} is not registered"
    unless l.declaration.toString == declaration do throwError "{limit} names another limit"
    let some r := state.limitRealizations.find? (·.id.raw == realization)
      | throwError "{realization} is not registered"
    unless r.limit == l.id && r.realization.toString == realizationName do
      throwError "{realization} realizes another limit"
  expect "lim.sets.pullback" "limr.sets.pullback.finite"
    "CasCatalogue.Limits.Registration.setsPullback" "CasCatalogue.Foundation.Pullbacks.finitePullback"
  expect "lim.groups.kernel" "limr.groups.kernel.table"
    "CasCatalogue.Limits.Registration.groupsKernel" "CasCatalogue.Algebra.Kernels.tableKernel"

end CasCatalogue.LimitProbes
