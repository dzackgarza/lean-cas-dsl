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
# Acceptance for `cc-specimens`

Each specimen declares only its immediate structure, and receives what is expected of its kind by
composition.

* Formed modules by form (`CasLeaves.Modules.Bilinear.Valued.Forms`): the hyperbolic plane
  `U = (ℤ², (x, y) ↦ x₀y₁ + x₁y₀)` and the symplectic plane `(x, y) ↦ x₀y₁ − x₁y₀`, given by their
  formulas. The leaf registers two realizers and one action each for the immediate functors
  (formed module → module, lattice → formed module); `cardinality` and `rank` arrive along
  `BilinModule → Mod_ℤ → ∫Mod → Sets`. `U` is proved a lattice and re-typed into lattices as the same
  handle, where the same methods resolve; the symplectic plane is refuted and stays a formed module.
* The ring diamond and `𝔽₉` under two presentations: `CohereExecProbes`, `RealizeProbes`.
* The hostile orthogonal subgroup: `BackendProbes` (a backend announcing its own subgroup operation
  is refused at connection).
-/

open CategoryTheory Lean Meta Elab Command
open CasCatalogue.Modules.Bilinear.Valued.Forms CasCatalogue.Foundation.Cardinality

namespace CasCatalogue.SpecimenProbes

/-- `(x, y) ↦ xᵢ yⱼ`. -/
def coord (i j : Fin 2) : LinearMap.BilinForm ℤ (Fin 2 → ℤ) :=
  (LinearMap.mul ℤ ℤ).compl₁₂ (LinearMap.proj i) (LinearMap.proj j)

/-- `(x, y) ↦ x₀y₁ + x₁y₀`. -/
def hyperbolic : LinearMap.BilinForm ℤ (Fin 2 → ℤ) := coord 0 1 + coord 1 0

/-- `(x, y) ↦ x₀y₁ − x₁y₀`. -/
def symplectic : LinearMap.BilinForm ℤ (Fin 2 → ℤ) := coord 0 1 - coord 1 0

def u : FormHandles := (⟨2, hyperbolic⟩ : FormHandle)
def w : FormHandles := (⟨2, symplectic⟩ : FormHandle)

/- Methods of formed modules arrive by composition. -/
#guard method% cardinality (u) in "cat.bilin_module" == ⟨CardinalHandle.aleph0⟩
#guard (decideLattice u).answer == some true
#guard (decideLattice w).answer == some false

/-- `U`, re-typed into lattices after its proved decision. -/
def uLattice? : Option (Refined formDenotation (LeanCategories.Lattices.Valued.isLattice ℤ ℤ)) :=
  refine u (decideLattice u)

#guard uLattice?.isSome
#guard (refine w (decideLattice w)).isNone

def uLattice := uLattice?.get (by decide +kernel)

theorem uLattice_same : latticeForgetAction.obj uLattice = u :=
  refine_eq_some (Option.some_get _).symm

/- The methods of lattices resolve on the same handle. -/
#guard method% cardinality (uLattice) in "cat.lattice" == ⟨CardinalHandle.aleph0⟩

/-! ### The specimen declares only its immediate structure -/

run_cmd liftTermElabM do
  let env ← getEnv
  let some (_, rows) := (registryRowsByModule env).find?
      (·.1 == `CasLeaves.Modules.Bilinear.Valued.Forms)
    | throwError "the forms specimen is not imported"
  let kinds := rows.map fun
    | .realizer e => s!"realizer {e.category.raw}"
    | .action e => s!"action {e.edge.label}"
    | row => s!"other {row.stableId}"
  unless kinds.qsort (· < ·) == #["action fun.bilin_module.forget",
      "action fun.lattice.forget_form", "realizer cat.bilin_module", "realizer cat.lattice"] do
    throwError "the forms specimen declares {kinds}"

end CasCatalogue.SpecimenProbes
