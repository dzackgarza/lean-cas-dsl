module

import CasRuntime.GroundedRealizations
public meta import Lean.Elab.Command
meta import CasRuntime.GroundedRealizations

open Lean CasRuntime

private def check (graph : RealizationGraph size) (node : Fin size)
    (count : RealizationCount) (choice : Option Nat) : Except String Unit := do
  let result := graph.grounded
  unless result.counts[node] == count do
    throw "finite grounded realization multiplicity differs from the required count"
  unless (← result.uniqueAlternative node) == choice do
    throw "the unique realization lost its original alternative identity"

run_cmd Lean.Elab.Command.liftIO <| IO.ofExcept do
  check (⟨#v[#[]]⟩ : RealizationGraph 1) 0 .zero none
  check (⟨#v[#[#[]]]⟩ : RealizationGraph 1) 0 .one (some 0)
  check (⟨#v[#[#[], #[]]]⟩ : RealizationGraph 1) 0 .many none
  -- Finite trees cannot be grounded by a cycle without a primitive leaf.
  check (⟨#v[#[#[0]]]⟩ : RealizationGraph 1) 0 .zero none
  -- Wrapped and unwrapped grounded realizations remain distinct.
  check (⟨#v[#[#[], #[0]]]⟩ : RealizationGraph 1) 0 .many none
  -- An ungrounded alternative does not invalidate a direct realization.
  check (⟨#v[#[#[], #[1]], #[#[1]]]⟩ : RealizationGraph 2) 0 .one (some 0)
  check (⟨#v[#[#[1]], #[#[0]]]⟩ : RealizationGraph 2) 0 .zero none
  -- Each ordered prerequisite occurrence participates in the product.
  check (⟨#v[#[#[1, 2]], #[#[]], #[]]⟩ : RealizationGraph 3) 0 .zero none
  check (⟨#v[#[#[1, 1]], #[#[]]]⟩ : RealizationGraph 2) 0 .one (some 0)
  check (⟨#v[#[#[1, 1]], #[#[], #[]]]⟩ : RealizationGraph 2) 0 .many none
  -- A unique parent cannot select one of an ambiguous child's alternatives.
  check (⟨#v[#[#[1]], #[#[], #[]]]⟩ : RealizationGraph 2) 0 .many none
  -- Source order changes an ordinal, never eligibility or multiplicity.
  check (⟨#v[#[#[1], #[]], #[#[1]]]⟩ : RealizationGraph 2) 0 .one (some 1)
  let graph : RealizationGraph 4 := ⟨#v[#[#[1]], #[#[2]], #[#[3]], #[#[]]]⟩
  let result := graph.grounded
  for node in [0:4] do
    if bound : node < 4 then
      unless result.counts[⟨node, bound⟩] == .one &&
          (← result.uniqueAlternative ⟨node, bound⟩) == some 0 do
        throw "the unique graph lost a reached child or its actual alternative"
  -- Structural finiteness supplies the closure size; no guessed depth bounds it.
  let deep : RealizationGraph 257 := ⟨Vector.ofFn fun node =>
    if bound : node.val + 1 < 257 then #[#[⟨node.val + 1, bound⟩]] else #[#[]]⟩
  check deep 0 .one (some 0)
