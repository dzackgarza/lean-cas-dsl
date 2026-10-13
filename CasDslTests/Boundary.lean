/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CasDsl.Notebook
public meta import CasDsl.Notebook

/-!
# The notebook package is syntax only (`cc-notebook` acceptance)

No module of `CasDsl` writes a registry row or declares a constant: no categories, typing rules,
codecs or executors live in the notebook package.
-/

open Lean Meta Elab Command CasCatalogue

run_cmd liftTermElabM do
  let env ← getEnv
  let notebook (module : Name) : Bool := module.getRoot == `CasDsl
  for (module, rows) in registryRowsByModule env do
    if notebook module && !rows.isEmpty then
      throwError "{module} registers {rows.map (·.stableId)}"
  let declared := env.constants.fold (init := #[]) fun acc name _ =>
    match env.getModuleIdxFor? name with
    | some i => if notebook env.header.moduleNames[i.toNat]! then acc.push name else acc
    | none => acc
  unless declared.isEmpty do
    throwError "the notebook package declares {declared.toList.take 10}"
