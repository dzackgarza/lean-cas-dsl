/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CasGates.KernelPurity
public meta import CasGates.KernelPurity
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public meta import Lean

/-!
# The kernel-purity gate refuses each way mathematics has entered the kernel

Each declaration below, read as though it were a kernel declaration, is refused: a constant of
mathematics, a lemma named by a name literal, a quoted tactic, a `by` block, tactic source parsed
from a string, and a tactic procedure run outside the evidence runner. A declaration of categorical
plumbing is accepted.
-/

open Lean Meta Elab Term

namespace CasGates.KernelPurityProbes

/-- Mathematics referred to directly. -/
noncomputable def determinant (M : Matrix (Fin 2) (Fin 2) Int) : Int := M.det
/-- A lemma named for a proof the kernel would build. -/
def lemmaName : Name := ``Matrix.det_fin_two
/-- A quoted tactic. -/
def quotedTactic : MetaM Syntax := `(tactic| decide)
/-- A `by` block built as a term. -/
def byBlock : MetaM Syntax := `(by decide)
/-- Tactic source parsed from a string. -/
def tacticSource (env : Environment) : Except String Syntax :=
  Parser.runParserCategory env `tactic "norm_num"
/-- A tactic procedure run outside the evidence runner. -/
def runsTactic (g : MVarId) (t : Lean.Elab.Tactic.TacticM Unit) : TermElabM (List MVarId) :=
  Lean.Elab.Tactic.run g t
/-- A constant evaluated outside the evidence runner. -/
unsafe def evaluates (n : Name) : MetaM Nat := evalConst Nat n
/-- Categorical plumbing: accepted. -/
def plumbing : Name := ``CategoryTheory.CategoryStruct.comp

end CasGates.KernelPurityProbes

run_cmd do
  let env ← getEnv
  let check (d : Name) : Array String := match env.find? d with
    | some info => CasGates.KernelPurity.declarationViolations env d `CasCatalogue.Probe info
    | none => #["missing"]
  for (d, fragment) in [(``CasGates.KernelPurityProbes.determinant, "carries no mathematics"),
      (``CasGates.KernelPurityProbes.lemmaName, "carries no mathematics"),
      (``CasGates.KernelPurityProbes.quotedTactic, "writes tactic syntax"),
      (``CasGates.KernelPurityProbes.byBlock, "writes tactic syntax"),
      (``CasGates.KernelPurityProbes.tacticSource, "writes tactic syntax"),
      (``CasGates.KernelPurityProbes.runsTactic, "runs a proof procedure"),
      (``CasGates.KernelPurityProbes.evaluates, "runs a proof procedure")] do
    let found := check d
    unless found.any (fun v => (v.splitOn fragment).length > 1) do
      throwError "the kernel-purity gate accepts {d} ({fragment} expected): {found}"
  let found := check ``CasGates.KernelPurityProbes.plumbing
  unless found.isEmpty do
    throwError "the kernel-purity gate refuses categorical plumbing: {found}"
