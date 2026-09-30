/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

import all CasCatalogue
import all CasCatalogue.Acceptance
import all CasCatalogue.AcceptanceSyntax
import all CasCatalogue.Admission
import all CasCatalogue.CellCall
import all CasCatalogue.CellSyntax
import all CasCatalogue.Codec
import all CasCatalogue.Decide
import all CasCatalogue.Language
import all CasCatalogue.Realize
import all CasCatalogue.Resolve
import all CasCatalogue.ResolveSyntax
import all CasCatalogue.Semantic
import all CasCatalogue.TestSuite
import all CasCatalogue.Trace
import all CasContract
import all CasContract.Failure
import all CasContract.Port
import all CasContract.Registration
import all CasContract.Registry.Extension
public meta import Lean

/-!
# The kernel carries no mathematics (`specs/architecture.md`, "What must be impossible")

The kernel (`CasCatalogue.*`, this repository) and the leaf contract (`CasContract.*`) are
categorical machinery: they read the catalogue, compose registered morphisms, and run what the
catalogue registers. Mathematics is `lean-categories`', formalized there by its own author
(`CONTRIBUTING.md`, "Authors are separated by layer"). This module is built with the kernel
(default target), and it fails the build when a declaration of the kernel or the contract:

1. **refers to mathematics**: any constant (in a declaration's type or value, or as a name literal
   in its code) from a module outside `allowedModules`: Lean's core and meta-programming,
   Mathlib's category theory and the general logic it is stated in, and the categorical
   foundation and registry schema of `lean-categories`. `Mathlib.Algebra`, `Mathlib.Analysis`,
   `Mathlib.Tactic`, the catalogue's semantic rows (`LeanCategories.Catalogue.Semantics`, except
   the foundation `Sets`) and every other module of mathematics are outside it;
2. **writes a tactic**: a name literal that is the kind of a tactic (a quotation of tactic syntax,
   a `by` block), or the tactic category itself (tactic source parsed from a string);
3. **runs code it did not write**: a use of `restrictedConstants` (running a tactic procedure,
   evaluating a constant) or of Lean's tactic machinery anywhere but `evidenceRunner`, which runs
   only the evidence a domain registers with its admission in `lean-categories` (LC-18);
4. **evaluates a term**: a use of `evaluationConstants`. Nothing in the kernel decides anything by
   evaluation: a decision is the kernel's proof by `decide`, checked by Lean's kernel
   (`CasCatalogue.Realize`), and a leaf's answer is decoded in a declared form, never run.

Every module file under `CasCatalogue/` and the contract's `CasContract/` must be imported here,
so that a new kernel module cannot escape the check.

The one proof the kernel forms itself is `decide` by evaluation (`decideObligation`, Lean's
`mkDecideProof`): general, and about no mathematics in particular.
-/

open Lean

public section

namespace CasGates.KernelPurity

/-- The module roots of the kernel and of the leaf contract. -/
meta def kernelRoots : List Name := [`CasCatalogue, `CasContract]

/-- The modules the kernel may refer to: Lean's core and meta-programming, Mathlib's category
theory with the general logic, quivers and bundled maps it is stated in, and `lean-categories`'
categorical foundation and registry schema. -/
meta def allowedModules : List Name :=
  [`Init, `Std, `Lean, `Mathlib.CategoryTheory, `Mathlib.Combinatorics.Quiver,
   `Mathlib.Logic.Equiv.Defs, `Mathlib.Data.FunLike, `Mathlib.Order.Defs.Prop,
   `LeanCategories.CategoryTheory, `LeanCategories.Foundation.Mathlib,
   `LeanCategories.Catalogue.Id, `LeanCategories.Catalogue.Syntax, `LeanCategories.Catalogue.Holds,
   `LeanCategories.Catalogue.Registry, `LeanCategories.Catalogue.Constructors,
   `LeanCategories.Catalogue.Semantics.Foundation.Catalogue,
   `CasCatalogue, `CasContract]

/-- Lean's tactic machinery: proof search is the domain's (LC-18), run only by `evidenceRunner`. -/
meta def tacticModules : List Name := [`Lean.Elab.Tactic, `Lean.Meta.Tactic]

/-- Running a tactic procedure or evaluating a constant by name: only `evidenceRunner` may, on
the registered evidence of a domain. -/
meta def restrictedConstants : List Name :=
  [``Lean.Elab.Term.runTactic, ``Lean.Environment.evalConst, ``Lean.Environment.evalConstCheck,
   ``Lean.evalConst, ``Lean.evalConstCheck, ``Lean.Elab.Term.evalTerm]

/-- Evaluating a closed term: no kernel declaration may (`evaluators` is empty). A decision is a
kernel-checked proof by `decide`; a leaf's answer is decoded, never evaluated. An addition to
`evaluators` changes the sealed boundary. -/
meta def evaluationConstants : List Name := [``Lean.Meta.evalExpr, ``Lean.Meta.evalExpr']

/-- The declarations allowed to evaluate a term: none. -/
meta def evaluators : List Name := []

/-- The one declaration that runs registered evidence (with its auxiliary declarations). -/
meta def evidenceRunner : Name := `CasCatalogue.Language.establish

/-- Tactic blocks as terms, and the tactic category, which the kernel may not name. -/
meta def tacticSyntax : List Name :=
  [`tactic, `Lean.Parser.Term.byTactic, `Lean.Parser.Term.byTactic',
   `Lean.Parser.Tactic.tacticSeq, `Lean.Parser.Tactic.tacticSeq1Indented,
   `Lean.Parser.Tactic.tacticSeqBracketed]

/-- The name a compiled name literal denotes (`Name.mkStr2 "Matrix" "det"`), if `e` is one. -/
meta partial def nameLiteral? (e : Expr) : Option Name :=
  let args := e.getAppArgs
  match e.getAppFn.constName? with
  | some ``Name.anonymous => if args.isEmpty then some .anonymous else none
  | some ``Name.str | some ``Name.mkStr => match args with
    | #[p, .lit (.strVal s)] => (nameLiteral? p).map (·.str s)
    | _ => none
  | some ``Name.num | some ``Name.mkNum => match args with
    | #[p, .lit (.natVal n)] => (nameLiteral? p).map (·.num n)
    | _ => none
  | some c =>
    let strings := args.filterMap fun | .lit (.strVal s) => some s | _ => none
    if c.getPrefix == ``Name && c.getString!.startsWith "mkStr" && !args.isEmpty &&
        strings.size == args.size then
      some (strings.foldl (·.str ·) .anonymous)
    else none
  | none => none

/-- Every name literal in `e`. -/
meta partial def nameLiterals (e : Expr) (acc : Array Name := #[]) : Array Name :=
  match nameLiteral? e with
  | some n => acc.push n
  | none => match e with
    | .app f a => nameLiterals a (nameLiterals f acc)
    | .lam _ t b _ | .forallE _ t b _ => nameLiterals b (nameLiterals t acc)
    | .letE _ t v b _ => nameLiterals b (nameLiterals v (nameLiterals t acc))
    | .mdata _ b | .proj _ _ b => nameLiterals b acc
    | _ => acc

/-- The module files under the directory `dir` of the module root `root`, as module names. -/
meta def moduleFiles (dir : System.FilePath) (root : Name) : IO (Array Name) := do
  unless ← dir.isDir do
    throw <| IO.userError s!"{dir} is absent: the kernel modules under it cannot be checked"
  let files ← dir.walkDir
  return files.filterMap fun f =>
    if f.extension != some "lean" then none else
    let rel := String.ofList (f.toString.toList.drop (dir.toString.length + 1))
    let parts := (String.ofList (rel.toList.dropLast.dropLast.dropLast.dropLast.dropLast)).splitOn "/"
    some (parts.foldl (·.str ·) root)

/-- The violations of the declaration `d` (with `info`) of the kernel module `m`. -/
meta def declarationViolations (env : Environment) (d m : Name) (info : ConstantInfo) :
    Array String := Id.run do
  let moduleOf (c : Name) : Option Name :=
    (env.getModuleIdxFor? c).map (env.header.moduleNames[·.toNat]!)
  let tacticKinds := match (Parser.parserExtension.getState env).categories.find? `tactic with
    | some category => category.kinds
    | none => {}
  let values := #[info.type] ++ info.value?.toArray
  let used := values.flatMap (·.getUsedConstants)
  let literals := values.foldl (fun acc e => nameLiterals e acc) #[]
  let mut found : Array String := #[]
  for c in used ++ literals.filter env.contains do
    let some cm := moduleOf c | continue
    if evaluationConstants.contains c then
      unless evaluators.contains d do
        found := found.push s!"{d} ({m}) evaluates a term with {c}: nothing in the kernel decides \
          by evaluation (a decision is a kernel-checked proof, a leaf's answer is decoded)"
      continue
    if restrictedConstants.contains c || tacticModules.any (·.isPrefixOf cm) then
      -- The runner itself, or a compiler-generated auxiliary of it (`establish.unsafe_1`).
      unless d == evidenceRunner || (d.getPrefix == evidenceRunner &&
          (match d with
            | .str _ s => s.startsWith "_" || s.startsWith "unsafe_" | _ => false)) do
        found := found.push s!"{d} ({m}) uses {c} of {cm}: only {evidenceRunner} runs a proof \
          procedure, and only a domain's registered evidence"
      continue
    unless allowedModules.any (·.isPrefixOf cm) do
      found := found.push s!"{d} ({m}) refers to {c} of {cm}: the kernel carries no mathematics"
  for n in literals do
    if tacticKinds.contains n || tacticSyntax.contains n then
      found := found.push s!"{d} ({m}) writes tactic syntax ({n}): the kernel runs no proof \
        search of its own; a domain's membership is established by its registered evidence"
  return found

/-- Every violation of the kernel's purity in `env`. -/
meta def violations (env : Environment) : IO (Array String) := do
  let mut found : Array String := #[]
  -- Every kernel module is checked.
  let imported := env.header.moduleNames
  for (dir, root) in [("CasCatalogue", `CasCatalogue),
      (".lake/packages/cas_leaf_contracts/CasContract", `CasContract)] do
    for m in ← moduleFiles dir root do
      unless imported.contains m do
        found := found.push s!"{m} is a kernel module not imported by CasGates.KernelPurity"
  for (d, info) in env.constants.map₁.toList do
    let some idx := env.getModuleIdxFor? d | continue
    let m := env.header.moduleNames[idx.toNat]!
    unless kernelRoots.contains m.getRoot do continue
    found := found ++ declarationViolations env d m info
  return found

run_cmd do
  let found ← violations (← getEnv)
  unless found.isEmpty do
    throwError m!"the kernel carries mathematics or proof search \
      (specs/architecture.md, \"What must be impossible\"):\n" ++
      MessageData.joinSep (found.toList.map (m!"  {·}")) "\n"

end CasGates.KernelPurity

end
