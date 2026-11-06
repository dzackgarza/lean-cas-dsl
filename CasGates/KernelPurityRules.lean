/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public meta import Lean

/-!
# Kernel purity rules

The production and whole-system audit entry points use these same rules. Each scope imports
every source module with private declarations available. Source discovery uses Lake's selected
source search path. Constants, name literals, tactic syntax and term evaluators are checked
against the ownership policy in `specs/architecture.md` and `CONTRIBUTING.md`.
-/

open Lean

public section

namespace CasGates.KernelPurity

/-- The module roots of the kernel and of the leaf contract. -/
meta def kernelRoots : List Name := [`CasCatalogue, `CasCompiler, `CasRuntime, `CasContract]

/-- The replacement production closure and its public leaf contract. -/
meta def productionRoots : List Name := [`CasCompiler, `CasRuntime, `CasContract]

/-- The modules the kernel may refer to: Lean's core and meta-programming, Mathlib's category
theory with the general logic, quivers and bundled maps it is stated in, and `lean-categories`'
categorical foundation and registry schema. -/
meta def allowedModules : List Name :=
  [`Init, `Std, `Lean, `Mathlib.CategoryTheory, `Mathlib.Combinatorics.Quiver,
   `Mathlib.Logic.Equiv.Defs, `Mathlib.Logic.ExistsUnique,
   `Mathlib.Data.FunLike, `Mathlib.Data.Fintype.Defs, `Mathlib.Data.Finset.Defs,
   `Mathlib.Order.Defs.Prop,
   `LeanCategories.CategoryTheory, `LeanCategories.Foundation.Mathlib,
   `LeanCategories.Catalogue.Id, `LeanCategories.Catalogue.Syntax, `LeanCategories.Catalogue.Holds,
   `LeanCategories.Catalogue.Registry, `LeanCategories.Catalogue.Constructors,
   `LeanCategories.Catalogue.Lift,
   `LeanCategories.Catalogue.Semantics.Foundation.Catalogue,
   `CasCatalogue, `CasCompiler, `CasRuntime, `CasContract]

/-- Lean's tactic machinery: proof search is the domain's (LC-18), run only by `evidenceRunner`. -/
meta def tacticModules : List Name := [`Lean.Elab.Tactic, `Lean.Meta.Tactic]

/-- Running a tactic procedure or evaluating a constant by name: only `evidenceRunner` may, on
the proof procedures `lean-categories` registers. -/
meta def restrictedConstants : List Name :=
  [``Lean.Elab.Term.runTactic, ``Lean.Environment.evalConst, ``Lean.Environment.evalConstCheck,
   ``Lean.evalConst, ``Lean.evalConstCheck, ``Lean.Elab.Term.evalTerm]

/-- Evaluating a closed term: no kernel declaration may (`evaluators` is empty). A decision is a
kernel-checked proof by `decide`; a leaf's answer is decoded, never evaluated. An addition to
`evaluators` changes the sealed boundary. -/
meta def evaluationConstants : List Name := [``Lean.Meta.evalExpr, ``Lean.Meta.evalExpr']

/-- The declarations allowed to evaluate a term: none. -/
meta def evaluators : List Name := []

/-- The one declaration that runs a registered proof procedure (with its auxiliary
declarations): a domain's evidence, a literal form's evaluation. -/
meta def evidenceRunner : Name := `CasCatalogue.Language.runProcedure

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
      -- The runner itself, or a compiler-generated auxiliary of it (`runProcedure.unsafe_1`).
      unless d == evidenceRunner || (d.getPrefix == evidenceRunner &&
          (match d with
            | .str _ s => s.startsWith "_" || s.startsWith "unsafe_" | _ => false)) do
        found := found.push s!"{d} ({m}) uses {c} of {cm}: only {evidenceRunner} runs a proof \
          procedure, and only a domain's registered evidence"
      continue
    -- These two acceptance fixtures elaborate upstream mathematical examples. Their
    -- generated declarations observe those examples, rather than implement kernel
    -- mathematics. Keep all execution, evaluation and tactic restrictions above; do
    -- not exempt new modules by naming convention.
    let observationModule := m == `CasCatalogue.BinderReaderProbes ||
      m == `CasCatalogue.StructuredReconstructionProbes
    unless observationModule || allowedModules.any (·.isPrefixOf cm) do
      found := found.push s!"{d} ({m}) refers to {c} of {cm}: the kernel carries no mathematics"
  for n in literals do
    if tacticKinds.contains n || tacticSyntax.contains n then
      found := found.push s!"{d} ({m}) writes tactic syntax ({n}): the kernel runs no proof \
        search of its own; a domain's membership is established by its registered evidence"
  return found

/-- Every violation of the kernel's purity in `env`. -/
meta def violations (env : Environment) (roots : List Name) : IO (Array String) := do
  let mut found : Array String := #[]
  let sourcePath ← getSrcSearchPath
  for root in roots do
    let source ← findLean sourcePath root
    let directory := source.withExtension ""
    let modules := #[root] ++ (← moduleFiles directory root)
    for m in modules do
      unless env.header.importAllModules.any (·.module == m) do
        found := found.push s!"{m} requires import all for its complete purity audit"
  for (d, info) in env.constants.map₁.toList do
    let some idx := env.getModuleIdxFor? d | continue
    let m := env.header.moduleNames[idx.toNat]!
    unless roots.contains m.getRoot do continue
    found := found ++ declarationViolations env d m info
  return found

end CasGates.KernelPurity

end
