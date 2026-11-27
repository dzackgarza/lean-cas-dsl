import Lake
open Lake DSL







package «cas-dsl» where
  version := v!"0.1.0"

require «nbdsl-worker» from git
  "https://github.com/dzackgarza/lean-jupyter-kernel"
    @ "main" / "worker"

require mathlib from git
  "https://github.com/leanprover-community/mathlib4" @ "v4.33.0"

require cslib from git
  "https://github.com/leanprover/cslib" @ "3951377e5a3f5772737f11cd62bc5bb6a72f95d1"

require PolyFun from git
  "https://github.com/Verified-zkEVM/PolyFun" @ "a5895e454254a400774fa396b64d5b968f0933df"




require lean_categories from git
  "https://github.com/dzackgarza/lean-categories" @ "main"







require cas_leaf_contracts from git
  "https://github.com/dzackgarza/lean-cas-dsl-leaf-contracts" @ "main"



lean_lib CasDsl where


  globs := #[.andSubmodules `CasDsl]


lean_lib CasCompiler

lean_lib CasRuntime


lean_lib CasCompilerTests

lean_lib CasRuntimeTests





@[default_target]
lean_lib CasCatalogue where
  globs := #[.andSubmodules `CasCatalogue]
  leanOptions := #[
    ⟨`relaxedAutoImplicit, false⟩,
    ⟨`weak.linter.mathlibStandardSet, true⟩,
    ⟨`weak.linter.style.header, false⟩,
    ⟨`maxSynthPendingDepth, (3 : Nat)⟩]




@[default_target]
lean_lib CasGates where
  globs := #[.submodules `CasGates]




lean_lib CasAcceptance where
  globs := #[.andSubmodules `CasAcceptance]
  leanOptions := #[
    ⟨`relaxedAutoImplicit, false⟩,
    ⟨`weak.linter.mathlibStandardSet, true⟩,
    ⟨`weak.linter.style.header, false⟩,
    ⟨`maxSynthPendingDepth, (3 : Nat)⟩]


lean_lib CasTools where
  globs := #[
    .one `CasTools.AxiomAudit,
    .one `CasTools.QuestionExport,
    .one `CasTools.ExportFull,
    .one `CasTools.AxiomAuditMain,
    .one `CasTools.SourceSnapshotTests,
    .one `CasTools.JsonGraphTests,
    .one `CasTools.HarnessMain,
    .one `CasTools.ExportBoundaryProbe,
    .one `CasTools.NativeExpressionTests,
    .one `CasTools.InterfaceExportTests,
    .one `CasTools.QuestionExportTests,
    .one `CasTools.QuestionObservation,
    .one `CasTools.ExportJson,
    .one `CasTools.ExportMain,
    .one `CasTools.InterfaceExport,
    .one `CasTools.InterfaceDocument,
    .one `CasTools.Harness]

lean_lib CasNative where
  roots := #[
    `CasTools.JsonGraph,
    `CasTools.NativeExpression,
    `CasTools.Diagnostics,
    `CasCompiler.NativeDeclarations,
    `CasCompiler.Context,
    `CasCompiler.ContextSnapshot]
  precompileModules := true


lean_exe «cas-registry-export» where
  root := `CasTools.ExportMain
  supportInterpreter := true


lean_exe «cas-harness» where
  root := `CasTools.HarnessMain
  supportInterpreter := true



lean_exe «cas-axiom-audit» where
  root := `CasTools.AxiomAuditMain
  supportInterpreter := true



lean_lib CasDslTests


script «feedback-context» do
  let workspace ← getWorkspace
  let packages := workspace.packages.map fun pkg => Lean.Json.mkObj [
    ("name", Lean.toJson pkg.prettyName),
    ("key", Lean.toJson (pkg.keyName.toString (escape := false))),
    ("path", Lean.toJson pkg.dir.toString),
    ("configuration", Lean.toJson pkg.configFile.toString)]
  IO.println <| (Lean.Json.mkObj [
    ("arguments", Lean.toJson workspace.lakeArgs?),
    ("packages", .arr packages)]).compress
  return 0


script «feedback-lean» args do
  let source :: moreArgs := args
    | throw <| IO.userError "usage: lake run feedback-lean SOURCE [LEAN-ARG ...]"
  let workspace ← getWorkspace
  let command ← workspace.runBuild <|
    Lake.prepareLeanCommand (System.FilePath.mk source) moreArgs.toArray
  let helper := workspace.root.dir / "scripts" / "feedback_records.py"
  let child ← IO.Process.spawn { command with
    cmd := "python3"
    args := #["-S", helper.toString, "execute-lean", command.cmd] ++ command.args }
  return ← child.wait


target «feedback-worker-commands» _pkg : System.FilePath := do
  let some context ← IO.getEnv "CAS_FEEDBACK_CONTEXT"
    | error "feedback worker preparation requires its current context"
  let some run := (System.FilePath.mk context).parent
    | error "feedback context has no run directory"
  let selection : Lean.Json ← match Lean.Json.parse (← IO.FS.readFile (run / "selection.json")) with
    | .ok value => pure value
    | .error message => error message
  let complete : Bool ← match selection.getObjValAs? Bool "complete" with
    | .ok value => pure value
    | .error message => error message
  unless complete do error "acceptance selection is incomplete"
  let workers : Nat ← match selection.getObjValAs? Nat "workers" with
    | .ok value => pure value
    | .error message => error message
  if workers == 0 then error "no acceptance workers"
  let jobs ← (List.range workers).toArray.mapM fun worker => do
    let source := run / s!"worker{worker}.lean"
    let contents ← IO.FS.readFile source
    let prepared ← Lake.prepareLeanCommand source #["-DstderrAsMessages=false"]
    prepared.mapM (sync := true) fun command => do
      match command.stdin, command.stdout, command.stderr with
      | .inherit, .inherit, .inherit => pure ()
      | _, _, _ => error "prepared worker requires inherited standard streams"
      if command.cwd.isSome || !command.inheritEnv || command.setsid then
        error "prepared worker requires the current directory, environment and process group"
      return Lean.Json.mkObj [
        ("worker", Lean.toJson worker),
        ("source", Lean.toJson source.toString),
        ("contents", Lean.toJson contents),
        ("cmd", Lean.toJson command.cmd),
        ("args", Lean.toJson command.args),
        ("env", Lean.toJson command.env)]
  (Lake.Job.collectArray jobs).mapM (sync := true) fun commands => do
    let output := run / "prepared-workers.json"
    let temporary := run / "prepared-workers.pending.json"
    IO.FS.writeFile temporary <| (Lean.Json.mkObj [
      ("context", Lean.toJson context),
      ("commands", .arr commands)]).compress ++ "\n"
    IO.FS.rename temporary output
    return output
