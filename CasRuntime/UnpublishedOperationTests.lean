module

import CasCatalogue.TestSuite
import all CasRuntime.Session
public meta import Lean.Elab.Command
meta import CasCatalogue.TestSuite

open Lean Meta Elab Command Term CasCompiler CasRuntime

-- The original native source definition is a closed operation with no published
-- family. Its public #cas consumer must report the missing operation; reducing
-- Nat.gcd in the kernel would turn this check into a retained value instead.
run_cmd do
  let environment ← getEnv
  try
    let initial ← liftTermElabM do
      let root ← IO.currentDir
      IO.FS.createDirAll (root / ".tmp")
      let path := root / ".tmp/unpublished-operation-empty-leaves.json"
      IO.FS.writeFile path
        (Json.mkObj [("backends", .arr #[]), ("registrations", .arr #[])]).compress
      KernelSession.start (some path) (computationOnly := true)
    try
      let term ← `(term| Nat.gcd 84 30)
      let source ← liftTermElabM <| initial.source.define `closedGcd term
      liftCoreM <| KernelSession.install { initial with source }
      elabCommand (← `(command| #cas "let result := closedGcd"))
      let some session ← liftCoreM KernelSession.current?
        | throwError "the public command lost its source session"
      let some entry := session.source.context.entries.back?
        | throwError "the public command lost the original result binding"
      unless entry.userName == `result do
        throwError "the public command replaced the original source definition"
      if (session.value? entry.id).isSome then
        throwError "the public #cas consumer computed unpublished Nat.gcd in the kernel"
      let run ← CasCatalogue.Language.runStatement session "let again := result"
      let .noImplementation reason := run.outcome
        | throwError "the original missing operation was not retained: {run.outcome.detail}"
      unless (reason.splitOn "Nat.gcd").length > 1 do
        throwError "the missing operation was not named: {reason}"
      unless (← liftM (m := IO) session.kernel.dispatches.get).isEmpty do
        throwError "an unpublished operation acquired a provider"
    finally liftM (m := IO) initial.close
  finally setEnv environment

-- Head reduction of an eliminator is computation too. This source must retain
-- its missing operation instead of becoming the literal returned by Nat.rec.
run_cmd do
  let environment ← getEnv
  try
    let initial ← liftTermElabM do
      let root ← IO.currentDir
      KernelSession.start (some (root / ".tmp/unpublished-operation-empty-leaves.json"))
        (computationOnly := true)
    try
      let term ← `(term| Nat.rec (motive := fun _ => Nat) 7 (fun _ n => n) 1)
      let source ← liftTermElabM <| initial.source.define `closedRecursor term
      liftCoreM <| KernelSession.install { initial with source }
      elabCommand (← `(command| #cas "let result := closedRecursor"))
      let some session ← liftCoreM KernelSession.current?
        | throwError "the public command lost its source session"
      let some entry := session.source.context.entries.back?
        | throwError "the public command lost the original result binding"
      if (session.value? entry.id).isSome then
        throwError "the public #cas consumer evaluated unpublished Nat.rec in the kernel"
      let run ← CasCatalogue.Language.runStatement session "let again := result"
      let .noImplementation reason := run.outcome
        | throwError "the original missing eliminator was not retained: {run.outcome.detail}"
      unless (reason.splitOn "Nat.rec").length > 1 do
        throwError "the missing eliminator was not named: {reason}"
      unless (← liftM (m := IO) session.kernel.dispatches.get).isEmpty do
        throwError "an unpublished eliminator acquired a provider"
    finally liftM (m := IO) initial.close
  finally setEnv environment
