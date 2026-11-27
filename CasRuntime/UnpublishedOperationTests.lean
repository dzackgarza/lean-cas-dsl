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

-- A reducible native constant has the same missing-operation boundary as an opaque one.
-- The source definition may be opened, but its unpublished Nat.add call is not kernel code.
run_cmd do
  let environment ← getEnv
  try
    let initial ← liftTermElabM do
      let root ← IO.currentDir
      KernelSession.start (some (root / ".tmp/unpublished-operation-empty-leaves.json"))
        (computationOnly := true)
    try
      let term ← `(term| Nat.add 84 30)
      let source ← liftTermElabM <| initial.source.define `closedAddition term
      liftCoreM <| KernelSession.install { initial with source }
      elabCommand (← `(command| #cas "let result := closedAddition"))
      let some session ← liftCoreM KernelSession.current?
        | throwError "the public command lost its source session"
      let some entry := session.source.context.entries.back?
        | throwError "the public command lost the original result binding"
      if (session.value? entry.id).isSome then
        throwError "the public #cas consumer computed unpublished Nat.add in the kernel"
      let run ← CasCatalogue.Language.runStatement session "let again := result"
      let .noImplementation reason := run.outcome
        | throwError "the original missing definition was not retained: {run.outcome.detail}"
      unless (reason.splitOn "Nat.add").length > 1 do
        throwError "the original unpublished declaration was not named: {reason}"
      unless (← liftM (m := IO) session.kernel.dispatches.get).isEmpty do
        throwError "an unpublished definition acquired a provider"
    finally liftM (m := IO) initial.close
  finally setEnv environment

-- Instance projection may inspect native constructor fields, but must not run a recursor
-- to obtain the instance. Its unpublished head remains the original missing operation.
run_cmd do
  let environment ← getEnv
  try
    let initial ← liftTermElabM do
      let root ← IO.currentDir
      KernelSession.start (some (root / ".tmp/unpublished-operation-empty-leaves.json"))
        (computationOnly := true)
    try
      let term ← `(term| @Inhabited.default Nat
        (Nat.rec (motive := fun _ => Inhabited Nat) ⟨7⟩ (fun _ prior => prior) 1))
      let source ← liftTermElabM <| initial.source.define `instanceRecursor term
      liftCoreM <| KernelSession.install { initial with source }
      elabCommand (← `(command| #cas "let result := instanceRecursor"))
      let some session ← liftCoreM KernelSession.current?
        | throwError "the public command lost its source session"
      let some entry := session.source.context.entries.back?
        | throwError "the public command lost the original result binding"
      if (session.value? entry.id).isSome then
        throwError "the public #cas consumer evaluated Nat.rec to obtain an instance field"
      let run ← CasCatalogue.Language.runStatement session "let again := result"
      let .noImplementation reason := run.outcome
        | throwError "the instance's missing eliminator was not retained: {run.outcome.detail}"
      unless (reason.splitOn "Nat.rec").length > 1 do
        throwError "the instance's original unpublished declaration was not named: {reason}"
      unless (← liftM (m := IO) session.kernel.dispatches.get).isEmpty do
        throwError "an unpublished instance eliminator acquired a provider"
    finally liftM (m := IO) initial.close
  finally setEnv environment

-- The numeral index alone does not determine an overloaded native numeral. Its selected
-- instance remains an original input, and an eliminator that supplies it must not execute.
run_cmd do
  let environment ← getEnv
  try
    let initial ← liftTermElabM do
      let root ← IO.currentDir
      KernelSession.start (some (root / ".tmp/unpublished-operation-empty-leaves.json"))
        (computationOnly := true)
    try
      let term ← `(term| @OfNat.ofNat Nat 3
        (Nat.rec (motive := fun _ => OfNat Nat 3) ⟨7⟩ (fun _ prior => prior) 1))
      let source ← liftTermElabM <| initial.source.define `numeralInstanceRecursor term
      liftCoreM <| KernelSession.install { initial with source }
      elabCommand (← `(command| #cas "let result := numeralInstanceRecursor"))
      let some session ← liftCoreM KernelSession.current?
        | throwError "the public command lost its source session"
      let some entry := session.source.context.entries.back?
        | throwError "the public command lost the original result binding"
      if (session.value? entry.id).isSome then
        throwError "the public #cas consumer ignored the numeral's selected instance"
      let run ← CasCatalogue.Language.runStatement session "let again := result"
      let .noImplementation reason := run.outcome
        | throwError "the numeral instance's missing operation was not retained: {run.outcome.detail}"
      unless (reason.splitOn "Nat.rec").length > 1 do
        throwError "the numeral instance's original missing operation was not named: {reason}"
      unless (← liftM (m := IO) session.kernel.dispatches.get).isEmpty do
        throwError "an unpublished numeral-instance eliminator acquired a provider"
    finally liftM (m := IO) initial.close
  finally setEnv environment

-- Native frontend adapters may supply the projection-constant syntax directly. It has
-- the same selected instance as the projection expression produced by term elaboration.
run_cmd do
  let environment ← getEnv
  try
    let initial ← liftTermElabM do
      let root ← IO.currentDir
      KernelSession.start (some (root / ".tmp/unpublished-operation-empty-leaves.json"))
        (computationOnly := true)
    try
      let source ← liftTermElabM do
        let original ← initial.source.elaborate Syntax.missing fun _ => do
          let dictionary ← elabTermAndSynthesize
            (← `(term| Nat.rec (motive := fun _ => OfNat Nat 3)
              ⟨7⟩ (fun _ prior => prior) 1)) none
          let expression := mkAppN (mkConst ``OfNat.ofNat [Level.zero])
            #[mkConst ``Nat, mkNatLit 3, dictionary]
          checkWithKernel expression
          return expression
        initial.source.defineTerm `nativeNumeralInstance original
      liftCoreM <| KernelSession.install { initial with source }
      elabCommand (← `(command| #cas "let result := nativeNumeralInstance"))
      let some session ← liftCoreM KernelSession.current?
        | throwError "the public command lost its native source session"
      let some entry := session.source.context.entries.back?
        | throwError "the public command lost its native result binding"
      if (session.value? entry.id).isSome then
        throwError "the native frontend numeral ignored its selected instance"
      let run ← CasCatalogue.Language.runStatement session "let again := result"
      let .noImplementation reason := run.outcome
        | throwError "the native numeral's missing operation was not retained: {run.outcome.detail}"
      unless (reason.splitOn "Nat.rec").length > 1 do
        throwError "the native numeral changed its original missing operation: {reason}"
      unless (← liftM (m := IO) session.kernel.dispatches.get).isEmpty do
        throwError "a native numeral-instance eliminator acquired a provider"
    finally liftM (m := IO) initial.close
  finally setEnv environment
