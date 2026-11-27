module

import CasCompiler.Surface
public meta import Lean.Elab.Command
meta import CasCompiler.Surface

open Lean Meta CasCompiler

-- Native type universes, endpoints and both independent original maps remain arbitrary.
-- This checks the exact Mathlib whole-family adapter equation, without any supplied data.
run_cmd Lean.Elab.Command.liftTermElabM do
  let level := Level.param `carrierAdapterUniverse
  withLocalDeclD `X (mkSort (.succ level)) fun source =>
    withLocalDeclD `Y (mkSort (.succ level)) fun target => do
      let type ← mkAppM ``TypeCat.Hom #[source, target]
      withLocalDeclD `first type fun first =>
        withLocalDeclD `second type fun second => do
          for original in #[first, second] do
            let before ← mkAppM ``TypeCat.Hom.hom #[original]
            let before ← mkAppM ``TypeCat.Fun.toFun #[before]
            let after ← sourceSetFunction original
            let proposition ← mkEq before after
            let proof ← mkExpectedTypeHint (← mkEqRefl after) proposition
            checkWithKernel proof
            unless after.getAppFn.isConstOf ``TypeCat.Fun.toFun do
              throwError "the native carrier adapter changed its original final field"
            let some hom := after.getAppArgs.back?
              | throwError "the native carrier adapter lost its original hom record"
            unless hom.getAppFn.isConstOf ``TypeCat.Hom.hom' &&
                hom.getAppArgs.back? == some original do
              throwError "the native carrier adapter replaced the actual original map"
            let closed ← mkLambdaFVars #[source, target, first, second] after
              (usedOnly := false) (usedLetOnly := false)
            checkWithKernel closed
