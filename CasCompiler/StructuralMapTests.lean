module

import CasCompiler.StructuralMap
import LeanCategories.Catalogue.Semantics.Limits.Registration
public meta import Lean.Elab.Command
meta import CasCompiler.StructuralMap
meta import LeanCategories.Catalogue.Semantics.Limits.Registration

namespace CasCompiler.StructuralMapTests

open Lean Meta Elab Term CasCatalogue

-- Both fixed native diagram maps are checked under their entire original rigid telescope.
-- In groups the original syntax is the trivial homomorphism 1, not a guessed scalar zero.
run_cmd Lean.Elab.Command.liftTermElabM do
  let state ← semanticState
  for id in #["lim.groups.kernel", "colim.bil_w_form.cokernel"] do
    let #[entry] := state.limits.filter (·.id.raw == id)
      | throwError "the structural-map control lost its original declared limit"
    let declaration ← getConstInfo entry.declaration
    for levels in #[declaration.levelParams.map (fun _ => Level.zero),
        declaration.levelParams.map Level.param] do
      let presentation := Lean.mkConst declaration.name levels
      forallTelescopeReducing (← inferType presentation) fun parameters result => do
        let bindings := parameters.mapIdx fun index expression =>
          ({ id := ⟨"fixed-native-diagram", index⟩, role := .parameter, expression } : LocalBinding)
        let context ← ContextTelescope.capture bindings
        let result ← whnfR result
        let diagram := result.getAppArgs.back!
        unless diagram.isAppOf ``CategoryTheory.Limits.parallelPair do
          throwError "the structural-map control changed its original native diagram"
        let original := diagram.getAppArgs.back!
        let some selected ← NativeStructuralMap.ofExpr? context original
          | throwError "the original fixed diagram map {id} has no unchanged structural descriptor"
        unless selected.tag == "zero" && selected.value.equal original do
          throwError "structural framing replaced the original fixed native map"
        let type ← inferType original
        unless type.isAppOfArity ``Quiver.Hom 4 &&
            selected.source.equal type.getAppArgs[2]! &&
            selected.target.equal type.getAppArgs[3]! do
          throwError "structural framing lost its original complete native endpoints"
        checkWithKernel (← mkLambdaFVars parameters selected.value
          (usedOnly := false) (usedLetOnly := false))

-- Ordinary arithmetic literals and unregistered function computations do not acquire a map.
run_cmd Lean.Elab.Command.liftTermElabM do
  let context ← ContextTelescope.capture #[]
  for source in #["(0 : Nat)", "(1 : Nat)", "Nat.add 0 0"] do
    let stx ← ofExcept <| Parser.runParserCategory (← getEnv) `term source
    let value ← elabTermAndSynthesize stx none
    if (← NativeStructuralMap.ofExpr? context value).isSome then
      throwError "native scalar computation acquired a categorical structural map"

end CasCompiler.StructuralMapTests
