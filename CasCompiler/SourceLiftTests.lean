module

import CasCompiler.Read
import CasCompiler.Parse
import LeanCategories.Catalogue
import LeanCategories.Catalogue.Semantics.Modules.Bilinear.Valued.DegeneratePlaneLifts
public meta import Lean.Elab.Command
meta import CasCompiler.Read
meta import CasCompiler.Parse
meta import LeanCategories.Catalogue
meta import LeanCategories.Catalogue.Semantics.Modules.Bilinear.Valued.DegeneratePlaneLifts

open Lean Meta Elab Term CasCompiler

-- Reuse the original selected application and accepted MonoLift projection terms.
-- This checks native source translation, without deciding any acceptance question.
run_cmd Lean.Elab.Command.liftTermElabM do
  let path := "tests/acceptance/proposals/independent-extension-reconstruction-20261024/" ++
    "completion/rx-lift-prescribed-stages.cas"
  let file ← SourceFile.parse path (← liftM (m := IO) (IO.FS.readFile path))
  let identities ← liftM (m := IO) CasRuntime.IdentitySupply.new
  let mut session ← SourceSession.empty identities
  let mut observed := #[]
  for item in file.items do
    let `(cas_item| $statement:cas_stmt) := item | continue
    if let `(cas_stmt| assert $_:cas_term) := statement then continue
    let name ← match statement with
      | `(cas_stmt| let $name:ident := $_:cas_term) => pure name.getId
      | `(cas_stmt| let $name:ident($_:cas_term) := $_:cas_term) => pure name.getId
      | _ => continue
    let .definition next value ← file.withContext (session.readStatement statement)
      | throwError "the original selected lift did not extend its source context"
    unless value.source.context.entries.map (·.id) == session.context.entries.map (·.id) do
      throwError "the selected lift shortened its original ordered context"
    let expectedName := match name with
      | `X1 => some "CasCatalogue.Modules.Bilinear.Valued.DegeneratePlaneLifts.firstObject"
      | `i1 => some "CasCatalogue.Modules.Bilinear.Valued.DegeneratePlaneLifts.firstInclusion"
      | `alpha1 => some "CasCatalogue.Modules.Bilinear.Valued.DegeneratePlaneLifts.alpha"
      | `beta1 => some "CasCatalogue.Modules.Bilinear.Valued.DegeneratePlaneLifts.beta"
      | _ => none
    if let some expectedName := expectedName then
      let .ok parsed := Parser.runParserCategory (← getEnv) `term expectedName
        | throwError "the owned lift projection did not parse"
      let expected ← session.term ⟨parsed⟩
      value.source.withOpen fun bindings expression => do
        let expected ← expected.source.inContext (← ContextTelescope.capture bindings)
        unless ← isDefEq expression expected do
          throwError "the original lift projection {name} changed its selected native application"
        checkWithKernel (← mkExpectedTypeHint (← mkEqRefl expression) (← mkEq expression expected))
      observed := observed.push name
    session := next
    if name == `beta1 then break
  unless observed == #[`X1, `i1, `alpha1, `beta1] do
    throwError "the original selected lift did not supply all four native projections"
