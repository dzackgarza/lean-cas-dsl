module

import CasCompiler.Read
import CasCompiler.SourceTestSupport
import CasCompiler.Parse
import LeanCategories.Catalogue
import LeanCategories.Catalogue.Semantics.Modules.Bilinear.Valued.DegeneratePlaneLifts
import LeanCategories.Catalogue.Semantics.Modules.Bilinear.Valued.DegeneratePlaneFactorization
public meta import Lean.Elab.Command
meta import CasCompiler.Read
meta import CasCompiler.SourceTestSupport
meta import CasCompiler.Parse
meta import LeanCategories.Catalogue
meta import LeanCategories.Catalogue.Semantics.Modules.Bilinear.Valued.DegeneratePlaneLifts
meta import LeanCategories.Catalogue.Semantics.Modules.Bilinear.Valued.DegeneratePlaneFactorization

open Lean Meta Elab Term CasCompiler
open CasCompiler.SourceTest







set_option maxHeartbeats 2000000 in
run_cmd Lean.Elab.Command.liftTermElabM do
  setPreferredRoutes #[⟨"/", "cat.commutative_rings",
    #["fun.commutative_rings.ring", "fun.rings.multiplicative_monoid"]⟩]
  let path := "tests/acceptance/proposals/independent-extension-reconstruction-20261024/" ++
    "completion/rx-lift-prescribed-stages.cas"
  let file ← SourceFile.parse path (← liftM (m := IO) (IO.FS.readFile path))
  let identities ← liftM (m := IO) CasRuntime.IdentitySupply.new
  let mut session ← SourceSession.empty identities
  for item in file.items do
    let `(cas_item| $statement:cas_stmt) := item | continue
    let name ← match statement with
      | `(cas_stmt| let $name:ident := $_:cas_term) => pure name.getId
      | `(cas_stmt| let $name:ident($_:cas_term) := $_:cas_term) => pure name.getId
      | _ => continue


    if name == `unscaled then continue
    let .definition next _ ← file.withContext (session.readStatement statement)
      | throwError "the original binding {name} did not extend its source context"
    session := next
    if name == `g0 then break
  let .ok source := Parser.runParserCategory (← getEnv) `cas_term
      ("factor(g0) through first with cone using proof(" ++
        "CasCatalogue.Modules.Bilinear.Valued.DegeneratePlaneFactorization.cone_base_factorization)")
    | throwError "the factor source did not parse"
  let factor ← session.read ⟨source⟩
  unless factor.category.any (·.role == .morphism) do
    throwError "the factor did not read as a morphism"
  checkSelected factor fun value => do
    let scope ← get
    let bindings ← authoredBindings
    let some entry := session.context.entries.find? (·.userName == `cone)
      | throwError "the session lost its cone binding"
    let some cone := bindings.find? (·.id == entry.id)
      | throwError "the original cone lost its exact native binding"
    let some retained ← SourceReadM.selection? value
      | throwError "the factor lost its exact original selected binding"
    let some field := retained.field
      | throwError "the factor lost its selected original computation field"
    unless field.projection == ``CasCatalogue.MonoLiftFactorComputation.factor do
      throwError "the factor changed its selected original computation field"
    let count ← visitNativeData (fun applied => do
      unless applied.isAppOf ``CasCatalogue.MonoLiftFactorComputation.factor do return false
      unless ← applied.getAppArgs.anyM fun original =>
          originatesAt scope.context scope.selections original cone.expression do
        throwError "the factor lost its actual source arrow: {applied}"
      return true) value
    unless count == 1 do
      throwError "the factor is not the selected lift's one original factor computation"
