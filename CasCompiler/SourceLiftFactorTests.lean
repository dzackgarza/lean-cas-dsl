module

import CasCompiler.Read
import CasCompiler.Parse
import LeanCategories.Catalogue
import LeanCategories.Catalogue.Semantics.Modules.Bilinear.Valued.DegeneratePlaneLifts
import LeanCategories.Catalogue.Semantics.Modules.Bilinear.Valued.DegeneratePlaneFactorization
public meta import Lean.Elab.Command
meta import CasCompiler.Read
meta import CasCompiler.Parse
meta import LeanCategories.Catalogue
meta import LeanCategories.Catalogue.Semantics.Modules.Bilinear.Valued.DegeneratePlaneLifts
meta import LeanCategories.Catalogue.Semantics.Modules.Bilinear.Valued.DegeneratePlaneFactorization

open Lean Meta Elab Term CasCompiler

/- RX-LIFT's first factor (rx-lift-prescribed-stages.cas): `factor(g0) through first with cone
using proof(…)` reads as the selected lift's upstream factor computation
(`MonoLift.factorComputation`) at the lift's actual object and inclusion, with the base arrow
`g0` and the source arrow `cone`. The file writes `g0` with the matrix `[3/2, -1]`, whose entry
`3/2` is the registered division at the multiplicative monoid of `Q`, selected by a declared
preferred route for `/` on commutative rings (C6). -/
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
    -- The binding `unscaled` needs source admission with explicit evidence; the factor does not
    -- use it.
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
  factor.source.withOpen fun bindings value => do
    let value ← instantiateMVars value
    let some applied := value.find? (·.isAppOf ``CasCatalogue.MonoLiftFactorComputation.factor)
      | throwError "the factor is not the selected lift's factor computation: {value}"
    let mut found := none
    for binding in bindings do
      if (← binding.expression.fvarId!.getDecl).userName == `cone then found := some binding.expression
    let some cone := found | throwError "the session lost its cone binding"
    unless applied.getAppArgs.any (·.containsFVar cone.fvarId!) do
      throwError "the factor lost its actual source arrow: {applied}"
