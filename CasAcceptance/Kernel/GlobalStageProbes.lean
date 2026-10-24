/- Copyright (c) 2026 Dzack Garza. Released under Apache 2.0 license. -/
module

import CasCatalogue.Language
meta import CasCatalogue.Language

open Lean Meta Elab Term CasCatalogue CasCatalogue.Language

/- Complete closed points are reindexed along the registered terminal map when
used in a variable context. The original endpoints and source trace are retained. -/
run_elab do
  let parse (text : String) : TermElabM Syntax := do
    let .ok term := Parser.runParserCategory (← getEnv) `cas_term text
      | throwError "the stage-control input did not parse"
    pure term
  let trace ← Trace.new
  let closed ← (eval {} (← parse "2 in ℤ")).run { trace := some trace }
  let domain ← (eval {} (← parse "ℕ in Sets")).run { trace := some trace }
  let product ← (eval {} (← parse "ℤ × ℕ")).run { trace := some trace }
  let .element original target := closed | throwError "the control lost its closed point"
  let identity ← (identityAt domain).run { trace := some trace }
  let context : Language.Ctx := {
    trace := some trace
    stage := some domain
    bound := [(`c, closed), (`n, .element identity domain)] }
  let .element staged _ ← (restage closed).run context
    | throwError "the closed point was not retained as an element"
  let expected ← mkAppM ``Quiver.Hom #[← (semanticObject domain).run {},
    ← (semanticObject target).run {}]
  unless ← withTransparency .all <| isDefEq (← inferType staged) expected do
    throwError "the closed point lost the independently selected variable domain"
  let .element tuple _ ← (eval {} (← parse "(c, n)") none (some product)).run context
    | throwError "the mixed global and variable operands did not form a declared product"
  let expectedProduct ← mkAppM ``Quiver.Hom #[← (semanticObject domain).run {},
    ← (semanticObject product).run {}]
  unless ← withTransparency .all <| isDefEq (← inferType tuple) expectedProduct do
    throwError "the mixed product changed its complete generalized domain"
  let some (.morphismComposition _ _ retained _ _ _) ← trace.node? staged
    | throwError "restaging lost its declared terminal-map composition"
  unless retained == original do
    throwError "restaging replaced the complete original closed point"
