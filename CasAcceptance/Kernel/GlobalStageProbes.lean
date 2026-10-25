/- Copyright (c) 2026 Dzack Garza. Released under Apache 2.0 license. -/
module

import CasCatalogue.Language
meta import CasCatalogue.Language

open Lean Meta Elab Command Term CasCatalogue CasCatalogue.Language

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

/- A private reading trace must never reuse or mutate its caller's cached values. -/
run_cmd liftTermElabM <| withoutErrToSorry <| withCurrHeartbeats do
  let .ok term := Parser.runParserCategory (← getEnv) `cas_term "ℤ in Rings"
    | throwError "cache isolation fixture did not parse"
  let old : Std.HashMap String Value := ({} : Std.HashMap String Value).insert
    (shown term) (.literal `unrelated)
  let supplied ← IO.mkRef old
  let value ← (eval {} term).run { closedTerms := some supplied }
  unless value matches .object .. do
    throwError "a private reading used a value from a different trace"
  let after ← supplied.get
  unless after.size == old.size do
    throwError "a private reading modified its caller's cache"
  unless (after[shown term]?).any (fun value => value matches .literal `unrelated) do
    throwError "a private reading replaced its caller's cached value"

/- A failed optional reading restores the cache together with its operation trace. -/
run_cmd liftTermElabM <| withoutErrToSorry <| withCurrHeartbeats do
  let .ok term := Parser.runParserCategory (← getEnv) `cas_term "ℤ in Rings"
    | throwError "cache rollback fixture did not parse"
  let trace ← Trace.new
  let cache ← IO.mkRef ({} : Std.HashMap String Value)
  let rejected ← (optionalReading (do
    discard <| eval {} term
    throwStratum .invalid "deliberate engineering rejection" : Language.M Value)).run
      { trace := some trace, closedTerms := some cache }
  unless rejected.isNone && (← cache.get).isEmpty && (← trace.get).isEmpty do
    throwError "a failed optional reading retained its speculative trace or cache"

/- A differential name depends on its bound generator. Passing it to a declared
map must retain that binding and the complete generalized source. -/
run_cmd liftTermElabM <| withoutErrToSorry <| withCurrHeartbeats do
  let parse (text : String) : TermElabM Syntax := do
    let .ok term := Parser.runParserCategory (← getEnv) `cas_term text
      | throwError "differential context fixture did not parse"
    pure term
  let trace ← Trace.new
  let cache ← IO.mkRef ({} : Std.HashMap String Value)
  let base : Language.Ctx := { trace := some trace, closedTerms := some cache }
  let P ← (eval {} (← parse "ℚ[x]")).run base
  let generator ← (generatorOf P).run base
  let domain ← (eval {} (← parse "ℕ in Sets")).run base
  let context := { base with stage := some domain, bound := [(`x, generator)] }
  let actual ← (eval {} (← parse "coordinate(dx)")).run context
  let explicit ← (eval {} (← parse "coordinate(d(x))")).run context
  let (.element left leftTarget, .element right rightTarget) := (actual, explicit)
    | throwError "the differential control lost its complete element"
  unless ← withTransparency .all <| isDefEq (← inferType left) (← inferType right) do
    throwError "the differential alias changed its generalized domain"
  unless ← withTransparency .all <| isDefEq left right do
    throwError "the differential alias changed its declared map"
  unless ← withTransparency .all <| isDefEq
      (← (semanticObject leftTarget).run base) (← (semanticObject rightTarget).run base) do
    throwError "the differential alias changed its complete target"
  pure ()

/- A bound element keeps its exact generalized source under ordinary application;
   a bound whole map still uses the categorical composition path. -/
run_cmd liftTermElabM <| withoutErrToSorry <| withCurrHeartbeats do
  let parse (text : String) : TermElabM Syntax := do
    let .ok term := Parser.runParserCategory (← getEnv) `cas_term text
      | throwError "bound application fixture did not parse"
    pure term
  let trace ← Trace.new
  let cache ← IO.mkRef ({} : Std.HashMap String Value)
  let base : Language.Ctx := { trace := some trace, closedTerms := some cache }
  let A ← (eval {} (← parse "ℤ in Sets")).run base
  let S ← (eval {} (← parse "ℕ in Sets")).run base
  let point ← (eval {} (← parse "2 in ℤ")).run base
  let .object object sets .. := A | throwError "bound application lost its set"
  let identity ← (identityAt A).run base
  let function := Value.morphism identity object object sets (some (A, A))
  let context := { base with stage := some S, bound := [(`c, point)] }
  let .element applied target ← (apply {} function #[(← parse "c")]).run context
    | throwError "a bound element was reinterpreted as a whole map"
  let .element expected _ ← (restage point).run context
    | throwError "bound element fixture lost its original point"
  unless ← withTransparency .all <| isDefEq applied expected do
    throwError "a bound point changed its actual generalized arrow"
  unless target.sameSource A do
    throwError "a bound point changed its complete selected target"
  let mapped ← (apply {} function #[(← parse "g")]).run
    { base with bound := [(`g, function)] }
  let .morphism composed source destination .. := mapped
    | throwError "a bound whole map was reinterpreted as a point"
  unless source == object && destination == object &&
      (← withTransparency .all <| isDefEq composed identity) do
    throwError "categorical composition changed its complete endpoints or arrow"
  let C ← (eval {} (← parse "ℂ in Sets")).run base
  let incompatible := Value.element (← (identityAt C).run base) C
  let rejected ← try
    discard <| (apply {} function #[(← parse "z")]).run
      { base with stage := some C, bound := [(`z, incompatible)] }
    pure false
  catch error =>
    if Exception.interpretationKind error == .invalid then pure true else throw error
  unless rejected do
    throwError "a bound point bypassed the complete registered source domain"

/- Repeated product factors retain the whole selected source. Same-carrier named
   objects still require an unambiguous complete reading before any factor is reused. -/
run_cmd liftTermElabM <| withoutErrToSorry <| withCurrHeartbeats do
  let state ← registryState
  let sets ← categoryNamed state "Sets"
  let .ok parsed := Parser.runParserCategory (← getEnv) `cas_term "ℤ in Rings"
    | throwError "repeated factor fixture did not parse"
  let trace ← Trace.new
  let context : Language.Ctx := { trace := some trace }
  let chosen ← (eval {} parsed).run context
  let carrier ← (carrierObject chosen).run context
  let term ← (semanticObject carrier).run context
  let product ← mkAppM ``Prod #[term, term]
  let .object _ _ _ _ (some (components, _, _, _, _)) ←
      (declaredEndpointObject product sets #[chosen]).run context
    | throwError "the repeated product lost its declared factors"
  unless components.size >= 2 && components[0]!.sameSource components[1]! do
    throwError "identical factors lost their complete common reading"
  for component in components.extract 0 2 do
    unless (sourceParameterValues component).any (·.sameSource chosen) do
      throwError "a repeated factor discarded its selected source"
  let domain ← (object state "Fin" #[.nat 3] (some sets)).run context
  let target ← (object state "Fin" #[.nat 5] (some sets)).run context
  let maps ← (object state "Maps" #[domain, target] (some sets)).run context
  let vectors ← (object state "Vec" #[target, .nat 3] (some sets)).run context
  let bare ← withTransparency .all <| whnf (← (semanticObject maps).run context)
  let ambiguousProduct ← mkAppM ``Prod #[bare, bare]
  for known in #[#[maps, vectors], #[vectors, maps]] do
    let ambiguous ← try
      discard <| (declaredEndpointObject ambiguousProduct sets known).run context
      pure false
    catch error =>
      if Exception.isSemanticAmbiguity error then pure true else throw error
    unless ambiguous do
      throwError "a repeated factor selected one of two distinct named objects"

/- A member receiver named by a differential also depends on its generator.
The enclosing declared map must preserve that bound source context. -/
run_cmd liftTermElabM <| withoutErrToSorry <| withCurrHeartbeats do
  let parse (text : String) : TermElabM Syntax := do
    let .ok term := Parser.runParserCategory (← getEnv) `cas_term text
      | throwError "differential context fixture did not parse"
    pure term
  let trace ← Trace.new
  let cache ← IO.mkRef ({} : Std.HashMap String Value)
  let base : Language.Ctx := { trace := some trace, closedTerms := some cache }
  let P ← (eval {} (← parse "ℚ[x]")).run base
  let generator ← (generatorOf P).run base
  let domain ← (eval {} (← parse "ℕ in Sets")).run base
  let context := { base with stage := some domain, bound := [(`x, generator)] }
  let actual ← (eval {} (← parse "d(dx.coordinate())")).run context
  let explicit ← (eval {} (← parse "d(coordinate(d(x)))")).run context
  let (.element left leftTarget, .element right rightTarget) := (actual, explicit)
    | throwError "the differential control lost its complete element"
  unless ← withTransparency .all <| isDefEq (← inferType left) (← inferType right) do
    throwError "the differential alias changed its generalized domain"
  unless ← withTransparency .all <| isDefEq left right do
    throwError "the differential alias changed its declared map"
  unless ← withTransparency .all <| isDefEq
      (← (semanticObject leftTarget).run base) (← (semanticObject rightTarget).run base) do
    throwError "the differential alias changed its complete target"
  pure ()
