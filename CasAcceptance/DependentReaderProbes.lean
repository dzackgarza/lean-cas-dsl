module

import CasCatalogue.Language
meta import CasCatalogue.Language

open Lean Meta Elab Command Term
open CasCatalogue CasCatalogue.Language

/- Reader mechanics only: these probes form requests at their complete declared types.
They add neither mathematical assertions nor backend implementations. -/
run_cmd do
  for text in #[
      "(x, y) ↦ x + y in (ℤ × ℤ) → ℤ",
      "((a, b), (c, d)) ↦ a*d + b*c in (Vec(ℤ, 2) × Vec(ℤ, 2)) → ℤ",
      "(a, b, c) ↦ (a + b - c, 0, 0) in Vec(ℚ, 3) → Vec(ℚ, 3)"] do
    liftTermElabM <| withoutErrToSorry <| withCurrHeartbeats do
      let .ok parsed := Parser.runParserCategory (← getEnv) `cas_term text
        | throwError "dependent reader probe failed to parse: {text}"
      let trace ← Trace.new
      let .morphism arrow source target _ (some _) ← (eval {} parsed).run { trace := some trace }
        | throwError "a component pattern did not form a arrow: {text}"
      unless !arrow.hasMVar && !arrow.hasLevelMVar && (← isTypeCorrect arrow) do
        throwError "the destructured arrow is not completely typed: {text}"
      let some (actualSource, actualTarget) := homEnds? (← inferType arrow)
        | throwError "the destructured arrow lost its endpoints"
      unless ← isDefEq source actualSource <&&> isDefEq target actualTarget do
        throwError "the destructured arrow replaced a selected endpoint"

/- A constructor parameter is a complete selected module over the selected ring, rather
than a function carrier equipped with fresh inferred structure. -/
run_cmd liftTermElabM <| withoutErrToSorry do
  let state ← registryState
  let integers ← (object state "ℤ" #[] none).run {}
  let vectors ← (object state "Vec" #[integers, .nat 2] none).run {}
  let expected ← elabTermAndSynthesize (← `(ModuleCat (RingCat.of ℤ))) none
  let selected ← (typedParameter expected vectors).run {}
  unless !selected.hasMVar && !selected.hasLevelMVar && (← isTypeCorrect selected) &&
      (← isDefEq (← inferType selected) expected) do
    throwError "the vector parameter did not retain the actual ModuleCat ring"

/- A supplied full structure needs no separate carrier name to inherit a registered numeral. -/
run_cmd liftTermElabM <| withoutErrToSorry <| withCurrHeartbeats do
  let state ← registryState
  let some category := state.categories.find?
      (·.declaration == `LeanCategories.Algebra.CommutativeRings)
    | throwError "the numeral owner probe has no registered category"
  let trace ← Trace.new
  let .object selected .. ← (object state "ℤ" #[] (some category)).run { trace := some trace }
    | throwError "the numeral owner probe has no complete selected object"
  let anonymous := Value.object selected category none none none
  let .element point _ ← (toElement (.nat 2) anonymous).run { trace := some trace }
    | throwError "the anonymous selected object lost its inherited numeral"
  unless !point.hasMVar && !point.hasLevelMVar && (← isTypeCorrect point) do
    throwError "the inherited numeral lost its complete type"
  let some (.elementNumeral 2 _ retained) ← trace.node? point
    | throwError "the inherited numeral lost its selected owner"
  unless ← isDefEq retained selected do
    throwError "the inherited numeral replaced its full selected object"

/- The admitted dependent function domain comes from the registered inclusion signature;
its closed value can subsequently be supplied to a formed-object constructor. Each subsequent
request has the ordinary interpretation budget and shares the original selected value and trace. -/
run_cmd liftTermElabM <| withoutErrToSorry <| withCurrHeartbeats do
  let .ok parsed := Parser.runParserCategory (← getEnv) `cas_term
      "((a, b), (c, d)) ↦ a*d + b*c in BilinearMaps(ℤ, Vec(ℤ, 2), Vec(ℤ, 2), RegularModule(ℤ))"
    | throwError "the dependent admission probe failed to parse"
  let trace ← Trace.new
  let value ← (eval {} parsed).run { trace := some trace }
  let .element point domain := value
    | throwError "the registered bilinear admission did not form a point"
  let parameter ← (typedParameter (← (semanticObject domain).run {}) value).run
    { trace := some trace }
  unless !point.hasMVar && !parameter.hasMVar && (← isTypeCorrect parameter) do
    throwError "a closed admitted parameter lost its complete declared type"
  let some (.elementValue original _ _) ← trace.node? parameter
    | throwError "extracting the admitted parameter lost its original point"
  unless ← isDefEq original point do
    throwError "extracting the admitted parameter changed its source point"
  let mut bindings := [(`b, value)]
  let .ok callableSyntax := Parser.runParserCategory (← getEnv) `cas_term
      "b((2, -1), (3, 4))"
    | throwError "the dependent callable application failed to parse"
  withCurrHeartbeats do
    let .element callableResult _ ← (eval {} callableSyntax).run
        { trace := some trace, bound := bindings }
      | throwError "the declared callable input did not pack its component arguments"
    unless !callableResult.hasMVar && !callableResult.hasLevelMVar &&
        (← isTypeCorrect callableResult) do
      throwError "the multiargument callable request lost its selected parameters"
  for (name, text) in #[
      (`U, "BilinearForm(ℤ, Vec(ℤ, 2), RegularModule(ℤ), b)"),
      (`Uv, "FormedModule(ℤ, Vec(ℤ, 2), RegularModule(ℤ), b)")] do
    let .ok formedSyntax := Parser.runParserCategory (← getEnv) `cas_term text
      | throwError "the dependent formed-object request failed to parse"
    let formed ← withCurrHeartbeats do
      let formed ← (eval {} formedSyntax).run { trace := some trace, bound := bindings }
      let .object handle _ (some _) _ _ := formed
        | throwError "the selected element parameter did not form its registered object"
      unless !handle.hasMVar && !handle.hasLevelMVar && (← isTypeCorrect handle) do
        throwError "the formed-object request lost a selected parameter"
      pure formed
    bindings := (name, formed) :: bindings
  let .ok pairingSyntax := Parser.runParserCategory (← getEnv) `cas_term "formed_pairing(ℤ, Uv)"
    | throwError "the selected formed pairing failed to parse"
  let pairing ← withCurrHeartbeats do
    let pairing ← (eval {} pairingSyntax).run { trace := some trace, bound := bindings }
    let .morphism pairingArrow _ _ _ (some _) := pairing
      | throwError "the registered formed pairing did not retain its endpoints"
    unless !pairingArrow.hasMVar && (← isTypeCorrect pairingArrow) do
      throwError "the registered formed pairing lost its selected form"
    pure pairing
  let .ok applicationSyntax := Parser.runParserCategory (← getEnv) `cas_term
      "bu((2, -1), (3, 4))"
    | throwError "the selected formed pairing application failed to parse"
  let resultObject ← withCurrHeartbeats do
    let .element result resultObject ← (eval {} applicationSyntax).run
        { trace := some trace, bound := (`bu, pairing) :: bindings }
      | throwError "the selected formed pairing did not form an element request"
    unless !result.hasMVar && !result.hasLevelMVar && (← isTypeCorrect result) do
      throwError "the selected formed pairing application lost a dependent parameter"
    pure resultObject
  withCurrHeartbeats do
    let .element subsequent _ ← (toElement (.nat 0) resultObject).run { trace := some trace }
      | throwError "the selected value field did not retain its registered zero operation"
    unless !subsequent.hasMVar && !subsequent.hasLevelMVar && (← isTypeCorrect subsequent) do
      throwError "the subsequent selected-value request lost its complete type"

/- Several independent variables are projections from one registered product stage.
No unary surrogate can satisfy the retained argument count and the common domain check. -/
run_cmd liftTermElabM <| withoutErrToSorry <| withCurrHeartbeats do
  let .ok binding := Parser.runParserCategory (← getEnv) `cas_stmt
      "let f(x, y) := x + y in (ℤ × ℤ) → ℤ"
    | throwError "the multiargument binding failed to parse"
  let some (name, body) ← letBinding? binding
    | throwError "the multiargument binding lost its argument pattern"
  let scope : Language.Scope := ({} : Language.Scope).insert name body
  let .ok statement := Parser.runParserCategory (← getEnv) `cas_stmt
      "assert f(x, y) = f(x, y)"
    | throwError "the independent-variable question failed to parse"
  let trace ← Trace.new
  let .homs left right _ _ _ _ ← (claim scope statement).run { trace := some trace }
    | throwError "the independent-variable question did not retain its arrow comparison"
  for arrow in #[left, right] do
    unless !arrow.hasMVar && !arrow.hasLevelMVar && (← isTypeCorrect arrow) do
      throwError "the independent-variable request retained an incomplete arrow"

/- A body outside its declared codomain must be rejected during interpretation. -/
run_cmd liftTermElabM <| withoutErrToSorry do
  let .ok parsed := Parser.runParserCategory (← getEnv) `cas_term
      "x ↦ x in Fin(3) → Fin(2)"
    | throwError "the codomain-negative probe failed to parse"
  let rejected ← try
      discard <| (eval {} parsed).run {}
      pure false
    catch error =>
      if Exception.stratum? error == some .invalid then pure true else throw error
  unless rejected do throwError "the arrow body escaped its declared codomain"

/- The existing series binder now sees its already formalized, registered topology owner. -/
run_cmd liftTermElabM <| withoutErrToSorry <| withCurrHeartbeats do
  let .ok parsed := Parser.runParserCategory (← getEnv) `cas_term
      "∑_{n ∈ ℕ} n² · t^n in ℤ[[t]]"
    | throwError "the registered series-domain probe failed to parse"
  let trace ← Trace.new
  let .element arrow _ ← (eval {} parsed).run { trace := some trace }
    | throwError "the registered series binder did not form a typed point"
  unless !arrow.hasMVar && !arrow.hasLevelMVar && (← isTypeCorrect arrow) do
    throwError "the registered series binder retained incomplete data"
  unless (← trace.get).toArray.any (fun (_, node) => match node with
      | .binder id .. => id.raw == "bind.sets.power_series_sum"
      | _ => false) do
    throwError "the series question did not consume its actual registered binder"

/- Explicit object contexts and literal defaults use registered constructions and actions. -/
run_cmd liftTermElabM <| withoutErrToSorry do
  for text in #["17 - 29 in ℤ/5", "1 + 2", "1 / 2", "{1, 2}"] do
    withCurrHeartbeats do
      let .ok parsed := Parser.runParserCategory (← getEnv) `cas_term text
        | throwError "literal probe parse"
      let trace ← Trace.new
      let value ← (eval {} parsed).run { trace := some trace }
      for term in value.terms do
        unless !term.hasMVar && !term.hasLevelMVar && (← isTypeCorrect term) do
          throwError "literal request lost its dependent type"
run_cmd liftTermElabM <| withoutErrToSorry <| withCurrHeartbeats do
  let mut scope : Language.Scope := {}
  for text in #[
      "let pb_f := {0 ↦ 0, 1 ↦ 1, 2 ↦ 1} : (Fin(3) in FiniteSets) → (Fin(2) in FiniteSets)",
      "let pb_g := {0 ↦ 1, 1 ↦ 0} : (Fin(2) in FiniteSets) → (Fin(2) in FiniteSets)",
      "let pb_P := pullback(pb_f, pb_g)"] do
    let .ok statement := Parser.runParserCategory (← getEnv) `cas_stmt text
      | throwError "finite binding parse"
    let some (name, body) ← letBinding? statement | throwError "not a binding"
    scope := scope.insert name body
  let .ok parsed := Parser.runParserCategory (← getEnv) `cas_term "pb_P × pb_P in Sets"
    | throwError "finite product parse"
  let trace ← Trace.new
  let cache ← IO.mkRef ({} : Std.HashMap String Value)
  let .object result category _ _ _ ← (eval scope parsed).run
      { trace := some trace, closedTerms := some cache }
    | throwError "explicit category product did not form an object"
  unless category.id == CategoryId.sets && !result.hasMVar && !result.hasLevelMVar &&
      (← isTypeCorrect result) do
    throwError "explicit category product has the wrong complete type"
  unless (← trace.get).toArray.any (fun (_, node) => match node with
      | .retainedRoute source target _ _ _ =>
          source == CategoryId.finiteSets && target == CategoryId.sets
      | _ => false) do
    throwError "the explicit category product lost its finite-set structural action"

/- The full public let-chain is re-read within one ordinary question budget. -/
run_cmd liftTermElabM <| withoutErrToSorry <| withCurrHeartbeats do
  let mut scope : Language.Scope := {}
  for text in #[
      "let b := ((a, b), (c, d)) ↦ a*d + b*c in BilinearMaps(ℤ, Vec(ℤ, 2), Vec(ℤ, 2), RegularModule(ℤ))",
      "let Uv := FormedModule(ℤ, Vec(ℤ, 2), RegularModule(ℤ), b)",
      "let bu := formed_pairing(ℤ, Uv)"] do
    let .ok statement := Parser.runParserCategory (← getEnv) `cas_stmt text
      | throwError "parse binding"
    let some (name, body) ← letBinding? statement | throwError "not a binding"
    scope := scope.insert name body
  let .ok statement := Parser.runParserCategory (← getEnv) `cas_stmt
      "assert implemented bu((2,-1),(3,4))" | throwError "parse question"
  let trace ← Trace.new
  let cache ← IO.mkRef ({} : Std.HashMap String Value)
  let .implemented result ← (claim scope statement).run
      { trace := some trace, closedTerms := some cache }
    | throwError "the let-chain did not form a computational question"
  unless !result.hasMVar && !result.hasLevelMVar && (← isTypeCorrect result) do
    throwError "the let-chain retained an incomplete result"

/- An opaque structured result keeps the complete owner of its registered value field. -/
run_cmd liftTermElabM <| withoutErrToSorry <| withCurrHeartbeats do
  let state ← registryState
  let some category := state.categories.find? (·.id == CategoryId.bilWForm)
    | throwError "missing formed category"
  let some pairing := state.morphisms.find? (·.name == "formed_pairing")
    | throwError "missing pairing"
  let expected ← elabTermAndSynthesize
    (← `(LeanCategories.Modules.Bilinear.Valued.BilWFormCat (CommRingCat.of ℤ))) none
  withLocalDeclD `computedOwner expected fun owner => do
    let trace ← Trace.new
    let selected := Value.object owner category none none none
    let value ← (invariantOf pairing selected).run { trace := some trace }
    let .morphism arrow _ _ _ (some (_, target)) := value
      | throwError "a field-valued morphism lost its endpoints"
    unless !arrow.hasMVar && !arrow.hasLevelMVar && (← isTypeCorrect arrow) do
      throwError "the field-valued morphism is not typed"
    let .object _ _ _ (some (.object fieldObject _ (some (row, _)) _ _)) _ := target
      | throwError "the endpoint lost its selected full field"
    unless row.name == "FormValues" do
      throwError "the endpoint chose a different registered field"
    let some (.object id params) ← trace.node? fieldObject
      | throwError "the endpoint lost its registered object construction"
    unless id == row.id && params.size == 2 && (← isDefEq params[1]! owner) do
      throwError "the field construction lost its complete owner"
    let .element result _ ← withCurrHeartbeats <| (toElement (.nat 0) target).run
      { trace := some trace }
      | throwError "the full field did not retain its registered zero operation"
    unless !result.hasMVar && !result.hasLevelMVar && (← isTypeCorrect result) do
      throwError "the field operation lost its dependent type"

/- The admitted questions retain their selected domains before an operation is chosen.
Named mathematical atoms are not numeral syntax merely because they are not identifiers. -/
run_cmd liftTermElabM <| withoutErrToSorry do
  for (text, expected) in #[
      ("-3 / 2", true), ("(1, -2)", true), ("[1, 2; 3, 4]", true),
      ("ℂ - ℚ", false), ("ℤ/5", false), ("{1, 2}", true)] do
    let .ok parsed := Parser.runParserCategory (← getEnv) `cas_term text
      | throwError "numeric syntax probe failed to parse"
    unless numeric parsed == expected do
      throwError "a named-domain expression was confused with contextual numeral syntax"
  for (bindings, question) in #[
      (#["let M := [1, 2; 3, 4] in Mat₂(ℚ)ˣ"],
        "assert M⁻¹ = [-2, 1; 3/2, -1/2] in Mat₂(ℚ)"),
      (#["let q := x ↦ x² - 2 in ℚ[x]"],
        "assert ((map q to ℂ[x]) in ℂ[x] ∖ 0).roots() ⊆ ℂ - ℚ")] do
    withCurrHeartbeats do
      let mut scope : Language.Scope := {}
      for text in bindings do
        let .ok parsed := Parser.runParserCategory (← getEnv) `cas_stmt text
          | throwError "admitted binding failed to parse"
        let some (name, body) ← letBinding? parsed | throwError "not a binding"
        scope := scope.insert name body
      let .ok parsed := Parser.runParserCategory (← getEnv) `cas_stmt question
        | throwError "admitted question failed to parse"
      let trace ← Trace.new
      let cache ← IO.mkRef ({} : Std.HashMap String Value)
      discard <| (claim scope parsed).run
        { trace := some trace, closedTerms := some cache }

/- Repeated application is checked while each binding is admitted, using the same fresh
closed-reading cache as the production binding path. No cache survives a scope change. -/
run_cmd liftTermElabM <| withoutErrToSorry do
  let .ok implementedCardinality := Parser.runParserCategory (← getEnv) `cas_stmt
      "assert implemented |Fin(3)|"
    | throwError "the implementation question failed to parse"
  let .implemented _ ← (claim {} implementedCardinality).run {}
    | throwError "the implementation keyword was parsed as an ordinary free symbol"
  let mut scope : Language.Scope := {}
  for text in #[
      "let repeated_M := [1, 2, -1; 0, 1, 3; 2, -1, 1] in Mat₃(ℚ)",
      "let repeated_v0 := (2, -1, 3) in ℚ³",
      "let repeated_v1 := repeated_M(repeated_v0)",
      "let repeated_v2 := repeated_M(repeated_v1)",
      "let repeated_v3 := repeated_M(repeated_v2)",
      "assert implemented repeated_v3"] do
    let .ok parsed := Parser.runParserCategory (← getEnv) `cas_stmt text
      | throwError "the repeated application failed to parse"
    withCurrHeartbeats do
      let cache ← IO.mkRef ({} : Std.HashMap String Value)
      discard <| (claim scope parsed).run { closedTerms := some cache }
    if let some (name, body) ← letBinding? parsed then scope := scope.insert name body
