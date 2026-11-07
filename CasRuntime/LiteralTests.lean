module

import CasRuntime.Literal
public meta import Lean.Elab.Command
meta import CasRuntime.Literal

open Lean Meta Elab Term CasCompiler CasRuntime

private def literalSource (term : Term) : TermElabM SourceLayout := do
  let context ← ContextTelescope.capture #[]
  SourceLayout.ofTerm (← context.close (← elabTermAndSynthesize term none))

private def reject (source : SourceLayout) (packet : Json) (expected : String) : MetaM Unit := do
  let failure : Option Exception ← try
    discard <| ScalarLiteral.check source packet
    pure none
  catch error => pure (some error)
  let some failure := failure | throwError "a scalar packet violated its source representation"
  unless (← failure.toMessageData.toString).startsWith expected do throw failure

run_cmd Lean.Elab.Command.liftTermElabM do
  let natural ← literalSource (← `((7 : Nat)))
  let integer ← literalSource (← `((-7 : Int)))
  let rational ← literalSource (← `(((1 : Rat) / 2)))
  let finite ← literalSource (← `((Fin.last 3)))
  let dependent ← literalSource (← `((⟨3, Fin.last 3⟩ : Σ n : Nat, Fin (n + 1))))
  let list ← literalSource (← `(([1, 2] : List Nat)))
  let boolean ← literalSource (← `((true : Bool)))
  let valid : Array (SourceLayout × Json) := #[
    (natural, toJson (0 : Nat)), (integer, toJson (-19 : Int)),
    (rational, .arr #[toJson (-2 : Int), toJson (3 : Nat)]),
    (rational, .arr #[toJson (0 : Int), toJson (1 : Nat)]),
    (finite, toJson (0 : Nat)), (finite, toJson (3 : Nat)),
    (dependent, .arr #[toJson (3 : Nat), toJson (3 : Nat)]),
    (list, .arr #[toJson (3 : Nat), toJson (4 : Nat)]),
    (boolean, Json.mkObj [("ctor", .str "false"), ("args", .arr #[])])]
  for (source, packet) in valid do
    unless (← ScalarLiteral.check source packet) == .checked do
      throwError "the native scalar representation was not checked"
  reject natural (.str "7") "a scalar literal requires a natural JSON number"
  reject integer (.arr #[]) "a scalar literal requires an integer JSON number"
  for packet in #[Json.arr #[toJson (1 : Int), toJson (0 : Nat)],
      .arr #[toJson (2 : Int), toJson (4 : Nat)],
      .arr #[toJson (0 : Int), toJson (2 : Nat)]] do
    reject rational packet "a scalar literal violates its declared representation constraint"
  reject finite (toJson (4 : Nat))
    "a scalar literal violates its declared representation constraint"
  reject dependent (.arr #[toJson (3 : Nat), toJson (4 : Nat)])
    "a scalar literal violates its declared representation constraint"
  reject list (.arr #[.str "3"]) "a scalar literal requires a natural JSON number"
  let function ← literalSource (← `((Nat.succ)))
  let type ← literalSource (← `((Nat)))
  for source in #[function, type] do
    unless (← ScalarLiteral.check source .null) == .notScalar do
      throwError "scalar validation reconstructed a callable or type-valued result"
  let native := CasCatalogue.Backend.ComputationalValue.encode (.opaque "actual-token")
  unless (← ScalarLiteral.check natural native) == .notScalar do
    throwError "scalar validation interpreted a native export as a literal"

run_cmd Lean.Elab.Command.liftTermElabM do
  let inspect (bound point : Expr) : MetaM SourceLayout := do
    let declaration ← getFVarLocalDecl bound
    let context ← ContextTelescope.capture #[
      { id := ⟨"literal-index", 0⟩,
        role := if declaration.isLet then .definition else .parameter, expression := bound },
      { id := ⟨"literal-index", 1⟩, role := .parameter, expression := point }]
    SourceLayout.ofTerm (← context.close point)
  withLetDecl `bound (mkConst ``Nat) (mkNatLit 4) fun bound =>
    withLocalDeclD `point (mkApp (mkConst ``Fin) bound) fun point => do
      let source ← inspect bound point
      unless (← ScalarLiteral.check source (toJson (3 : Nat))) == .checked do
        throwError "scalar validation lost the actual native source let definition"
      reject source (toJson (4 : Nat))
        "a scalar literal violates its declared representation constraint"
  withLocalDeclD `bound (mkConst ``Nat) fun bound =>
    withLocalDeclD `point (mkApp (mkConst ``Fin) bound) fun point => do
      let source ← inspect bound point
      unless (← ScalarLiteral.check source (toJson (3 : Nat))) == .notScalar do
        throwError "scalar validation specialized a rigid source index from returned data"

run_cmd Lean.Elab.Command.liftTermElabM do
  let source ← literalSource (← `(((1 : Rat) / 2)))
  let original ← getEnv
  try
    let info ← getConstInfo ``Classical.propDecidable
    let name := `ScalarLiteralUnsafeDecision
    addDecl <| .defnDecl {
      name, levelParams := info.levelParams, type := info.type
      value := mkConst info.name (info.levelParams.map Level.param)
      hints := .abbrev, safety := .unsafe }
    setReducibilityStatus name .instanceReducible
    addInstance name .local 100000
    resetSynthInstanceCache
    reject source (.arr #[toJson (1 : Int), toJson (3 : Nat)])
      "source declaration ScalarLiteralUnsafeDecision is unsafe"
  finally
    setEnv original
    resetSynthInstanceCache
