module

import CasCompiler.Layout
public meta import Lean.Elab.Command
meta import CasCompiler.Layout

open Lean Meta CasCompiler

-- A source function may return a projection before its record argument is supplied.
-- Splitting and reapplying the projection's existing parameter prefix is not progress.
-- The heartbeat bound belongs only to this regression: the old traversal must fail in
-- finite time. Production routing receives no test-specific cutoff.
set_option maxHeartbeats 20000 in
run_cmd Lean.Elab.Command.liftTermElabM do
  let context ← ContextTelescope.capture #[]
  let check (label : String) (declaration : Name) (partialProjection : Expr) :
      MetaM Unit := do
    let partialProjection := partialProjection.consumeMData
    let some info := (← getEnv).getProjectionFnInfo? declaration
      | throwError m!"{label}: the control is not a registered native projection"
    unless partialProjection.getAppFn.constName? == some declaration &&
        partialProjection.getAppArgs.size == info.numParams do
      throwError m!"{label}: the control must omit exactly its native record argument"
    let .none ← SourceProjection.ofExpr? partialProjection
      | throwError m!"{label}: an unsaturated control was already a record projection"
    let source ← withLocalDeclD `_seed (mkConst ``Nat) fun seed =>
      mkLambdaFVars #[seed] partialProjection (usedOnly := false) (usedLetOnly := false)
    let role ← SourceLayout.ofTerm (← context.close source)
    let (_, first) ← ApplicationLayout.ofSource role context
      #[← context.close (mkNatLit 7)]
    unless first.arguments.size == 1 && first.result.kind == .function do
      throwError m!"{label}: the first application did not retain its partial callable"

    -- No actual record has been supplied: there is no selected input occurrence.
    -- This call recreated the same partial projection indefinitely before the repair.
    let .none ← first.inputProjectionThrough #[] #[]
      | throwError m!"{label}: an unapplied projection acquired a fixed input route"

    -- A later genuine application supplies the record as formal slot 1. The unused
    -- seed remains slot 0; neither the projection's type parameters nor a reconstructed
    -- callable may replace the selected record or its exact native field path.
    let some (.projection route) ← first.inputProjectionThrough #[(#[], 1)] #[]
      | throwError m!"{label}: a saturated later application lost its fixed input route"
    match route.target with
    | .argument 1 => pure ()
    | _ => throwError m!"{label}: the route did not select the later record argument"
    unless route.path == #[declaration] do
      throwError m!"{label}: the route changed its native projection path"

  -- The actual RX08 recursion repeatedly exposed the bare Subtype.val head after
  -- decomposing its already supplied type and predicate parameters.
  let subtype ← Elab.Term.elabTermAndSynthesize
    (← `(@Subtype.val Nat (fun _ : Nat => True))) none
  check "partial Subtype.val" ``Subtype.val subtype

  -- Keep the fix generic across native record projections, including ordinary products.
  let product ← Elab.Term.elabTermAndSynthesize (← `(@Prod.fst Nat Nat)) none
  check "partial Prod.fst" ``Prod.fst product
