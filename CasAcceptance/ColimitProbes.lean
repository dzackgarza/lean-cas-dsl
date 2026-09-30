/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CasAcceptance.Standard
public import CasCatalogue.Semantic
public meta import CasAcceptance.Standard
public meta import CasCatalogue.Semantic

@[expose] public section

/-!
# Acceptance for `cc-colimits` (CC-UNIV)

The registered coproduct `colim.sets.coproduct` and cokernel `colim.bil_w_form.cokernel` are
colimit presentations of their categories, and a colimit presentation is not a limit: declaring
the coproduct a limit is rejected. The semantic reading forms a coproduct as the registered
presentation at the diagram, identified with the standard form (`colimitCoconeOfIso`,
`diagramIsoPair`), and records it; what its apex's cardinality is, is a statement of the language
(`|Fin(2) ⊔ Fin(3)| = 5`), decided through the admitted registrations.
-/

open CategoryTheory Limits Lean Meta Elab Term Command

namespace CasCatalogue.ColimitProbes

run_cmd liftTermElabM do
  let state ← registryState
  for (id, category) in [("colim.sets.coproduct", "cat.sets"),
      ("colim.bil_w_form.cokernel", "cat.bil_wform")] do
    let some l := state.limits.find? (·.id.raw == id) | throwError "{id} is not registered"
    unless l.colimit && l.category.raw == category do throwError "{id} is misregistered"
  -- The coproduct resolves in sets with no lift.
  match state.resolveLimit CategoryId.sets "coproduct" (colimit := true) with
  | .ok r => unless r == { limit := ⟨"colim.sets.coproduct"⟩ } do
      throwError "coproducts of sets resolved to {repr r}"
  | .error e => throwError e
  -- A colimit presentation is not a limit: declaring the coproduct a limit is rejected.
  let some l := state.limits.find? (·.id.raw == "colim.sets.coproduct") | unreachable!
  let asLimit : LimitEntry := { l with id := ⟨"lim.probe.coproduct"⟩, colimit := false }
  if (← try validateRegistryEntryDeclaration (.limit asLimit); pure true
      catch _ => pure false) then
    throwError "a colimit cocone family was accepted as a limit"
  -- The semantic reading forms the coproduct of two named sets, and records it as the colimit.
  let some fin := state.objects.find? (·.id.raw == "obj.sets.fin")
    | throwError "obj.sets.fin is not registered"
  let trace ← (Trace.new : IO _)
  let two ← Semantic.object fin #[Syntax.mkNumLit "2"] (some trace)
  let three ← Semantic.object fin #[Syntax.mkNumLit "3"] (some trace)
  let diagram ← instantiateMVars (← elabTermAndSynthesize
    (← `(CategoryTheory.Limits.pair $(← exprToSyntax two) $(← exprToSyntax three))) none)
  let cocone ← Semantic.limit true "coproduct" diagram "cat.sets" (some trace)
  unless (← whnfR (← inferType cocone)).isAppOf ``CategoryTheory.Limits.ColimitCocone do
    throwError "the coproduct is not a colimit cocone"
  let some (.limit id _) ← (trace.node? cocone : IO _)
    | throwError "the coproduct is not recorded as a registered colimit"
  unless id.raw == "colim.sets.coproduct" do throwError "recorded as {id.raw}"

end CasCatalogue.ColimitProbes
