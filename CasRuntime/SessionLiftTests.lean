module

import CasRuntime.Session
import LeanCategories.Catalogue
import LeanCategories.Catalogue.Semantics.Modules.Bilinear.Valued.DegeneratePlaneLifts
public meta import Lean.Elab.Command
meta import CasRuntime.Session
meta import LeanCategories.Catalogue
meta import LeanCategories.Catalogue.Semantics.Modules.Bilinear.Valued.DegeneratePlaneLifts

open Lean Elab Command Term CasRuntime

/- RX-LIFT's first selected lift (tests/acceptance/proposals/independent-extension-reconstruction-
20261024/completion/rx-lift-prescribed-stages.cas) through the public path with no leaf. The lift
is a record of delayed fields: defining it dispatches nothing, and its fields are then projected
from that same retained record. A computation that needs a leaf is a gap, and so is a
projection whose dependent type needs such a value; reading holds. Functional work may use the
heartbeats it needs (constitution C21). -/
set_option maxHeartbeats 2000000 in
run_cmd liftTermElabM do
  let environment ← getEnv
  try
    let mut session ← KernelSession.start none
    try
      for (text, kind) in #[
          ("let Q := ℚ in CommutativeRings", "holds"),
          ("let Qring := view Q along «fun.commutative_rings.ring»()", "gap"),
          ("let scalarModule := RegularModule(Qring)", "gap"),
          ("let X := DegeneratePlane()", "holds"),
          ("let sourceModule := view X along «fun.bilin_module.forget»(ℚ, ℚ)", "gap"),
          ("let i0(t) := (2*t, -2*t) in scalarModule → sourceModule", "holds"),
          ("let first := lift(X) along «lift.bilin_module.restrict»(ℚ, ℚ) with i0 using proof(CasCatalogue.Modules.Bilinear.Valued.DegeneratePlaneLifts.kernelInclusion_mono)", "holds"),
          -- The lift's fields depend on the module scalarModule, whose computation has no
          -- leaf here: projecting them is that gap.
          ("let X1 := first.obj()", "gap"),
          ("let i1 := first.hom()", "gap")] do
        let statement ← match Parser.runParserCategory (← getEnv) `cas_stmt text with
          | .ok statement => pure statement
          | .error error => throwError "the statement did not parse: {error}"
        let run ← withoutErrToSorry <| session.run ⟨statement⟩
        unless run.outcome.kind == kind do
          throwError "`{text}` is {run.outcome.kind} ({run.outcome.detail}), not {kind}"
        session := run.session
    finally liftM (m := IO) session.close
  finally setEnv environment
