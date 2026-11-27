module

import CasRuntime.Session
import CasCompiler.SourceTestSupport
import LeanCategories.Catalogue.Semantics.Algebra.NamedRings
import LeanCategories.Catalogue.Semantics.Algebra.NamedCommutativeRings
import LeanCategories.Catalogue.Semantics.Algebra.Polynomials
import LeanCategories.Catalogue.Semantics.Foundation.FiniteObjects
import LeanCategories.Catalogue.Semantics.Foundation.FiniteSubsetLiterals
import LeanCategories.Catalogue.Semantics.Foundation.Finiteness
import LeanCategories.Catalogue.Semantics.Foundation.Cardinality
import LeanCategories.Catalogue.Semantics.Limits.Registration
import LeanCategories.Catalogue.Semantics.Modules.Bilinear.Valued.Lattices
import LeanCategories.Catalogue.Semantics.Algebra.LinearAlgebra
import LeanCategories.Catalogue.Semantics.Algebra.NumberSystems
import LeanCategories.Catalogue.Semantics.Algebra.Series
public meta import Lean.Elab.Command
meta import CasRuntime.Session
meta import CasCompiler.SourceTestSupport
meta import LeanCategories.Catalogue.Semantics.Algebra.NamedRings
meta import LeanCategories.Catalogue.Semantics.Algebra.NamedCommutativeRings
meta import LeanCategories.Catalogue.Semantics.Algebra.Polynomials
meta import LeanCategories.Catalogue.Semantics.Foundation.FiniteObjects
meta import LeanCategories.Catalogue.Semantics.Foundation.FiniteSubsetLiterals
meta import LeanCategories.Catalogue.Semantics.Foundation.Finiteness
meta import LeanCategories.Catalogue.Semantics.Foundation.Cardinality
meta import LeanCategories.Catalogue.Semantics.Limits.Registration
meta import LeanCategories.Catalogue.Semantics.Modules.Bilinear.Valued.Lattices
meta import LeanCategories.Catalogue.Semantics.Algebra.LinearAlgebra
meta import LeanCategories.Catalogue.Semantics.Algebra.NumberSystems
meta import LeanCategories.Catalogue.Semantics.Algebra.Series

open Lean Meta Elab Command Term CasRuntime CasCompiler





run_cmd liftTermElabM do
  let environment ← getEnv
  try
    let contract ← liftM (m := IO) <| CasCatalogue.Backend.packageDir
      CasCatalogue.Backend.contractPackage
    let root ← liftM (m := IO) IO.currentDir
    let python := (← liftM (m := IO) <| IO.FS.realPath contract) / ".venv/bin/python"
    liftM (m := IO) <| IO.FS.createDirAll (root / ".tmp")
    let log := root / ".tmp" / "kernel-leg-peer.log"
    liftM (m := IO) <| IO.FS.writeFile log ""
    let operation := "fun.bil_wform.base_change#map"
    let manifest := Json.mkObj [
      ("backends", .arr #[Json.mkObj [("name", "peer"), ("command", python.toString),
        ("args", .arr #[toJson (root / "scripts/probes/kernel_lift_peer.py").toString,
          toJson log.toString, toJson operation])]]),
      ("registrations", .arr #[Json.mkObj [("operation", toJson operation),
        ("input", "fun.bil_wform.base_change#input"), ("backend", "peer")]])]
    let path := root / ".tmp" / "kernel-leg-leaves.json"
    liftM (m := IO) <| IO.FS.writeFile path manifest.compress
    let mut session ← KernelSession.start (some path)
    let (published, occurrence, observation, logBeforeClose) ← try
      for text in #["let C := cokernel(to_dual(1))",
          "let r := map C.leg(1) along «fun.bil_wform.base_change»(ℤ, ℚ)"] do
        let statement ← match Parser.runParserCategory (← getEnv) `cas_stmt text with
          | .ok statement => pure statement
          | .error error => throwError "the statement did not parse: {error}"
        let run ← withoutErrToSorry <| session.run ⟨statement⟩
        unless run.outcome.kind == "holds" do
          throwError "`{text}` is {run.outcome.kind} ({run.outcome.detail}), not holds"
        session := run.session
      let requests := ((← liftM (m := IO) <| IO.FS.readFile log).splitOn "\n").filter (!·.isEmpty)
      let some line := requests.head? | throwError "the base change's map action was not dispatched"
      let .ok request := Json.parse line | throwError "the peer log is malformed: {line}"
      let .ok arguments := (request.getObjValD "context").getObjValAs? (Array Json) "arguments"
        | throwError "the map action has no arguments: {line}"
      let leg := arguments.back?.getD .null
      unless (leg.getObjValAs? String "ctor").toOption == some "colim.bil_w_form.cokernel#leg" &&
          ((leg.getObjValD "args").getArr?.toOption.bind (·.back?)) == some (toJson (1 : Nat)) do
        throwError "the map action did not receive C's leg 1: {line}"
      let #[selected, result] ← CasCompiler.SourceTest.authoredEntries
          session.source.context session.source.selections
        | throwError "the public cokernel and map definitions lost their two authored bindings"
      let some binding := session.value? result.id
        | throwError "the public map definition lost its actual computed value"
      let published ← SessionSnapshot.current
      let some node := published.graph.find binding.value
        | throwError "the public map result is absent from the committed graph"
      let occurrence := binding.applications.back?.map (·.association.occurrence)
        |>.getD node.origin.occurrence
      let some receipt := published.receipt occurrence
        | throwError "the public map result lost its committed request"
      let some source := receipt.association.request.observation.sourceSnapshot
        | throwError "the public source handoff omitted its original source snapshot"
      let .ok context := source.getObjValAs? (Array Json) "context"
        | throwError "the public source snapshot lost its original context"
      let .ok categories := source.getObjValAs? (Array Json) "categories"
        | throwError "the public source snapshot lost its selected categories"
      unless selected.userName == `C && result.userName == `r &&
          context.map (·.getObjValD "id") ==
            (session.source.context.entries.extract 0 (session.source.context.entries.size - 1)).map
              (fun entry => CasCompiler.ContextSnapshot.bindingJson entry.id) &&
          session.source.context.entries.back?.map (·.id) == some result.id &&
          (source.getObjValD "resultBinding").getObjValD "id" ==
            CasCompiler.ContextSnapshot.bindingJson result.id do
        throwError "the source snapshot changed the original context or result binding"
      let some selection := (session.source.categoryFor selected.id).bind (·.limit)
        | throwError "the public cokernel binding lost its selected presentation"
      let some selectedIndex := context.findIdx? fun entry =>
          entry.getObjValD "id" == CasCompiler.ContextSnapshot.bindingJson selected.id
        | throwError "the source snapshot omitted the original cokernel binding identity"
      let some category := categories[selectedIndex]?
        | throwError "the source snapshot omitted the cokernel's selected category"
      let limit := category.getObjValD "limit"
      unless limit.getObjValD "construction" ==
          CasTools.NativeExpression.nameJson selection.construction do
        throwError "the source snapshot changed the original construction selection"
      let .ok nodes := CasTools.NativeExpression.decodeNodes
          (source.getObjValD "nativeExpressions")
        | throwError "the source snapshot lost its exact native expression graph"
      for (name, original) in #[("cone", selection.cone),
          ("presentation", selection.presentation), ("diagram", selection.diagram)] do
        let retained := limit.getObjValD name
        let .ok expression := retained.getObjValAs? Nat "expression"
          | throwError "the source snapshot lost the selected {name}"
        let .ok type := retained.getObjValAs? Nat "type"
          | throwError "the source snapshot lost the selected {name}'s type"
        unless nodes[expression]? == some original.expression &&
            nodes[type]? == some original.type do
          throwError "the source snapshot changed the actual selected {name}"
      unless (limit.getObjValD "interface").getObjVal? "dataConstructor" |>.isOk do
        throwError "the source snapshot omitted the selected native data interface"
      let .ok typed := source.getObjValAs? (Array Json) "sessionSelections"
        | throwError "the source snapshot omitted its complete typed selection table"
      unless typed.size == session.source.selections.size && !typed.isEmpty do
        throwError "the source snapshot dropped an original typed selection"
      for (id, original) in session.source.selections.toArray do
        let #[retained] := typed.filter fun row =>
            row.getObjValD "binding" == CasCompiler.ContextSnapshot.bindingJson id
          | throwError "the source snapshot lost or repeated an exact selection binding"
        let selected := retained.getObjValD "selection"
        unless selected.getObjValD "formalBindings" ==
              toJson (original.formalBindings.map CasCompiler.ContextSnapshot.bindingJson) &&
            selected.getObjValD "reference" == toJson original.reference do
          throwError "the source snapshot changed the original full row or formal source positions"
        let value := selected.getObjValD "value"
        let .ok expression := value.getObjValAs? Nat "expression"
          | throwError "the typed source selection omitted its original native expression"
        let .ok type := value.getObjValAs? Nat "type"
          | throwError "the typed source selection omitted its complete native type"
        let .ok valueContext := value.getObjValAs? (Array Json) "context"
          | throwError "the typed source selection omitted its complete source telescope"
        unless nodes[expression]? == some original.value.expression &&
            nodes[type]? == some original.value.type &&
            valueContext.map (·.getObjValD "id") ==
              original.value.context.entries.map
                (fun entry => CasCompiler.ContextSnapshot.bindingJson entry.id) do
          throwError "the typed source selection changed its expression, type or original telescope"
        if let some application := original.application then
          let retained := selected.getObjValD "application"
          unless retained.getObjValD "family" == toJson application.family &&
              retained.getObjValD "universes" == toJson application.universes do
            throwError "the source snapshot discarded a complete original family or universe"

      pure (published, occurrence, receipt.association.request.observation.toJson,
        ← liftM (m := IO) <| IO.FS.readFile log)
    finally liftM (m := IO) session.close
    let some retained := published.receipt occurrence
      | throwError "provider shutdown hid the public result's inert observation"
    unless retained.association.request.observation.toJson == observation &&
        (← liftM (m := IO) <| IO.FS.readFile log) == logBeforeClose do
      throwError "reading the committed observation changed it or dispatched another request"
  finally setEnv environment




run_cmd liftTermElabM do
  let environment ← getEnv
  try
    let root ← IO.currentDir
    IO.FS.createDirAll (root / ".tmp")
    let path := root / ".tmp/kernel-equal-apex-empty-leaves.json"
    IO.FS.writeFile path
      (Json.mkObj [("backends", .arr #[]), ("registrations", .arr #[])]).compress
    let initial ← KernelSession.start (some path) (computationOnly := true)
    try
      let mut session := initial
      let mut originals : Array (BindingId × ValueBinding) := #[]
      for (name, text) in #[
          (`X, "let X := RegularModule(ℤ)"),
          (`Y, "let Y := RegularModule(ℤ)"),
          (`first, "let first := X × Y"),
          (`second, "let second := X × Y"),
          (`firstLeg, "let firstLeg := first.leg(0)"),
          (`secondLeg, "let secondLeg := second.leg(0)"),
          (`alias, "let «alias» := first"),
          (`aliasLeg, "let aliasLeg := «alias».leg(0)"),
          (`laterLeg, "let laterLeg := first.leg(0)")] do
        let .ok parsed := Parser.runParserCategory (← getEnv) `cas_stmt text
          | throwError "the public equal-apex statement did not parse: {text}"
        let run ← withoutErrToSorry <| session.run ⟨parsed⟩
        unless run.outcome.kind == "holds" && run.attempted && run.published do
          throwError "the public equal-apex statement did not commit: {text}: {run.outcome.detail}"
        session := run.session
        let some entry := (← SourceTest.authoredEntries
            session.source.context session.source.selections).back?
          | throwError "the public equal-apex statement lost its authored binding"
        unless entry.userName == name do
          throwError "the public equal-apex statement changed its result binding"
        let some actual := session.value? entry.id
          | throwError "the public equal-apex statement lost its actual result"
        originals := originals.push (entry.id, actual)
      let #[x, y, first, second, firstLeg, secondLeg, aliasValue, aliasLeg, laterLeg] := originals
        | throwError "the public equal-apex control changed its original statement count"
      unless first.1 != second.1 && first.2.value != second.2.value &&
          retainsReference first.2 aliasValue.2 do
        throwError "two public limit definitions or their alias lost their original occurrences"
      let graph := (← SessionSnapshot.current).graph
      let empty ← ContextTelescope.capture #[]
      withBindingContext graph empty {} first.2 fun context bound => do
        withBindingContext graph context bound second.2 fun context bound => do
          let some firstSelected ← first.2.role.selected? context
            | throwError "the first public limit lost its complete typed selection"
          let some secondSelected ← second.2.role.selected? context
            | throwError "the second public limit lost its complete typed selection"
          let some firstLimit := firstSelected.limit
            | throwError "the first public limit lost its original cone"
          let some secondLimit := secondSelected.limit
            | throwError "the second public limit lost its original cone"
          let some firstReference := firstSelected.reference
            | throwError "the first public limit lost its original full row"
          let some secondReference := secondSelected.reference
            | throwError "the second public limit lost its original full row"
          unless firstReference.exactlyMatches secondReference &&
              firstLimit.source.construction != secondLimit.source.construction do
            throwError "the equal-apex limits changed their full family or shared one construction"
          unless ← context.withOriginalSources #[firstLimit.receiver, secondLimit.receiver]
              (fun values => isDefEq values[0]! values[1]!) do
            throwError "the two original selected limits no longer have the same native apex"
          for (leg, owner, construction, reference) in #[
              (firstLeg.2, first.2, firstLimit.source.construction, firstReference),
              (secondLeg.2, second.2, secondLimit.source.construction, secondReference),
              (aliasLeg.2, first.2, firstLimit.source.construction, firstReference),
              (laterLeg.2, first.2, firstLimit.source.construction, firstReference)] do
            withBindingContext graph context bound leg fun context bound => do
              let some selected ← leg.role.selected? context
                | throwError "a later public leg lost its complete typed selection"
              let some original := selected.leg
                | throwError "a later public leg lost its original cone component"
              let some retainedReference := selected.reference
                | throwError "a later public leg lost its complete original limit row"
              unless original.construction.source.construction == construction &&
                  reference.exactlyMatches retainedReference do
                throwError "a later public leg crossed an equal-apex construction boundary"
              let some (binding, suffix) ← boundProjection? context bound
                  original.construction.receiver
                | throwError "a later public leg lost its original bound receiver"
              let some receiver := bound[binding]?
                | throwError "a later public leg names an unavailable receiver identity"
              unless suffix.isEmpty && retainsReference owner receiver do
                throwError "a later public leg substituted the other equal-apex receiver"
      unless (← session.kernel.dispatches.get).isEmpty do
        throwError "forming selected limits or retaining their legs dispatched an implementation"



      unless x.1 != y.1 && x.2.value != y.2.value do
        throwError "the ordered-cone control lost its distinct original module inputs"
      let some firstSource := session.source.selections[first.1]?
        | throwError "the first public limit lost its original complete reader selection"
      let mut reversedSource : Option (SourceSelection ClosedTerm) := none
      let mut ordered : Array (BindingId × ValueBinding) := #[]
      for (name, text) in #[
          (`reversed, "let reversed := Y × X"),
          (`reversedLeg, "let reversedLeg := reversed.leg(0)"),
          (`reversedOtherLeg, "let reversedOtherLeg := reversed.leg(1)"),
          (`reversedAlias, "let reversedAlias := reversed"),
          (`reversedAliasLeg, "let reversedAliasLeg := reversedAlias.leg(0)")] do
        let .ok parsed := Parser.runParserCategory (← getEnv) `cas_stmt text
          | throwError "the public ordered-cone statement did not parse: {text}"
        let run ← withoutErrToSorry <| session.run ⟨parsed⟩
        unless run.outcome.kind == "holds" && run.attempted && run.published do
          throwError "the public ordered-cone statement did not commit: {text}: {run.outcome.detail}"
        session := run.session
        let some entry := (← SourceTest.authoredEntries
            session.source.context session.source.selections).back?
          | throwError "the public ordered-cone statement lost its authored binding"
        unless entry.userName == name do
          throwError "the public ordered-cone statement changed its original result binding"
        let some actual := session.value? entry.id
          | throwError "the public ordered-cone statement lost its actual result"
        ordered := ordered.push (entry.id, actual)
        if name == `reversed then
          let some selected := session.source.selections[entry.id]?
            | throwError "the reversed public limit lost its original complete reader selection"
          reversedSource := some selected
      let #[reversed, reversedLeg, reversedOtherLeg, reversedAlias, reversedAliasLeg] := ordered
        | throwError "the public ordered-cone control changed its original statement count"
      let some originalReversed := reversedSource
        | throwError "the public ordered-cone control lost its original reversed selection"
      unless first.2.value != reversed.2.value && retainsReference reversed.2 reversedAlias.2 do
        throwError "the reversed cone or its alias lost its original actual occurrence"
      session.source.context.withOpen fun bindings => do
        let context ← ContextTelescope.capture bindings
        let selections ← session.source.selections.inContext context
        let firstSource ← firstSource.mapM (fun source => source.inContext context)
        let reversedSource ← originalReversed.mapM (fun source => source.inContext context)
        let some firstLimit := firstSource.limit
          | throwError "the first original reader selection lost its full cone"
        let some reversedLimit := reversedSource.limit
          | throwError "the reversed original reader selection lost its full cone"
        unless ← context.withOriginalSources #[firstLimit.receiver, reversedLimit.receiver]
            (fun values => isDefEq values[0]! values[1]!) do
          throwError "the distinct ordered source cones no longer share their native apex"
        let exchangedOwner ← NativeLimitSelection.ofSource
          { reversedLimit.source with construction := firstLimit.source.construction }
          firstLimit.receiver
        if firstSource.exactlyMatches Expr.equal { firstSource with limit := some exchangedOwner } then
          throwError "the complete source comparison accepted the other ordered construction"


        let exchanged ← NativeLimitSelection.ofSource
          { firstLimit.source with
            cone := reversedLimit.source.cone
            presentation := reversedLimit.source.presentation
            diagram := reversedLimit.source.diagram
            interface := reversedLimit.source.interface }
          firstLimit.receiver
        if firstSource.exactlyMatches Expr.equal { firstSource with limit := some exchanged } then
          throwError "the complete cone comparison ignored exchanged diagram or interface data"
        for (leg, expected) in #[(firstLeg, firstSource), (aliasLeg, firstSource),
            (laterLeg, firstSource), (reversedLeg, reversedSource),
            (reversedOtherLeg, reversedSource), (reversedAliasLeg, reversedSource)] do
          let some selected := selections[leg.1]?
            | throwError "a public ordered leg lost its original complete reader selection"
          let some original := selected.leg
            | throwError "a public ordered leg lost its original full construction"
          let some owner := selections.findAt? context original.construction.receiver
            | throwError "a public ordered leg lost its exact original source owner binding"
          unless expected.exactlyMatches Expr.equal owner do
            throwError "a public ordered leg changed its original complete selected owner"
          let some expectedLimit := expected.limit
            | throwError "an original ordered-cone selection lost its full native interface"
          let actual ← NativeLimitSelection.ofSource original.construction.source expectedLimit.receiver
          let retained := { expected with
            reference := selected.reference
            limitFamily := selected.limitFamily
            limit := some actual }
          unless expected.exactlyMatches Expr.equal retained do
            throwError "a public ordered leg changed its original cone, diagram, interface or family"
      let graph := (← SessionSnapshot.current).graph
      let empty ← ContextTelescope.capture #[]
      for (leg, owner) in #[(reversedLeg.2, reversed.2),
          (reversedOtherLeg.2, reversed.2), (reversedAliasLeg.2, reversed.2)] do
        withBindingContext graph empty {} leg fun context bound => do
          let some selected ← leg.role.selected? context
            | throwError "an ordered public leg lost its actual selected source role"
          let some original := selected.leg
            | throwError "an ordered public leg lost its actual original construction"
          let some (binding, suffix) ← boundProjection? context bound original.construction.receiver
            | throwError "an ordered public leg lost its actual source receiver"
          let some receiver := bound[binding]?
            | throwError "an ordered public leg names an unavailable actual receiver"
          unless suffix.isEmpty && retainsReference owner receiver &&
              receiver.value != first.2.value do
            throwError "an ordered public leg substituted the other same-apex construction"
      unless (← session.kernel.dispatches.get).isEmpty do
        throwError "retaining ordered source cones or their legs dispatched an implementation"
    finally initial.close
  finally setEnv environment
