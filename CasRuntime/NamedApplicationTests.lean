module

import CasRuntime.Kernel
import CasCompiler.Read
import LeanCategories.Catalogue
public meta import Lean.Elab.Command
meta import CasRuntime.Kernel
meta import CasCompiler.Read
meta import LeanCategories.Catalogue

namespace CasRuntime.NamedApplicationTests

open Lean Meta Elab Term CasCompiler CasCatalogue

private def sourceTerm (text : String) : TermElabM (TSyntax `cas_term) := do
  let .ok parsed := Parser.runParserCategory (← getEnv) `cas_term text
    | throwError "the named-application source control did not parse"
  return ⟨parsed⟩

private def nativeTerm (text : String) : TermElabM Term := do
  let .ok parsed := Parser.runParserCategory (← getEnv) `term text
    | throwError "the named-application native context did not parse"
  return ⟨parsed⟩

private def descriptor (address : String) (arguments : Array Json) : Json :=
  Json.mkObj [("ctor", toJson address), ("args", .arr arguments)]

private def withNamedSource (term : SourceTerm)
    (action : OpenContext → SourceSelectionScope Expr → Expr → MetaM α) : MetaM α :=
  term.source.withOpen fun bindings expression => do
    let context ← ContextTelescope.capture bindings
    action context (← term.selections.inContext context) expression

private def namedSelection (context : OpenContext) (selections : SourceSelectionScope Expr)
    (expression : Expr) : MetaM (SourceSelection Expr) := do
  let some selected := selections.findAt? context expression.getAppFn
    | throwError "the named source lost its exact original typed binding"
  selected.specialize expression.getAppArgs

private def lower (kernel : Kernel) (transaction : CellTransaction) (term : SourceTerm)
    (bound : Std.HashMap BindingId ValueBinding := {}) : MetaM ValueBinding :=
  withNamedSource term fun context selections expression =>
    kernel.run transaction context bound expression (selections := selections)

private def packet (transaction : CellTransaction) (value : ValueBinding) : MetaM Json := do
  let .ok (some packet) := (← transaction.view).packet? value
    | throwError "the named application did not retain its descriptor and actual arguments"
  return packet




run_cmd Lean.Elab.Command.liftTermElabM do
  let environment ← getEnv
  let owners ← OwnerRegistry.new
  let kernel ← Kernel.load owners none none 1000
  discard <| SessionSnapshot.initialize owners
  let transaction ← CellTransaction.begin kernel.ledger
  try
    let empty ← SourceSession.empty owners.identities
    let source ← empty.assume `X (← nativeTerm "Type")
    let source ← source.assume `Y (← nativeTerm "Type")
    let source ← source.assume `Z (← nativeTerm "Type")
    let #[x, y, z] := source.context.entries
      | throwError "the nested presentation lost its three original source parameters"


    let inputs := #[
      descriptor "finiteData" #[descriptor "obj.sets.fin" #[toJson (2 : Nat)],
        toJson (#[0, 1] : Array Nat)],
      descriptor "finiteData" #[descriptor "obj.sets.fin" #[toJson (3 : Nat)],
        toJson (#[0, 1, 2] : Array Nat)],
      descriptor "finiteData" #[descriptor "obj.sets.fin" #[toJson (4 : Nat)],
        toJson (#[0, 1, 2, 3] : Array Nat)]]
    let #[xPacket, yPacket, zPacket] := inputs
      | throwError "the nested presentation lost its three supplied input packets"
    let bound ← source.context.withOpen fun bindings => do
      let context ← ContextTelescope.capture bindings
      let environment ← RuntimeEnvironment.capture owners.worker context #[]
      let program ← owners.identities.fresh .program
      let mut bound : Std.HashMap BindingId ValueBinding := {}
      for binding in bindings, input in inputs do
        let role ← SourceLayout.ofTerm (← context.close binding.expression)
        let origin ← environment.origin program (← kernel.ledger.allocate) role
        let value ← transaction.stage origin (.portable input.compress.toUTF8)
        bound := bound.insert binding.id value
      return bound
    let some xValue := bound[x.id]?
      | throwError "the first original parameter lost its supplied value"
    let some yValue := bound[y.id]?
      | throwError "the second original parameter lost its supplied value"
    let some zValue := bound[z.id]?
      | throwError "the last original parameter lost its supplied value"
    unless xValue.value != yValue.value && xValue.value != zValue.value &&
        yValue.value != zValue.value do
      throwError "the nested presentation merged distinct supplied parameter occurrences"
    for (text, declaration, address) in #[
        ("(X × Y) × Z", ``CasCatalogue.Limits.Registration.setsProduct, "lim.sets.product"),
        ("(X ⊔ Y) ⊔ Z", ``CasCatalogue.Limits.Registration.setsCoproduct, "colim.sets.coproduct")] do
      let object ← source.read (← sourceTerm text)
      let some category := object.category
        | throwError "the nested presentation lost its selected category"
      let some selection := category.limit
        | throwError "the nested presentation lost its selected universal construction"
      unless selection.row == address && selection.declaration == declaration &&
          selection.category.syntacticEq (.atom CategoryId.sets) do
        throwError "the nested presentation changed its actual registered selection"
      withNamedSource object fun context selections value => do
        let selected ← namedSelection context selections value
        let some application ← sourceApplication? declaration selected
          | throwError "the nested presentation lost its exact original application"
        let some originalZ := context.bindings.find? (·.id == z.id)
          | throwError "the nested presentation lost the original Z"
        unless application.getAppArgs.back? == some originalZ.expression do
          throwError "the outer presentation took its arguments from the nested presentation"
        let some construction := selected.limit
          | throwError "the selected cone lost its exact original presentation"
        unless construction.source.interface.presentation.equal application do
          throwError "the selected apex and cone retained different original applications"
        checkWithKernel value


        selections.withBinding owners.identities context
            { selected with originalApplication := none } fun context selections missing => do
          checkWithKernel missing
          let rejected : Option Exception ← try
            discard <| kernel.run transaction context bound missing (selections := selections)
            pure none
          catch error => pure (some error)
          let some rejected := rejected
            | throwError "lowering recovered a lost named application from a nested declaration"
          unless (← rejected.toMessageData.toString) ==
              "the named element lost its explicitly retained original application" do
            throw rejected
      let expected := descriptor address #[descriptor address #[xPacket, yPacket], zPacket]
      unless (← packet transaction (← lower kernel transaction object bound)) == expected do
        throwError "the nested construction's public descriptor changed its actual outer arguments"

      let source ← source.defineTerm `K object
      let source ← source.assume `X (← nativeTerm "Type")
      let retained ← source.read (← sourceTerm "K")
      unless (← packet transaction (← lower kernel transaction retained bound)) == expected do
        throwError "a retained construction changed its original application after shadowing"
      let leg ← source.read (← sourceTerm "K.leg(0)")
      withNamedSource leg fun context selections value => do
        let selected ← namedSelection context selections value
        let some application ← sourceApplication? declaration selected
          | throwError "the defining leg lost its original presentation application"
        let some originalZ := context.bindings.find? (·.id == z.id)
          | throwError "the defining leg lost its original final object"
        unless application.getAppArgs.back? == some originalZ.expression do
          throwError "the defining leg selected the nested presentation's arguments"
        checkWithKernel value
    unless (← kernel.dispatches.get).isEmpty do
      throwError "retaining a named construction dispatched an external computation"
  finally
    discard <| transaction.abort
    kernel.close
    setEnv environment



run_cmd Lean.Elab.Command.liftTermElabM do
  let environment ← getEnv
  let owners ← OwnerRegistry.new
  let kernel ← Kernel.load owners none none 1000
  discard <| SessionSnapshot.initialize owners
  let transaction ← CellTransaction.begin kernel.ledger
  try
    let source ← SourceSession.empty owners.identities
    for (text, address) in #[
        ("3 in ℤ", "num.rings"),
        ("{1, 2} in 𝒫(ℤ)", "lit.sets.finite_subsets"),
        ("x in ℤ[x]", "obj.sets.polynomials#generator"),
        ("generator(ℤ[x])", "obj.sets.polynomials#generator")] do
      let term ← source.read (← sourceTerm text)
      let result ← lower kernel transaction term
      let actual ← packet transaction result
      unless (actual.getObjValAs? String "ctor").toOption == some address do
        throwError "`{text}` changed its registered named-element descriptor: {actual}"
    unless (← kernel.dispatches.get).isEmpty do
      throwError "a named-element descriptor dispatched an external computation"
  finally
    discard <| transaction.abort
    kernel.close
    setEnv environment



run_cmd Lean.Elab.Command.liftTermElabM do
  let environment ← getEnv
  let owners ← OwnerRegistry.new
  let kernel ← Kernel.load owners none none 1000
  discard <| SessionSnapshot.initialize owners
  let transaction ← CellTransaction.begin kernel.ledger
  try
    let source ← SourceSession.empty owners.identities
    let object ← source.read (← sourceTerm "Fin(3)")
    let other ← source.read (← sourceTerm "ℤ")
    let otherEntry ← withNamedSource other fun context selections expression => do
      let selected ← namedSelection context selections expression
      let some (.named (.registered (.inl entry) _)) := selected.reference
        | throwError "the independent address control is not a registered object"
      return entry
    let actual ← lower kernel transaction object
    unless ((← packet transaction actual).getObjValAs? String "ctor").toOption ==
        some "obj.sets.fin" do
      throwError "the public finite object did not retain its independently registered address"
    withNamedSource object fun context selections expression => do
      let selected ← namedSelection context selections expression
      let some (.named (.registered (.inl entry) category)) := selected.reference
        | throwError "the actual public object lost its retained source selection"
      unless entry.id.raw == "obj.sets.fin" &&
          entry.declaration != otherEntry.declaration && !otherEntry.id.raw.isEmpty do
        throwError "the two original source objects do not have distinct registered declarations"
      let application := selected.value
      let throughLambda := fun (value : Expr) => do
        let function ← withLocalDeclD `unused (mkConst ``Unit) fun argument =>
          mkLambdaFVars #[argument] value (usedOnly := false)
        pure (mkApp function (mkConst ``Unit.unit))
      let throughIdentity := fun value => mkAppM ``id #[value]
      let selectedReference := SelectedSourceReference.named (.registered (.inl entry) category)
      selections.withBinding owners.identities context
          (sourceReference selectedReference application.getAppFn)
          fun headContext headSelections selectedHead => do
        let atHead := mkAppN selectedHead application.getAppArgs
        checkWithKernel atHead
        let selected ← kernel.run transaction headContext {} atHead (selections := headSelections)
        unless (← packet transaction selected) == (← packet transaction actual) do
          throwError "native application of the selected descriptor changed its original address"
      for (wrapped, message) in #[
          (← throughLambda expression, "native beta reduction changed the original selected descriptor"),
          (← throughIdentity expression, "native delta reduction changed the original selected descriptor")] do
        checkWithKernel wrapped
        let selected ← kernel.run transaction context {} wrapped (selections := selections)
        unless (← packet transaction selected) == (← packet transaction actual) do
          throwError message
      for unselected in #[application, ← throughLambda application,
          ← throughIdentity application] do
        checkWithKernel unselected
        let graph ← transaction.view
        let codeCount := (← kernel.codes.get).size
        let failed : Option Exception ← try
          discard <| kernel.run transaction context {} unselected (selections := selections)
          pure none
        catch error => pure (some error)
        let some failed := failed
          | throwError "an unselected declaration acquired its address from the registry"
        unless (← failed.toMessageData.toString) ==
            s!"the registered source declaration {entry.declaration} lost its selected source address" do
          throw failed
        unless graph.sameRevision (← transaction.view) &&
            (← kernel.codes.get).size == codeCount do
          throwError "an unselected declaration published a replacement value or closure"
      for (broken, message) in #[
          ({ entry with id := ⟨""⟩ },
            "the selected source lost its unique original registered address"),
          ({ entry with id := otherEntry.id },
            "the selected source changed its complete independently registered row"),
          ({ entry with declaration := .anonymous },
            "the selected source changed its complete independently registered row")] do
        let reference := SelectedSourceReference.named (.registered (.inl broken) category)
        selections.withBinding owners.identities context
            { selected with reference := some reference } fun context selections whole =>
          selections.withBinding owners.identities context
              (sourceReference reference application.getAppFn) fun context selections selectedHead => do
            let head := mkAppN selectedHead application.getAppArgs
            for malformed in #[whole, head, ← throughLambda whole, ← throughLambda head,
                ← throughIdentity whole, ← throughIdentity head] do
              checkWithKernel malformed
              let graph ← transaction.view
              let codeCount := (← kernel.codes.get).size
              let failed : Option Exception ← try
                discard <| kernel.run transaction context {} malformed (selections := selections)
                pure none
              catch error => pure (some error)
              let some failed := failed
                | throwError "a lost source selection fell back to an address found in the registry"
              unless (← failed.toMessageData.toString) == message do throw failed
              unless graph.sameRevision (← transaction.view) &&
                  (← kernel.codes.get).size == codeCount do
                throwError "a malformed source selection published a replacement value or closure"
    unless (← kernel.dispatches.get).isEmpty do
      throwError "a descriptor-address control dispatched an external computation"
  finally
    discard <| transaction.abort
    kernel.close
    setEnv environment




run_cmd Lean.Elab.Command.liftTermElabM do
  let identities ← liftM (m := IO) IdentitySupply.new
  let source ← SourceSession.empty identities
  for text in #["1 + 2 in ℤ", "0 in ℚ³", "|Fin(3)|",
      "view Fin(3) along «fun.sets.list»()"] do
    let term ← source.read (← sourceTerm text)
    withNamedSource term fun _ selections expression => do
      checkWithKernel expression
      let mut active := false
      for (_, selected) in selections.toList do
        let some reference := selected.reference | continue
        unless reference.computation?.isSome do continue
        active := true
        if let some application := selected.application then
          let .routedMethod family := application.family
            | throwError "`{text}` moved its active reference to an unrelated native family"
          let native := mkAppN
            (family.family.instantiateLevelParams family.universeParams application.universes)
            (application.parameters ++ application.arguments)
          unless SourceSelection.exactlyMatches Expr.equal
              { value := native, reference := some reference }
              { value := native, reference := some (.method family.entry family.functor) } &&
              selected.originalApplication.any (·.equal native) do
            throwError "`{text}` changed its selected complete method or original application"
        else
          let some declaration := reference.declaration
            | throwError "`{text}` lost its selected native declaration"
          let actual := selected.originalApplication.getD selected.value
          unless actual.consumeMData.getAppFn.isConstOf declaration do
            throwError "`{text}` retained its active computation reference on a derived value"
      unless active do
        throwError "`{text}` lost its actual selected computation application"

end CasRuntime.NamedApplicationTests
