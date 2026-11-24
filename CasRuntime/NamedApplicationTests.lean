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

private def symbol (id : BindingId) : Json :=
  Json.mkObj [("ctor", "variable"), ("args", .arr #[toJson s!"{id.session}:{id.serial}"])]

private def descriptor (address : String) (arguments : Array Json) : Json :=
  Json.mkObj [("ctor", toJson address), ("args", .arr arguments)]

private def lower (kernel : Kernel) (transaction : CellTransaction) (term : SourceTerm) :
    MetaM ValueBinding :=
  term.source.withOpen fun bindings expression => do
    kernel.run transaction (← ContextTelescope.capture bindings) {} expression

private def packet (transaction : CellTransaction) (value : ValueBinding) : MetaM Json := do
  let .ok (some packet) := (← transaction.view).packet? value
    | throwError "the named application did not retain its descriptor and actual arguments"
  return packet

-- Both the outer diagram and its first object contain the same registered presentation.
-- Its public runtime descriptor must contain the outer pair, including Z. The earlier X,Y
-- application is a proper argument, never a substitute for the outer application.
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
      object.source.withOpen fun bindings value => do
        let context ← ContextTelescope.capture bindings
        let some application ← sourceApplication? declaration value
          | throwError "the nested presentation lost its exact original application"
        let some originalZ := bindings.find? (·.id == z.id)
          | throwError "the nested presentation lost the original Z"
        unless application.getAppArgs.back? == some originalZ.expression do
          throwError "the outer presentation took its arguments from the nested presentation"
        let some coneApplication ← sourceApplication? declaration
            (← selection.cone.inContext context)
          | throwError "the selected cone lost its exact original presentation"
        unless coneApplication == application do
          throwError "the selected apex and cone retained different original applications"
        checkWithKernel value
        -- Losing the new application field must not revive the old subterm search, even
        -- though this checked apex still contains both registered presentations.
        let .mdata reference (.mdata _ envelope) := value
          | throwError "the named-application control lost its formed source envelope"
        unless envelope.isAppOfArity ``Function.const 4 do
          throwError "the named-application control lost its typed native envelope"
        let missing := Expr.mdata reference envelope.getAppArgs[2]!
        checkWithKernel missing
        let rejected : Option Exception ← try
          discard <| kernel.run transaction context {} missing
          pure none
        catch error => pure (some error)
        let some rejected := rejected
          | throwError "lowering recovered a lost named application from a nested declaration"
        unless (← rejected.toMessageData.toString) ==
            "internal: the named element lost its original registered application" do
          throw rejected
      let expected := descriptor address #[descriptor address #[symbol x.id, symbol y.id], symbol z.id]
      unless (← packet transaction (← lower kernel transaction object)) == expected do
        throwError "the nested construction's public descriptor changed its actual outer arguments"

      let source ← source.defineTerm `K object
      let source ← source.assume `X (← nativeTerm "Type")
      let retained ← source.read (← sourceTerm "K")
      unless (← packet transaction (← lower kernel transaction retained)) == expected do
        throwError "a retained construction changed its original application after shadowing"
      let leg ← source.read (← sourceTerm "K.leg(0)")
      leg.source.withOpen fun bindings value => do
        let some application ← sourceApplication? declaration value
          | throwError "the defining leg lost its original presentation application"
        let some originalZ := bindings.find? (·.id == z.id)
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

-- Every named-element producer supplies the same typed application origin. These are
-- ordinary registered source forms; their descriptors need no provider or fabricated data.
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

-- The actual public source row is authoritative. A still well-typed native declaration
-- cannot replace a missing address or an address changed to another real registered row.
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
    let (otherId, otherDeclaration) ← other.source.withOpen fun _ expression => do
      let .mdata data _ := expression
        | throwError "the independent registered object lost its source selection"
      unless data.getName `CasCompiler.source.kind == ``ObjectEntry do
        throwError "the independent address control is not a registered object"
      return (data.getString `CasCompiler.source.id,
        data.getName `CasCompiler.source.declaration)
    let actual ← lower kernel transaction object
    unless ((← packet transaction actual).getObjValAs? String "ctor").toOption ==
        some "obj.sets.fin" do
      throwError "the public finite object did not retain its independently registered address"
    object.source.withOpen fun bindings expression => do
      let context ← ContextTelescope.capture bindings
      let .mdata data body := expression
        | throwError "the actual public object lost its retained source selection"
      unless data.getName `CasCompiler.source.kind == ``ObjectEntry &&
          data.getString `CasCompiler.source.id == "obj.sets.fin" &&
          data.getName `CasCompiler.source.declaration != otherDeclaration &&
          !otherId.isEmpty do
        throwError "the two original source objects do not have distinct registered declarations"
      let application := body.consumeMData
      let atHead := mkAppN (.mdata data application.getAppFn) application.getAppArgs
      checkWithKernel atHead
      let selected ← kernel.run transaction context {} atHead
      unless (← packet transaction selected) == (← packet transaction actual) do
        throwError "native application of the selected descriptor changed its original address"
      let throughLambda := fun (value : Expr) => do
        let function ← withLocalDeclD `unused (mkConst ``Unit) fun argument =>
          mkLambdaFVars #[argument] value (usedOnly := false)
        pure (mkApp function (mkConst ``Unit.unit))
      let applied ← throughLambda expression
      checkWithKernel applied
      let selected ← kernel.run transaction context {} applied
      unless (← packet transaction selected) == (← packet transaction actual) do
        throwError "native beta reduction changed the original selected descriptor"
      let throughIdentity := fun value => mkAppM ``id #[value]
      let identity ← throughIdentity expression
      checkWithKernel identity
      let selected ← kernel.run transaction context {} identity
      unless (← packet transaction selected) == (← packet transaction actual) do
        throwError "native delta reduction changed the original selected descriptor"
      for unselected in #[application, ← throughLambda application,
          ← throughIdentity application] do
        checkWithKernel unselected
        let graph ← transaction.view
        let codeCount := (← kernel.codes.get).size
        let failed : Option Exception ← try
          discard <| kernel.run transaction context {} unselected
          pure none
        catch error => pure (some error)
        let some failed := failed
          | throwError "an unselected declaration acquired its address from the registry"
        unless (← failed.toMessageData.toString) ==
            s!"the registered source declaration {data.getName `CasCompiler.source.declaration} lost its selected source address" do
          throw failed
        unless graph.sameRevision (← transaction.view) &&
            (← kernel.codes.get).size == codeCount do
          throwError "an unselected declaration published a replacement value or closure"
      for (broken, message) in #[
          (data.setString `CasCompiler.source.id "",
            "the selected descriptor lost its original registered address"),
          (data.setString `CasCompiler.source.id otherId,
            "the selected descriptor changed its original registered declaration"),
          (data.setName `CasCompiler.source.declaration .anonymous,
            "the selected descriptor changed its original registered declaration")] do
        let whole := Expr.mdata broken body
        let head := mkAppN (.mdata broken application.getAppFn) application.getAppArgs
        for malformed in #[whole, head, ← throughLambda whole, ← throughLambda head,
            ← throughIdentity whole, ← throughIdentity head] do
          checkWithKernel malformed
          let graph ← transaction.view
          let codeCount := (← kernel.codes.get).size
          let failed : Option Exception ← try
            discard <| kernel.run transaction context {} malformed
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

-- The public source records both the visible derived selection and the active native
-- declaration application. Native functor projection, method composition and lambda
-- specialization cannot turn an outer observation into an instruction to scan subterms.
run_cmd Lean.Elab.Command.liftTermElabM do
  let identities ← liftM (m := IO) IdentitySupply.new
  let source ← SourceSession.empty identities
  for text in #["1 + 2 in ℤ", "0 in ℚ³", "|Fin(3)|",
      "view Fin(3) along «fun.sets.list»()"] do
    let term ← source.read (← sourceTerm text)
    term.source.withOpen fun _ expression => do
      checkWithKernel expression
      let active := fun (expression : Expr) => match expression with
        | .mdata data _ =>
          !data.getBool `CasCompiler.source.derived &&
          #[``OperationEntry, ``MethodEntry, ``MorphismEntry, ``ConstructionEntry,
            ``EdgeRef.functor].contains (data.getName `CasCompiler.source.kind)
        | _ => false
      unless (expression.find? active).isSome do
        throwError "`{text}` lost its actual selected computation application"
      let wrong := expression.find? fun expression =>
        if active expression then
          match expression with
          | .mdata data body =>
            !body.consumeMData.getAppFn.isConstOf
              (data.getName `CasCompiler.source.declaration)
          | _ => false
        else false
      if wrong.isSome then
        throwError "`{text}` retained its active computation reference on a derived value"

end CasRuntime.NamedApplicationTests
