module

import CasRuntime.Kernel
import CasCompiler.Read
import CasCompiler.Parse
import LeanCategories.Catalogue
public meta import Lean.Elab.Command
meta import CasRuntime.Kernel
meta import CasCompiler.Read
meta import CasCompiler.Parse
meta import LeanCategories.Catalogue

namespace CasRuntime.BindingIdentityTests

open Lean Meta Elab Term CasCompiler CasCatalogue CasCatalogue.Language

private def statement (session : SourceSession) (text : String) :
    TermElabM SourceStatement := do
  let file ← SourceFile.parse "binding-identities.cas" text
  let #[item] := file.items
    | throwError "the binder control changed its original statement count"
  let `(cas_item| $source:cas_stmt) := item
    | throwError "the binder control changed its public statement syntax"
  file.withContext <| session.readStatement source

private def sourceTerm (text : String) : TermElabM (TSyntax `cas_term) := do
  let .ok parsed := Parser.runParserCategory (← getEnv) `cas_term text
    | throwError "the binder control's original source term did not parse"
  return ⟨parsed⟩

private def nativeTerm (text : String) : TermElabM Term := do
  let .ok parsed := Parser.runParserCategory (← getEnv) `term text
    | throwError "the binder control's native function type did not parse"
  return ⟨parsed⟩

-- The original public declarations have the same displayed name, but independent
-- native identities. Reopening and shadowing preserve the first source occurrence.
-- Native aliases retain actual captured values, not a value found by its display name.
run_cmd Lean.Elab.Command.liftTermElabM do
  let original ← getEnv
  let owners ← OwnerRegistry.new
  let kernel ← Kernel.load owners none none 1000
  discard <| SessionSnapshot.initialize owners
  let producer ← CellTransaction.begin kernel.ledger
  let firstOwner ← owners.spawn { cmd := "/bin/cat" }
  let secondOwner ← owners.spawn { cmd := "/bin/cat" }
  try
    let empty ← SourceSession.empty owners.identities
    let .assumption firstSource ← statement empty "let x ∈ ℤ"
      | throwError "the original abstract element did not remain a native parameter"
    let some firstEntry := firstSource.context.entries.back?
      | throwError "the first source parameter lost its native identity"
    let firstTerm ← firstSource.read (← sourceTerm "x")
    let .definition aliasSource _ ← statement firstSource "let saved := x"
      | throwError "the original source alias did not retain a native definition"
    let some aliasEntry := aliasSource.context.entries.back?
      | throwError "the source alias lost its original native binding"
    let .assumption shadowSource ← statement aliasSource "let x ∈ ℤ"
      | throwError "the shadowing element did not remain a native parameter"
    let some secondEntry := shadowSource.context.entries.back?
      | throwError "the shadowing source parameter lost its native identity"
    let shadowTerm ← shadowSource.read (← sourceTerm "x")
    let aliasTerm ← shadowSource.read (← sourceTerm "saved")
    unless firstEntry.id != secondEntry.id && firstEntry.userName == `x &&
        secondEntry.userName == `x && aliasEntry.userName == `saved do
      throwError "source shadowing changed display names or reused an earlier binding identity"

    let lower := fun (term : SourceTerm) => term.source.withOpen fun bindings expression => do
      kernel.run producer (← ContextTelescope.capture bindings) {} expression
    let firstSymbol ← lower firstTerm
    let secondSymbol ← lower shadowTerm
    let aliasSymbol ← lower aliasTerm
    let reopenedSymbol ← shadowTerm.source.withOpen fun bindings _ => do
      let context ← ContextTelescope.capture bindings
      let earlier ← firstTerm.source.inContext context
      let some retained := bindings.find? (·.id == firstEntry.id)
        | throwError "context reopening lost the original shadowed binder"
      unless earlier == retained.expression do
        throwError "context transport changed the earlier binder to its same-named successor"
      kernel.run producer context {} earlier
    let symbolId := fun (value : ValueBinding) => do
      let .ok (some packet) := (← producer.view).packet? value
        | throwError "the formal parameter did not retain its portable symbol descriptor"
      let .ok constructor := packet.getObjValAs? String "ctor"
        | throwError "the original symbol descriptor lost its constructor"
      let .ok arguments := packet.getObjValAs? (Array Json) "args"
        | throwError "the original symbol descriptor lost its argument array"
      let #[.str identity] := arguments
        | throwError "the original symbol descriptor changed its one-string wire grammar"
      unless constructor == "variable" do
        throwError "the original formal parameter changed its wire constructor"
      return identity
    let firstIdentity ← symbolId firstSymbol
    let secondIdentity ← symbolId secondSymbol
    unless firstIdentity == s!"{firstEntry.id.session}:{firstEntry.id.serial}" &&
        secondIdentity == s!"{secondEntry.id.session}:{secondEntry.id.serial}" &&
        firstIdentity != secondIdentity &&
        (← symbolId reopenedSymbol) == firstIdentity &&
        (← symbolId aliasSymbol) == firstIdentity do
      throwError "formal wire identity changed under shadowing, native aliasing or reopening"

    -- Both tokens are opaque actual parameter values from distinct live owners.
    -- They supply no arithmetic result or mathematical assertion.
    let firstToken ← liftM (m := IO) do
      firstOwner.child.stdin.putStr "first captured parameter\n"
      firstOwner.child.stdin.flush
      return (← firstOwner.child.stdout.getLine).trimAscii.toString
    let secondToken ← liftM (m := IO) do
      secondOwner.child.stdin.putStr "second shadowed parameter\n"
      secondOwner.child.stdin.flush
      return (← secondOwner.child.stdout.getLine).trimAscii.toString
    let stage := fun (term : SourceTerm) (payload : ValuePayload) =>
      term.source.withOpen fun bindings expression => do
        let context ← ContextTelescope.capture bindings
        let environment ← RuntimeEnvironment.capture owners.worker context #[]
        let origin ← environment.origin (← owners.identities.fresh .program)
          (← kernel.ledger.allocate) (← SourceLayout.ofTerm (← context.close expression))
        producer.stage origin payload
    let firstValue ← stage firstTerm (.ownedExport firstOwner firstToken #[])
    let secondValue ← stage shadowTerm (.ownedExport secondOwner secondToken #[])
    let bound : Std.HashMap BindingId ValueBinding :=
      ({} : Std.HashMap BindingId ValueBinding).insert firstEntry.id firstValue
        |>.insert secondEntry.id secondValue
    unless (bound[aliasEntry.id]?).isNone do
      throwError "the native-alias control accidentally supplied its own runtime binding"

    let type ← shadowSource.term (← nativeTerm "Int → Int")
    let function ← shadowSource.read (← sourceTerm "t ↦ saved") (some type.source)
    let callable ← function.source.withOpen fun bindings expression => do
      kernel.run producer (← ContextTelescope.capture bindings) bound expression
    let graph ← producer.view
    let .ok code := graph.callable callable
      | throwError "the source lambda lost its actual callable"
    let some node := graph.find code.value
      | throwError "the source lambda lost its retained native code"
    let .closure program captures := node.payload.data
      | throwError "the source lambda was replaced by another computational interface"
    let #[capture] := captures
      | throwError "a native alias lost or enlarged its exact earlier capture"
    unless capture.value == firstValue.value &&
        capture.associationIds == firstValue.associationIds &&
        capture.value != secondValue.value do
      throwError "the native alias captured the shadowing value instead of its original occurrence"
    let some (.term retainedSource) := (← kernel.codes.get)[program]?
      | throwError "the source lambda lost its original closed term"
    unless retainedSource.context.exactlyMatches function.source.context &&
        retainedSource.expression.equal function.source.expression do
      throwError "closure capture changed the complete original source or native telescope"
    let .ok dependencies := graph.requiredOwners #[callable]
      | throwError "the original closure capture is outside its active graph"
    unless dependencies == #[firstOwner.generation] do
      throwError "the closure did not retain exactly the owner of its original alias capture"

    let functions ← shadowSource.defineTerm `f function
    let some functionEntry := functions.context.entries.back?
      | throwError "the source function lost its original definition binding"
    let applied ← functions.read (← sourceTerm "f(saved)")
    let consuming := bound.insert functionEntry.id callable
    let .ok _ ← producer.commit
      | throwError "the source closure and its actual input values did not publish"
    owners.close secondOwner.generation
    let consumer ← CellTransaction.begin kernel.ledger
    try
      let result ← applied.source.withOpen fun bindings expression => do
        kernel.run consumer (← ContextTelescope.capture bindings) consuming expression
      unless result.value == firstValue.value &&
          firstValue.associationIds.toList.isPrefixOf result.associationIds.toList do
        throwError "the actual source application replaced its original captured value"
      unless ← (← consumer.view).isAvailable owners callable do
        throwError "an unused shadowing owner invalidated the original closure"
      let .ok _ ← consumer.commit
        | throwError "the source application could not publish its original captured result"
    finally discard <| consumer.abort
    owners.close firstOwner.generation
    let unavailable ← CellTransaction.begin kernel.ledger
    try
      unless !(← (← unavailable.view).isAvailable owners callable) do
        throwError "the closed original capture remained available after its owner retired"
      let failure : Option Exception ← try
        discard <| applied.source.withOpen fun bindings expression => do
          kernel.run unavailable (← ContextTelescope.capture bindings) consuming expression
        pure none
      catch error => pure (some error)
      let some failure := failure
        | throwError "an actual application consumed its retired captured owner"
      unless CasCatalogue.Exception.stratum? failure == some .unavailable do throw failure
    finally discard <| unavailable.abort
    unless (← kernel.dispatches.get).isEmpty do
      throwError "native binder identity or capture preservation dispatched an external operation"
  finally
    discard <| producer.abort
    owners.close firstOwner.generation
    owners.close secondOwner.generation
    kernel.close
    setEnv original

end CasRuntime.BindingIdentityTests
