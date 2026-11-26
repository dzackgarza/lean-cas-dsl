module

import CasCompiler.Read
import CasCompiler.Parse
import CasCompiler.SourceTestSupport
import LeanCategories.Catalogue.Semantics.Foundation.Objects
public meta import Lean.Elab.Command
meta import CasCompiler.Read
meta import CasCompiler.Parse
meta import CasCompiler.SourceTestSupport
meta import LeanCategories.Catalogue.Semantics.Foundation.Objects

open Lean Meta Elab Term CasCompiler
open CasCompiler.SourceTest

private def nativeTerm (text : String) : TermElabM Term := do
  let .ok stx := Parser.runParserCategory (← getEnv) `term text
    | throwError "the native lambda parameter did not parse"
  return ⟨stx⟩

private def sourceTerm (text : String) : TermElabM (TSyntax `cas_term) := do
  let .ok stx := Parser.runParserCategory (← getEnv) `cas_term text
    | throwError "the source lambda did not parse"
  return ⟨stx⟩

run_cmd Lean.Elab.Command.liftTermElabM do
  let identities ← liftM (m := IO) CasRuntime.IdentitySupply.new
  let empty ← SourceSession.empty identities
  let parameters ← empty.assume `n (← nativeTerm "Nat")
  let hypotheses ← parameters.assume `h (← nativeTerm "n = n")
  let session ← hypotheses.assume `i (← nativeTerm "Fin n")
  let type ← session.term (← nativeTerm "(m : Nat) → Fin m → Fin m")
  let expected ← session.term (← nativeTerm "fun (n : Nat) (i : Fin n) => i")
  let term ← session.read (← sourceTerm "n ↦ i ↦ i") (some type.source) type.selections
  unless (← authoredEntries term.source.context term.selections).size == 3 do
    throwError "a source lambda discarded its complete preceding context"
  discard <| session.elaborateScoped Syntax.missing do
    let expression ← session.readTerm term
    let expected ← session.readTerm expected
    let .lam `n _ (.lam `i _ (.bvar 0) _) _ ← selectedValue expression
      | liftM (m := TermElabM) <| throwError "dependent source binders changed their lexical occurrences"
    checkOriginal #[expression, expected] fun native => do
      unless ← isDefEq native[0]! native[1]! do
        throwError "a source lambda changed its dependent native type"
    return expression
  let type ← session.term (← nativeTerm "Fin n → Fin n")
  let term ← session.read (← sourceTerm "x ↦ i") (some type.source) type.selections
  checkSelected term fun expression => do
    let scope ← get
    let bindings ← authoredBindings
    let .lam `x _ body _ ← selectedValue expression
      | liftM (m := TermElabM) <| throwError "a constant source function discarded its binder"
    unless ← originatesAt scope.context scope.selections body bindings[2]!.expression false do
      liftM (m := TermElabM) <| throwError "a source lambda rebound its captured preceding value"
  let term ← session.read (← sourceTerm "i ↦ i") (some type.source) type.selections
  let bound ← session.defineTerm `identity term
  let applied ← bound.read (← sourceTerm "identity(i)")
  checkSelected applied fun expression => do
    let scope ← get
    let bindings ← authoredBindings
    for binding in bindings.extract 2 4 do
      unless (← visitNativeData (fun term =>
          originatesAt scope.context scope.selections term binding.expression false)
          expression false) > 0 do
        liftM (m := TermElabM) <| throwError "a source function application replaced its actual retained bindings"
  for text in #["i ↦ n", "i ↦ missing"] do
    let failure : Option Exception ← try
      discard <| session.read (← sourceTerm text) (some type.source) type.selections
      pure none
    catch error => pure (some error)
    unless failure.isSome do
      throwError "a source lambda accepted an ill-typed or unbound body"
  let rejected ← try
    discard <| session.read (← sourceTerm "i ↦ i")
    pure false
  catch _ => pure true
  unless rejected do
    throwError "a source lambda invented its independently required argument type"

run_cmd Lean.Elab.Command.liftTermElabM do
  let identities ← liftM (m := IO) CasRuntime.IdentitySupply.new
  let empty ← SourceSession.empty identities
  let parameters ← empty.assume `n (← nativeTerm "Nat")
  let session ← parameters.define `consume
    (← nativeTerm "fun {A : Type} (f : A → A) (a : A) => f a")
  let session ← session.assume `i (← nativeTerm "Fin n")
  let term ← session.read (← sourceTerm "consume(x ↦ x, i)")
  checkSelected term fun expression => do
    let scope ← get
    let bindings ← authoredBindings
    checkOriginal #[← inferType expression, ← inferType bindings[2]!.expression] fun native => do
      unless ← isDefEq native[0]! native[1]! do
        throwError "a source lambda lost argument inference from a later dependent argument"
    for binding in bindings.extract 1 3 do
      unless (← visitNativeData (fun term =>
          originatesAt scope.context scope.selections term binding.expression false)
          expression false) > 0 do
        liftM (m := TermElabM) <| throwError "a source lambda application replaced its original callable or argument"

run_cmd Lean.Elab.Command.liftTermElabM do
  let identities ← liftM (m := IO) CasRuntime.IdentitySupply.new
  let empty ← SourceSession.empty identities
  let session ← empty.define `choose
    (← nativeTerm "fun {A : Type} [Inhabited A] => (default : A)")
  let type ← session.term (← nativeTerm "(A : Type) → [Inhabited A] → A")
  let term ← session.read (← sourceTerm "A ↦ witness ↦ choose()") (some type.source) type.selections
  checkSelected term fun expression => do
    let scope ← get
    let bindings ← authoredBindings
    let .lam `A domain inner .default ← selectedValue expression
      | liftM (m := TermElabM) <| throwError "a source lambda changed its declared instance binder"
    let .lam `witness _ body .instImplicit := inner
      | liftM (m := TermElabM) <| throwError "a source lambda changed its declared instance binder"
    unless body.hasLooseBVars do
      liftM (m := TermElabM) <| throwError "a source lambda lost its original callable or bound instance"
    let count ← SourceReadM.withBinder `A domain none .default
      (fun _ count => pure count) fun parameter => do
        let .lam `witness type body .instImplicit := inner.instantiate1 parameter
          | liftM (m := MetaM) <| throwError "a source lambda changed its declared instance binder"
        SourceReadM.withBinder `witness type none .instImplicit
          (fun _ count => pure count) fun instanceValue =>
            visitNativeData (fun term =>
              originatesAt scope.context scope.selections term bindings[0]!.expression false)
              (body.instantiate1 instanceValue) false
    unless count > 0 do
      liftM (m := TermElabM) <| throwError "a source lambda lost its original callable or bound instance"

run_cmd Lean.Elab.Command.liftTermElabM do
  let identities ← liftM (m := IO) CasRuntime.IdentitySupply.new
  let empty ← SourceSession.empty identities
  let types ← empty.assume `X (← nativeTerm "Type")
  let session ← types.assume `i (← nativeTerm "X")
  let type ← session.term (← nativeTerm "TypeCat.Hom X X")
  let term ← session.read (← sourceTerm "x ↦ i") (some type.source) type.selections
  let expected ← session.term (← nativeTerm "TypeCat.ofHom (fun (_ : X) => i)")
  discard <| session.elaborateScoped Syntax.missing do
    let expression ← session.readTerm term
    let expected ← session.readTerm expected
    checkOriginal #[expression, expected] fun native => do
      unless ← isDefEq native[0]! native[1]! do
        throwError "a source set map changed its declared native function or captured value"
    return expression
  let some category := term.category
    | throwError "a source set map discarded its selected category"
  unless category.role == .morphism do
    throwError "a source set map changed its morphism role"

run_cmd Lean.Elab.Command.liftTermElabM do
  let identities ← liftM (m := IO) CasRuntime.IdentitySupply.new
  let empty ← SourceSession.empty identities
  let types ← empty.assume `X (← nativeTerm "Type")
  let session ← types.assume `i (← nativeTerm "X")
  let file ← SourceFile.parse "source-functions.cas"
    "let f := x ↦ x in X → X\nlet g(x) := f(x) in X → X\n\
     let k := g ∘ f\nassert k(i) = i\n"
  let mut session := session
  for item in file.items do
    let `(cas_item| $statement:cas_stmt) := item
      | throwError "a source function statement did not parse"
    match ← file.withContext (session.readStatement statement) with
    | .definition next value =>
      unless value.span.fileName == "source-functions.cas" && value.span.start.isSome &&
          value.span.stop.isSome do
        throwError "a source function binding lost its original source span"
      if (← authoredEntries next.context next.selections).size == 4 then
        unless value.span.start == statement.raw.getPos? &&
            value.span.stop == statement.raw.getTailPos? do
          throwError "a function expansion replaced the original statement range"
      let some category := value.category
        | throwError "a retained source function discarded its selected category"
      unless category.role == .morphism do
        throwError "a source function binding changed its morphism role"
      session := next
    | .assumption _ | .proved .. | .inspection _ | .contextBlock _ =>
      throwError "these original source statements contain no scoped declaration or explicit proof"
    | .implemented _ => throwError "these source statements contain no implementation request"
    | .settled _ => throwError "these source statements contain no typing question"
    | .question proposition =>
      unless (← authoredEntries proposition.source.context proposition.selections).size == 5 do
        throwError "a later function question lost its complete preceding context"
      checkSelected proposition fun expression => do
        let scope ← get
        let bindings ← authoredBindings
        for binding in #[bindings[1]!, bindings[4]!] do
          unless (← visitNativeData (fun term =>
              originatesAt scope.context scope.selections term binding.expression false)
              expression false) > 0 do
            liftM (m := TermElabM) <| throwError "a later function question replaced its actual argument or composed map"

run_cmd Lean.Elab.Command.liftTermElabM do
  let identities ← liftM (m := IO) CasRuntime.IdentitySupply.new
  let empty ← SourceSession.empty identities
  let types ← empty.assume `X (← nativeTerm "Type")
  let functions ← types.define `F (← nativeTerm "X → X")
  let session ← functions.assume `i (← nativeTerm "X")
  let term ← session.read (← sourceTerm "x ↦ i in F")
  checkSelected term fun expression => do
    let bindings ← authoredBindings
    checkOriginal #[expression, bindings[2]!.expression] fun native => do
      unless native[0]!.containsFVar native[1]!.fvarId! do
        throwError "a local type annotation replaced the function's captured value"
  let annotated ← session.read (← sourceTerm "i in X")
  checkSelected annotated fun expression => do
    let scope ← get
    let bindings ← authoredBindings
    unless ← originatesAt scope.context scope.selections expression bindings[2]!.expression false do
      liftM (m := TermElabM) <| throwError "a local domain annotation replaced the original source occurrence"
