module

import CasTools.NativeExpression
public meta import Lean.Elab.Command
meta import CasTools.NativeExpression

open Lean CasTools.NativeExpression

run_cmd do
  let name := Name.str (.num (.str .anonymous "scope@") 7) "field.with.dot"
  let leading : Substring.Raw := ⟨" α ", ⟨0⟩, ⟨1⟩⟩
  let trailing : Substring.Raw := ⟨" α ", ⟨3⟩, ⟨4⟩⟩
  let syntaxValue := Syntax.node (.synthetic ⟨1⟩ ⟨3⟩ true) name
    #[Syntax.atom (.original leading ⟨1⟩ trailing ⟨3⟩) "α", mkIdent name, .missing]
  let metadata : MData := { entries := [
    (name, .ofString "native α"), (`flag, .ofBool true), (`name, .ofName name),
    (`natural, .ofNat 23), (`integer, .ofInt (-7)), (`syntaxValue, .ofSyntax syntaxValue)] }
  let shiftedSyntax := Syntax.node (.synthetic ⟨2⟩ ⟨4⟩ true) name syntaxValue.getArgs
  let shiftedMetadata : MData := { entries := metadata.entries.map fun (key, value) =>
    (key, if key == `syntaxValue then .ofSyntax shiftedSyntax else value) }
  let level := Level.imax (.max (.param name) (.succ .zero)) (.mvar ⟨name⟩)
  let leaf := Expr.const name [level]
  let roots : Array Expr := #[leaf, .sort level, .bvar 3, .fvar ⟨name⟩, .mvar ⟨name⟩,
    .app leaf leaf, .lam name (.sort .zero) (.bvar 0) .implicit,
    .lam `other (.sort .zero) (.bvar 0) .instImplicit,
    .forallE name (.sort .zero) (.bvar 0) .strictImplicit,
    .letE name (.sort .zero) leaf (.bvar 0) true,
    .letE name (.sort .zero) leaf (.bvar 0) false,
    .lit (.natVal 5), .lit (.strVal "α"), .mdata metadata leaf,
    .mdata shiftedMetadata leaf, .mdata { entries := metadata.entries.reverse } leaf,
    .proj name 2 leaf]
  let document := encode roots
  let .ok json := Json.parse document.compress | throwError "native graph JSON did not parse"
  let .ok restored := decode json | throwError "native graph JSON did not decode"
  unless restored.size == roots.size &&
      (roots.zip restored).all (fun (source, target) =>
        source.equal target && reprStr source == reprStr target) do
    throwError "native graph transport changed a constructor, binder, metadata value or universe"

run_cmd do
  let leaf := Expr.const `shared []
  let root := (List.range 24).foldl (fun value _ => Expr.app value value) leaf
  let document := encode #[root]
  let .ok restored := decode document | throwError "the shared native graph did not decode"
  unless restored.size == 1 && root.equal restored[0]! do
    throwError "shared native graph transport changed its complete expression"
  let .ok nodes := document.getObjValAs? (Array Json) "nodes"
    | throwError "the native graph omitted its shared node table"
  unless nodes.size == 25 do
    throwError "the native graph expanded repeated subterms"
  let json := Json.mkObj [("roots", toJson #[0]), ("nodes", toJson #[Node.app 0 0])]
  if let .ok _ := decode json then
    throwError "the native graph accepted a forward or cyclic reference"
