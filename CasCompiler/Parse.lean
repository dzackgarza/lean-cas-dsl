module

public import CasCompiler.Syntax

public section

open Lean

namespace CasCompiler

open CasCatalogue.Language

/-- The exact source input and every parsed item, before interpretation or provider selection. -/
structure SourceFile where
  private mk ::
  context : Parser.InputContext
  items : Array (TSyntax `cas_item)

/-- Translate native normalized positions back through the original file map.
Reference: Lean/Parser/Extension.lean mkInputContext uses this map composition for endPos;
Lean/Syntax.lean rewriteBottomUp preserves the tree while updating source metadata. -/
private def originalPositions (normalized original : FileMap) (stx : Syntax) : Syntax :=
  let position := fun pos => original.ofPosition (normalized.toPosition pos)
  let substring := fun (text : Substring.Raw) =>
    { str := original.source, startPos := position text.startPos,
      stopPos := position text.stopPos : Substring.Raw }
  let info : SourceInfo → SourceInfo := fun
    | .original leading start trailing stop =>
      SourceInfo.original (substring leading) (position start) (substring trailing) (position stop)
    | .synthetic start stop canonical => .synthetic (position start) (position stop) canonical
    | .none => .none
  stx.rewriteBottomUp fun
    | .node source kind args => .node (info source) kind args
    | .atom source value => .atom (info source) value
    | .ident source raw name resolved => .ident (info source) (substring raw) name resolved
    | .missing => .missing

/-- Parse all items using Lean's native tokenizer, grammar and source positions.
Reuse: Lean 4.33.0 Lean/Parser/Extension.lean, runParserCategory.
The input context retains original line endings so byte positions refer to the actual file. -/
opaque SourceFile.parse (fileName input : String) : CoreM SourceFile := do
  let parser := Parser.andthenFn Parser.whitespace
    (Parser.manyFn (Parser.categoryParserFnImpl `cas_item))
  let context := Parser.mkInputContext input fileName
  let state := parser.run context { env := ← getEnv, options := ← getOptions }
    (Parser.getTokenTable (← getEnv)) (Parser.mkParserState input)
  unless state.allErrors.isEmpty do throwError "{state.toErrorMsg context}"
  unless context.atEnd state.pos do
    throwError "{(state.mkError "end of input").toErrorMsg context}"
  let items : Array (TSyntax `cas_item) := state.stxStack.back.getArgs.map (⟨·⟩)
  let original := Parser.mkInputContext input fileName (normalizeLineEndings := false)
  let items := if context.inputString == original.inputString then items else
    items.map fun item => ⟨originalPositions context.fileMap original.fileMap item.raw⟩
  return ⟨original, items⟩

end CasCompiler
