module

import CasTools.Diagnostics
public meta import Lean.Elab.Command
meta import CasTools.Diagnostics

open Lean CasTools

run_cmd do
  let cases : Array (String × Json) := #[
    ("number", .num ⟨10, 1⟩),
    ("array", .arr #[.str "x", .null]),
    ("object", Json.mkObj [("b", toJson (2 : Nat)), ("a", toJson (1 : Nat))]),
    ("nested", Json.mkObj [("a", .arr #[.num ⟨10, 1⟩, .null]),
      ("b", Json.mkObj [("original", .bool true)])])]
  for (label, original) in cases do
    let encoded := JsonGraph.encode original
    let .ok decoded := JsonGraph.decode encoded
      | throwError "exact diagnostic graph failed to decode"
    logInfo m!"CASE {label}: equal={decoded == original} original={original.compress} encoded={encoded.compress} decoded={decoded.compress}"
