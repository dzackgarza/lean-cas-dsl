module

import CasTools.Diagnostics
public meta import Lean.Elab.Command
meta import CasTools.Diagnostics

open Lean CasTools

run_cmd do
  let native := Json.mkObj [
    ("context", .arr #[Json.mkObj [
      ("id", Json.mkObj [("session", "source-α"), ("serial", toJson (7 : Nat))]),
      ("originalSource", .null), ("instances", .arr #[]),
      ("metadata", Json.mkObj [("$ref", toJson (19 : Nat)), ("nodes", "authored")])]]),
    ("selection", .arr #[.null, .bool true, .bool false, .num ⟨10, 1⟩,
      .num ⟨-123, 4⟩, .str "α\nquoted \"source\"", .arr #[], Json.mkObj []])]
  let source := Json.mkObj [
    ("source", native), ("producer", native), ("parameters", .arr #[native, .null, native])]
  let encoded := JsonGraph.encode source
  let .ok wire := Json.parse encoded.compress
    | throwError "the exact diagnostic graph did not survive JSON transport"
  let .ok decoded := JsonGraph.decode wire
    | throwError "the exact diagnostic graph did not decode"
  unless decoded == source do
    throwError "diagnostic graph transport changed original structured data"

run_cmd do
  let rows := (Array.range 29).map fun index => Json.mkObj [
    ("binding", Json.mkObj [("session", "one-source"), ("serial", toJson index)]),
    ("selection", Json.mkObj [("value", toJson index), ("route", toJson #["first", "second"]),
      ("parameters", .arr #[.null, .num ⟨10, 1⟩])])]
  let table := Json.arr rows
  let once := JsonGraph.encode table
  let repeated := JsonGraph.encode (.arr (Array.replicate 64 table))
  let .ok onceNodes := once.getObjValAs? (Array Json) "nodes"
    | throwError "a diagnostic table lost its exact node graph"
  let .ok repeatedNodes := repeated.getObjValAs? (Array Json) "nodes"
    | throwError "a repeated diagnostic table lost its exact node graph"
  unless repeatedNodes.size == onceNodes.size + 1 do
    throwError "diagnostic transport expanded repeated complete tables"
  let first := Json.mkObj [("value", toJson (4 : Nat)), ("packet", "same"),
    ("source", table), ("occurrence", toJson (11 : Nat))]
  let second := first.setObjVal! "occurrence" (toJson (12 : Nat))
  let original := Json.arr #[first, second, first]
  let .ok decoded := JsonGraph.decode (JsonGraph.encode original)
    | throwError "diagnostic occurrence data did not decode"
  unless decoded == original do
    throwError "diagnostic graph sharing identified distinct original occurrences"

run_cmd do
  let malformed := #[
    Json.mkObj [("root", toJson (0 : Nat)), ("nodes", .arr #[.arr #["null"]]),
      ("extra", .bool true)],
    Json.mkObj [("root", toJson (0 : Nat)), ("nodes", .arr #[])],
    Json.mkObj [("root", toJson (1 : Nat)), ("nodes", .arr #[.arr #["null"]])],
    Json.mkObj [("root", toJson (0 : Nat)), ("nodes", .arr #[.arr #["arr", toJson #[0]]])],
    Json.mkObj [("root", toJson (0 : Nat)), ("nodes", .arr #[.arr #["arr", toJson #[1]],
      .arr #["null"]])],
    Json.mkObj [("root", toJson (1 : Nat)), ("nodes", .arr #[.arr #["null"],
      .arr #["obj", toJson #[("same", 0), ("same", 0)]]])],
    Json.mkObj [("root", toJson (0 : Nat)), ("nodes", .arr #[.arr #["num", toJson (1 : Int),
      toJson (-1 : Int)]] )],
    Json.mkObj [("root", toJson (0 : Nat)), ("nodes", .arr #[.arr #["unknown"]])]]
  for document in malformed do
    if (JsonGraph.decode document).isOk then
      throwError "diagnostic transport accepted an invalid exact graph"

run_cmd do
  let old := Json.mkObj [("schema", toJson (1 : Nat)), ("sequence", toJson (8 : Nat)),
    ("session", "old-session"), ("parents", toJson #[2, 5]), ("event", "old"),
    ("monotonicMilliseconds", toJson (13 : Nat)), ("data", .arr #[.null, "original"])]
  let .ok decodedOld := ApplicationLog.decodeEvent old
    | throwError "the diagnostic reader rejected an original schema-1 event"
  unless decodedOld == old do
    throwError "the diagnostic reader changed an original schema-1 event"
  if (ApplicationLog.decodeEvent (old.setObjVal! "schema" (toJson (3 : Nat)))).isOk then
    throwError "the diagnostic reader accepted an unsupported stream schema"
  let data := Json.mkObj [("source", .arr #[.null, .num ⟨10, 1⟩, "original"]),
    ("selection", Json.mkObj [("$ref", toJson (9 : Nat))])]
  let log ← ApplicationLog.new "exact-log-transport" (Json.mkObj [])
  let first ← log.write #[0] "first" data
  let second ← log.write #[first] "second" data
  let events ← ApplicationLog.readEvents log.path
  unless events.size == 3 && first == 1 && second == 2 do
    throwError "the production diagnostic stream lost an original event"
  for event in events, sequence in [:events.size] do
    unless (event.getObjValAs? Nat "sequence").toOption == some sequence &&
        (event.getObjValAs? String "session").toOption == some log.session &&
        (event.getObjValAs? Nat "schema").toOption == some 2 &&
        (event.getObjValAs? Nat "monotonicMilliseconds").isOk do
      throwError "the diagnostic decoder changed an original envelope"
  for sequence in #[1, 2] do
    unless (events[sequence]!.getObjVal? "data").toOption == some data do
      throwError "the production diagnostic stream changed its complete original data"
  unless (events[2]!.getObjValAs? (Array Nat) "parents").toOption == some #[1] do
    throwError "the diagnostic stream changed an original causal parent"

run_cmd do
  let leaf := Json.mkObj [
    ("source", .arr #[.null, "original", .num ⟨10, 1⟩]), ("selected", .bool true)]
  let encodedLeaf := JsonGraph.encode leaf
  let .ok leafNodes := encodedLeaf.getObjValAs? (Array Json) "nodes"
    | throwError "the shared diagnostic leaf lost its complete node table"
  let .ok leafRoot := encodedLeaf.getObjValAs? Nat "root"
    | throwError "the shared diagnostic leaf lost its original root"
  let mut source := leaf
  let mut nodes := leafNodes
  let mut root := leafRoot
  for _ in [:24] do
    source := .arr #[source, source]
    let next := nodes.size
    nodes := nodes.push (.arr #["arr", toJson #[root, root]])
    root := next
  let expected := Json.mkObj [("root", toJson root), ("nodes", .arr nodes)]
  let encoded := JsonGraph.encode source
  unless encoded == expected do
    throwError "shared diagnostic traversal changed the exact canonical graph"
  let .ok wire := Json.parse encoded.compress
    | throwError "the shared diagnostic graph did not survive JSON transport"
  let .ok restored := JsonGraph.decode wire
    | throwError "the shared diagnostic graph did not restore its complete original data"
  unless JsonGraph.encode restored == encoded do
    throwError "shared diagnostic roundtrip changed its exact canonical graph"

run_cmd do
  let .ok first := Json.parse "{\"same\":[true,null]}"
    | throwError "the first independent diagnostic object did not parse"
  let .ok second := Json.parse " { \"same\" : [ true, null ] } "
    | throwError "the second independent diagnostic object did not parse"
  let once := JsonGraph.encode first
  let .ok originalNodes := once.getObjValAs? (Array Json) "nodes"
    | throwError "the independent diagnostic object lost its node table"
  let .ok originalRoot := once.getObjValAs? Nat "root"
    | throwError "the independent diagnostic object lost its root"
  let expected := Json.mkObj [
    ("root", toJson originalNodes.size),
    ("nodes", .arr (originalNodes.push
      (.arr #["arr", toJson #[originalRoot, originalRoot, originalRoot]])))]
  unless JsonGraph.encode (.arr #[first, second, first]) == expected do
    throwError "pointer traversal changed exact structural interning of independent objects"
  let numbers := Json.arr #[.num ⟨10, 1⟩, .num ⟨1, 0⟩, .num ⟨10, 1⟩, .num ⟨1, 0⟩]
  let expectedNumbers := Json.mkObj [("root", toJson (2 : Nat)),
    ("nodes", .arr #[.arr #["num", toJson (10 : Int), toJson (1 : Nat)],
      .arr #["num", toJson (1 : Int), toJson (0 : Nat)],
      .arr #["arr", toJson (#[0, 1, 0, 1] : Array Nat)]])]
  let encodedNumbers := JsonGraph.encode numbers
  unless encodedNumbers == expectedNumbers do
    throwError "diagnostic pointer traversal normalized an original JSON number"
  let .ok restoredNumbers := JsonGraph.decode encodedNumbers
    | throwError "the exact diagnostic numbers did not decode"
  unless restoredNumbers == numbers do
    throwError "diagnostic pointer traversal changed an original JSON number on roundtrip"

private unsafe def jsonGraphPointerCacheControl : IO Unit := do
  let original := Json.arr #[.str "retained-json-pointer", Json.mkObj [("field", .bool true)]]
  let other := Json.arr #[.str "other-json-pointer", .null]
  let first : Nat := 73
  let second : Nat := 109
  let cache : PtrMap Json Nat := mkPtrMap
  let cache := cache.insert original first
  unless cache.find? original == some first do
    throw <| IO.userError "the pointer cache missed the exact retained JSON immediately after insertion"
  let cache := cache.insert other second
  unless cache.find? original == some first do
    throw <| IO.userError "the pointer cache lost the exact retained JSON after another insertion"
  unless cache.find? other == some second do
    throw <| IO.userError "the pointer cache changed the second retained JSON sentinel"

#eval jsonGraphPointerCacheControl
