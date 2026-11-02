module

import CasCatalogue.DataOwnership
meta import CasCatalogue.DataOwnership

/-! Pure engineering controls for exact opaque occurrence ownership. No mathematical verdict. -/

namespace Occurrence

open Lean
open CasCatalogue.DataOwnership

private def expect (condition : Bool) (message : String) : IO Unit := do
  unless condition do throw (IO.userError message)

private def rejected (result : Except String Unit) : Bool :=
  match result with
  | .error _ => true
  | .ok _ => false

private def returns [BEq α] (expected : α) (result : Except String α) : Bool :=
  match result with
  | .ok actual => actual == expected
  | .error _ => false

private def token : Json := Json.mkObj [
  ("ctor", toJson "opaqueData"), ("args", toJson #["same-token-bytes"])]

def main : IO Unit := do
  let child : Owner := ("child-service", 17)
  let parent : Owner := ("outer-service", 23)
  let childTable := capture token child
  let parentTable := capture token parent
  let packet := Json.arr #[token, token, toJson "portable"]
  let mixed := append (CasCatalogue.DataOwnership.prefix #[.index 0] childTable)
    (CasCatalogue.DataOwnership.prefix #[.index 1] parentTable)
  expect (returns () (checkCoverage packet mixed)) "two live-supplier occurrences were not retained"
  expect (returns (some child) (lookup mixed #[.index 0])) "first equal token changed supplier"
  expect (returns (some parent) (lookup mixed #[.index 1])) "second equal token changed supplier"
  expect (owners mixed == #[child, parent]) "equal token JSON collapsed independent suppliers"
  expect (project #[.index 0] mixed == childTable) "child projection retained the wrong supplier"
  expect (project #[.index 1] mixed == parentTable) "parent projection retained the wrong supplier"
  expect ((project #[.index 2] mixed).isEmpty) "portable projection inherited sibling ownership"
  expect (get? packet #[.index 1] == some token) "array path selected a different occurrence"
  expect (get? packet #[.field "1"] == none) "field and index steps were conflated"
  expect (get? packet #[.index 4] == none) "out-of-range path selected existing equal data"

  let nested := Json.mkObj [("data[0]", packet), ("data", toJson "portable")]
  let nestedTable := CasCatalogue.DataOwnership.prefix #[.field "data[0]"] mixed
  expect (returns () (checkCoverage nested nestedTable)) "object assembly changed exact paths"
  expect (returns (some parent) (lookup nestedTable #[.field "data[0]", .index 1]))
    "a field name resembling a path was interpreted as a path"
  expect (project #[.field "data[0]", .index 0] nestedTable == childTable)
    "nested projection did not strip precisely the selected prefix"
  expect (get? nested #[.field "data[0]", .index 0] == some token)
    "nested exact lookup failed"
  expect ((project #[.field "data"] nestedTable).isEmpty)
    "similar field names were conflated"
  expect (project #[] mixed == mixed) "root projection changed occurrence identity"

  let repeated := append (CasCatalogue.DataOwnership.prefix #[.index 0] childTable)
    (CasCatalogue.DataOwnership.prefix #[.index 1] childTable)
  expect (returns () (checkCoverage packet repeated)) "repeating a child result lost an occurrence"
  expect (repeated.size == 2 && owners repeated == #[child])
    "repeated references lost positions or invented suppliers"
  expect (returns () (checkCoverage (toJson "portable") #[]))
    "portable data required a supplier"
  expect ((capture (toJson "portable") parent).isEmpty)
    "capture invented ownership for portable data"
  expect (returns () (checkCoverage token childTable)) "root opaque token lost its supplier"

  expect (rejected (checkCoverage packet (mixed.extract 0 1)))
    "a missing opaque occurrence supplier was accepted"
  expect (rejected (checkCoverage packet (append mixed #[{ path := #[.index 2], owner := child }])))
    "a binding to portable data was accepted"
  expect (rejected (checkCoverage packet (append mixed #[{ path := #[.index 7], owner := child }])))
    "a binding to an absent position was accepted"
  expect (rejected (checkCoverage token (append childTable childTable)))
    "duplicate same-supplier bindings were accepted"
  expect (rejected (checkCoverage token (append childTable parentTable)))
    "conflicting suppliers for one occurrence were accepted"
  expect (returns none (lookup #[] #[])) "an absent binding acquired an owner"
  expect (childTable != capture token ("child-service", 18))
    "different session identities were collapsed"
  IO.println "DataOwnership: 28 occurrence, projection, coverage and negative controls passed"

#eval main

end Occurrence

namespace Fragment

open Lean CasCatalogue.DataOwnership

private def expect (condition : Bool) (message : String) : IO Unit := do
  unless condition do throw (IO.userError message)

private def requireOk (result : Except String α) : IO α :=
  match result with
  | .ok value => pure value
  | .error message => throw (IO.userError message)

private def rejects (result : Except String α) : Bool :=
  match result with | .error _ => true | .ok _ => false

private def token : Json := Json.mkObj [
  ("ctor", toJson "opaqueData"), ("args", toJson #["same-token-bytes"])]

def main : IO Unit := do
  let firstOwner : Owner := ("first", 31)
  let secondOwner : Owner := ("second", 47)
  let first := Data.capture token firstOwner
  let second := Data.capture token secondOwner
  let portable ← requireOk (Data.portable (toJson "portable"))
  let array := Data.array #[first, second, portable]
  discard <| requireOk array.validate
  expect (array.json == Json.arr #[token, token, toJson "portable"])
    "array constructor changed public JSON"
  expect (owners array.ownership == #[firstOwner, secondOwner])
    "array constructor collapsed independent equal-byte suppliers"
  let selectedFirst ← requireOk (array.project #[.index 0])
  let selectedSecond ← requireOk (array.project #[.index 1])
  let selectedPortable ← requireOk (array.project #[.index 2])
  expect (selectedFirst == first && selectedSecond == second)
    "exact array projection changed occurrence identity"
  expect (selectedPortable == portable && selectedPortable.ownership.isEmpty)
    "portable sibling inherited an opaque supplier"
  let object ← requireOk (Data.object [("nested", array), ("other", portable)])
  let nestedSecond ← requireOk (object.project #[.field "nested", .index 1])
  expect (nestedSecond == second) "nested exact projection changed supplier"
  expect (rejects (object.project #[.field "nested", .field "1"]))
    "projection confused array indices with object keys"
  expect (rejects (object.project #[.field "absent"]))
    "projection selected an absent field"

  let constructor ← requireOk (Data.ctor "objectProduct" #[first, second])
  let constructorFirst ← requireOk (constructor.project #[.field "args", .index 0])
  let constructorSecond ← requireOk (constructor.project #[.field "args", .index 1])
  expect (constructorFirst == first && constructorSecond == second)
    "constructor fields lost their exact supplier"
  expect (constructor.json == Json.mkObj [
    ("ctor", toJson "objectProduct"), ("args", Json.arr #[token, token])])
    "constructor helper changed public envelope"
  expect (rejects (Data.object [("same", first), ("same", second)]))
    "duplicate object keys collapsed different suppliers"
  expect (rejects (Data.object [("same", portable), ("same", portable)]))
    "duplicate portable object keys were accepted"
  expect (rejects (Data.portable token)) "portable introduction accepted an opaque token"
  let bytes ← requireOk (Data.portable (toJson "same-token-bytes"))
  expect (rejects (Data.ctor "opaqueData" #[bytes]))
    "ordinary constructor introduced opaque data without a supplier"
  let invalid : Data := { json := token }
  expect (rejects (Data.array #[invalid]).validate)
    "array construction concealed missing child ownership"
  expect (rejects (Data.object [("invalid", invalid)]))
    "object construction concealed missing child ownership"

  let reassigned := Data.array #[selectedSecond, selectedFirst]
  discard <| requireOk reassigned.validate
  expect (owners reassigned.ownership == #[secondOwner, firstOwner])
    "reassembly selected supplier by equal JSON rather than placed fragment"
  let explicit : Data := {
    json := Json.arr #[selectedFirst.json, selectedSecond.json]
    ownership := append
      (CasCatalogue.DataOwnership.prefix #[.index 0] selectedFirst.ownership)
      (CasCatalogue.DataOwnership.prefix #[.index 1] selectedSecond.ownership) }
  discard <| requireOk explicit.validate
  expect (explicit == Data.array #[first, second])
    "explicit positioned append disagreed with exact array assembly"
  let invalidWhole : Data := { object with
    ownership := append object.ownership #[{ path := #[.field "other"], owner := firstOwner }] }
  expect (rejects (invalidWhole.project #[.field "nested", .index 0]))
    "projection hid invalid ownership outside its selected subtree"
  IO.println "DataOwnership.Data: 18 scoped fragment controls passed"

#eval main

end Fragment
