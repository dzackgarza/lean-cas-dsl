module

import CasCompiler.RouteGrammar
public meta import Lean.Elab.Command
meta import CasCompiler.RouteGrammar

open CasCompiler.RouteGrammar

private def verify : Except String Unit := do
  let rules := #[
    { lhs := #[0], rhs := #[0, 2] : PrefixRule },
    { lhs := #[0], rhs := #[1] },
    { lhs := #[1, 2], rhs := #[1] }]
  let language ← compile rules #[0] #[#[1]]
  unless language.grammar.shortest == some #[1] && language.grammar.distinctWordCount == 2 do
    throw "the complete growing route language lost its witness or alternative traces"
  for n in [:18] do
    let trace := Array.replicate n 0 ++ #[1] ++ Array.replicate n 2
    unless language.grammar.contains trace do throw "a balanced route is absent"
    let occurrences ← language.reconstruct trace
    unless occurrences[n]?.map (·.outerContext) == some (Array.replicate n 2) do
      throw "a route lost its actual constructor occurrence"
    if n > 0 && language.grammar.contains trace.pop then
      throw "an unbalanced trace was admitted"
  let shadowed ← compile rules #[0] #[#[1], #[0, 2]]
  unless shadowed.grammar.contains #[0] && shadowed.grammar.contains #[1] &&
      !shadowed.grammar.contains #[0, 1, 2] do
    throw "first-binding targets did not stop subsequent source transitions"
  let absent ← compile #[rules[0]!] #[0] #[#[1]]
  unless absent.grammar.shortest.isNone && absent.grammar.distinctWordCount == 0 do
    throw "ungrounded growth was confused with a reachable target"
  let deep ← compile #[{ lhs := #[0, 2], rhs := #[0] }]
    (#[0] ++ Array.replicate 80 2) #[#[0]]
  unless deep.grammar.shortest == some (Array.replicate 80 0) &&
      deep.grammar.distinctWordCount == 1 do
    throw "source routes were truncated at a guessed depth"
  let parallel ← compile #[{ lhs := #[0], rhs := #[1] }, { lhs := #[0], rhs := #[1] }]
    #[0] #[#[1]]
  unless parallel.grammar.contains #[0] && parallel.grammar.contains #[1] &&
      parallel.grammar.distinctWordCount == 2 do
    throw "distinct edge occurrences were merged by their endpoints"
  let initial ← compile #[{ lhs := #[0], rhs := #[0] }] #[0] #[#[0]]
  unless initial.grammar.shortest == some #[] && initial.grammar.distinctWordCount == 1 &&
      !initial.grammar.contains #[0] do
    throw "an initial target did not absorb the empty route"
  let noTargets ← compile rules #[0] #[]
  unless noTargets.grammar.shortest.isNone do throw "an empty target set acquired a route"

run_cmd do
  if let .error message := verify then throwError "{message}"

private def verifyFiniteWords : Except String Unit := do
  let diamond ← compile #[
    { lhs := #[0], rhs := #[1] }, { lhs := #[0], rhs := #[2] },
    { lhs := #[1], rhs := #[3] }, { lhs := #[2], rhs := #[3] }] #[0] #[#[3]]
  let some words := diamond.grammar.finiteWords | throw "a finite route family became infinite"
  unless words.size == 2 && words.contains #[0, 2] && words.contains #[1, 3] do
    throw "finite extraction did not retain the complete diamond"
  for word in words do discard <| diamond.reconstruct word
  let looping ← compile #[{ lhs := #[0], rhs := #[0] }, { lhs := #[0], rhs := #[1] }]
    #[0] #[#[1]]
  unless looping.grammar.finiteWords.isNone do throw "a growing route cycle became finite"
  let dead ← compile #[{ lhs := #[0], rhs := #[0] }] #[0] #[#[1]]
  unless dead.grammar.finiteWords == some #[] do
    throw "an unproductive cycle became an infinite nonempty language"
  let initial ← compile #[{ lhs := #[0], rhs := #[0] }] #[0] #[#[0]]
  unless initial.grammar.finiteWords == some #[#[]] do
    throw "finite extraction lost the empty first-hit route"
  let parallel ← compile #[{ lhs := #[0], rhs := #[1] }, { lhs := #[0], rhs := #[1] }]
    #[0] #[#[1]]
  let some words := parallel.grammar.finiteWords | throw "parallel finite routes became infinite"
  unless words.size == 2 && words.contains #[0] && words.contains #[1] do
    throw "finite extraction collapsed distinct source edges"

run_cmd do
  if let .error message := verifyFiniteWords then throwError "{message}"
