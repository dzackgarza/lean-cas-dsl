module

public import Lean

@[expose] public section

namespace CasCompiler.RouteGrammar

/-- Ground prefix words use exact symbol ordinals supplied by the source adapter.
Algorithm: structural_routes_reference.py at cd3cf75; lean-cas-dsl#66 comment 6693871042.
Reuse: the standard PDA-to-CFG productive-summary construction, AFP Pushdown Systems.
No source stack depth or trace length is bounded by this representation. -/
abbrev Word := Array Nat

structure PrefixRule where
  lhs : Word
  rhs : Word
  deriving BEq, Inhabited

private inductive Letter
  | source (symbol : Nat)
  | bottom
  deriving BEq, Inhabited

private inductive StackSymbol
  | source (symbol summary : Nat)
  | bottom (summary : Nat)
  | start
  deriving BEq, Hashable, Inhabited

private structure Summary where
  source : Nat
  symbol : StackSymbol
  target : Nat
  deriving BEq, Hashable, Inhabited

private structure Production where
  emit : Option Nat
  children : Array Summary
  deriving BEq, Inhabited

structure TraceGrammar where
  private mk ::
  private start : Summary
  private productions : Std.HashMap Summary (Array Production)

private def pushUnique [BEq α] (values : Array α) (value : α) : Array α :=
  if values.contains value then values else values.push value

private structure TargetDFA where
  leading : Array (Array Letter)
  accepting : Array Nat

private def targetDFA (targets : Array Word) : TargetDFA := Id.run do
  let mut leading := #[#[]]
  let mut accepting := #[]
  for target in targets do
    let reversed := ((target.map Letter.source).push .bottom).reverse
    for n in [1:reversed.size + 1] do
      leading := pushUnique leading (reversed.extract 0 n)
    if let some index := leading.findIdx? (· == reversed) then
      accepting := pushUnique accepting index
  return ⟨leading, accepting⟩

private def TargetDFA.step (dfa : TargetDFA) (state : Nat) (letter : Letter) : Nat :=
  if state >= dfa.leading.size then dfa.leading.size
  else (dfa.leading.findIdx? (· == dfa.leading[state]!.push letter)).getD dfa.leading.size

private def TargetDFA.annotate (dfa : TargetDFA) (word : Array Letter) (below : Nat) :
    Array StackSymbol := Id.run do
  let mut result := #[]
  let mut state := below
  for letter in word.reverse do
    result := result.push (match letter with
      | .source symbol => .source symbol state
      | .bottom => .bottom state)
    state := dfa.step state letter
  return result.reverse

private inductive Push
  | none
  | one (first : StackSymbol)
  | two (first second : StackSymbol)
  deriving BEq, Inhabited

private structure Transition where
  source : Nat
  pop : StackSymbol
  target : Nat
  push : Push
  emit : Option Nat
  deriving BEq, Inhabited

private structure Machine where
  nextControl : Nat := 4
  transitions : Array Transition := #[]

private def fresh : StateM Machine Nat := do
  let control := (← get).nextControl
  modify fun machine => { machine with nextControl := control + 1 }
  return control

private def transition (source : Nat) (pop : StackSymbol) (target : Nat) (push : Push)
    (emit : Option Nat) : StateM Machine Unit :=
  modify fun machine => { machine with
    transitions := pushUnique machine.transitions ⟨source, pop, target, push, emit⟩ }

private def pushWord (source : Nat) (pop : StackSymbol) (target : Nat)
    (word : Array StackSymbol) (emit : Option Nat) : StateM Machine Unit := do
  match word with
  | #[] => transition source pop target .none emit
  | #[first] => transition source pop target (.one first) emit
  | #[first, second] => transition source pop target (.two first second) emit
  | _ =>
    let mut control ← fresh
    transition source pop control (.two word[word.size - 2]! word[word.size - 1]!) emit
    for offset in [:word.size - 2] do
      let index := word.size - 3 - offset
      let following ← if index == 0 then pure target else fresh
      transition control word[index + 1]! following (.two word[index]! word[index + 1]!) none
      control := following

private def machine (rules : Array PrefixRule) (initial : Word) (targets : Array Word) :
    Machine := (do
  let dfa := targetDFA targets
  let mut alphabet := #[]
  for word in #[initial] ++ targets ++ rules.flatMap (fun rule => #[rule.lhs, rule.rhs]) do
    for symbol in word do alphabet := pushUnique alphabet symbol
  for index in [:rules.size] do
    let rule := rules[index]!
    let mut matching := #[0]
    for _ in [1:rule.lhs.size] do matching := matching.push (← fresh)
    for position in [:rule.lhs.size] do
      let expected := rule.lhs[position]!
      for summary in [:dfa.leading.size + 1] do
        if position == 0 && dfa.accepting.contains (dfa.step summary (.source expected)) then
          continue
        let top := StackSymbol.source expected summary
        if position + 1 < rule.lhs.size then
          transition matching[position]! top matching[position + 1]! .none none
        else
          pushWord matching[position]! top 0 (dfa.annotate (rule.rhs.map Letter.source) summary)
            (some index)
  for summary in [:dfa.leading.size + 1] do
    transition 1 (.bottom summary) 2 .none none
    for symbol in alphabet do
      let top := StackSymbol.source symbol summary
      transition 1 top 1 .none none
      if dfa.accepting.contains (dfa.step summary (.source symbol)) then
        transition 0 top 1 .none none
  pushWord 3 .start 0 (dfa.annotate ((initial.map Letter.source).push .bottom) 0) none
  : StateM Machine Unit).run {} |>.2

private partial def productiveGrammar (transitions : Array Transition) :
    Summary × Std.HashMap Summary (Array Production) := Id.run do
  let mut finishes : Std.HashMap (Nat × StackSymbol) (Array Nat) := {}
  let mut changed := true
  while changed do
    changed := false
    for rule in transitions do
      let ends := match rule.push with
        | .none => #[rule.target]
        | .one first => finishes.getD (rule.target, first) #[]
        | .two first second =>
          (finishes.getD (rule.target, first) #[]).flatMap fun middle =>
            finishes.getD (middle, second) #[]
      let key := (rule.source, rule.pop)
      let previous := finishes.getD key #[]
      let next := ends.foldl pushUnique previous
      if next.size != previous.size then
        changed := true
        finishes := finishes.insert key next
  let mut productions : Std.HashMap Summary (Array Production) := {}
  for rule in transitions do
    let alternatives : Array (Nat × Array Summary) := match rule.push with
      | .none => #[(rule.target, #[])]
      | .one first => (finishes.getD (rule.target, first) #[]).map fun target =>
          (target, #[⟨rule.target, first, target⟩])
      | .two first second => (finishes.getD (rule.target, first) #[]).flatMap fun middle =>
          (finishes.getD (middle, second) #[]).map fun target =>
            (target, #[⟨rule.target, first, middle⟩, ⟨middle, second, target⟩])
    for (target, children) in alternatives do
      let key : Summary := ⟨rule.source, rule.pop, target⟩
      productions := productions.insert key
        (pushUnique (productions.getD key #[]) ⟨rule.emit, children⟩)
  let start : Summary := ⟨3, .start, 2⟩
  let mut work := #[start]
  let mut cursor := 0
  let mut reachable : Std.HashMap Summary (Array Production) := {}
  while cursor < work.size do
    let key := work[cursor]!
    let alternatives := productions.getD key #[]
    reachable := reachable.insert key alternatives
    for alternative in alternatives do
      for child in alternative.children do work := pushUnique work child
    cursor := cursor + 1
  return (start, reachable)

private partial def shortestTrace (grammar : TraceGrammar) : Option Word := Id.run do
  let mut best : Std.HashMap Summary Word := {}
  let mut changed := true
  while changed do
    changed := false
    for (lhs, alternatives) in grammar.productions do
      for alternative in alternatives do
        if alternative.children.any (fun child => !best.contains child) then continue
        let word := alternative.children.foldl (fun result child => result ++ best.getD child #[])
          (alternative.emit.toArray)
        let improves : Bool := match best[lhs]? with
          | none => true
          | some old => word.size < old.size ||
              (word.size == old.size && compare word.toList old.toList == .lt)
        if improves then
          best := best.insert lhs word
          changed := true
  return best[grammar.start]?

/-- A diagnostic least trace. It confers no mathematical preference among source readings. -/
opaque TraceGrammar.shortest (grammar : TraceGrammar) : Option Word := shortestTrace grammar

private partial def intersects (grammar : TraceGrammar) (states : Nat)
    (accept : Nat → Bool) (step : Nat → Nat → Nat) : Bool := Id.run do
  let mut relations : Std.HashMap Summary (Array (Nat × Nat)) := {}
  let mut changed := true
  while changed do
    changed := false
    for (lhs, alternatives) in grammar.productions do
      for alternative in alternatives do
        let mut edges := (Array.range states).map fun state =>
          (state, alternative.emit.map (step state) |>.getD state)
        for child in alternative.children do
          edges := edges.flatMap fun (source, middle) =>
            (relations.getD child #[]).filterMap fun (left, target) =>
              if middle == left then some (source, target) else none
        let previous := relations.getD lhs #[]
        let next := edges.foldl pushUnique previous
        if next.size != previous.size then
          relations := relations.insert lhs next
          changed := true
  return (relations.getD grammar.start #[]).any fun (source, target) => source == 0 && accept target

private def singletonStep (word : Word) (position letter : Nat) : Nat :=
  if position < word.size && word[position]? == some letter then position + 1 else word.size + 1

/-- Exact membership via grammar intersection with the singleton-word automaton. -/
opaque TraceGrammar.contains (grammar : TraceGrammar) (word : Word) : Bool :=
  intersects grammar (word.size + 2) (· == word.size) (singletonStep word)

/-- Saturated raw trace-word count, not a count of mathematical meanings or grammar parses. -/
opaque TraceGrammar.distinctWordCount (grammar : TraceGrammar) : Nat :=
  match grammar.shortest with
  | none => 0
  | some word =>
    if intersects grammar (word.size + 2) (· != word.size) (singletonStep word) then 2 else 1

structure Occurrence where
  rule : Nat
  source : Word
  target : Word
  outerContext : Word
  deriving Inhabited

structure RouteLanguage where
  private mk ::
  rules : Array PrefixRule
  initial : Word
  targets : Array Word
  grammar : TraceGrammar

/-- Recover each formal source-rule occurrence and its exact constructor suffix. -/
def RouteLanguage.reconstruct (language : RouteLanguage) (trace : Word) :
    Except String (Array Occurrence) := do
  let mut current := language.initial
  let mut occurrences := #[]
  for index in trace do
    if language.targets.contains current then throw "route continues beyond its first binding"
    let some rule := language.rules[index]? | throw "route references an absent source rule"
    unless current.extract 0 rule.lhs.size == rule.lhs do
      throw "source route has a noncomposable prefix"
    let outerContext := current.extract rule.lhs.size current.size
    let target := rule.rhs ++ outerContext
    occurrences := occurrences.push ⟨index, current, target, outerContext⟩
    current := target
  unless language.targets.contains current do throw "source route does not reach a binding"
  return occurrences

/-- Exact finite grammar of all finite first-hit routes for a finite ground-prefix system.
The ordinal of each input rule remains its distinct trace identity. -/
opaque compile (rules : Array PrefixRule) (initial : Word) (targets : Array Word) :
    Except String RouteLanguage := do
  if initial.isEmpty || targets.any (·.isEmpty) ||
      rules.any (fun rule => rule.lhs.isEmpty || rule.rhs.isEmpty) then
    throw "source category words and ground-rule endpoints must be nonempty"
  let (start, productions) := productiveGrammar (machine rules initial targets).transitions
  return ⟨rules, initial, targets, ⟨start, productions⟩⟩

end CasCompiler.RouteGrammar
