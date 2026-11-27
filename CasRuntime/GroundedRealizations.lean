module

public import Lean

@[expose] public section

namespace CasRuntime

/-- Saturated multiplicity of distinct finite grounded realization trees. -/
inductive RealizationCount
  | zero | one | many
  deriving BEq, DecidableEq, Inhabited, Repr

/-- Distinct alternatives add, even when their denotations or dependency lists coincide.
Reference: Goodman, Semiring Parsing (1999), https://aclanthology.org/J99-4004/;
the specific saturated equation is execution contract v2 §5.1, issue 69 comment 6664277464. -/
def RealizationCount.add : RealizationCount → RealizationCount → RealizationCount
  | .zero, count | count, .zero => count
  | _, _ => .many

/-- Every ordered prerequisite occurrence must have a grounded realization. -/
def RealizationCount.multiply : RealizationCount → RealizationCount → RealizationCount
  | .zero, _ | _, .zero => .zero
  | .one, count | count, .one => count
  | .many, .many => .many

/-- A structurally finite AND/OR graph with fixed child demands.
Each row is an OR node; its alternatives contain ordered AND prerequisite occurrences.
An empty alternative is grounded. Its row/alternative ordinal retains its distinct identity.
Finite indices exclude missing child nodes. Source lowering must separately establish that
this graph includes the complete actual demand closure; this type does not assert that claim. -/
structure RealizationGraph (size : Nat) where
  alternatives : Vector (Array (Array (Fin size))) size

/-- Product of prerequisite counts in their original occurrence order. -/
def RealizationGraph.alternativeCount (counts : Vector RealizationCount size)
    (children : Array (Fin size)) : RealizationCount :=
  children.foldl (fun count child => count.multiply counts[child]) .one

/-- One simultaneous generation of the exact saturated grounding equations.
Recompute from the preceding generation; accumulating an old count would count a tree twice. -/
def RealizationGraph.step (graph : RealizationGraph size) (counts : Vector RealizationCount size) :
    Vector RealizationCount size :=
  Vector.ofFn fun node => graph.alternatives[node].foldl
    (fun count children => count.add (RealizationGraph.alternativeCount counts children)) .zero

/-- Simultaneous zero-seeded approximation at a fixed finite tree height. -/
def RealizationGraph.atHeight (graph : RealizationGraph size) : Nat → Vector RealizationCount size
  | 0 => Vector.replicate size .zero
  | height + 1 => graph.step (graph.atHeight height)

/-- Stable counts for the supplied finite graph, retaining its original adjacency and ordinals.
No provider call, selected execution binding or mathematical judgment is created here. -/
structure GroundedRealizations (graph : RealizationGraph size) where
  height : Nat
  counts : Vector RealizationCount size
  generated : counts = graph.atHeight height
  fixed : graph.step counts = counts

/-- Iterate until the equations stabilize, retaining checked generation and fixed-point proofs.
Reuse: Lean's equation-preserving monadic partial_fixpoint construction,
https://lean-lang.org/doc/reference/latest/Definitions/Recursive-Definitions/.
There is no depth or search bound. Nontermination is not a zero count. Source-demand closure,
universal termination and the realization-tree interpretation remain separate obligations. -/
def RealizationGraph.stabilize (graph : RealizationGraph size) (height : Nat)
    (counts : Vector RealizationCount size) (generated : counts = graph.atHeight height) :
    Option (GroundedRealizations graph) :=
  if fixed : graph.step counts = counts then
    some ⟨height, counts, generated, fixed⟩
  else graph.stabilize (height + 1) (graph.step counts) (congrArg graph.step generated)
partial_fixpoint

/-- Least grounding iteration from zero, as specified by execution contract v2 §5.1. -/
def RealizationGraph.grounded (graph : RealizationGraph size) : Option (GroundedRealizations graph) :=
  graph.stabilize 0 (Vector.replicate size .zero) rfl

/-- Retain the original unique alternative ordinal; zero and many counts remain in counts.
This is graph analysis only. A caller cannot infer noImplementation from an incomplete
source closure, or authorize dispatch from an ordinal without the exact prepared bindings. -/
def GroundedRealizations.uniqueAlternative {size : Nat} {graph : RealizationGraph size}
    (result : GroundedRealizations graph)
    (node : Fin size) : Except String (Option Nat) := do
  unless result.counts[node] == .one do return none
  let choices := (graph.alternatives[node].mapIdx fun index children =>
    (index, RealizationGraph.alternativeCount result.counts children)).filterMap fun (index, count) =>
      if count == .one then some index else none
  match choices with
  | #[index] => return some index
  | _ => throw "internal: a unique grounded count has no unique original alternative"

end CasRuntime
