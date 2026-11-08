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

/-- Iterate until the equations themselves stabilize, without a depth or search bound.
Reuse: Lean's equation-preserving tail-recursive partial_fixpoint construction,
https://lean-lang.org/doc/reference/latest/Definitions/Recursive-Definitions/.
From zero the finite saturated counts can rise at most twice per node. The complete
source-closure and tree-count correctness obligations remain separate from this iteration. -/
def RealizationGraph.stabilize (graph : RealizationGraph size)
    (counts : Vector RealizationCount size) : Vector RealizationCount size :=
  let next := graph.step counts
  if next == counts then next else graph.stabilize next
partial_fixpoint

/-- Stable counts for the supplied finite graph, retaining its original adjacency and ordinals.
No provider call, selected execution binding or mathematical judgment is created here. -/
structure GroundedRealizations (graph : RealizationGraph size) where
  private mk ::
  counts : Vector RealizationCount size

/-- Least grounding iteration from zero, as specified by execution contract v2 §5.1. -/
def RealizationGraph.grounded (graph : RealizationGraph size) : GroundedRealizations graph :=
  ⟨graph.stabilize (Vector.replicate size .zero)⟩

/-- Retain the original unique alternative ordinal; zero and many counts remain in counts.
This is graph analysis only. A caller cannot infer noImplementation from an incomplete
source closure, or authorize dispatch from an ordinal without the exact prepared bindings. -/
def GroundedRealizations.uniqueAlternative (result : GroundedRealizations graph)
    (node : Fin size) : Except String (Option Nat) := do
  unless result.counts[node] == .one do return none
  let choices := (graph.alternatives[node].mapIdx fun index children =>
    (index, RealizationGraph.alternativeCount result.counts children)).filterMap fun (index, count) =>
      if count == .one then some index else none
  match choices with
  | #[index] => return some index
  | _ => throw "internal: a unique grounded count has no unique original alternative"

end CasRuntime
