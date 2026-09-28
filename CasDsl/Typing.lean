/-
Typing at construction: the registered category a presentation is made in.

A notebook value is a point of a registered `CasCatalogue` category. A value
made by an ascription (`let F := ℤ/4 in Modules(ℤ)`) is a `.point` and carries
its category; any other value is typed once, by the registered typing rules,
from the constructor that produced it — an integer literal is an element of the
euclidean domain ℤ, a polynomial over ℚ an element of a polynomial ring over a
field. When several rules match, the most specific pattern types the value; two
incomparable matches are a registration defect, reported, never ordered.

Typing assigns ONE category. What the value can do is then the registry's
closure of that category (`CasCatalogue.RegistryState.resolveMethod`): nothing
here decides inheritance, transport or availability.
-/
import Lean
import CasDsl.Registry

namespace CasDsl

open Lean

/-- The category a value is constructed in, with its base ring and the classes the typing needs
at the value's denoted domain (verified at a concrete receiver, `verifyTyping`). -/
structure Typed where
  category : String
  base : Option Domain := none
  classes : Array Name := #[]

/-- The category a presentation is constructed in, by the given rules. -/
def typeOfIn (rules : Array TypingRule) (o : Obj) : Except String Typed :=
  match o with
  | .point category base _ => .ok { category, base }
  | _ =>
    let matching := rules.filter (·.pattern.accepts o)
    let minimal := matching.filter fun r =>
      !matching.any fun r' => r'.pattern != r.pattern && r'.pattern.implies r.pattern
    match minimal.toList with
    | [r] => .ok { category := r.category, base := r.base, classes := r.classes }
    | [] => .error s!"{o.presentation} is not constructed in any registered category: no \
typing rule presents it"
    | rs => .error s!"{o.presentation} is typed by incomparable rules \
({", ".intercalate (rs.map (·.category))}): the typing rules are defective here"

/-- The category a value is constructed in. -/
def typeOf (env : Environment) (o : Obj) : Except String Typed :=
  typeOfIn (typingRules env) o

end CasDsl
