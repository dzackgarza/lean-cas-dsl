# Reuse record: `cc-dsl-language`

## Queries
`formalization_corpus.py search`:
- "custom syntax category DSL elaborator declare_syntax_cat": no owner;
- "parse external file runParserCategory": a file-extraction tactic (tcslib), no owner;
- "surface notation registry name lookup": no owner.

The language authors no mathematics. Every name it accepts is a catalogue row's surface name
(`lc-api-names`), and every literal is a catalogue literal (`lc-api-literals`).

## Owner
- Lean's `declare_syntax_cat`, `Parser.runParserCategory` and term elaboration.
- The catalogue rows (`lean-categories`), and the kernel's resolution of methods, objects and
  limits (`method%`, `obj%`, `limit%`).

## New code, and why no dependency supplies it
The syntax category of SPEC.md's statements and its elaboration through the catalogue.

## Compositional application and selected identity

The reader's `applyFamily` starts from the registered declaration's dependent telescope. Supplied
structure parameters are read at their declared types, numeral and map parameters are checked at
their own positions, and the operands must reach the declared source through their actual typed
objects and admitted inclusions. The result is the complete declaration application, including
implicit arguments, instances, maps, and established closed hypotheses. Unresolved parameters or a
type-incorrect complete application are rejected. A requested result object constrains that same
application; it does not license a replacement operation or a guessed structure on its carrier.

Source inference first matches a registered source declaration's ordered arguments against
the actual source application. Retained nested arguments can supply their complete selected
objects directly or through their registered refinements. A speculative joint assignment is
committed only when every explicit parameter, the complete declaration application, and all
actual source endpoints are closed and type correct. Distinct compatible complete parameter
witnesses remain ambiguous. This prevents a requested result object from replacing an operand's
coefficient structure merely because their carriers permit a conversion.

Each successful local application therefore composes the retained operand maps with one accepted
typed arrow. The binder rule composes these same applications with its declared domain and
admission; it has no independent arithmetic or analysis interpretation. The argument is local and
compositional: a larger expression is formed only when each operand, parameter, source map, and
selected arrow supplies the premise required by its enclosing application.

Selected object identity is retained separately from a carrier. A value keeps its exact object,
category, named declaration and ordered parameters when present, and the chosen structured value
when viewed through a carrier. A declaration match identifies its own registered object before
carrier unfolding is considered. Distinct declaration identities are not made interchangeable by
a definitional equality of their carriers. Anonymous structures supplied by an accepted
declaration remain exact typed bundled values; absence of a separate named row does not justify
replacing them with a named refinement.

Structural parameter transport uses actual registered functor routes. The selected source remains
in the trace with the route and target category; route comparison consumes the admitted cells and
propagates ambiguity. Registered presentation syntax similarly retains the chosen isomorphism's
complete parameters, orientation, actual source and target, and applied argument. Its carrier map
is the action of the admitted route on that actual isomorphism arrow. A shared carrier or an
identity-shaped backend value cannot substitute for these selected data.

When the demanded category lies on a named refinement's declared carrier route to the exact
set, acquisition uses those route prefixes. Otherwise it checks the registered incoming routes
against complete structured images, retaining ambiguity between distinct images. A selected
named structure also uses declared prefixes when available. This retains the declared
operation: an additive-to-multiplicative relabelling elsewhere in the category graph does not
replace the multiplication selected by a ring's carrier refinement. Route choices are first
resolved within each source through admitted comparisons. Different incoming source declarations
are merged only when their complete objects at the expected structured type are definitionally
identical, with a kernel-checked equality proof for every image. The trace retains every source,
full parameter list, chosen route, complete carrier route, registered refinement identifications,
and typed image. The deterministic representative affects serialization alone; distinct full
structures remain ambiguous even when their carriers coincide.

The approved quotient-arithmetic notation `ℤ/n` denotes the public ring object
`obj.rings.integers_mod`, whose declaration is `NamedRings.ringIntegersMod n`.
Its refinement to `obj.sets.integers_mod` specifies the multiplicative `ringsToSets`
route and `ringIntegersModIdentification`. The reader instantiates that full ring at
the declared parameter, then exposes its carrier while retaining the ring, route and
identification. An explicit requested category converts this chosen object through
the existing checked structural interface. The same carrier's separately selected
additive group or monoid does not replace the quotient ring's multiplication; different
complete structures still remain ambiguous. This follows the notation's mathematical
source definition and does not select a structure by carrier equality or by the operation
later applied to it.

A dependent structure parameter may also be supplied by a registered declaration whose actual
structural forgetful image is the operand's selected structure. This comparison is at the bundled
structure, never just at its set carrier; distinct compatible declarations remain ambiguous. A
remaining morphism parameter is inferred only after its complete endpoint type is fixed, from a
unique registered declaration with all arguments determined. Its actual application remains in the
trace, so a coefficient map is not replaced by an unrelated inclusion of underlying sets.

A distinguished generator binds a variable locally inside an explicitly written selected object.
The binding comes from that object's generator declaration, respects existing external bindings,
and removes only those local occurrences from free-variable collection. Distinct presentations
may consequently use the same written variable name while retaining distinct generator values.

The explicit object-action surface is `view X along F` or `view X along F(a₁,…,aₙ)`.
Here `F` is the complete public registered functor identifier, including its dotted components;
the parenthesized arguments supply its declaration's explicit binders in declaration order.
The selected object `X` must belong to the declared source category. The reader uses its actual
complete object type to infer remaining parameters, synthesizes the declared instances and
establishes closed obligations, and rejects any unresolved parameter. It applies that exact
registered declaration and retains its complete chosen arguments, source object, target category,
and actual image. No default functor or inverse to a forgetful map is inferred.

`id(view X along F)` is the categorical identity of the actual selected image. A registered
kernel or other limit applied to that identity uses its actual category, diagram, and chosen
limit declaration. Observing an inclusion or pairing requires the corresponding public
registered observation; the view surface does not invent one. The object value retains the
original supplied value, actual source, ordered edges and complete action arguments, and every
checked full source presentation even when semantic reading runs without a trace. A structural
view may recover a named carrier only through its declared refinement and checked route suffix;
a general functor image obtains its own carrier through its actual target structure.

`K.leg(n)` selects the defining cone leg of the actual registered construction `K`.
The ordinal `n` is interpreted at the complete diagram-index type: finite enumerations use
their actual declaration constructor order, with every constructor nullary after its full
parameters are instantiated; `Fin` uses its actual bound. Unresolved parameters, recursive
constructors, and out-of-range indices are rejected. The resulting arrow retains the actual
apex, diagram, typed index, and creation lift. Reading without a trace validates the same
registered construction presentation. For a parallel-pair kernel, index `0` selects its
source leg; this follows the actual shape declaration rather than a kernel-specific rule.

These invariants describe the reader's composition of accepted premises. They do not establish
mathematical input completeness, backend implementation, result reconstruction, or final B0
acceptance; those are independently required by the owning computational-core plan.

Registered name calls are resolved by complete argument signatures across object, morphism,
method, and construction rows. A candidate is discarded only when its declared signature is
inapplicable; unresolved semantic ambiguity survives. Construction applicability is checked
at the actual receiver category before building its diagram. Multiple applicable complete
signatures remain ambiguous, including signatures returning different categories.

Registered admission evidence receives a definitionally equal presentation of its original
complete target. Closed chosen class dictionaries may use another same-class presentation
only after kernel conversion checks equality of the entire supplied dictionary. Predicate
heads and chosen data remain fixed; the same registered evidence procedure runs once. Its
closed result is checked at the original target, including Type-valued admission witnesses.
Different structures on one carrier cannot pass the full dictionary equality check.

Structural traces retain the exact ordered complete edge applications constructed with the
source and endpoint constraints. Parameter equivalence records every source presentation,
its complete applications, and its full image identity; replay does not infer new parameters
from a route identifier.

Carrier presentation exposure preserves ordinary semireducible type heads: actual closed
structure and class data may be exposed fully, while their carrier aliases use reducible
projection exposure. This retains the declared carrier presentation needed by registered
evidence rather than unfolding a type alias into an implementation datatype. The complete
original target and returned witness are still checked by kernel conversion.
