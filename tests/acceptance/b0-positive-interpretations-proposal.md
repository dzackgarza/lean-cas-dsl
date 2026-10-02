# Interpretation proposal for the owed executable B0 positives

These are admission proposals for the already required B0 positive questions,
not changes to the original 153 admitted assertions. Mathematical source:
independently reviewed finished candidate `57c85852de8127b9d229878061bfb26c47998814`.
Expected values were independently established in `b0-required-positive-proposal.md`
before inspecting this source release. No candidate computation supplies an answer.

The original `lattices.rank.a2`, `lattices.card.a2` and `lattices.card.a0`
already supply the required A₂ rank and formed-module carrier observations.
The two existing `formed_modules.cas` proposals distinguish the dual carrier
from its value module; their original expected answers remain unchanged.

| Assertion identity | Complete mathematical question |
| --- | --- |
| `b0.lattices.rank.e8` | The Z-module rank of the selected `e8Lattice` object of `IntegralLatticeCat Z`, reached through its actual integral-lattice module functor, equals 8. Its selected form and integral base ring remain attached to the operand. |
| `b0.groups.abelian.cyclic3` | Commutativity holds for the selected group `cyclic(3)=GrpCat.of(Multiplicative(ZMod 3))`. Its group operation is residue addition, displayed multiplicatively. This is a property proposition on that group; it does not refine or retype its carrier. |
| `b0.groups.abelian.symmetric3` | Commutativity of the selected group `symmetric(3)=GrpCat.of(Perm(Fin 3))`, with permutation composition, has Boolean value false. This is not a property of an unspecified operation on its carrier. |
| `b0.groups.kernel.sign.card` | The group kernel of the actual parity map `sign(3):symmetric(3) → cyclic(2)` has carrier cardinality 3, retaining its kernel inclusion into `symmetric(3)` and the kernel cone. The sign value +1 corresponds to group identity in the cyclic target, that is additive residue 0. |
| `b0.groups.kernel.trivial.card` | The group kernel of the actual trivial homomorphism from `symmetric(3)` to `cyclic(2)` has carrier cardinality 6, retaining its inclusion into the selected source and the kernel cone. Its kernel is the whole source, not a newly selected six-element group. |
| `b0.groups.kernel.identity.card` | The group kernel of the actual identity homomorphism of `symmetric(3)` has carrier cardinality 1, retaining its inclusion into that selected source and the kernel cone. |
| `b0.groups.alternating3.card` | The subgroup object `alternating(3)`, the alternating subgroup of the chosen `symmetric(3)`, has carrier cardinality 3 through its structural domain-to-group-to-set route. The defining monomorphism is the element inclusion into `symmetric(3)`. |
| `formed_modules.card.dual_a0` | The carrier cardinality of the selected `rootADual(0)` object of `BilWFormCat Z`, with value module Q and its restricted rational form, equals 1. Cardinality of its value module Q is not the requested observation. |
| `formed_modules.card.dual_a2` | The carrier cardinality of the selected `rootADual(2)` object of `BilWFormCat Z`, with value module Q and its restricted rational form, equals aleph_0. Its actual formed carrier and structural carrier route remain attached to the question. |

Kernel inclusions are retained universal data. Their defining equation in groups
is that composing the inclusion with the specified map yields the trivial
homomorphism, whose value is the group identity. The kernel universal property
uses this same selected map and these same source/target groups. A result missing
the inclusion or using another source group cannot satisfy the declared result
form even when the numerical cardinality is correct. The `Alt(3)` observation
specifically retains the subgroup inclusion interface by construction.

The selected category annotation `in Groups` refers to the named group rows:
it selects `cyclic(n)` rather than the independently chosen ring structure also
displayed as ZMod(n). The declaration and group parameters, rather than
transparent carrier equality, establish this selection.

Nonidentity F₉ transport retains the separately named `first` and `second`
quotient presentations and `quadraticComparison`; its independently established
expected image is the target generator plus its constant 2. The approved
language spelling of generator selection and explicit comparison application
is a remaining source input for its executable assertion. The mathematical
question and expected answer are already fixed in the prior proposal.
