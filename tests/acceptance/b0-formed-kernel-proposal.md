# Fixed B0 formed-kernel positive proposal

This independently authored mathematical question addresses the existing formed
kernel/restricted-form obligation. It is not an exit-trial choice, protected
admission, or computation result. Its source input is independently assessed
candidate `61b110defeab5b6f3042e6473e4356a03124b895`, not a protected-admitted
release. Original assertions and ledgers remain untouched.

## Selected existing mathematical data

Let L be `LeanCategories.Lattices.Valued.e8Lattice.obj`, the existing retained
object of `BilinModuleCat Z Z`. Its module is the selected rank-eight integer
module, and its pairing is the selected E8 Gram pairing. Choose the categorical
identity f:L→L in this fixed-value category. This is a legitimate form-preserving
map: its carrier map is the identity and its value module remains Z.

This does not use `rootAToDual`, which belongs to the different variable-value
category `BilWFormCat Z`. The public `integralLatticeForget` route goes directly
to modules; it must not be described as a registered formed-object view.

The existing declarations `kernelSubmodule`, `formedKernel`, and
`formedKernelInclusion` in
`LeanCategories/Catalogue/Semantics/Modules/Bilinear/Valued/Kernels.lean`
define the underlying module kernel, restriction lift and its inclusion for f.

## Independently fixed expected structured result

For every vector v, f(v)=v, so f(v)=0 iff v=0. Hence the kernel submodule is
exactly {0}, with its usual inclusion into the very selected L. Its carrier has
one element, but that count alone is not the positive's meaning.

The lifted object retains scalar ring Z and value module Z. Its restricted form
is B_K(u,v)=B_L(i(u),i(v))=B_L(0,0)=0. Its inclusion sends its unique vector to
the zero vector of L and preserves that exact restricted pairing. The composite
of its underlying inclusion with the underlying f is the zero module map.
Every module map h:T→U(L) with U(f)∘h=0 has h=0 and factors uniquely through
the zero kernel. Alternative kernel representations must compare over U(L),
and their forms must be the pullback of L's selected form along that comparison.
The lift comparison relates the actual module-kernel inclusion to the formed
restriction inclusion. Replacing the value module by the zero module is not
the specified lift, even though all pairings are zero.

This is the lift of a module kernel. No categorical zero map or categorical
kernel in the fixed-W formed category is assumed: arbitrary zero carrier maps
are not form-preserving on nonzero forms.

## Executable mathematical question and surface dependency

`b0_formed_kernel_question.lean` gives a Lean proposition using only these public
mathematical declarations. It fixes L, f, the carrier equation, inclusion and
selected restriction pairing before any candidate computation. It contains no
candidate-generated expected value and no proof/admission claim.

The current public registry has no named fixed-W object row exposing
`e8Lattice.obj`, no named fixed-W identity morphism row, and no documented DSL
syntax comparing a formed kernel's inclusion and pairing. A candidate DSL
assertion cannot therefore be faithfully asserted merely by spelling
`kernel(id(E8))`: E8's selected catalogue category is integral lattices, and a
missing formed view/lift cannot be supplied by transparent carrier matching.
The actual remaining surface dependency is a generic documented way to select
this existing formed object and identity, and to state its retained inclusion
and pairing conditions. This proposal supplies the exact mathematical question
for that surface, rather than substituting a carrier cardinality assertion.

## Subsequently supplied formed-view exposure

Independently source-assessed candidate
`d75f8cc7b3e4d7d9f385bd992743bcfd52290bb0` now exposes the actual structural
inclusion of integral lattices into `BilinModule(R,R)` via `isLattice(R,R).ι`.
Inspection of its public mathematical diff identifies the E8 image with the
same existing `e8Lattice.obj` selected above, retaining its negative Gram
pairing and W=Z. Its subsequent module forget is compared with the earlier
direct carrier route by the actual `Iso.refl` comparison. Thus the selected
formed-view exposure dependency described above has progressed; the existing
mathematical choice and expected structured result are unchanged.

The public fixed-value catalogue still does not name its identity, pairing
observation or formed-kernel defining inclusion as morphism/method rows.
Language-author confirmation of generic `kernel(f)` does not itself expose
these absent mathematical rows. A faithful executable structured DSL question
still needs those public mathematical interfaces and their documented generic
application syntax. This source finding is submitted for independent interface
assessment; it is not authority to fabricate rows or mark a count-only assertion
as the structured positive.
