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

## Exact remaining public DSL dependencies

The public d75 metadata identifies `fun.integral_lattice.forget_form` as the
actual integral-lattice-to-fixed-value-formed functor. However `cat.bilin_module`
has no public category display name and requires both R and W; ordinary
`X in <registered category>` does not currently document a way to select this
precise dependent fibre and its functor image. In particular a carrier match
does not define `L`.

The language author proposes the generic surface
`view E8 along fun.integral_lattice.forget_form`, with full source inference
and the exact registered functor node. This would denote the already chosen
L, not a new E8 object. It is a proposal pending approved documentation and
implementation; it is not currently an executable acceptance assertion.
Likewise a generic categorical `id(L)` must select the identity in this formed
category. The current named `id` morphism row is group identity, so its display
name alone does not supply the required formed identity.

Once those generic forms are supported, the intended request begins with
`let L := view E8 along fun.integral_lattice.forget_form`,
`let f := id(L)`, `let K := kernel(f)`. This prospective prefix alone still
does not express the full observation: the kernel must return the lifted formed
subobject and its defining inclusion i:K→L, retaining W=Z, rather than only the
underlying module subobject. Public fixed-W inclusion and pairing observations
must expose the exact mathematical data so the existing equations
`i(x)=x`, `B_K(x,y)=B_L(i(x),i(y))=0`, and `U(f)∘U(i)=0` can be stated with
declared argument types. The existing group inclusion method cannot silently
stand for the absent fixed-W formed inclusion interface.

No `.cas` assertion is added using this presently unsupported surface. The
preauthored Lean mathematical question has been typechecked by the separately
assigned compiler, but that does not establish DSL expressibility or execution.
The actual remaining mechanisms are generic registered-functor selection,
categorical identity in the selected fibre, and the public typed observations
of the lifted inclusion and restricted pairing. This is the same fixed positive,
with its independently established kernel zero and retained Z-valued form.

## Newly assessed observation rows and remaining application mechanisms

Independently source-assessed mathematical candidate
`5a0e13d3d306c4363d163a5d02257995d13cefd0` supplies the missing public
mathematical observations. Its 441-row metadata SHA-256 is
`82af944fb4c1660c96bb7ff84e908a9db51f1ac95a7ece906ea00045d10306a1`.
The category name `Bil` denotes the fixed-W family, distinct from `BilWForm`.
`fun.subobjects_bilin_module.domain` exposes the formed domain;
`fun.subobjects_bilin_module.inclusion` and `meth.bilin_module.inclusion`
expose the stored full arrow with both formed endpoints. The named morphism
`pairing(R,W,L)` has exact type L.carrier×L.carrier→W, with R a selected
commutative ring, W its actual module and L its actual W-valued formed object.
These rows close the earlier public mathematical exposure finding. Protected
admission is still pending; no candidate outcome establishes this comparison.

The language author confirms the generic view and categorical-identity surface
is now approved/documented in `specs/reuse/cc-dsl-language.md`. It permits the
following fixed mathematical request prefix:

```text
let L := view E8 along fun.integral_lattice.forget_form
let f := id(L)
let K := kernel(f)
let D := view K along fun.subobjects_bilin_module.domain
let i := K.inclusion()
```

This prefix fixes the exact request but is not the complete structured
assertion. Independent expected observations remain those authored above.
Language-author assessment identifies three remaining generic application
mechanisms: pairing must recover the actual chosen ModuleCat W from L's full
dependent type and check any explicitly supplied carrier through its genuine
module forgetful image; a bare set Z cannot invent that module. The stored
inclusion is an Arr(Bil) object and needs actual arrow projection/application,
not reinterpretation as an arbitrary map between equal carriers. Finally, the
zero element of D must be supplied by its selected module/additive structure,
not guessed from a literal's carrier type. The universal/all-vector observation
must then retain these exact typed data and the restricted pairing equation.

Until those generic applications are supported, `pairing(Z,Z,D)` and applying
`i` to a guessed zero are not claimed executable assertions. No cardinality-only
substitute is added. Mathematical exposure and supported selection syntax have
progressed while the same original structured formed-kernel positive remains
open at the application boundary.

The subsequently supplied independently assessed e03 public metadata (442 rows,
SHA-256 `d6c0b03271fd0a51d44dbf9c4fd6c958e383e587a756f60aceea988639074b7d`)
exposes `op.modules.zero` as the actual selected-module operation
`zero(R : RingCat, M : ModuleCat R) : PUnit → M`. Thus the mathematical zero
exposure is now present. Its use must retain the selected kernel's actual
carrier module and scalar ring through the formed-module forgetful route.

Language-author-approved prospective observations are `D.pairing()` with whole
dependent inference of its actual R/W/L, and `K.inclusion().hom()` extracting
the actual arrow before application. These generic mechanisms are still under
implementation/compilation; their approval is not evidence of an executable
structured assertion. The existing zero-kernel inclusion/restriction meanings
are unchanged, and full all-vector equations remain the positive's observation.

## Full structured observation authored for execution

`b0_formed_kernel.cas` now states the unchanged selected E8 identity-kernel
question using these public interfaces. It observes the actual defining
inclusion, its composite with the selected identity, and the restricted pairing
on **every ordered pair** of kernel vectors. For the pairing observations it
forms the actual carrier set through the registered formed-module forget,
module fibre inclusion and module underlying-set functors. The product of that
set with itself supplies its actual two defining legs. One free generalized
element of this product therefore covers all ordered pairs; a diagonal pairing
test would not suffice.

Both pairings retain their actual selected formed receivers. Their equality
states `B_D(u,v)=B_L(i(u),i(v))`; the separate zero equality has the unchanged
selected value carrier Z. The inclusion equations use zero in the selected L,
so no ambient scalar or value module is replaced to obtain a result.

The independently authored Lean question also now includes the previously
specified module universal property: for every module T and h:T→U(L) annihilated
by U(f), there exists a unique k:T→U(D) whose composite with U(i) is h. The
surface language currently has no quantification over arbitrary module objects
and maps. This condition remains part of the full question and of reconstruction
of the actual universal construction; the four executable observation proposals
do not remove it or count a carrier cardinality as its replacement.

The new sources await their actual typecheck/reader/execution assessment. No
result or protected admission is claimed here, and original assertions and
permanent ledgers are unchanged.

## Exact universal-factorization acceptance boundary

The five proposed `.cas` observations (cardinality, inclusion zero, restricted
pairing, pairing zero and defining condition) do not themselves state universal
factorization. Their generalized-element equations range over the actual
carrier or its product. They do not range over arbitrary selected modules and
module maps. This distinction is mathematical, independent of any implementation
or reported computation.

For the same fixed selected L, f, formed domain D and defining inclusion i, the
remaining proposition is exactly:

```text
For every T : ModuleCat Z and h : T -> U(L),
  if U(f) composed with h is the zero module map,
  there exists a unique k : T -> U(D)
  such that U(i) composed with k equals h.
```

`b0_formed_kernel_question.lean` already states this proposition with full
selected objects and maps. The condition is in modules, where zero maps and
kernels are defined; it is not a demand for a zero morphism or categorical
kernel in Bil(Z,Z). The original source requirement also retains the comparison
between the module kernel and the formed restriction, so a factorization through
an unrelated singleton carrier would not state this proposition.

The approved language describes application of registered families, structural
views, identities and composition, generalized carrier elements, registered
binders and the actual defining construction legs. It does not presently
document a way to quantify over arbitrary module objects and maps, assert unique
existence of the corresponding factorization, or apply a public mathematical
universality observation to this complete chosen construction. Thus no faithful
additional `.cas` factorization assertion is authored by assuming such syntax.

The precise remaining acceptance interface must express or consume this
existing full mathematical proposition for U(D), U(i), U(L) and U(f), preserving
the actual module category, zero-map condition and uniqueness. Any public
mathematical observation used for it must be the already formal universal
construction with its defining inclusion and lift comparison. A count, a
single example T/h, a carrier-equivalent zero object, or a form-preserving-map
factorization in the wrong category does not replace the specified universal
module proposition. This identifies a mathematical language/exposure dependency;
it does not report a computational outcome or protected admission.

## Existing public universal API for the actual reconstructed result

No new mathematical predicate or quantifier notation is needed to state the
full observation on the formal acceptance side. The public generic declarations
are already sufficient:

* `CategoryTheory.Limits.IsKernel.isoKernel` in Mathlib
  `CategoryTheory/Limits/Shapes/Kernels.lean` takes an actual limit kernel fork
  `s : KernelFork f`, its `IsLimit s`, an actual proposed inclusion `l : Z -> X`,
  and an isomorphism `e : Z ≅ s.pt` satisfying `e.hom ≫ Fork.ι s = l`. It yields
  `IsLimit (KernelFork.ofι l ...)` for that very inclusion.
* `CategoryTheory.Limits.Fork.IsLimit.existsUnique` in Mathlib
  `CategoryTheory/Limits/Shapes/Equalizers.lean` takes `hs : IsLimit s`,
  `h : T -> X` and `h ≫ f = h ≫ g`. It yields
  `∃! k : T -> s.pt, k ≫ Fork.ι s = h`.

For this fixed observation, instantiate the category as `ModuleCat Z`,
`f = U(selectedMap)`, `Z = U(actual reconstructed D)` and
`l = U(actual reconstructed i)`. The comparison e and its defining equation
must concern those actual returned structures over the fixed selected U(L).
The public `MonoLift.iso` and `MonoLift.fac` specify exactly the lifted base
identification and defining equation for the prescribed restriction lift.
They can be composed with the checked comparison of the actual module kernel;
canonical object or inclusion fields cannot replace the actual reconstructed
ones. With `g = 0`, the annihilation condition supplies `h ≫ f = h ≫ 0`, so
`Fork.IsLimit.existsUnique` states precisely the preauthored factorization.

`b0_formed_kernel_question.lean` now provides
`reconstructedUniversalQuestion(D,i)` to instantiate that unchanged universal
observation at actual reconstructed formed data. Its helper is only an
application of the existing public `Fork.IsLimit.existsUnique` theorem to an
`IsLimit` premise on the actual inclusion. Such a premise must be independently
checked formal reconstruction evidence, never a leaf-supplied proof or a
claim about its own output. The source has not been newly typechecked while
the designated compiler is occupied, and no execution or admission is claimed.

The remaining limitation is connecting the permanent mathematical observation
to those actual reconstructed full values and their checked universal
comparison through the acceptance interface. Lack of textual quantifier
notation alone is not a reason to request new upstream mathematics or abandon
the existing formal universal API.
