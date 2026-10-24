# RX08: explicit selection of the existing module kernel

## Status and scope

**Source proposal clarification only. No runtime outcome, admission, or interpretation-migration approval is claimed.**

`rx08-ordinary-module-kernel.cas.proposal` is a complete additive copy of the seven
original questions in `../rx08-ordinary-kernel.cas`. It changes one binding's public
method name to select the independently specified ordinary module kernel. The
original file, question specification, expected facts, assertion IDs, inventories,
and protected interpretation records remain unchanged. The `.cas.proposal` suffix
keeps this proposal distinct from the fixed `.cas` inventory; these are the same
seven mathematical questions, not seven newly admitted assertions.

The original unqualified source remains a valid ambiguity control. This proposal
does not relabel an unsuccessful interpretation of that source as successful and
does not establish completion of the original 134-question extension review.
The final 287-question interpretation review remains a separate pending task.

This assessment used the independently fixed RX08 question and source, the public
`SPEC.md`, the supplied public API export, and exact upstream mathematical
registrations and definitions. It used no kernel implementation, leaf
implementation, diagnostic, runtime answer, execution report, or build result.
No Lean build, interpreter, or harness was run. Source-only byte comparisons
confirmed all 61 preexisting permitted source and protected-record files unchanged
in both the isolated worktree and the original checkout at verification time.

## Exact source delta and provenance

The isolated source proposal is based on root repository commit
`d9389198eab04b3523783a58333461b249776528`. Original and clarified files have the same
line count, seven identical assertion headers and statements, and identical bytes
except for this binding at **line 14**:

```diff
-let K := projection.ker()
+let K := projection.kernel()
```

| Source | SHA-256 |
| --- | --- |
| `../rx08-ordinary-kernel.cas` | `5bcb0bf768bd231dc93dd81fd4344fd12666145163f1df6327ed6731000ce118` |
| `rx08-ordinary-module-kernel.cas.proposal` | `38a8c9d4fb8145ea337f33d8aa724effae21ae06c616681c89a077ff2311e89f` |
| Supplied public API export, `kernel-mvp-public-api-candidate-546cffae-20261024.json` | `eecf444f9a3f007684c2c494085b02cbe6945b1add5ea90db2da5ad9a33c7612` |

The supplied mathematical source is the published commit
`ae3c76e7a439681ad264a3d1cf113cb55d4f8fcc`, tree
`f63a38cd2bfa245eafe21af351fd6c754dc02e34`, provided at
`/tmp/kernel-public-api-final-producer-20261024/mathematics`. The coordinator
identifies its sources with the independently reviewed checkout
`8c8c32716fd80b26251719e009bde230c8cbd290`, whose same tree was directly recorded
during preparation. The published commit attribution is supplied provenance; this assessment does
not authenticate build artifacts from that source path. Exact declarations,
rather than the API file's label or an output value, ground the interpretation
judgment below.

## Why the unqualified name does not uniquely select the requested result

The complete mathematical requirement remains RX08 in `../../questions.md`,
with the fixed rectangular row and ordinary module arrow from source [M11,M12]:

`p : ModuleCat.of ℚ (Fin 2 → ℚ) → ModuleCat.of ℚ ℚ`, `p(a,b) = a`.

The public registrations expose two distinct operations under `ker`:

| Method row | Owner | Declared functor |
| --- | --- | --- |
| `meth.arrow_ker`, name `ker` | `ArrowsModules` | `fun.arrows_modules.kernel` |
| `meth.group_arrow_kernel`, name `ker` | `ArrowsGroups` | `fun.arrows_groups.kernel` |

The module row is in
`LeanCategories/Catalogue/Semantics/Modules/Operations.lean`, line 655. The group
row is in `LeanCategories/Catalogue/Semantics/Algebra/Subgroups.lean`, line 168.
The structural route from modules to groups is the ordered composite
`fun.modules.fibre_inclusion`, `fun.modules.additive_group`,
`fun.additive_groups.to_groups`. The first two are registered as structural in
`Modules/CatalogueRegistration.lean`, lines 554–563 and 581–587. The last is
registered as structural in `Algebra/Ports.lean`, lines 109–114, and denotes
`AddGrpCat.toGrp`. The Arrow constructor's functorial action is supplied by
`CasCatalogue.Constructors.arrowMap` in `ConstructorRegistration.lean`.
Thus the mathematical structural interfaces also give a route from the selected
whole module arrow to its whole underlying group arrow.

The module kernel has result in `Subobjects(ModuleCat ℚ)`; the group kernel has
result in `Subobjects(Groups)`. Their zero fibers being related does not identify
their complete result categories, scalar structure, or defining inclusions.
No preference for a direct owner, shorter route, registration order, or a later
available method follows from these registrations. The public ambiguity rules
supply no such preference. All of these existing mathematical operations remain
available; this proposal removes or weakens none of them.

The separately registered `mor.sets.matrix_ker`, also spelled `ker`, is
`CasCatalogue.Algebra.LinearAlgebra.ker` in `Algebra/LinearAlgebra.lean`, line 310,
registered at line 488. Its input is a square matrix and its output is a set of
vectors. It does not provide the complete kernel of RX08's selected rectangular
row module arrow.

## Why the clarification preserves the fixed question

`Modules/Bilinear/Valued/Kernels.lean`, lines 296–303, registers
`meth.kernel`, with public name `kernel`, at `ArrowsModules`, using exactly
`fun.arrows_modules.kernel`. Its defining declaration at lines 135–143 is

```lean
kernelDeclaration (R : RingCat) :
    arrowsModulesCategory R ⥤ subobjectsModulesCategory R :=
  LeanCategories.kernelFunctor (ModuleCat R)
```

`LeanCategories/CategoryTheory/OneCat/KernelFunctor.lean` defines that functor's
object to be `Arrow.mk (kernel.ι f.hom)` together with its monicity. It is the
chosen complete categorical kernel with its defining inclusion. The newly
selected surface row and the originally intended module `ker` row therefore
name the same mathematical functor and the same complete result at the same
input arrow.

The `kernel` row has `returnsToSource := true`. Here the input is already an
arrow in its exact owner, `ModuleCat ℚ`; the owner route is the identity. That
flag introduces no formed-module lift for this selection. In particular it does
not turn RX08's projection into the different formed arrow of RX-LIFT. The
original universal negative concerning all target forms remains unchanged.

The complete selected operation is the object action

```lean
(CasCatalogue.Modules.Bilinear.Valued.Kernels.kernelDeclaration Qring).obj
  (CategoryTheory.Arrow.mk projection)
```

where `Qring` and `projection` are the original bindings. This identifies the
mathematics; the proposal uses the already registered public method name and
does not introduce new public syntax or a kernel selection rule.

Public `SPEC.md`, “Registered actions, components, and selected lifts,” supplies
complete ordinary-subobject projections `obj()` and `hom()` and preserves their
original category parameters and defining map. `Modules/Operations.lean`
registers `meth.subobject_dim` at `SubobjectsModules` using the rank of the
subobject domain. Accordingly the unchanged bindings `K.obj()`, `K.hom()`,
`K.dim()`, and the complete zero-composite question retain their required module
meaning. The separate `RestrictToModuleKernel` call, all five of its ordered
inputs, its defining formed inclusion, the complete coordinate admission, and
the full pairing questions are unchanged byte-for-byte.

The smallest clarification therefore selects an existing mathematical operation
without changing any operand, selected map, result interface, expected value,
assertion inventory, or mathematical requirement. Correct reading and execution
of this proposed source require their own independent assessment; this source
change supplies neither.
