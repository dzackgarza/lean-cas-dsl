# Existing computation: leaf registrations and kernel evaluation

This document is an inventory of the computation that the system does today. It gives each leaf registration with its engine routine, the catalogue category that owns each operation, the evaluation that the kernel does itself, the protocol state of the backends, and the rules that the leaves repository gives to leaf authors. It is a snapshot of the revisions in "Sources". It changes no file of a repository.

## Sources

| Name | Repository and ref | Revision | Use in this document |
| --- | --- | --- | --- |
| LEAVES | `lean-cas-dsl-leaves`, export of `main` | `8b181d7` | Registrations, backend programs, author rules. The export is equal to `origin/main` of the local clone, file by file (SHA-1 of each file). |
| CONTRACT | `lean-cas-dsl-leaf-contracts`, export of `main` | `ef3771d` | Catalogue `api/declared-ports.json`, manifest rules, v1 SDK. The export is equal to `origin/main` of the local clone, file by file. |
| Catalogue | `api/declared-ports.json` of CONTRACT | mathematics `3f8aedf`, protocol `fcefc8b`, kernel `695210e` (its `provenance`) | Owner category of each operation and of each input form. |
| Contract kernel branch | `lean-cas-dsl-leaf-contracts`, `integration/kernel-v1-20261106` (local clone) | `a0417b0` | v2 SDK. The kernel branch of `lean-cas-dsl` pins this revision in `lake-manifest.json`. |
| MAIN | `lean-cas-dsl`, `main` | `a9f3790` | `specs/001-categorical-research-language/tasks.md`, `contracts/computational-runtime.md`. |
| Kernel branch | `lean-cas-dsl`, `integration/kernel-v1-20261106` | `447469b` | Kernel source, read with `git show`. |

### What was read

| Material | Coverage |
| --- | --- |
| LEAVES: `leaves.json`, `AGENTS.md`, `README.md`, `DEFECTS.md`, `INTENT.md`, `justfile`, `lakefile.toml`, `CLAUDE.md`, `.gitignore`, `.github/workflows/ci.yml`, the 13 files of `backends/`, the 8 files of `specimens/` | Each file in full (31 files). |
| CONTRACT: `README.md`, `api/README.md`, `api/manifest.md`, `api/kernel-service.md`, `python/cas_port.py` | Each file in full. `INTENT.md` is byte-identical to the LEAVES copy. |
| CONTRACT: `api/declared-ports.json` | All records of `operations` (502), `inputForms` (717), `objects` (124), `functors` (106), `categories` (96), `cells`, `lifts`, `constructions`, `edgeActions`, and the `registeredMetadata` of the 608 `entries`, by program. The signatures and docstrings were not read. |
| CONTRACT: `api/extension-ports.json` | The id inventories only, compared with `declared-ports.json` by program. |
| CONTRACT: `api/wire-examples.md`, `CasContract/*.lean`, `AGENTS.md`, `tools/`, the two JSON schemas | Not read. `CasContract/Port.lean` was searched for the protocol markers only. |
| Contract kernel branch: `api/python-sdk.md` | In full. `python/cas_port.py` lines 1-20 and 798-869, `python/cas_session.py` lines 1-50, 380-410 and 600-630, `pyproject.toml`, and the diff of `api/manifest.md`, `api/manifest.schema.json`, `README.md`, `api/kernel-service.md` against contract `main`. |
| MAIN: `tasks.md` | Lines 1-214 in full, which include the table "Kernel computation (C22)", and each other line that names `Evaluation`, `Decide`, `Codec`, `whnf` or `benchmark-leaves`. Lines 215-648 were not read in full. |
| MAIN: `contracts/computational-runtime.md` | In full. |
| Kernel branch: `CasCatalogue/Evaluation.lean`, `Decide.lean`, `Codec.lean`, `CasCompiler/ReadSubsetNotation.lean` | Each file in full. |
| Kernel branch: `CasCompiler/Lower.lean` (212-232, 296-322, 385-400, 512-560, 862-920, 1180-1220, 2060-2130), `CasRuntime/Session.lean` (176-206, 262-300), `CasRuntime/Literal.lean` (1-60, 96-130), `CasCompiler/SourceNumeral.lean` (30-62), `ReadGraphRules.lean` (40-79), `SourceAdmission.lean` (56-160), `SourceLimit.lean` (396-426), `SourceRing.lean` (40-80) | The stated line ranges only. |

### Terms

A **registration** is one record `(operation, input, backend)` of `leaves.json`.

The **owner category** of an operation is the category that the catalogue records for it. The id of an operation does not always contain the owner: `meth.cardinality`, `prop.is_finite` and `cmp.f9.translation` have no category component. The next table gives the rule for each family of address.

| Family of address | Owner category taken from |
| --- | --- |
| Method (`meth.*`) | The `owner` field of the method row. |
| Property (`prop.*`) | The host category of the classifier that the property row names. |
| Element operation (`op.*`), named morphism (`mor.*`), binder (`bind.*`), limit or colimit (`lim.*`, `colim.*`) | The `category` field of the row. |
| Functor action (`fun.*`, `fun.*#map`) | The source category of the functor. |
| Presentation comparison (`cmp.*`) | The category of its source object. |
| Lift field (`lift.*#field`) | The base category of the source arrows of the lift (`cat.arrows_bilin_module` gives `cat.bilin_module`). |
| Cell component (`*#component`) | The source category of the cell. |
| Object application (`obj.*#application`) | The category of the object. |
| Direct construction (`con.*`, `con.*#map`) | The target category. The source is $\mathrm{Core}(C)$ for a category parameter $C$. |
| Classifier-forget and constructor-induced action (`action:...`) | The source category of the action. |

An owner written `total(clf.X)` is the total category of the classifier `clf.X`; the catalogue has no `cat.` row for it. The owner `fam.modules(S)` is the family `fam.modules` at the parameter `S`; `cat.modules_r` is the same family at `R`.

The **input-form category** is the `category` field of the input form in `inputForms`.

The column **Hand-rolled** has four values.

| Value | Meaning |
| --- | --- |
| `no` | An engine routine computes the answer. The leaf translates the input and the output. |
| `partial` | An engine routine computes one part. The leaf computes another part of the answer in Python. |
| `yes` | The leaf computes the answer in Python. The engine supplies containers only. |
| `lookup` | No engine computation gives the answer. The leaf answers a catalogue name, a literal of its source, or a part of its input. |

The column **Mathematics held in the leaf** records a mathematical datum, definition, convention or table that the leaf source contains. `AGENTS.md:92-93` of LEAVES says that a leaf ships no mathematics.

## Counts

| Quantity | Count |
| --- | --- |
| Registrations in `leaves.json` | 115 |
| Backend programs in `leaves.json` | 11 |
| Engines | 2 (Sage; GAP through Sage `libgap`) |
| Distinct operations with a registration | 38 |
| Distinct input forms | 43 |
| Operation addresses in the catalogue (`operations`) | 502 |
| Catalogue addresses with a registration | 38 |
| Catalogue addresses with no registration | 464 |
| Named objects in the catalogue (`objects`) | 124 |
| Named objects that are the input form of a registration | 34 |
| Registered categories in the catalogue (`categories`) | 96 |
| Owner categories with a registration | 7 |
| Registrations, hand-rolled = no | 102 |
| Registrations, hand-rolled = partial | 4 |
| Registrations, hand-rolled = yes | 2 |
| Registrations, hand-rolled = lookup | 7 |
| Registrations with mathematics held in the leaf source | 75 |

## Main findings

1. Of 115 registrations, 54 compute the cardinality or the finiteness of a carrier (`meth.cardinality` 30, `prop.is_finite` 24). The catalogue gives both operations to `cat.sets`. The registrations are in 8 programs, on input forms of 9 categories.
2. The catalogue gives 81 of the 115 registrations to `cat.sets`. No registration belongs to `cat.groups`, `cat.rings`, `cat.semirings`, `cat.monoids` or `cat.linear_orders`. No element operation (`op.*`, 21 addresses) has a registration. The product $2 \cdot 3$ in $\mathbb{Z}$ has no registered implementation.
3. Two registrations hand-roll the algorithm: `lim.sets.pullback` and `lift.bilin_module.restrict#obj`. Four are partial. Seven answer with no engine computation of the result; `colim.bil_w_form.cokernel` is one of them.
4. Five programs execute catalogue operations, or the composition of morphisms, inside handlers of other operations, with no registration: ring arithmetic on points (`op.rings.*`, `op.semirings.*`), named group arrows (`mor.groups.sign`), named real and complex maps, one functor action on morphisms, and composition of morphisms.
5. The Gram matrix of $A_n$ is written in three programs. The ranks of $A_n$ and $E_8$ and the two defining polynomials of $\mathbb{F}_9$ are literals of the leaf source.
6. All 11 programs use the v1 SDK. Contract `main` (`ef3771d`) also ships the v1 SDK. The v2 SDK is on the contract branch `integration/kernel-v1-20261106` only.
7. The kernel branch computes equality, order comparison, arithmetic and finite enumeration by Lean reduction. These operations belong to `cat.sets`, `cat.finite_sets`, `cat.linear_orders`, `cat.semirings` and `cat.rings`, or to a procedure registered in `lean-categories`.
8. `examples/kernel-v1/benchmark-leaves.json` is in no ref that was searched.

## 1. Registrations

### 1.1 Backend programs

`backends/wire.py` (130 lines) and `backends/engine_python.py` (57 lines) are shared modules. `wire.py` holds the wire encodings. `engine_python.py` runs the program again under the interpreter that has the engine.

| Backend | Program | Engine | Engine entry point | Registrations | Distinct operations | Owner categories of the operations | Registrations with hand-rolled = no |
| --- | --- | --- | --- | --- | --- | --- | --- |
| `sage` | `backends/sage_backend.py` | Sage | `sage.all__sagemath_modules or sage.all` | 16 | 2 | `cat.sets` 16 | 16 |
| `gap` | `backends/gap_backend.py` | GAP (through Sage libgap) | `sage.all__sagemath_gap or sage.all` | 6 | 2 | `cat.sets` 6 | 6 |
| `sage-power-set` | `backends/sage_power_set.py` | Sage | `sage.all__sagemath_combinat or sage.all` | 1 | 1 | `cat.sets` 1 | 1 |
| `sage-set-limits` | `backends/sage_set_limits.py` | Sage | `sage.all__sagemath_combinat or sage.all` | 4 | 4 | `cat.sets` 4 | 1 |
| `sage-discriminant` | `backends/sage_discriminant.py` | Sage | `sage.all__sagemath_modules or sage.all` | 2 | 2 | `cat.bil_wform` 1, `cat.sets` 1 | 0 |
| `sage-fin-rev` | `backends/sage_fin_rev.py` | Sage | `sage.all__sagemath_combinat or sage.all` | 1 | 1 | `cat.sets` 1 | 1 |
| `gap-groups` | `backends/gap_groups.py` | GAP (through Sage libgap) | `sage.all__sagemath_gap or sage.all` | 37 | 6 | `cat.arrows_groups` 2, `cat.magmas` 19, `cat.sets` 16 | 37 |
| `sage-modules` | `backends/sage_modules.py` | Sage | `sage.all__sagemath_modules or sage.all` | 11 | 2 | `cat.modules_r` 6, `cat.sets` 5 | 8 |
| `sage-presentations` | `backends/sage_presentations.py` | Sage | `sage.all__sagemath_modules or sage.all (needs PARI)` | 14 | 5 | `cat.commutative_rings` 2, `cat.sets` 12 | 14 |
| `sage-bilinear-lift` | `backends/sage_bilinear_lift.py` | Sage | `sage.all__sagemath_combinat or sage.all` | 4 | 4 | `cat.bilin_module` 4 | 0 |
| `sage-symbolic` | `backends/sage_symbolic.py` | Sage | `sage.all (full Sage only)` | 19 | 19 | `cat.sets` 19 | 18 |

Nine programs announce the backend name `sage` and two announce `gap` in the `ready` frame. The names of `leaves.json` are different.

### 1.2 Registrations by backend

Each row is one registration. "Function" is the handler and the line of its `def`. "Engine routine" is the routine that the handler calls for that input form, with the line of the call. A handler is selected by the operation only; it finds the input form from the `ctor` of the argument.

#### Backend `sage`: `backends/sage_backend.py` (83 lines)

Engine: Sage. Engine entry point: `sage.all__sagemath_modules or sage.all`. Registrations: 16.

| `leaves.json` line | Operation | Input form | Function | Engine routine | Hand-rolled | Mathematics held in the leaf |
| --- | --- | --- | --- | --- | --- | --- |
| 16 | `meth.cardinality` | `obj.sets.fin` | `op_cardinality` `sage_backend.py:66` | IntegerRange(0, n).cardinality()  [Parent.cardinality] (`:72`) | no |  |
| 17 | `meth.cardinality` | `obj.sets.naturals` | `op_cardinality` `sage_backend.py:66` | NonNegativeIntegers().cardinality()  [Parent.cardinality] (`:72`) | no | Sage answers `+Infinity`; the leaf answers `aleph0` from its own table `COUNTABLE` (sage_backend.py:51-52, :73) |
| 18 | `meth.cardinality` | `obj.sets.positive_naturals` | `op_cardinality` `sage_backend.py:66` | PositiveIntegers().cardinality()  [Parent.cardinality] (`:72`) | no | Sage answers `+Infinity`; the leaf answers `aleph0` from its own table `COUNTABLE` (sage_backend.py:51-52, :73) |
| 19 | `meth.cardinality` | `obj.sets.primes` | `op_cardinality` `sage_backend.py:66` | Primes().cardinality()  [Parent.cardinality] (`:72`) | no | Sage answers `+Infinity`; the leaf answers `aleph0` from its own table `COUNTABLE` (sage_backend.py:51-52, :73) |
| 20 | `meth.cardinality` | `obj.sets.integers` | `op_cardinality` `sage_backend.py:66` | ZZ.cardinality()  [Parent.cardinality] (`:72`) | no | Sage answers `+Infinity`; the leaf answers `aleph0` from its own table `COUNTABLE` (sage_backend.py:51-52, :73) |
| 21 | `meth.cardinality` | `obj.sets.rationals` | `op_cardinality` `sage_backend.py:66` | QQ.cardinality()  [Parent.cardinality] (`:72`) | no | Sage answers `+Infinity`; the leaf answers `aleph0` from its own table `COUNTABLE` (sage_backend.py:51-52, :73) |
| 24 | `prop.is_finite` | `obj.sets.fin` | `op_is_finite` `sage_backend.py:76` | IntegerRange(0, n).is\_finite()  [Parent.is\_finite] (`:79`) | no |  |
| 25 | `prop.is_finite` | `obj.sets.naturals` | `op_is_finite` `sage_backend.py:76` | NonNegativeIntegers().is\_finite()  [Parent.is\_finite] (`:79`) | no |  |
| 26 | `prop.is_finite` | `obj.sets.positive_naturals` | `op_is_finite` `sage_backend.py:76` | PositiveIntegers().is\_finite()  [Parent.is\_finite] (`:79`) | no |  |
| 27 | `prop.is_finite` | `obj.sets.primes` | `op_is_finite` `sage_backend.py:76` | Primes().is\_finite()  [Parent.is\_finite] (`:79`) | no |  |
| 28 | `prop.is_finite` | `obj.sets.integers` | `op_is_finite` `sage_backend.py:76` | ZZ.is\_finite()  [Parent.is\_finite] (`:79`) | no |  |
| 29 | `prop.is_finite` | `obj.sets.rationals` | `op_is_finite` `sage_backend.py:76` | QQ.is\_finite()  [Parent.is\_finite] (`:79`) | no |  |
| 30 | `prop.is_finite` | `obj.sets.reals` | `op_is_finite` `sage_backend.py:76` | RR.is\_finite()  [Parent.is\_finite] (`:79`) | no | the leaf models the set by the 53-bit floating-point field `RR` (sage_backend.py:44-45) |
| 31 | `prop.is_finite` | `obj.sets.complexes` | `op_is_finite` `sage_backend.py:76` | CC.is\_finite()  [Parent.is\_finite] (`:79`) | no | the leaf models the set by the 53-bit floating-point field `CC` (sage_backend.py:44-45) |
| 93 | `meth.cardinality` | `obj.finite_sets.fin` | `op_cardinality` `sage_backend.py:66` | IntegerRange(0, n).cardinality()  [Parent.cardinality] (`:72`) | no |  |
| 95 | `prop.is_finite` | `obj.finite_sets.fin` | `op_is_finite` `sage_backend.py:76` | IntegerRange(0, n).is\_finite()  [Parent.is\_finite] (`:79`) | no |  |

#### Backend `gap`: `backends/gap_backend.py` (66 lines)

Engine: GAP (through Sage libgap). Engine entry point: `sage.all__sagemath_gap or sage.all`. Registrations: 6.

| `leaves.json` line | Operation | Input form | Function | Engine routine | Hand-rolled | Mathematics held in the leaf |
| --- | --- | --- | --- | --- | --- | --- |
| 22 | `meth.cardinality` | `obj.sets.integers_mod` | `op_cardinality` `gap_backend.py:54` | Size(ZmodnZ(n), or Integers at n = 0) (`:56`) | no | `ZMod 0` is $\mathbb{Z}$ by a rule of the leaf (gap_backend.py:33); GAP `infinity` is answered as `aleph0` (gap_backend.py:55-57) |
| 23 | `meth.cardinality` | `obj.sets.integers_mod_power` | `op_cardinality` `gap_backend.py:54` | Size(FullRowModule(ZmodnZ(n), k)) (`:56`) | no | `ZMod 0` is $\mathbb{Z}$ by a rule of the leaf (gap_backend.py:33); GAP `infinity` is answered as `aleph0` (gap_backend.py:55-57) |
| 32 | `prop.is_finite` | `obj.sets.integers_mod` | `op_is_finite` `gap_backend.py:60` | IsFinite(ZmodnZ(n), or Integers at n = 0) (`:62`) | no | `ZMod 0` is $\mathbb{Z}$ by a rule of the leaf (gap_backend.py:33) |
| 33 | `prop.is_finite` | `obj.sets.integers_mod_power` | `op_is_finite` `gap_backend.py:60` | IsFinite(FullRowModule(ZmodnZ(n), k)) (`:62`) | no | `ZMod 0` is $\mathbb{Z}$ by a rule of the leaf (gap_backend.py:33) |
| 94 | `meth.cardinality` | `obj.rings.integers_mod` | `op_cardinality` `gap_backend.py:54` | Size(ZmodnZ(n), or Integers at n = 0) (`:56`) | no | `ZMod 0` is $\mathbb{Z}$ by a rule of the leaf (gap_backend.py:33); GAP `infinity` is answered as `aleph0` (gap_backend.py:55-57) |
| 96 | `prop.is_finite` | `obj.rings.integers_mod` | `op_is_finite` `gap_backend.py:60` | IsFinite(ZmodnZ(n), or Integers at n = 0) (`:62`) | no | `ZMod 0` is $\mathbb{Z}$ by a rule of the leaf (gap_backend.py:33) |

#### Backend `sage-power-set`: `backends/sage_power_set.py` (96 lines)

Engine: Sage. Engine entry point: `sage.all__sagemath_combinat or sage.all`. Registrations: 1.

| `leaves.json` line | Operation | Input form | Function | Engine routine | Hand-rolled | Mathematics held in the leaf |
| --- | --- | --- | --- | --- | --- | --- |
| 34 | `meth.cardinality` | `obj.sets.power_set` | `op_cardinality` `sage_power_set.py:88` | Subsets(S).cardinality()  [sage.combinat.subset] (`:93`) | no | the leaf refuses an infinite `S` with the statement that its power set is uncountable (sage_power_set.py:53-55); `S` comes from a second table of parents (sage_power_set.py:38-48) |

#### Backend `sage-set-limits`: `backends/sage_set_limits.py` (330 lines)

Engine: Sage. Engine entry point: `sage.all__sagemath_combinat or sage.all`. Registrations: 4.

| `leaves.json` line | Operation | Input form | Function | Engine routine | Hand-rolled | Mathematics held in the leaf |
| --- | --- | --- | --- | --- | --- | --- |
| 35 | `lim.sets.product` | `cat.sets` | `op_product` `sage_set_limits.py:238` | cartesian\_product([S, T])  [sage.sets.cartesian\_product], enumerated; no engine object for an infinite factor (`:245`) | partial | the tables `COUNTABLE` and `UNCOUNTABLE` decide which named sets are countable (sage_set_limits.py:75-83, :192-199) |
| 36 | `colim.sets.coproduct` | `cat.sets` | `op_coproduct` `sage_set_limits.py:283` | DisjointUnionEnumeratedSets(Family([S, T]), keepkey=True)  [sage.sets.disjoint\_union\_enumerated\_sets] (`:287`) | no |  |
| 37 | `lim.sets.pullback` | `cat.sets` | `op_pullback` `sage_set_limits.py:317` | cartesian\_product([FiniteEnumeratedSet(dom f), FiniteEnumeratedSet(dom g)]), then a Python filter (`:320`) | yes |  |
| 109 | `meth.cardinality` | `cat.sets` | `op_cardinality` `sage_set_limits.py:272` | S.cardinality() of the enumerated carrier (FiniteEnumeratedSet, IntegerRange, Zmod(n), cartesian\_product) (`:277`) | partial | the tables `COUNTABLE` and `UNCOUNTABLE` decide which named sets are countable (sage_set_limits.py:75-83, :192-199) |

Quoted lines:

- sage_set_limits.py:246-248 `[[k, ex(p[0])] for k, p in enumerate(P)]` (legs by Python indexing); :256 `return {"ctor": "cone", "args": [{"ctor": "objectProduct", "args": [X, Y]}, *legs]}` (infinite factor: a descriptor and two tokens); :269 `return value_data(data[PROJECTIONS[args[0]]])` (projection of a point)
- sage_set_limits.py:320-321 `P = [p for p in cartesian_product([FiniteEnumeratedSet(f), FiniteEnumeratedSet(g)])` / `if f[p[0]] == g[p[1]]]`
- sage_set_limits.py:184-186 `if any(f[0] == "finite" and f[1].cardinality() == 0 for f in factors):` / `return "finite", FiniteEnumeratedSet([]), json.loads` / `return "infinite", value, all(f[0] == "finite" or f[2] for f in factors)` (cardinality of a product with an infinite factor); :280 `return aleph0()`

#### Backend `sage-discriminant`: `backends/sage_discriminant.py` (60 lines)

Engine: Sage. Engine entry point: `sage.all__sagemath_modules or sage.all`. Registrations: 2.

| `leaves.json` line | Operation | Input form | Function | Engine routine | Hand-rolled | Mathematics held in the leaf |
| --- | --- | --- | --- | --- | --- | --- |
| 38 | `colim.bil_w_form.cokernel` | `cat.bil_wform` | `cokernel` `sage_discriminant.py:41` | matrix(ZZ, n, n, f).elementary\_divisors()  [Smith form], used only to refuse an infinite cokernel (`:35`) | lookup | the Gram matrix of $A_n$ is written in the leaf (sage_discriminant.py:33); the handler accepts one diagram only, the inclusion $A_n \to A_n^\vee$ with the zero arrow (sage_discriminant.py:43-48) |
| 39 | `meth.cardinality` | `obj.bil_wform.root_lattice_a_discriminant` | `cardinality` `sage_discriminant.py:52` | matrix(ZZ, n, n, f).elementary\_divisors()  [Smith form], then a Python product (`:35`) | partial | the Gram matrix of $A_n$ is written in the leaf (sage_discriminant.py:33) |

Quoted lines:

- sage_discriminant.py:49-50 `smith_order(n)` / `return {'ctor':'cocone','args':[named(DISCRIMINANT,n),named(PROJECTION,n)]}` (the answer is two catalogue names; the engine result is discarded)
- sage_discriminant.py:34-39 `order = ZZ(1)` / `for d in gram.elementary_divisors():` / `order *= abs(d)`

#### Backend `sage-fin-rev`: `backends/sage_fin_rev.py` (51 lines)

Engine: Sage. Engine entry point: `sage.all__sagemath_combinat or sage.all`. Registrations: 1.

| `leaves.json` line | Operation | Input form | Function | Engine routine | Hand-rolled | Mathematics held in the leaf |
| --- | --- | --- | --- | --- | --- | --- |
| 40 | `mor.sets.fin_rev` | `mor.sets.fin_rev` | `op_fin_rev` `sage_fin_rev.py:25` | Permutation([n, ..., 1])  [sage.combinat.permutation]; composition by right\_action\_product; application by Permutation.\_\_call\_\_ (`:22`) | no | the definition of the reversal is the image list written in the leaf (sage_fin_rev.py:22 `Permutation(list(range(n, 0, -1)))`) |

#### Backend `gap-groups`: `backends/gap_groups.py` (325 lines)

Engine: GAP (through Sage libgap). Engine entry point: `sage.all__sagemath_gap or sage.all`. Registrations: 37.

| `leaves.json` line | Operation | Input form | Function | Engine routine | Hand-rolled | Mathematics held in the leaf |
| --- | --- | --- | --- | --- | --- | --- |
| 41 | `meth.cardinality` | `obj.groups.symmetric` | `cardinality` `gap_groups.py:245` | Size(SymmetricGroup(n)) (`:250`) | no |  |
| 42 | `meth.cardinality` | `obj.groups.cyclic` | `cardinality` `gap_groups.py:245` | Size(CyclicGroup(n), or FreeGroup(1) at n = 0) (`:250`) | no | $\mathbb{Z}/0$ is the free group of rank $1$ by a rule of the leaf (gap_groups.py:46) |
| 43 | `meth.cardinality` | `obj.sets.permutations` | `cardinality` `gap_groups.py:245` | Size(SymmetricGroup(n)) (`:250`) | no |  |
| 44 | `meth.cardinality` | `obj.subgroups.alternating` | `cardinality` `gap_groups.py:245` | Size(AlternatingGroup(n)) (`:250`) | no |  |
| 45 | `meth.cardinality` | `obj.subgroups.kernel` | `cardinality` `gap_groups.py:245` | Size(Kernel(GroupHomomorphismByImages(G, H, gens, images))) (`:250`) | no |  |
| 46 | `prop.is_finite` | `obj.groups.symmetric` | `finiteness` `gap_groups.py:254` | IsFinite(SymmetricGroup(n)) (`:259`) | no |  |
| 47 | `prop.is_finite` | `obj.groups.cyclic` | `finiteness` `gap_groups.py:254` | IsFinite(CyclicGroup(n), or FreeGroup(1) at n = 0) (`:259`) | no | $\mathbb{Z}/0$ is the free group of rank $1$ by a rule of the leaf (gap_groups.py:46) |
| 48 | `prop.is_finite` | `obj.sets.permutations` | `finiteness` `gap_groups.py:254` | IsFinite(SymmetricGroup(n)) (`:259`) | no |  |
| 49 | `prop.is_finite` | `obj.subgroups.alternating` | `finiteness` `gap_groups.py:254` | IsFinite(AlternatingGroup(n)) (`:259`) | no |  |
| 50 | `prop.is_finite` | `obj.subgroups.kernel` | `finiteness` `gap_groups.py:254` | IsFinite(Kernel(GroupHomomorphismByImages(G, H, gens, images))) (`:259`) | no |  |
| 51 | `prop.is_abelian` | `obj.groups.symmetric` | `abelianness` `gap_groups.py:274` | IsAbelian(SymmetricGroup(n)) (`:287`) | no |  |
| 52 | `prop.is_abelian` | `obj.groups.cyclic` | `abelianness` `gap_groups.py:274` | IsAbelian(CyclicGroup(n), or FreeGroup(1) at n = 0) (`:287`) | no | $\mathbb{Z}/0$ is the free group of rank $1$ by a rule of the leaf (gap_groups.py:46) |
| 53 | `prop.is_abelian` | `obj.subgroups.kernel` | `abelianness` `gap_groups.py:274` | IsAbelian(Kernel(GroupHomomorphismByImages(G, H, gens, images))) (`:287`) | no |  |
| 54 | `prop.is_commutative` | `obj.groups.symmetric` | `abelianness` `gap_groups.py:274` | IsAbelian(SymmetricGroup(n)) (`:287`) | no |  |
| 55 | `prop.is_commutative` | `obj.groups.cyclic` | `abelianness` `gap_groups.py:274` | IsAbelian(CyclicGroup(n), or FreeGroup(1) at n = 0) (`:287`) | no | $\mathbb{Z}/0$ is the free group of rank $1$ by a rule of the leaf (gap_groups.py:46) |
| 56 | `prop.is_commutative` | `obj.subgroups.alternating` | `abelianness` `gap_groups.py:274` | IsAbelian(AlternatingGroup(n)) (`:287`) | no |  |
| 57 | `prop.is_commutative` | `obj.subgroups.kernel` | `abelianness` `gap_groups.py:274` | IsAbelian(Kernel(GroupHomomorphismByImages(G, H, gens, images))) (`:287`) | no |  |
| 58 | `meth.group_arrow_kernel` | `cat.arrows_groups` | `kernel` `gap_groups.py:298` | Kernel(f) for f = GroupHomomorphismByImages \| IdentityMapping \| CompositionMapping; Elements(K) (`:306`) | no | the handler lowers the named arrows `mor.groups.sign`, `mor.groups.identity`, `mor.groups.trivial`, `identity`, `zero` and `compose` itself (gap_groups.py:134-176); the sign map is built from `SignPerm` of each generator (:155-159); points of a cyclic group are encoded through a Python table of powers (:239-241) |
| 59 | `fun.arrows_groups.kernel` | `cat.arrows_groups` | `kernel` `gap_groups.py:298` | Kernel(f) for f = GroupHomomorphismByImages \| IdentityMapping \| CompositionMapping; Elements(K) (`:306`) | no | the handler lowers the named arrows `mor.groups.sign`, `mor.groups.identity`, `mor.groups.trivial`, `identity`, `zero` and `compose` itself (gap_groups.py:134-176); the sign map is built from `SignPerm` of each generator (:155-159); points of a cyclic group are encoded through a Python table of powers (:239-241) |
| 81 | `meth.cardinality` | `cat.subobjects_groups` | `cardinality` `gap_groups.py:245` | Size(the group of the retained apex descriptor) (`:250`) | no |  |
| 82 | `prop.is_finite` | `cat.subobjects_groups` | `finiteness` `gap_groups.py:254` | IsFinite(the group of the retained apex descriptor) (`:259`) | no |  |
| 83 | `prop.is_abelian` | `cat.subobjects_groups` | `abelianness` `gap_groups.py:274` | IsAbelian(Subgroup(G, points)) for a supplied inventory; IsAbelian(group) otherwise (`:295`) | no |  |
| 84 | `prop.is_commutative` | `cat.subobjects_groups` | `abelianness` `gap_groups.py:274` | IsAbelian(Subgroup(G, points)) for a supplied inventory; IsAbelian(group) otherwise (`:295`) | no |  |
| 85 | `prop.is_abelian` | `obj.bil_wform.root_lattice_a` | `abelianness` `gap_groups.py:274` | IsAbelian(AbelianGroup([0]\*n)) (`:287`) | no | the rank $n$ of $A_n$ is a literal of the leaf (gap_groups.py:55) |
| 86 | `prop.is_abelian` | `obj.bil_wform.root_lattice_a_dual` | `abelianness` `gap_groups.py:274` | IsAbelian(AbelianGroup([0]\*n)) (`:287`) | no | the rank $n$ of $A_n^\vee$ is a literal of the leaf (gap_groups.py:55) |
| 87 | `prop.is_abelian` | `obj.bil_wform.root_lattice_a_discriminant` | `abelianness` `gap_groups.py:274` | IsAbelian(AbelianGroup(\|DiagonalOfMat(SmithNormalFormIntegerMat(gram))\|)) (`:287`) | no | the Gram matrix of $A_n$ is written in the leaf (gap_groups.py:61-62) |
| 88 | `prop.is_abelian` | `obj.integral_lattice.e8` | `abelianness` `gap_groups.py:274` | IsAbelian(AbelianGroup([0]\*8)) (`:287`) | no | the rank $8$ of $E_8$ is a literal of the leaf (gap_groups.py:57) |
| 89 | `prop.is_commutative` | `obj.bil_wform.root_lattice_a` | `abelianness` `gap_groups.py:274` | IsAbelian(AbelianGroup([0]\*n)) (`:287`) | no | the rank $n$ of $A_n$ is a literal of the leaf (gap_groups.py:55) |
| 90 | `prop.is_commutative` | `obj.bil_wform.root_lattice_a_dual` | `abelianness` `gap_groups.py:274` | IsAbelian(AbelianGroup([0]\*n)) (`:287`) | no | the rank $n$ of $A_n^\vee$ is a literal of the leaf (gap_groups.py:55) |
| 91 | `prop.is_commutative` | `obj.bil_wform.root_lattice_a_discriminant` | `abelianness` `gap_groups.py:274` | IsAbelian(AbelianGroup(\|DiagonalOfMat(SmithNormalFormIntegerMat(gram))\|)) (`:287`) | no | the Gram matrix of $A_n$ is written in the leaf (gap_groups.py:61-62) |
| 92 | `prop.is_commutative` | `obj.integral_lattice.e8` | `abelianness` `gap_groups.py:274` | IsAbelian(AbelianGroup([0]\*8)) (`:287`) | no | the rank $8$ of $E_8$ is a literal of the leaf (gap_groups.py:57) |
| 97 | `meth.cardinality` | `obj.groups.units` | `cardinality` `gap_groups.py:245` | Size(Units(R) for R = Integers, Rationals, ZmodnZ(n); Units(G) for a group) (`:250`) | no |  |
| 98 | `prop.is_finite` | `obj.groups.units` | `finiteness` `gap_groups.py:254` | IsFinite(Units(R) for R = Integers, Rationals, ZmodnZ(n); Units(G) for a group) (`:259`) | no |  |
| 99 | `prop.is_abelian` | `obj.groups.units` | `abelianness` `gap_groups.py:274` | IsAbelian(Units(R) for R = Integers, Rationals, ZmodnZ(n); Units(G) for a group) (`:287`) | no |  |
| 100 | `prop.is_commutative` | `obj.groups.units` | `abelianness` `gap_groups.py:274` | IsAbelian(Units(R) for R = Integers, Rationals, ZmodnZ(n); Units(G) for a group) (`:287`) | no |  |
| 101 | `meth.cardinality` | `obj.sets.units` | `cardinality` `gap_groups.py:245` | Size(Units(R) for R = Integers, Rationals, ZmodnZ(n); Units(G) for a group) (`:250`) | no |  |
| 102 | `prop.is_finite` | `obj.sets.units` | `finiteness` `gap_groups.py:254` | IsFinite(Units(R) for R = Integers, Rationals, ZmodnZ(n); Units(G) for a group) (`:259`) | no |  |

#### Backend `sage-modules`: `backends/sage_modules.py` (93 lines)

Engine: Sage. Engine entry point: `sage.all__sagemath_modules or sage.all`. Registrations: 11.

| `leaves.json` line | Operation | Input form | Function | Engine routine | Hand-rolled | Mathematics held in the leaf |
| --- | --- | --- | --- | --- | --- | --- |
| 60 | `meth.rank` | `obj.modules.regular` | `rank` `sage_modules.py:64` | FreeModule(R, 1).rank() (`:71`) | no |  |
| 61 | `meth.cardinality` | `obj.modules.regular` | `cardinality` `sage_modules.py:74` | FreeModule(R, 1).cardinality() (`:86`) | no | Sage `+Infinity` is answered as `aleph0` (sage_modules.py:87) |
| 62 | `meth.rank` | `obj.modules.vectors` | `rank` `sage_modules.py:64` | FreeModule(R, n).rank() (`:71`) | no |  |
| 63 | `meth.cardinality` | `obj.modules.vectors` | `cardinality` `sage_modules.py:74` | FreeModule(R, n).cardinality() (`:86`) | no | Sage `+Infinity` is answered as `aleph0` (sage_modules.py:87) |
| 64 | `meth.rank` | `obj.bil_wform.root_lattice_a` | `rank` `sage_modules.py:64` | FreeModule(ZZ, n).rank() (`:71`) | lookup | the rank $n$ of $A_n$ is a literal of the leaf (sage_modules.py:50) |
| 65 | `meth.cardinality` | `obj.bil_wform.root_lattice_a` | `cardinality` `sage_modules.py:74` | FreeModule(ZZ, n).cardinality() (`:86`) | no | the rank $n$ of $A_n$ is a literal of the leaf (sage_modules.py:50); Sage `+Infinity` is answered as `aleph0` (sage_modules.py:87) |
| 66 | `meth.rank` | `obj.bil_wform.root_lattice_a_dual` | `rank` `sage_modules.py:64` | FreeModule(ZZ, n).rank() (`:71`) | lookup | the rank $n$ of $A_n^\vee$ is a literal of the leaf (sage_modules.py:50) |
| 67 | `meth.cardinality` | `obj.bil_wform.root_lattice_a_dual` | `cardinality` `sage_modules.py:74` | FreeModule(ZZ, n).cardinality() (`:86`) | no | the rank $n$ of $A_n^\vee$ is a literal of the leaf (sage_modules.py:50); Sage `+Infinity` is answered as `aleph0` (sage_modules.py:87) |
| 68 | `meth.rank` | `obj.bil_wform.root_lattice_a_discriminant` | `rank` `sage_modules.py:64` | FreeModule(QQ, n).quotient(gram.change\_ring(QQ).row\_space()).dimension() (`:70`) | no | the Gram matrix of $A_n$ is written in the leaf (sage_modules.py:60-61) |
| 69 | `meth.rank` | `obj.integral_lattice.e8` | `rank` `sage_modules.py:64` | FreeModule(ZZ, 8).rank() (`:71`) | lookup | the rank $8$ of $E_8$ is a literal of the leaf (sage_modules.py:52) |
| 70 | `meth.cardinality` | `obj.integral_lattice.e8` | `cardinality` `sage_modules.py:74` | FreeModule(ZZ, 8).cardinality() (`:86`) | no | the rank $8$ of $E_8$ is a literal of the leaf (sage_modules.py:52); Sage `+Infinity` is answered as `aleph0` (sage_modules.py:87) |

Quoted lines:

- sage_modules.py:50-52 `return engine.FreeModule(engine.ZZ, numeral(args[0]))` / `return engine.FreeModule(engine.ZZ, 8)` (the engine returns the rank that the leaf wrote)

#### Backend `sage-presentations`: `backends/sage_presentations.py` (355 lines)

Engine: Sage. Engine entry point: `sage.all__sagemath_modules or sage.all (needs PARI)`. Registrations: 14.

| `leaves.json` line | Operation | Input form | Function | Engine routine | Hand-rolled | Mathematics held in the leaf |
| --- | --- | --- | --- | --- | --- | --- |
| 71 | `meth.cardinality` | `obj.sets.f9_x` | `cardinality` `sage_presentations.py:333` | PolynomialRing(GF(3), 't').quotient(modulus).cardinality() (`:338`) | no | the two defining polynomials $t^2 + 1$ and $t^2 + t + 2$ over $\mathbb{F}_3$ are literals of the leaf (sage_presentations.py:75) |
| 72 | `prop.is_finite` | `obj.sets.f9_x` | `finiteness` `sage_presentations.py:341` | PolynomialRing(GF(3), 't').quotient(modulus).is\_finite() (`:346`) | no | the two defining polynomials $t^2 + 1$ and $t^2 + t + 2$ over $\mathbb{F}_3$ are literals of the leaf (sage_presentations.py:75) |
| 73 | `meth.cardinality` | `obj.sets.f9_y` | `cardinality` `sage_presentations.py:333` | PolynomialRing(GF(3), 't').quotient(modulus).cardinality() (`:338`) | no | the two defining polynomials $t^2 + 1$ and $t^2 + t + 2$ over $\mathbb{F}_3$ are literals of the leaf (sage_presentations.py:75) |
| 74 | `prop.is_finite` | `obj.sets.f9_y` | `finiteness` `sage_presentations.py:341` | PolynomialRing(GF(3), 't').quotient(modulus).is\_finite() (`:346`) | no | the two defining polynomials $t^2 + 1$ and $t^2 + t + 2$ over $\mathbb{F}_3$ are literals of the leaf (sage_presentations.py:75) |
| 75 | `meth.cardinality` | `obj.commutative_rings.f9_x` | `cardinality` `sage_presentations.py:333` | PolynomialRing(GF(3), 't').quotient(modulus).cardinality() (`:338`) | no | the two defining polynomials $t^2 + 1$ and $t^2 + t + 2$ over $\mathbb{F}_3$ are literals of the leaf (sage_presentations.py:75) |
| 76 | `prop.is_finite` | `obj.commutative_rings.f9_x` | `finiteness` `sage_presentations.py:341` | PolynomialRing(GF(3), 't').quotient(modulus).is\_finite() (`:346`) | no | the two defining polynomials $t^2 + 1$ and $t^2 + t + 2$ over $\mathbb{F}_3$ are literals of the leaf (sage_presentations.py:75) |
| 77 | `cmp.f9.translation` | `obj.commutative_rings.f9_x` | `translation` `sage_presentations.py:263` | F.hom([E.gen() + E(shift)], E)  [quotient-ring homomorphism], applied to the point (`:148`) | no | the two defining polynomials $t^2 + 1$ and $t^2 + t + 2$ over $\mathbb{F}_3$ are literals of the leaf (sage_presentations.py:75); the image of the generator is the literal shift $2$ or $-2$ (sage_presentations.py:147) |
| 78 | `meth.cardinality` | `obj.commutative_rings.f9_y` | `cardinality` `sage_presentations.py:333` | PolynomialRing(GF(3), 't').quotient(modulus).cardinality() (`:338`) | no | the two defining polynomials $t^2 + 1$ and $t^2 + t + 2$ over $\mathbb{F}_3$ are literals of the leaf (sage_presentations.py:75) |
| 79 | `prop.is_finite` | `obj.commutative_rings.f9_y` | `finiteness` `sage_presentations.py:341` | PolynomialRing(GF(3), 't').quotient(modulus).is\_finite() (`:346`) | no | the two defining polynomials $t^2 + 1$ and $t^2 + t + 2$ over $\mathbb{F}_3$ are literals of the leaf (sage_presentations.py:75) |
| 80 | `cmp.f9.translation` | `obj.commutative_rings.f9_y` | `translation` `sage_presentations.py:263` | F.hom([E.gen() + E(shift)], E)  [quotient-ring homomorphism], applied to the point (`:148`) | no | the two defining polynomials $t^2 + 1$ and $t^2 + t + 2$ over $\mathbb{F}_3$ are literals of the leaf (sage_presentations.py:75); the image of the generator is the literal shift $2$ or $-2$ (sage_presentations.py:147) |
| 107 | `mor.sets.f9_x_constants` | `mor.sets.f9_x_constants` | `x_constants` `sage_presentations.py:325` | F.coerce\_map\_from(F.base\_ring())  [coercion map GF(3) -> F] (`:156`) | no | the two defining polynomials $t^2 + 1$ and $t^2 + t + 2$ over $\mathbb{F}_3$ are literals of the leaf (sage_presentations.py:75) |
| 108 | `mor.sets.f9_y_constants` | `mor.sets.f9_y_constants` | `y_constants` `sage_presentations.py:329` | F.coerce\_map\_from(F.base\_ring())  [coercion map GF(3) -> F] (`:156`) | no | the two defining polynomials $t^2 + 1$ and $t^2 + t + 2$ over $\mathbb{F}_3$ are literals of the leaf (sage_presentations.py:75) |
| 110 | `mor.sets.f9_x_constants` | `obj.sets.integers_mod` | `x_constants` `sage_presentations.py:325` | F.coerce\_map\_from(F.base\_ring())  [coercion map GF(3) -> F] (`:156`) | no | the two defining polynomials $t^2 + 1$ and $t^2 + t + 2$ over $\mathbb{F}_3$ are literals of the leaf (sage_presentations.py:75) |
| 111 | `mor.sets.f9_y_constants` | `obj.sets.integers_mod` | `y_constants` `sage_presentations.py:329` | F.coerce\_map\_from(F.base\_ring())  [coercion map GF(3) -> F] (`:156`) | no | the two defining polynomials $t^2 + 1$ and $t^2 + t + 2$ over $\mathbb{F}_3$ are literals of the leaf (sage_presentations.py:75) |

#### Backend `sage-bilinear-lift`: `backends/sage_bilinear_lift.py` (153 lines)

Engine: Sage. Engine entry point: `sage.all__sagemath_combinat or sage.all`. Registrations: 4.

| `leaves.json` line | Operation | Input form | Function | Engine routine | Hand-rolled | Mathematics held in the leaf |
| --- | --- | --- | --- | --- | --- | --- |
| 103 | `lift.bilin_module.restrict#obj` | `lift.bilin_module.restrict#input` | `object_output` `sage_bilinear_lift.py:66` | FiniteSetMaps(...).from\_dict(table)  [lookup of a supplied graph]; cartesian\_product(points, points) (`:92`) | yes |  |
| 104 | `lift.bilin_module.restrict#hom` | `lift.bilin_module.restrict#input` | `hom_output` `sage_bilinear_lift.py:136` | none: the supplied inclusion graph is returned as a typedMap (`:123`) | lookup |  |
| 105 | `lift.bilin_module.restrict#forward` | `lift.bilin_module.restrict#input` | `forward_output` `sage_bilinear_lift.py:140` | FiniteSetMaps(points).one()  [identity map of the point set] (`:130`) | lookup | the leaf answers the comparison between the image of the restricted object and the base apex as the identity on point keys (sage_bilinear_lift.py:128-133) |
| 106 | `lift.bilin_module.restrict#backward` | `lift.bilin_module.restrict#input` | `backward_output` `sage_bilinear_lift.py:144` | FiniteSetMaps(points).one()  [identity map of the point set] (`:130`) | lookup | the leaf answers the comparison between the image of the restricted object and the base apex as the identity on point keys (sage_bilinear_lift.py:128-133) |

Quoted lines:

- sage_bilinear_lift.py:94-103 `for pair in pairs:` ... `inner = native_map(json.loads(pairing(inc(x))))` / `result = json.loads(inner(inc(y)))` / `pulled.append([[json.loads(x), json.loads(y)], result])` (restriction of the pairing, point by point)
- sage_bilinear_lift.py:123 `return named("typedMap", obj, source, finite_graph(points, rows))`
- sage_bilinear_lift.py:130-131 `identity = FiniteSetMaps(list(map(key, points))).one()` / `graph = finite_graph(points, [[p, json.loads(identity(key(p)))] for p in points])`

#### Backend `sage-symbolic`: `backends/sage_symbolic.py` (672 lines)

Engine: Sage. Engine entry point: `sage.all (full Sage only)`. Registrations: 19.

| `leaves.json` line | Operation | Input form | Function | Engine routine | Hand-rolled | Mathematics held in the leaf |
| --- | --- | --- | --- | --- | --- | --- |
| 112 | `mor.sets.complex_re` | `obj.sets.complexes` | `scalar` `sage_symbolic.py:454` | SR(x).real\_part() (`:228`) | no | points of $\mathbb{R}$ and $\mathbb{C}$ are values of Sage's symbolic ring `SR` (sage_symbolic.py:56) |
| 113 | `mor.sets.complex_im` | `obj.sets.complexes` | `scalar` `sage_symbolic.py:454` | SR(x).imag\_part() (`:229`) | no | points of $\mathbb{R}$ and $\mathbb{C}$ are values of Sage's symbolic ring `SR` (sage_symbolic.py:56) |
| 114 | `mor.sets.complex_bar` | `obj.sets.complexes` | `scalar` `sage_symbolic.py:454` | SR(x).conjugate() (`:230`) | no | points of $\mathbb{R}$ and $\mathbb{C}$ are values of Sage's symbolic ring `SR` (sage_symbolic.py:56) |
| 115 | `mor.sets.complex_abs` | `obj.sets.complexes` | `scalar` `sage_symbolic.py:454` | SR(x).abs() (`:231`) | no | points of $\mathbb{R}$ and $\mathbb{C}$ are values of Sage's symbolic ring `SR` (sage_symbolic.py:56) |
| 116 | `mor.sets.real_sqrt` | `obj.sets.reals` | `scalar` `sage_symbolic.py:454` | sqrt(SR(x)) (`:224`) | no | points of $\mathbb{R}$ and $\mathbb{C}$ are values of Sage's symbolic ring `SR` (sage_symbolic.py:56) |
| 117 | `mor.sets.polynomial_degree` | `obj.sets.polynomials` | `degree` `sage_symbolic.py:464` | Polynomial.degree() (`:465`) | no | coefficients in $\mathbb{R}$ and $\mathbb{C}$ are read in `AA` and `QQbar` (sage_symbolic.py:89-92); the degree of $0$ is answered `none` (sage_symbolic.py:466) |
| 118 | `mor.sets.polynomial_derivative` | `obj.sets.polynomials` | `derivative` `sage_symbolic.py:469` | Polynomial.derivative() (`:470`) | no | coefficients in $\mathbb{R}$ and $\mathbb{C}$ are read in `AA` and `QQbar` (sage_symbolic.py:89-92) |
| 119 | `mor.sets.polynomial_differential` | `obj.sets.polynomials` | `differential` `sage_symbolic.py:473` | Polynomial.derivative(), answered as the composite with `mor.sets.kaehler_from_coordinate` (`:475`) | no | coefficients in $\mathbb{R}$ and $\mathbb{C}$ are read in `AA` and `QQbar` (sage_symbolic.py:89-92) |
| 120 | `mor.sets.polynomial_map` | `obj.sets.polynomials` | `change_ring` `sage_symbolic.py:487` | Polynomial.change\_ring(S) (`:494`) | no | coefficients in $\mathbb{R}$ and $\mathbb{C}$ are read in `AA` and `QQbar` (sage_symbolic.py:89-92) |
| 121 | `mor.sets.polynomial_factors` | `obj.sets.nonzero_polynomials` | `factors` `sage_symbolic.py:504` | Polynomial.factor() (`:507`) | no | coefficients in $\mathbb{R}$ and $\mathbb{C}$ are read in `AA` and `QQbar` (sage_symbolic.py:89-92) |
| 122 | `mor.sets.polynomial_roots` | `obj.sets.nonzero_polynomials` | `roots` `sage_symbolic.py:510` | Polynomial.roots(multiplicities=False); radical\_expression() for AA/QQbar (`:513`) | no | coefficients in $\mathbb{R}$ and $\mathbb{C}$ are read in `AA` and `QQbar` (sage_symbolic.py:89-92) |
| 123 | `mor.sets.companion_matrix` | `obj.sets.monics` | `companion` `sage_symbolic.py:516` | companion\_matrix(p, format="right")  [sage.matrix.special] (`:521`) | no | coefficients in $\mathbb{R}$ and $\mathbb{C}$ are read in `AA` and `QQbar` (sage_symbolic.py:89-92) |
| 124 | `mor.sets.mv_total_degree` | `obj.sets.mv_polynomials` | `total_degree` `sage_symbolic.py:533` | MPolynomial.total\_degree() (`:534`) | no | the total degree of $0$ is answered $0$ (sage_symbolic.py:535 `return max(int(d), 0)`) |
| 125 | `mor.sets.nat_prime_factors` | `obj.sets.positive_naturals` | `prime_factors` `sage_symbolic.py:538` | Integer.prime\_divisors() (`:542`) | no |  |
| 126 | `mor.sets.equality` | `mor.sets.equality` | `equality` `sage_symbolic.py:545` | bool(x == y) in the decoded Sage parent (`:561`) | no | on `SR` the value `False` also means that Sage did not prove the equality (sage_symbolic.py:561) |
| 127 | `mor.sets.span` | `obj.sets.power_set` | `span` `sage_symbolic.py:579` | (K \*\* n).span(vectors).basis()  [echelon basis] (`:592`) | partial |  |
| 128 | `bind.sets.integral` | `cat.sets` | `integral` `sage_symbolic.py:627` | integrate(f, t, a, b)  [symbolic integration] (`:631`) | no | the bound map is evaluated by the leaf's own interpreter of composites, mediators and pointwise operations (`function_of`, `apply_map`, sage_symbolic.py:235-293) |
| 129 | `bind.sets.limit` | `cat.sets` | `real_limit` `sage_symbolic.py:634` | limit(f, t=a) (`:637`) | no | the bound map is evaluated by the leaf's own interpreter of composites, mediators and pointwise operations (`function_of`, `apply_map`, sage_symbolic.py:235-293) |
| 130 | `bind.sets.limit_at_infinity` | `cat.sets` | `infinite_limit` `sage_symbolic.py:640` | limit(f, t=oo) or limit(f, t=-oo) (`:646`) | no | the bound map is evaluated by the leaf's own interpreter of composites, mediators and pointwise operations (`function_of`, `apply_map`, sage_symbolic.py:235-293) |

Quoted lines:

- sage_symbolic.py:593 `columns = [list(b) for b in basis] + [[K(0)] * n] * (n - len(basis))` (the leaf pads the basis to a square matrix and answers the image of that matrix)


### 1.3 Registrations whose answer does not come from an engine routine alone

| Operation | Input form | Backend | Class | Owner category |
| --- | --- | --- | --- | --- |
| `lim.sets.product` | `cat.sets` | `sage-set-limits` | partial | `cat.sets` |
| `lim.sets.pullback` | `cat.sets` | `sage-set-limits` | yes | `cat.sets` |
| `colim.bil_w_form.cokernel` | `cat.bil_wform` | `sage-discriminant` | lookup | `cat.bil_wform` |
| `meth.cardinality` | `obj.bil_wform.root_lattice_a_discriminant` | `sage-discriminant` | partial | `cat.sets` |
| `meth.rank` | `obj.bil_wform.root_lattice_a` | `sage-modules` | lookup | `cat.modules_r` |
| `meth.rank` | `obj.bil_wform.root_lattice_a_dual` | `sage-modules` | lookup | `cat.modules_r` |
| `meth.rank` | `obj.integral_lattice.e8` | `sage-modules` | lookup | `cat.modules_r` |
| `lift.bilin_module.restrict#obj` | `lift.bilin_module.restrict#input` | `sage-bilinear-lift` | yes | `cat.bilin_module` |
| `lift.bilin_module.restrict#hom` | `lift.bilin_module.restrict#input` | `sage-bilinear-lift` | lookup | `cat.bilin_module` |
| `lift.bilin_module.restrict#forward` | `lift.bilin_module.restrict#input` | `sage-bilinear-lift` | lookup | `cat.bilin_module` |
| `lift.bilin_module.restrict#backward` | `lift.bilin_module.restrict#input` | `sage-bilinear-lift` | lookup | `cat.bilin_module` |
| `meth.cardinality` | `cat.sets` | `sage-set-limits` | partial | `cat.sets` |
| `mor.sets.span` | `obj.sets.power_set` | `sage-symbolic` | partial | `cat.sets` |

The quoted lines are in section 1.2 below the table of each backend.

### 1.4 Catalogue addresses that a program handles with no registration

A program names these addresses in its text and holds no registration of them. "Computes" means that the program executes the operation inside a handler of another operation.

| Catalogue address | Family | Owner category | Program | What the program does with it | Registrations of the address in other programs |
| --- | --- | --- | --- | --- | --- |
| `fun.rings.multiplicative_monoid` | functor action (object) | `cat.rings` | `gap-groups` | recognized in the input of the units objects; the composite with units is lowered to GAP `Units(R)` (gap_groups.py:88-98, :213) | 0 |
| `fun.rings.multiplicative_monoid` | functor action (object) | `cat.rings` | `sage-symbolic` | written in answers as the parameter of `mor.sets.divide` (sage_symbolic.py:382-384) | 0 |
| `fun.groups.monoid` | functor action (object) | `cat.groups` | `gap-groups` | recognized in the input of the units objects; lowered to GAP `Units(G)` (gap_groups.py:99-100, :219-221) | 0 |
| `fun.subobjects_groups.domain` | functor action (object) | `cat.subobjects_groups` | `gap-groups` | written in the answer of the kernel as the apex descriptor (gap_groups.py:308) | 0 |
| `fun.commutative_rings.ring` | functor action (object) | `cat.commutative_rings` | `sage-presentations` | computes the morphism action of the functor on a comparison map (sage_presentations.py:226-241) | 0 |
| `fun.bilin_module.forget` | functor action (object) | `cat.bilin_module` | `sage-bilinear-lift` | recognized in the input as the selected action (sage_bilinear_lift.py:48-50); written in the answer as the image descriptor (:124) | 0 |
| `mor.sets.fin_rev` | named morphism | `cat.sets` | `sage-set-limits` | computes the graph of the reversal a second time, for a leg of a cospan (sage_set_limits.py:298-304) | 1 |
| `mor.sets.complex_i` | named morphism | `cat.sets` | `sage-symbolic` | computes: Sage `I` (sage_symbolic.py:202-203); written in answers (:319, :356-357) | 0 |
| `mor.sets.divide` | named morphism | `cat.sets` | `sage-symbolic` | computes: Sage `/` (sage_symbolic.py:183-184, :266-267); written in answers (:310-312, :352-354) | 0 |
| `mor.sets.kaehler_from_coordinate` | named morphism | `cat.sets` | `sage-symbolic` | written in the answer of `mor.sets.polynomial_differential` (sage_symbolic.py:476-477) | 0 |
| `mor.commutative_rings.integer_coefficients` | named morphism | `cat.commutative_rings` | `sage-symbolic` | recognized as the coefficient arrow of `mor.sets.polynomial_map`; lowered to `Polynomial.change_ring` (sage_symbolic.py:480-494) | 0 |
| `mor.commutative_rings.rational_real_coefficients` | named morphism | `cat.commutative_rings` | `sage-symbolic` | recognized as the coefficient arrow of `mor.sets.polynomial_map`; lowered to `Polynomial.change_ring` (sage_symbolic.py:480-494) | 0 |
| `mor.commutative_rings.rational_complex_coefficients` | named morphism | `cat.commutative_rings` | `sage-symbolic` | recognized as the coefficient arrow of `mor.sets.polynomial_map`; lowered to `Polynomial.change_ring` (sage_symbolic.py:480-494) | 0 |
| `mor.commutative_rings.real_complex_coefficients` | named morphism | `cat.commutative_rings` | `sage-symbolic` | recognized as the coefficient arrow of `mor.sets.polynomial_map`; lowered to `Polynomial.change_ring` (sage_symbolic.py:480-494) | 0 |
| `mor.sets.terminal` | named morphism | `cat.sets` | `sage-symbolic` | computes: answers `Integer(0)` (sage_symbolic.py:251-252); written in the answer of `mor.sets.span` (:599) | 0 |
| `mor.groups.sign` | named morphism | `cat.groups` | `gap-groups` | computes: GAP `SignPerm` of each generator, then `GroupHomomorphismByImages` (gap_groups.py:155-159) | 0 |
| `mor.groups.identity` | named morphism | `cat.groups` | `gap-groups` | computes: GAP `IdentityMapping(G)` (gap_groups.py:149-150) | 0 |
| `mor.groups.trivial` | named morphism | `cat.groups` | `gap-groups` | computes: GAP `GroupHomomorphismByImages` onto `One(H)` (gap_groups.py:151-154) | 0 |
| `mor.sets.real_sin` | named morphism | `cat.sets` | `sage-symbolic` | computes: `sin(SR(x))` (sage_symbolic.py:225); written in answers (:363-366) | 0 |
| `mor.sets.real_cos` | named morphism | `cat.sets` | `sage-symbolic` | computes: `cos(SR(x))` (sage_symbolic.py:226); written in answers (:363-366) | 0 |
| `mor.sets.real_exp` | named morphism | `cat.sets` | `sage-symbolic` | computes: `exp(SR(x))` (sage_symbolic.py:227); written in answers (:360-366) | 0 |
| `mor.sets.real_pi` | named morphism | `cat.sets` | `sage-symbolic` | computes: Sage `pi` (sage_symbolic.py:204-205); written in answers (:358-359) | 0 |
| `mor.sets.infinity` | named morphism | `cat.sets` | `sage-symbolic` | computes: `+Infinity` (sage_symbolic.py:206-207) | 0 |
| `mor.sets.neg_infinity` | named morphism | `cat.sets` | `sage-symbolic` | computes: `-Infinity` (sage_symbolic.py:208-209) | 0 |
| `mor.bil_wform.root_lattice_a_to_dual` | named morphism | `cat.bil_wform` | `sage-discriminant` | recognized in the input diagram (sage_discriminant.py:15, :45) | 0 |
| `mor.bil_wform.root_lattice_a_to_discriminant` | named morphism | `cat.bil_wform` | `sage-discriminant` | written in the answer (sage_discriminant.py:16, :50) | 0 |
| `op.rings.add` | element operation | `cat.rings` | `sage-presentations` | computes on points with Sage arithmetic (sage_presentations.py:92-102) | 0 |
| `op.rings.add` | element operation | `cat.rings` | `sage-symbolic` | computes on points with Sage arithmetic (sage_symbolic.py:170-182) | 0 |
| `op.rings.mul` | element operation | `cat.rings` | `sage-presentations` | computes on points with Sage arithmetic (sage_presentations.py:92-102) | 0 |
| `op.rings.mul` | element operation | `cat.rings` | `sage-symbolic` | computes on points with Sage arithmetic (sage_symbolic.py:170-182) | 0 |
| `op.rings.pow` | element operation | `cat.rings` | `sage-presentations` | computes on points with Sage arithmetic (sage_presentations.py:92-102) | 0 |
| `op.rings.pow` | element operation | `cat.rings` | `sage-symbolic` | computes on points with Sage arithmetic (sage_symbolic.py:170-182) | 0 |
| `op.rings.neg` | element operation | `cat.rings` | `sage-presentations` | computes on points with Sage arithmetic (sage_presentations.py:92-102) | 0 |
| `op.rings.neg` | element operation | `cat.rings` | `sage-symbolic` | computes on points with Sage arithmetic (sage_symbolic.py:170-182) | 0 |
| `op.semirings.add` | element operation | `cat.semirings` | `sage-symbolic` | computes on points with Sage arithmetic (sage_symbolic.py:170-182) | 0 |
| `op.semirings.mul` | element operation | `cat.semirings` | `sage-symbolic` | computes on points with Sage arithmetic (sage_symbolic.py:170-182) | 0 |
| `op.semirings.pow` | element operation | `cat.semirings` | `sage-symbolic` | computes on points with Sage arithmetic (sage_symbolic.py:170-182) | 0 |
| `obj.sets.matrices#application` | object application | `cat.sets` | `sage-symbolic` | written in the answer of `mor.sets.span` (sage_symbolic.py:603) | 0 |

Four programs also execute the composition of morphisms, which the wire spells `compose`: `gap_groups.py:160-175` (`CompositionMapping`), `sage_presentations.py:217-225` (`g * f`), `sage_fin_rev.py:17-18` (`right_action_product`), `sage_symbolic.py:212-213` and `:244-245`. `sage_symbolic.py:248-250` answers four inclusions (`incl.sets.naturals_integers`, `incl.sets.integers_rationals`, `incl.sets.rationals_reals`, `incl.sets.reals_complexes`) and `objectField` as the identity on the Sage value. `AGENTS.md:129-132` of LEAVES gives composition to the kernel.

### 1.5 Mathematics that is written more than one time

| Datum | Places |
| --- | --- |
| Gram matrix of $A_n$ (`-2` on the diagonal, `1` next to it) | `sage_discriminant.py:33`, `sage_modules.py:60-61`, `gap_groups.py:61-62` |
| Table from a named set to its engine parent | `sage_backend.py:36-46`, `sage_power_set.py:38-48`, `sage_set_limits.py:63-68` |
| Table of the countable named sets | `sage_backend.py:51-52`, `sage_set_limits.py:75-83` |
| Reversal of `Fin n` as a permutation | `sage_fin_rev.py:22`, `sage_set_limits.py:303` |
| Order of the discriminant group of $A_n$ from the Smith form | `sage_discriminant.py:31-39`, `sage_modules.py:81-85`, `gap_groups.py:58-66` |
| Rank of $A_n$ and of $E_8$ | `sage_modules.py:50-52`, `gap_groups.py:55-57` |

`sage_modules.py:81-85` is not reached through `leaves.json`: `meth.cardinality` on `obj.bil_wform.root_lattice_a_discriminant` belongs to `sage-discriminant` (`leaves.json:39`). The two programs differ on a zero divisor: `sage_modules.py:83-84` answers `aleph0`, and `sage_discriminant.py:36-37` raises an error.

### 1.6 `examples/kernel-v1/benchmark-leaves.json`

- Searched: the file lists (`git ls-tree -r`) of `main`, `integration/kernel-v1-20261106`, `origin/main`, `origin/integration/kernel-v1-20261106`, `origin/work/kernel-v1-20261023` and `origin/fix/categorical-selection-boundary-20261107` in MAIN, for a path with `benchmark` or `leaves.json`; `git log --all --diff-filter=A -- '*benchmark-leaves.json'` in MAIN; the working tree of MAIN; each of the 12 refs of the local clone of `lean-cas-dsl-leaves`, for a path with `benchmark` or `examples/`; the LEAVES export; a file search for the name under `/home/dzack/gitclones` and under the `sage-repos` volume, to depth 6.
- Found: no file with that name. `examples/` is not in the working tree of MAIN. On the kernel branch, `examples/kernel-v1/` holds four `.cas` files and two requirements files. `quickstart.md:165`, `:580` and `:601` and `tasks.md:552` (T104) name the file as a planned profile that a leaf release supplies, with a binding of `mor.sets.matrix_ker` to Sage `right_kernel()`.
- Conclusion: I believe that the file is not written. This is an inference from the refs that were searched.
- Confidence: High for the local refs. GitHub was not queried.
- Gaps: branches that the local clones did not fetch; other machines.

`mor.sets.matrix_ker` has no registration in LEAVES.

The branches `origin/work/kernel-v1-independent-leaf-20261024` and `origin/work/lift-image-metadata-20261029` (`diagnostics/extensions-20261024/leaves.json`) and `origin/work/v1-contract-diagnostic-20261023` (`diagnostics/v1/leaves.json`) of the leaves repository hold other manifests. They are not on `main`. They were not read.

## 2. Owner categories

### 2.1 Registrations by owner category of the operation

| Owner category of the operation | Registrations | Operations (registrations) | Backends | Categories of the input forms (registrations) |
| --- | --- | --- | --- | --- |
| `cat.arrows_groups` | 2 | `meth.group_arrow_kernel` 1, `fun.arrows_groups.kernel` 1 | `gap-groups` | `cat.arrows_groups` 2 |
| `cat.bil_wform` | 1 | `colim.bil_w_form.cokernel` 1 | `sage-discriminant` | `cat.bil_wform` 1 |
| `cat.bilin_module` | 4 | `lift.bilin_module.restrict#obj` 1, `lift.bilin_module.restrict#hom` 1, `lift.bilin_module.restrict#forward` 1, `lift.bilin_module.restrict#backward` 1 | `sage-bilinear-lift` | `cat.arrows_bilin_module` 4 |
| `cat.commutative_rings` | 2 | `cmp.f9.translation` 2 | `sage-presentations` | `cat.commutative_rings` 2 |
| `cat.magmas` | 19 | `prop.is_commutative` 10, `prop.is_abelian` 9 | `gap-groups` | `cat.groups` 6, `cat.bil_wform` 6, `cat.subobjects_groups` 5, `cat.integral_lattice` 2 |
| `cat.modules_r` | 6 | `meth.rank` 6 | `sage-modules` | `cat.bil_wform` 3, `cat.modules_r` 2, `cat.integral_lattice` 1 |
| `cat.sets` | 81 | `meth.cardinality` 30, `prop.is_finite` 24, `mor.sets.f9_x_constants` 2, `mor.sets.f9_y_constants` 2, `lim.sets.product` 1, `colim.sets.coproduct` 1, `lim.sets.pullback` 1, `mor.sets.fin_rev` 1, `mor.sets.complex_re` 1, `mor.sets.complex_im` 1, `mor.sets.complex_bar` 1, `mor.sets.complex_abs` 1, `mor.sets.real_sqrt` 1, `mor.sets.polynomial_degree` 1, `mor.sets.polynomial_derivative` 1, `mor.sets.polynomial_differential` 1, `mor.sets.polynomial_map` 1, `mor.sets.polynomial_factors` 1, `mor.sets.polynomial_roots` 1, `mor.sets.companion_matrix` 1, `mor.sets.mv_total_degree` 1, `mor.sets.nat_prime_factors` 1, `mor.sets.equality` 1, `mor.sets.span` 1, `bind.sets.integral` 1, `bind.sets.limit` 1, `bind.sets.limit_at_infinity` 1 | `gap`, `gap-groups`, `sage`, `sage-discriminant`, `sage-fin-rev`, `sage-modules`, `sage-power-set`, `sage-presentations`, `sage-set-limits`, `sage-symbolic` | `cat.sets` 55, `cat.groups` 6, `cat.subobjects_groups` 6, `cat.commutative_rings` 4, `cat.bil_wform` 3, `cat.modules_r` 2, `cat.finite_sets` 2, `cat.rings` 2, `cat.integral_lattice` 1 |
| Total | 115 |  |  |  |

### 2.2 Registrations by category of the input form

This table shows the category of the object that each registration takes as its input. A row whose operations have another owner is a computation on the carrier or on the underlying structure of that object.

| Category of the input form | Registrations | Operations [owner category] (registrations) |
| --- | --- | --- |
| `cat.arrows_bilin_module` | 4 | `lift.bilin_module.restrict#obj [cat.bilin_module]` 1, `lift.bilin_module.restrict#hom [cat.bilin_module]` 1, `lift.bilin_module.restrict#forward [cat.bilin_module]` 1, `lift.bilin_module.restrict#backward [cat.bilin_module]` 1 |
| `cat.arrows_groups` | 2 | `meth.group_arrow_kernel [cat.arrows_groups]` 1, `fun.arrows_groups.kernel [cat.arrows_groups]` 1 |
| `cat.bil_wform` | 13 | `meth.cardinality [cat.sets]` 3, `meth.rank [cat.modules_r]` 3, `prop.is_abelian [cat.magmas]` 3, `prop.is_commutative [cat.magmas]` 3, `colim.bil_w_form.cokernel [cat.bil_wform]` 1 |
| `cat.commutative_rings` | 6 | `meth.cardinality [cat.sets]` 2, `prop.is_finite [cat.sets]` 2, `cmp.f9.translation [cat.commutative_rings]` 2 |
| `cat.finite_sets` | 2 | `meth.cardinality [cat.sets]` 1, `prop.is_finite [cat.sets]` 1 |
| `cat.groups` | 12 | `meth.cardinality [cat.sets]` 3, `prop.is_finite [cat.sets]` 3, `prop.is_abelian [cat.magmas]` 3, `prop.is_commutative [cat.magmas]` 3 |
| `cat.integral_lattice` | 4 | `meth.rank [cat.modules_r]` 1, `meth.cardinality [cat.sets]` 1, `prop.is_abelian [cat.magmas]` 1, `prop.is_commutative [cat.magmas]` 1 |
| `cat.modules_r` | 4 | `meth.rank [cat.modules_r]` 2, `meth.cardinality [cat.sets]` 2 |
| `cat.rings` | 2 | `meth.cardinality [cat.sets]` 1, `prop.is_finite [cat.sets]` 1 |
| `cat.sets` | 55 | `meth.cardinality [cat.sets]` 14, `prop.is_finite [cat.sets]` 14, `mor.sets.f9_x_constants [cat.sets]` 2, `mor.sets.f9_y_constants [cat.sets]` 2, `lim.sets.product [cat.sets]` 1, `colim.sets.coproduct [cat.sets]` 1, `lim.sets.pullback [cat.sets]` 1, `mor.sets.fin_rev [cat.sets]` 1, `mor.sets.complex_re [cat.sets]` 1, `mor.sets.complex_im [cat.sets]` 1, `mor.sets.complex_bar [cat.sets]` 1, `mor.sets.complex_abs [cat.sets]` 1, `mor.sets.real_sqrt [cat.sets]` 1, `mor.sets.polynomial_degree [cat.sets]` 1, `mor.sets.polynomial_derivative [cat.sets]` 1, `mor.sets.polynomial_differential [cat.sets]` 1, `mor.sets.polynomial_map [cat.sets]` 1, `mor.sets.polynomial_factors [cat.sets]` 1, `mor.sets.polynomial_roots [cat.sets]` 1, `mor.sets.companion_matrix [cat.sets]` 1, `mor.sets.mv_total_degree [cat.sets]` 1, `mor.sets.nat_prime_factors [cat.sets]` 1, `mor.sets.equality [cat.sets]` 1, `mor.sets.span [cat.sets]` 1, `bind.sets.integral [cat.sets]` 1, `bind.sets.limit [cat.sets]` 1, `bind.sets.limit_at_infinity [cat.sets]` 1 |
| `cat.subobjects_groups` | 11 | `meth.cardinality [cat.sets]` 3, `prop.is_finite [cat.sets]` 3, `prop.is_commutative [cat.magmas]` 3, `prop.is_abelian [cat.magmas]` 2 |
| Total | 115 |  |

### 2.3 The named morphisms and binders that `cat.sets` owns, by declaring module

The catalogue registers 78 named morphisms and 8 binders at `cat.sets`. Most of them are maps between the carriers of other structures. The module of `lean-categories` that declares each one shows its mathematical area.

| Declaring module in `lean-categories` (`CasCatalogue.`...) | With a registration | With no registration | Registered addresses | Addresses with no registration |
| --- | --- | --- | --- | --- |
| `Algebra.Calculus` | 1 | 10 | `bind.sets.integral` | `mor.sets.real_sin`, `mor.sets.real_cos`, `mor.sets.real_exp`, `mor.sets.real_pi`, `mor.sets.power_series_coefficient`, `mor.sets.power_series_of_coefficients`, `mor.sets.monoid_power`, `mor.sets.taylor_expansion`, `mor.sets.smooth_derivative`, `mor.sets.smooth_continuous` |
| `Algebra.Differentials` | 2 | 5 | `mor.sets.polynomial_differential`, `mor.sets.polynomial_derivative` | `mor.sets.kaehler_coordinate`, `mor.sets.kaehler_from_coordinate`, `mor.sets.kaehler_dx`, `mor.sets.kaehler_scale`, `mor.sets.kaehler_primitives` |
| `Algebra.FiniteSums` | 0 | 4 |  | `mor.sets.finite_sum`, `mor.sets.finite_product`, `bind.sets.finite_sum`, `bind.sets.finite_product` |
| `Algebra.LinearAlgebra` | 2 | 11 | `mor.sets.companion_matrix`, `mor.sets.span` | `mor.sets.vector_component`, `mor.sets.vectors_zero`, `mor.sets.tuple_empty`, `mor.sets.tuple_cons`, `mor.sets.matrix_rows`, `mor.sets.matrix_det`, `mor.sets.matrix_trace`, `mor.sets.matrix_rank`, `mor.sets.matrix_charpoly`, `mor.sets.matrix_ker`, `mor.sets.span_dim` |
| `Algebra.MvPolynomials` | 1 | 1 | `mor.sets.mv_total_degree` | `mor.sets.krull_dimension` |
| `Algebra.NumberSystems` | 5 | 2 | `mor.sets.complex_re`, `mor.sets.complex_im`, `mor.sets.complex_bar`, `mor.sets.complex_abs`, `mor.sets.real_sqrt` | `mor.sets.gcd`, `mor.sets.complex_i` |
| `Algebra.PolynomialPresentations` | 2 | 0 | `mor.sets.f9_x_constants`, `mor.sets.f9_y_constants` |  |
| `Algebra.Polynomials` | 4 | 7 | `mor.sets.polynomial_degree`, `mor.sets.polynomial_factors`, `mor.sets.polynomial_roots`, `mor.sets.polynomial_map` | `mor.sets.polynomial_factorization`, `mor.sets.polynomial_factorization_unit`, `mor.sets.polynomial_factorization_factors`, `mor.sets.polynomial_factorization_product`, `mor.sets.polynomial_factorization_map`, `mor.sets.polynomial_own_evaluation`, `mor.sets.polynomial_selected_evaluation` |
| `Algebra.RealLimits` | 2 | 3 | `bind.sets.limit`, `bind.sets.limit_at_infinity` | `mor.sets.infinity`, `mor.sets.neg_infinity`, `mor.sets.punctured_units` |
| `Algebra.Semirings` | 1 | 2 | `mor.sets.nat_prime_factors` | `mor.sets.nat_is_prime`, `mor.sets.nat_multiplicity` |
| `Algebra.Series` | 0 | 3 |  | `bind.sets.real_series`, `bind.sets.complex_series`, `bind.sets.power_series_sum` |
| `Algebra.ShiftedDualNumbers` | 0 | 2 |  | `mor.sets.rational_dual_x_constants`, `mor.sets.rational_dual_y_constants` |
| `Algebra.Units` | 0 | 1 |  | `mor.sets.divide` |
| `Foundation.Morphisms` | 1 | 0 | `mor.sets.fin_rev` |  |
| `Foundation.PowerSets` | 1 | 1 | `mor.sets.equality` | `mor.sets.direct_image` |
| `Foundation.Terminals` | 0 | 1 |  | `mor.sets.terminal` |
| `Limits.Registration` | 0 | 6 |  | `mor.sets.diagram_limit_lift`, `mor.sets.diagram_limit_projection`, `mor.sets.diagram_colimit_desc`, `mor.sets.diagram_colimit_injection`, `mor.sets.diagram_limit_map`, `mor.sets.diagram_colimit_map` |
| `Modules.Bilinear.Valued.CatalogueRegistration` | 0 | 1 |  | `mor.sets.bilin_module_pairing` |
| `Modules.Bilinear.Valued.Constructions` | 0 | 3 |  | `mor.sets.formed_pairing`, `mor.sets.formed_form_map`, `mor.sets.formed_quadratic` |
| `Modules.Bilinear.Valued.Kernels` | 0 | 1 |  | `mor.sets.restricted_form_pairing` |

### 2.4 Coverage counts of each owner category

An object "that no backend text names or matches" is a constructor that no program lowers to an engine value.

| Owner category | Operation addresses | Addresses with a registration | Addresses with no registration | Registrations of its operations | Named objects | Objects that are an input form of a registration | Objects that no backend text names or matches |
| --- | --- | --- | --- | --- | --- | --- | --- |
| `cat.additive_commutative_monoids` | 2 | 0 | 2 | 0 | 0 | 0 | 0 |
| `cat.additive_groups` | 5 | 0 | 5 | 0 | 0 | 0 | 0 |
| `cat.additive_magmas` | 0 | 0 | 0 | 0 | 0 | 0 | 0 |
| `cat.additive_monoids` | 3 | 0 | 3 | 0 | 1 | 0 | 1 |
| `cat.additive_semigroups` | 0 | 0 | 0 | 0 | 0 | 0 | 0 |
| `cat.algebras` | 2 | 0 | 2 | 0 | 8 | 0 | 8 |
| `cat.alternating_forms` | 2 | 0 | 2 | 0 | 1 | 0 | 1 |
| `cat.arrows_bilin_module` | 4 | 0 | 4 | 0 | 0 | 0 | 0 |
| `cat.arrows_groups` | 7 | 2 | 5 | 2 | 0 | 0 | 0 |
| `cat.arrows_modules_r` | 19 | 0 | 19 | 0 | 0 | 0 | 0 |
| `cat.arrows_sets` | 2 | 0 | 2 | 0 | 0 | 0 | 0 |
| `cat.based_module` | 4 | 0 | 4 | 0 | 0 | 0 | 0 |
| `cat.based_module_indexed` | 2 | 0 | 2 | 0 | 0 | 0 | 0 |
| `cat.bil_wform` | 13 | 1 | 12 | 1 | 10 | 3 | 7 |
| `cat.bilin_forms_over_rings` | 2 | 0 | 2 | 0 | 0 | 0 | 0 |
| `cat.bilin_module` | 17 | 4 | 13 | 4 | 2 | 0 | 1 |
| `cat.boolean_algebras` | 7 | 0 | 7 | 0 | 1 | 0 | 1 |
| `cat.cardinalities` | 0 | 0 | 0 | 0 | 0 | 0 | 0 |
| `cat.cardinals` | 2 | 0 | 2 | 0 | 0 | 0 | 0 |
| `cat.commutative_monoids` | 2 | 0 | 2 | 0 | 0 | 0 | 0 |
| `cat.commutative_rings` | 14 | 1 | 13 | 2 | 10 | 2 | 3 |
| `cat.coord` | 2 | 0 | 2 | 0 | 0 | 0 | 0 |
| `cat.coord_indexed` | 0 | 0 | 0 | 0 | 0 | 0 | 0 |
| `cat.coord_lattice` | 4 | 0 | 4 | 0 | 0 | 0 | 0 |
| `cat.core_groups` | 9 | 0 | 9 | 0 | 0 | 0 | 0 |
| `cat.core_modules_r` | 11 | 0 | 11 | 0 | 0 | 0 | 0 |
| `cat.core_pointed_sets` | 5 | 0 | 5 | 0 | 0 | 0 | 0 |
| `cat.core_sets` | 9 | 0 | 9 | 0 | 0 | 0 | 0 |
| `cat.core_subobjects_modules_r` | 4 | 0 | 4 | 0 | 0 | 0 | 0 |
| `cat.core_subobjects_sets` | 10 | 0 | 10 | 0 | 0 | 0 | 0 |
| `cat.coslice_sets` | 0 | 0 | 0 | 0 | 0 | 0 | 0 |
| `cat.countable_sets` | 2 | 0 | 2 | 0 | 0 | 0 | 0 |
| `cat.crystals` | 0 | 0 | 0 | 0 | 0 | 0 | 0 |
| `cat.definite_lattice` | 0 | 0 | 0 | 0 | 0 | 0 | 0 |
| `cat.division_rings` | 2 | 0 | 2 | 0 | 0 | 0 | 0 |
| `cat.endofunctors_sets` | 0 | 0 | 0 | 0 | 0 | 0 | 0 |
| `cat.enumerated_sets` | 4 | 0 | 4 | 0 | 0 | 0 | 0 |
| `cat.even_integral_lattices` | 0 | 0 | 0 | 0 | 0 | 0 | 0 |
| `cat.even_lattice` | 0 | 0 | 0 | 0 | 0 | 0 | 0 |
| `cat.fields` | 2 | 0 | 2 | 0 | 3 | 0 | 0 |
| `cat.finite_free_lattice` | 0 | 0 | 0 | 0 | 0 | 0 | 0 |
| `cat.finite_free_lattices_over_rings` | 0 | 0 | 0 | 0 | 0 | 0 | 0 |
| `cat.finite_projective_lattice` | 2 | 0 | 2 | 0 | 0 | 0 | 0 |
| `cat.finite_projective_lattices_over_rings` | 2 | 0 | 2 | 0 | 0 | 0 | 0 |
| `cat.finite_sets` | 4 | 0 | 4 | 0 | 1 | 1 | 0 |
| `cat.finitelygeneratedmodules` | 2 | 0 | 2 | 0 | 0 | 0 | 0 |
| `cat.finiterankmodules` | 2 | 0 | 2 | 0 | 0 | 0 | 0 |
| `cat.fraction_field_perfect_finite_projective_lattice` | 2 | 0 | 2 | 0 | 0 | 0 | 0 |
| `cat.free_cover` | 0 | 0 | 0 | 0 | 0 | 0 | 0 |
| `cat.free_cover_indexed` | 2 | 0 | 2 | 0 | 0 | 0 | 0 |
| `cat.freemodules` | 2 | 0 | 2 | 0 | 0 | 0 | 0 |
| `cat.groups` | 9 | 0 | 9 | 0 | 3 | 3 | 0 |
| `cat.hausdorff_topological_commutative_monoids` | 2 | 0 | 2 | 0 | 1 | 0 | 1 |
| `cat.ideals_r` | 0 | 0 | 0 | 0 | 0 | 0 | 0 |
| `cat.indefinite_lattice` | 0 | 0 | 0 | 0 | 0 | 0 | 0 |
| `cat.integral_forms` | 2 | 0 | 2 | 0 | 0 | 0 | 0 |
| `cat.integral_lattice` | 2 | 0 | 2 | 0 | 1 | 1 | 0 |
| `cat.integral_lattices` | 2 | 0 | 2 | 0 | 0 | 0 | 0 |
| `cat.lattice` | 6 | 0 | 6 | 0 | 0 | 0 | 0 |
| `cat.lattices_over_rings` | 2 | 0 | 2 | 0 | 0 | 0 | 0 |
| `cat.linear_orders` | 7 | 0 | 7 | 0 | 4 | 0 | 0 |
| `cat.magmas` | 4 | 2 | 2 | 19 | 0 | 0 | 0 |
| `cat.magmaswithtwooperations` | 0 | 0 | 0 | 0 | 0 | 0 | 0 |
| `cat.module_points` | 2 | 0 | 2 | 0 | 0 | 0 | 0 |
| `cat.modules_over_rings_ext` | 2 | 0 | 2 | 0 | 0 | 0 | 0 |
| `cat.modules_r` | 22 | 1 | 21 | 6 | 7 | 2 | 5 |
| `cat.modules_total` | 7 | 0 | 7 | 0 | 0 | 0 | 0 |
| `cat.monoids` | 9 | 0 | 9 | 0 | 0 | 0 | 0 |
| `cat.ordinals` | 6 | 0 | 6 | 0 | 7 | 0 | 7 |
| `cat.partial_orders` | 3 | 0 | 3 | 0 | 0 | 0 | 0 |
| `cat.partially_ordered_sets` | 2 | 0 | 2 | 0 | 0 | 0 | 0 |
| `cat.pointed_sets` | 2 | 0 | 2 | 0 | 0 | 0 | 0 |
| `cat.quad_forms_over_rings` | 2 | 0 | 2 | 0 | 0 | 0 | 0 |
| `cat.quad_module` | 4 | 0 | 4 | 0 | 0 | 0 | 0 |
| `cat.quad_wform` | 4 | 0 | 4 | 0 | 0 | 0 | 0 |
| `cat.quotients_modules_r` | 6 | 0 | 6 | 0 | 0 | 0 | 0 |
| `cat.rings` | 15 | 0 | 15 | 0 | 9 | 1 | 4 |
| `cat.schemes` | 0 | 0 | 0 | 0 | 1 | 0 | 1 |
| `cat.schemes_over` | 0 | 0 | 0 | 0 | 0 | 0 | 0 |
| `cat.schemes_over_ring` | 0 | 0 | 0 | 0 | 2 | 0 | 2 |
| `cat.semigroups` | 2 | 0 | 2 | 0 | 0 | 0 | 0 |
| `cat.semirings` | 8 | 0 | 8 | 0 | 1 | 0 | 0 |
| `cat.sets` | 115 | 27 | 88 | 81 | 45 | 19 | 23 |
| `cat.sets.pair_diagrams` | 2 | 0 | 2 | 0 | 0 | 0 | 0 |
| `cat.slice_sets` | 2 | 0 | 2 | 0 | 0 | 0 | 0 |
| `cat.subobjects_bilin_module` | 5 | 0 | 5 | 0 | 0 | 0 | 0 |
| `cat.subobjects_groups` | 7 | 0 | 7 | 0 | 5 | 2 | 3 |
| `cat.subobjects_modules_r` | 9 | 0 | 9 | 0 | 1 | 0 | 1 |
| `cat.subobjects_sets` | 4 | 0 | 4 | 0 | 0 | 0 | 0 |
| `cat.subsets.point_predicates` | 0 | 0 | 0 | 0 | 0 | 0 | 0 |
| `cat.subsets.subset_predicates` | 0 | 0 | 0 | 0 | 0 | 0 | 0 |
| `cat.torsion_free_modules` | 2 | 0 | 2 | 0 | 0 | 0 | 0 |
| `cat.totally_ordered_sets` | 2 | 0 | 2 | 0 | 0 | 0 | 0 |
| `cat.unimodular_lattice` | 0 | 0 | 0 | 0 | 0 | 0 | 0 |
| `cat.unimodular_lattices_over_rings` | 0 | 0 | 0 | 0 | 0 | 0 | 0 |
| `cat.walking_pair` | 0 | 0 | 0 | 0 | 0 | 0 | 0 |
| `fam.modules(S)` | 3 | 0 | 3 | 0 | 0 | 0 | 0 |
| `total(clf.bilin_forms.even)` | 2 | 0 | 2 | 0 | 0 | 0 | 0 |
| `total(clf.bilin_forms.finite)` | 2 | 0 | 2 | 0 | 0 | 0 | 0 |
| `total(clf.bilin_forms.free)` | 2 | 0 | 2 | 0 | 0 | 0 | 0 |
| `total(clf.bilin_forms.lattice)` | 2 | 0 | 2 | 0 | 0 | 0 | 0 |
| `total(clf.bilin_forms.unimodular)` | 2 | 0 | 2 | 0 | 0 | 0 | 0 |
| `total(clf.bilin_forms.values)` | 2 | 0 | 2 | 0 | 0 | 0 | 0 |
| `total(clf.bilin_module.lattice)` | 2 | 0 | 2 | 0 | 0 | 0 | 0 |
| `total(clf.magmas.additive)` | 2 | 0 | 2 | 0 | 0 | 0 | 0 |
| `total(clf.magmas.commutative)` | 2 | 0 | 2 | 0 | 0 | 0 | 0 |
| `total(clf.magmas.inverse)` | 2 | 0 | 2 | 0 | 0 | 0 | 0 |
| `total(clf.magmas.multiplicative)` | 2 | 0 | 2 | 0 | 0 | 0 | 0 |
| `total(clf.magmas.unital)` | 2 | 0 | 2 | 0 | 0 | 0 | 0 |
| `total(clf.magmaswithtwooperations.distributive)` | 2 | 0 | 2 | 0 | 0 | 0 | 0 |
| `total(clf.sets.graded)` | 2 | 0 | 2 | 0 | 0 | 0 | 0 |
| Total | 502 | 38 | 464 | 115 | 124 | 34 | 69 |

### 2.5 Detail of each category

For each category the lists are complete. "Handled inside X" marks an address of section 1.4. For an object, "input of n" gives the number of registrations with that input form; "named in" gives the programs whose text contains the id; "matched by rule in" gives the programs that match the id by a rule on its text (`sage_symbolic.py:58-78`, `:93`, `:112`; `sage_set_limits.py:86-93`).

#### Categories that own a registered operation

##### `cat.arrows_groups`

Registrations present:

| Operation | Backend | Input forms | Input form addresses |
| --- | --- | --- | --- |
| `meth.group_arrow_kernel` | `gap-groups` | 1 | `cat.arrows_groups` |
| `fun.arrows_groups.kernel` | `gap-groups` | 1 | `cat.arrows_groups` |

Operations and functor actions with no registration:

- Classifier-forget and constructor-induced actions (source is this category) (2): `action:{"constructorMap":["ctor.arrow",{"functor":"fun.groups.monoid"}]}`, `action:{"constructorMap":["ctor.arrow",{"functor":"fun.groups.monoid"}]}#map`
- Functor actions (source is this category) (3): `fun.arrows_groups.codomain`, `fun.arrows_groups.kernel#map`, `fun.arrows_groups.codomain#map`

##### `cat.bil_wform`

Registrations present:

| Operation | Backend | Input forms | Input form addresses |
| --- | --- | --- | --- |
| `colim.bil_w_form.cokernel` | `sage-discriminant` | 1 | `cat.bil_wform` |

Operations and functor actions with no registration:

- Functor actions (source is this category) (4): `fun.bil_wform.carrier`, `fun.bil_wform.base_change`, `fun.bil_wform.carrier#map`, `fun.bil_wform.base_change#map`
- Named morphisms (8): `mor.bil_wform.from_module_maps`, `mor.bil_wform.to_metric_dual`, `mor.bil_wform.to_discriminant`, `mor.bil_wform.cokernel_projection`, `mor.bil_wform.cokernel_desc`, `mor.bil_wform.to_changed_values`, `mor.bil_wform.root_lattice_a_to_dual` (handled inside sage-discriminant), `mor.bil_wform.root_lattice_a_to_discriminant` (handled inside sage-discriminant)

Constructors (named objects):

- Input form of a registration (3): `obj.bil_wform.root_lattice_a` (input of 4; named in gap-groups, sage-discriminant, sage-modules), `obj.bil_wform.root_lattice_a_dual` (input of 4; named in gap-groups, sage-discriminant, sage-modules), `obj.bil_wform.root_lattice_a_discriminant` (input of 4; named in gap-groups, sage-discriminant, sage-modules)
- No registration names the object as its input form (7): `obj.bil_wform.formed`, `obj.bil_wform.integral_form`, `obj.bil_wform.metric_dual`, `obj.bil_wform.discriminant`, `obj.bil_wform.cokernel`, `obj.bil_wform.changed_values`, `obj.bil_wform.extended_scalars`

##### `cat.bilin_module`

Registrations present:

| Operation | Backend | Input forms | Input form addresses |
| --- | --- | --- | --- |
| `lift.bilin_module.restrict#obj` | `sage-bilinear-lift` | 1 | `lift.bilin_module.restrict#input` |
| `lift.bilin_module.restrict#hom` | `sage-bilinear-lift` | 1 | `lift.bilin_module.restrict#input` |
| `lift.bilin_module.restrict#forward` | `sage-bilinear-lift` | 1 | `lift.bilin_module.restrict#input` |
| `lift.bilin_module.restrict#backward` | `sage-bilinear-lift` | 1 | `lift.bilin_module.restrict#input` |

Operations and functor actions with no registration:

- Cell components (1): `cell.bilin_module.carrier_routes#component`
- Functor actions (source is this category) (8): `fun.bilin_module.forget` (handled inside sage-bilinear-lift), `fun.bilin_module.change_value`, `fun.bilin_module.base_change`, `fun.bilin_module.fixed_value`, `fun.bilin_module.forget#map`, `fun.bilin_module.change_value#map`, `fun.bilin_module.base_change#map`, `fun.bilin_module.fixed_value#map`
- Lift fields (1): `lift.bilin_module.restrict#factor`
- Named morphisms (1): `mor.bilin_module.restriction_inclusion`
- Properties (2): `prop.is_lattice`, `prop.bilin_module.is_alternating`

Constructors (named objects):

- No registration names the object as its input form (2): `obj.bilin_module.restriction`, `obj.bilin_module.bilinear_form` (named in sage-bilinear-lift)

##### `cat.commutative_rings`

Registrations present:

| Operation | Backend | Input forms | Input form addresses |
| --- | --- | --- | --- |
| `cmp.f9.translation` | `sage-presentations` | 2 | `obj.commutative_rings.f9_x`, `obj.commutative_rings.f9_y` |

Operations and functor actions with no registration:

- Cell components (1): `cell.commutative_rings.multiplicative_monoid#component`
- Functor actions (source is this category) (6): `fun.commutative_rings.ring` (handled inside sage-presentations), `fun.modules_ext.regular_section`, `fun.commutative_rings.multiplicative_commutative_monoid`, `fun.commutative_rings.ring#map`, `fun.modules_ext.regular_section#map`, `fun.commutative_rings.multiplicative_commutative_monoid#map`
- Named morphisms (4): `mor.commutative_rings.integer_coefficients` (handled inside sage-symbolic), `mor.commutative_rings.rational_real_coefficients` (handled inside sage-symbolic), `mor.commutative_rings.rational_complex_coefficients` (handled inside sage-symbolic), `mor.commutative_rings.real_complex_coefficients` (handled inside sage-symbolic)
- Presentation comparisons (2): `cmp.polynomial_quotient.translation`, `cmp.rational_dual.translation`

Constructors (named objects):

- Input form of a registration (2): `obj.commutative_rings.f9_x` (input of 3; named in sage-presentations), `obj.commutative_rings.f9_y` (input of 3; named in sage-presentations)
- No registration names the object as its input form (8): `obj.commutative_rings.polynomial_quotient`, `obj.commutative_rings.rational_dual_x`, `obj.commutative_rings.rational_dual_y`, `obj.commutative_rings.integers` (named in gap-groups, sage-modules; matched by rule in sage-set-limits, sage-symbolic), `obj.commutative_rings.integers_mod` (named in gap-groups, sage-modules, sage-presentations; matched by rule in sage-set-limits, sage-symbolic), `obj.commutative_rings.rationals` (named in gap-groups, sage-modules; matched by rule in sage-set-limits, sage-symbolic), `obj.commutative_rings.reals` (matched by rule in sage-symbolic), `obj.commutative_rings.complexes` (matched by rule in sage-symbolic)

##### `cat.magmas`

Registrations present:

| Operation | Backend | Input forms | Input form addresses |
| --- | --- | --- | --- |
| `prop.is_abelian` | `gap-groups` | 9 | `obj.groups.symmetric`, `obj.groups.cyclic`, `obj.subgroups.kernel`, `cat.subobjects_groups`, `obj.bil_wform.root_lattice_a`, `obj.bil_wform.root_lattice_a_dual`, `obj.bil_wform.root_lattice_a_discriminant`, `obj.integral_lattice.e8`, `obj.groups.units` |
| `prop.is_commutative` | `gap-groups` | 10 | `obj.groups.symmetric`, `obj.groups.cyclic`, `obj.subgroups.alternating`, `obj.subgroups.kernel`, `cat.subobjects_groups`, `obj.bil_wform.root_lattice_a`, `obj.bil_wform.root_lattice_a_dual`, `obj.bil_wform.root_lattice_a_discriminant`, `obj.integral_lattice.e8`, `obj.groups.units` |

Operations and functor actions with no registration:

- Classifier-forget and constructor-induced actions (source is this category) (2): `action:{"classifierForget":"clf.sets.binary_operation"}`, `action:{"classifierForget":"clf.sets.binary_operation"}#map`

##### `cat.modules_r`

Registrations present:

| Operation | Backend | Input forms | Input form addresses |
| --- | --- | --- | --- |
| `meth.rank` | `sage-modules` | 6 | `obj.modules.regular`, `obj.modules.vectors`, `obj.bil_wform.root_lattice_a`, `obj.bil_wform.root_lattice_a_dual`, `obj.bil_wform.root_lattice_a_discriminant`, `obj.integral_lattice.e8` |

Operations and functor actions with no registration:

- Element operations (2): `op.modules.zero`, `op.modules.scalar_action`
- Functor actions (source is this category) (2): `fun.modules.fibre_inclusion`, `fun.modules.fibre_inclusion#map`
- Limits and colimits (1): `lim.modules.product`
- Methods (2): `meth.annihilator`, `meth.dim`
- Named morphisms (14): `mor.modules.coimage_projection`, `mor.modules.image_inclusion`, `mor.modules.coimage_to_image`, `mor.modules.image_to_coimage`, `mor.modules.factor_thru_image`, `mor.modules.factor_thru_coimage`, `mor.modules.coimage_image_factorization`, `mor.modules.kernel_inclusion`, `mor.modules.linear_kernel_inclusion`, `mor.modules.kernel_to_linear_kernel`, `mor.modules.linear_kernel_to_kernel`, `mor.modules.matrix_linear_map`, `mor.modules.formed_carrier_map`, `mor.modules.formed_value_map`

Constructors (named objects):

- Input form of a registration (2): `obj.modules.regular` (input of 2; named in sage-modules), `obj.modules.vectors` (input of 2; named in sage-modules)
- No registration names the object as its input form (5): `obj.modules.linear_kernel`, `obj.modules.subobject_domain`, `obj.modules.subobject_ambient`, `obj.modules.formed_carrier`, `obj.modules.formed_values`

Inclusions, literal forms and graph forms: `incl.modules.chosen_subobject` (inclusion)

##### `cat.sets`

Registrations present:

| Operation | Backend | Input forms | Input form addresses |
| --- | --- | --- | --- |
| `meth.cardinality` | `sage` | 7 | `obj.sets.fin`, `obj.sets.naturals`, `obj.sets.positive_naturals`, `obj.sets.primes`, `obj.sets.integers`, `obj.sets.rationals`, `obj.finite_sets.fin` |
| `meth.cardinality` | `gap` | 3 | `obj.sets.integers_mod`, `obj.sets.integers_mod_power`, `obj.rings.integers_mod` |
| `prop.is_finite` | `sage` | 9 | `obj.sets.fin`, `obj.sets.naturals`, `obj.sets.positive_naturals`, `obj.sets.primes`, `obj.sets.integers`, `obj.sets.rationals`, `obj.sets.reals`, `obj.sets.complexes`, `obj.finite_sets.fin` |
| `prop.is_finite` | `gap` | 3 | `obj.sets.integers_mod`, `obj.sets.integers_mod_power`, `obj.rings.integers_mod` |
| `meth.cardinality` | `sage-power-set` | 1 | `obj.sets.power_set` |
| `lim.sets.product` | `sage-set-limits` | 1 | `cat.sets` |
| `colim.sets.coproduct` | `sage-set-limits` | 1 | `cat.sets` |
| `lim.sets.pullback` | `sage-set-limits` | 1 | `cat.sets` |
| `meth.cardinality` | `sage-discriminant` | 1 | `obj.bil_wform.root_lattice_a_discriminant` |
| `mor.sets.fin_rev` | `sage-fin-rev` | 1 | `mor.sets.fin_rev` |
| `meth.cardinality` | `gap-groups` | 8 | `obj.groups.symmetric`, `obj.groups.cyclic`, `obj.sets.permutations`, `obj.subgroups.alternating`, `obj.subgroups.kernel`, `cat.subobjects_groups`, `obj.groups.units`, `obj.sets.units` |
| `prop.is_finite` | `gap-groups` | 8 | `obj.groups.symmetric`, `obj.groups.cyclic`, `obj.sets.permutations`, `obj.subgroups.alternating`, `obj.subgroups.kernel`, `cat.subobjects_groups`, `obj.groups.units`, `obj.sets.units` |
| `meth.cardinality` | `sage-modules` | 5 | `obj.modules.regular`, `obj.modules.vectors`, `obj.bil_wform.root_lattice_a`, `obj.bil_wform.root_lattice_a_dual`, `obj.integral_lattice.e8` |
| `meth.cardinality` | `sage-presentations` | 4 | `obj.sets.f9_x`, `obj.sets.f9_y`, `obj.commutative_rings.f9_x`, `obj.commutative_rings.f9_y` |
| `prop.is_finite` | `sage-presentations` | 4 | `obj.sets.f9_x`, `obj.sets.f9_y`, `obj.commutative_rings.f9_x`, `obj.commutative_rings.f9_y` |
| `mor.sets.f9_x_constants` | `sage-presentations` | 2 | `mor.sets.f9_x_constants`, `obj.sets.integers_mod` |
| `mor.sets.f9_y_constants` | `sage-presentations` | 2 | `mor.sets.f9_y_constants`, `obj.sets.integers_mod` |
| `meth.cardinality` | `sage-set-limits` | 1 | `cat.sets` |
| `mor.sets.complex_re` | `sage-symbolic` | 1 | `obj.sets.complexes` |
| `mor.sets.complex_im` | `sage-symbolic` | 1 | `obj.sets.complexes` |
| `mor.sets.complex_bar` | `sage-symbolic` | 1 | `obj.sets.complexes` |
| `mor.sets.complex_abs` | `sage-symbolic` | 1 | `obj.sets.complexes` |
| `mor.sets.real_sqrt` | `sage-symbolic` | 1 | `obj.sets.reals` |
| `mor.sets.polynomial_degree` | `sage-symbolic` | 1 | `obj.sets.polynomials` |
| `mor.sets.polynomial_derivative` | `sage-symbolic` | 1 | `obj.sets.polynomials` |
| `mor.sets.polynomial_differential` | `sage-symbolic` | 1 | `obj.sets.polynomials` |
| `mor.sets.polynomial_map` | `sage-symbolic` | 1 | `obj.sets.polynomials` |
| `mor.sets.polynomial_factors` | `sage-symbolic` | 1 | `obj.sets.nonzero_polynomials` |
| `mor.sets.polynomial_roots` | `sage-symbolic` | 1 | `obj.sets.nonzero_polynomials` |
| `mor.sets.companion_matrix` | `sage-symbolic` | 1 | `obj.sets.monics` |
| `mor.sets.mv_total_degree` | `sage-symbolic` | 1 | `obj.sets.mv_polynomials` |
| `mor.sets.nat_prime_factors` | `sage-symbolic` | 1 | `obj.sets.positive_naturals` |
| `mor.sets.equality` | `sage-symbolic` | 1 | `mor.sets.equality` |
| `mor.sets.span` | `sage-symbolic` | 1 | `obj.sets.power_set` |
| `bind.sets.integral` | `sage-symbolic` | 1 | `cat.sets` |
| `bind.sets.limit` | `sage-symbolic` | 1 | `cat.sets` |
| `bind.sets.limit_at_infinity` | `sage-symbolic` | 1 | `cat.sets` |

Operations and functor actions with no registration:

- Binders (5): `bind.sets.finite_sum`, `bind.sets.finite_product`, `bind.sets.real_series`, `bind.sets.complex_series`, `bind.sets.power_series_sum`
- Cell components (3): `cell.sets.list.unit#component`, `cell.sets.list.join#component`, `cell.sets.list.reverse#component`
- Functor actions (source is this category) (10): `fun.sets.identity`, `fun.sets.finite_subsets.direct_image`, `fun.sets.list`, `fun.sets.pair_diagonal`, `fun.sets.whole_subset`, `fun.sets.identity#map`, `fun.sets.finite_subsets.direct_image#map`, `fun.sets.list#map`, `fun.sets.pair_diagonal#map`, `fun.sets.whole_subset#map`
- Limits and colimits (3): `lim.sets.diagram`, `colim.sets.diagram`, `lim.sets.terminal`
- Named morphisms (59): `mor.sets.gcd`, `mor.sets.complex_i` (handled inside sage-symbolic), `mor.sets.direct_image`, `mor.sets.divide` (handled inside sage-symbolic), `mor.sets.nat_is_prime`, `mor.sets.nat_multiplicity`, `mor.sets.polynomial_factorization`, `mor.sets.polynomial_factorization_unit`, `mor.sets.polynomial_factorization_factors`, `mor.sets.polynomial_factorization_product`, `mor.sets.polynomial_factorization_map`, `mor.sets.polynomial_own_evaluation`, `mor.sets.polynomial_selected_evaluation`, `mor.sets.krull_dimension`, `mor.sets.rational_dual_x_constants`, `mor.sets.rational_dual_y_constants`, `mor.sets.bilin_module_pairing`, `mor.sets.diagram_limit_lift`, `mor.sets.diagram_limit_projection`, `mor.sets.diagram_colimit_desc`, `mor.sets.diagram_colimit_injection`, `mor.sets.diagram_limit_map`, `mor.sets.diagram_colimit_map`, `mor.sets.kaehler_coordinate`, `mor.sets.kaehler_from_coordinate` (handled inside sage-symbolic), `mor.sets.kaehler_dx`, `mor.sets.kaehler_scale`, `mor.sets.kaehler_primitives`, `mor.sets.terminal` (handled inside sage-symbolic), `mor.sets.restricted_form_pairing`, `mor.sets.vector_component`, `mor.sets.vectors_zero`, `mor.sets.tuple_empty`, `mor.sets.tuple_cons`, `mor.sets.matrix_rows`, `mor.sets.matrix_det`, `mor.sets.matrix_trace`, `mor.sets.matrix_rank`, `mor.sets.matrix_charpoly`, `mor.sets.matrix_ker`, `mor.sets.span_dim`, `mor.sets.finite_sum`, `mor.sets.finite_product`, `mor.sets.real_sin` (handled inside sage-symbolic), `mor.sets.real_cos` (handled inside sage-symbolic), `mor.sets.real_exp` (handled inside sage-symbolic), `mor.sets.real_pi` (handled inside sage-symbolic), `mor.sets.power_series_coefficient`, `mor.sets.power_series_of_coefficients`, `mor.sets.monoid_power`, `mor.sets.taylor_expansion`, `mor.sets.smooth_derivative`, `mor.sets.smooth_continuous`, `mor.sets.infinity` (handled inside sage-symbolic), `mor.sets.neg_infinity` (handled inside sage-symbolic), `mor.sets.punctured_units`, `mor.sets.formed_pairing`, `mor.sets.formed_form_map`, `mor.sets.formed_quadratic`
- Object applications (6): `obj.sets.polynomials#application`, `obj.sets.matrices#application` (handled inside sage-symbolic), `obj.sets.smooth_maps#application`, `obj.sets.bilinear_maps#application`, `obj.sets.group_morphisms#application`, `obj.sets.module_morphisms#application`
- Presentation comparisons (2): `cmp.sets.kaehler_polynomial_coordinates`, `cmp.sets.singleton_terminal`

Constructors (named objects):

- Input form of a registration (19): `obj.sets.naturals` (input of 2; named in sage, sage-power-set, sage-set-limits; matched by rule in sage-symbolic), `obj.sets.integers` (input of 2; named in gap-groups, sage, sage-modules, sage-power-set, sage-set-limits; matched by rule in sage-symbolic), `obj.sets.fin` (input of 2; named in sage, sage-fin-rev, sage-power-set, sage-presentations, sage-set-limits, sage-symbolic), `obj.sets.integers_mod` (input of 4; named in gap, gap-groups, sage-modules, sage-power-set, sage-presentations, sage-set-limits; matched by rule in sage-symbolic), `obj.sets.integers_mod_power` (input of 2; named in gap), `obj.sets.rationals` (input of 2; named in gap-groups, sage, sage-modules, sage-power-set, sage-set-limits; matched by rule in sage-symbolic), `obj.sets.reals` (input of 2; named in sage, sage-set-limits, sage-symbolic), `obj.sets.complexes` (input of 5; named in sage, sage-set-limits; matched by rule in sage-symbolic), `obj.sets.power_set` (input of 2; named in sage-power-set), `obj.sets.units` (input of 2; named in gap-groups), `obj.sets.positive_naturals` (input of 3; named in sage, sage-power-set, sage-set-limits; matched by rule in sage-symbolic), `obj.sets.primes` (input of 2; named in sage, sage-power-set, sage-set-limits), `obj.sets.polynomials` (input of 4; named in sage-set-limits, sage-symbolic), `obj.sets.nonzero_polynomials` (input of 2; named in sage-symbolic), `obj.sets.mv_polynomials` (input of 1; named in sage-symbolic), `obj.sets.f9_x` (input of 2; named in sage-presentations), `obj.sets.f9_y` (input of 2; named in sage-presentations), `obj.sets.monics` (input of 1; named in sage-symbolic), `obj.sets.permutations` (input of 2; named in gap-groups)
- No registration names the object as its input form (26): `obj.sets.truth_values`, `obj.sets.finite_subsets`, `obj.sets.degrees`, `obj.sets.polynomial_factorization_data`, `obj.sets.polynomial_factor_multisets`, `obj.sets.krull_dimensions`, `obj.sets.polynomial_quotient`, `obj.sets.rational_dual_x`, `obj.sets.rational_dual_y`, `obj.sets.kaehler_polynomials`, `obj.sets.terminal` (named in sage-fin-rev, sage-presentations, sage-symbolic), `obj.sets.vectors` (named in sage-symbolic), `obj.sets.matrices`, `obj.sets.maps`, `obj.sets.continuous_maps`, `obj.sets.smooth_maps`, `obj.sets.power_series`, `obj.sets.summable_families`, `obj.sets.extended_reals`, `obj.sets.infinities`, `obj.sets.punctured_line`, `obj.sets.convergent_maps`, `obj.sets.convergent_maps_at_infinity`, `obj.sets.bilinear_maps` (named in sage-bilinear-lift), `obj.sets.group_morphisms`, `obj.sets.module_morphisms`

Inclusions, literal forms and graph forms: `graph.sets` (graphLiteral), `incl.sets.fin_integers_mod` (inclusion), `incl.sets.naturals_integers` (inclusion; named in sage-symbolic), `incl.sets.integers_rationals` (inclusion; named in sage-symbolic), `incl.sets.rationals_reals` (inclusion; named in sage-symbolic), `incl.sets.reals_complexes` (inclusion; named in sage-symbolic), `incl.sets.naturals_degrees` (inclusion), `incl.sets.naturals_krull_dimensions` (inclusion), `incl.sets.reals_extended_reals` (inclusion), `incl.sets.punctured_units` (inclusion)

#### Categories that own no registered operation

##### `cat.additive_commutative_monoids`

Operations and functor actions with no registration:

- Functor actions (source is this category) (2): `fun.additive_commutative_monoids.additive_monoid`, `fun.additive_commutative_monoids.additive_monoid#map`

##### `cat.additive_groups`

Operations and functor actions with no registration:

- Cell components (1): `cell.additive_groups.carrier#component`
- Functor actions (source is this category) (4): `fun.additive_groups.to_groups`, `fun.additive_groups.additive_monoid`, `fun.additive_groups.to_groups#map`, `fun.additive_groups.additive_monoid#map`

##### `cat.additive_monoids`

Operations and functor actions with no registration:

- Element operations (1): `op.additive_monoids.add`
- Functor actions (source is this category) (2): `fun.additive_monoids.underlying`, `fun.additive_monoids.underlying#map`

Constructors (named objects):

- No registration names the object as its input form (1): `obj.additive_monoids.vectors`

##### `cat.algebras`

Operations and functor actions with no registration:

- Functor actions (source is this category) (2): `fun.algebras.forget`, `fun.algebras.forget#map`

Constructors (named objects):

- No registration names the object as its input form (8): `obj.algebras.scalar_extension`, `obj.algebras.mv_polynomials`, `obj.algebras.polynomials`, `obj.algebras.real_integer`, `obj.algebras.real_rational`, `obj.algebras.complex_integer`, `obj.algebras.complex_rational`, `obj.algebras.complex_real`

##### `cat.alternating_forms`

Operations and functor actions with no registration:

- Classifier-forget and constructor-induced actions (source is this category) (2): `action:{"classifierForget":"clf.bilin_module.alternating"}`, `action:{"classifierForget":"clf.bilin_module.alternating"}#map`

Constructors (named objects):

- No registration names the object as its input form (1): `obj.alternating_forms.chosen_form`

##### `cat.arrows_bilin_module`

Operations and functor actions with no registration:

- Classifier-forget and constructor-induced actions (source is this category) (4): `action:{"constructorMap":["ctor.arrow",{"functor":"fun.bilin_module.forget"}]}`, `action:{"constructorMap":["ctor.arrow",{"functor":"fun.bilin_module.forget"}]}#map`, `action:{"constructorMap":["ctor.arrow",{"functor":"fun.bilin_module.fixed_value"}]}`, `action:{"constructorMap":["ctor.arrow",{"functor":"fun.bilin_module.fixed_value"}]}#map`

##### `cat.arrows_modules_r`

Operations and functor actions with no registration:

- Cell components (1): `cell.modules.coimage_image#component`
- Classifier-forget and constructor-induced actions (source is this category) (2): `action:{"constructorMap":["ctor.arrow",{"functor":"fun.modules.fibre_inclusion"}]}`, `action:{"constructorMap":["ctor.arrow",{"functor":"fun.modules.fibre_inclusion"}]}#map`
- Functor actions (source is this category) (10): `fun.arrows_modules.kernel`, `fun.arrows_modules.cokernel`, `fun.arrows_modules.image`, `fun.arrows_modules.coimage`, `fun.arrows_modules.coimage_image_comparison`, `fun.arrows_modules.kernel#map`, `fun.arrows_modules.cokernel#map`, `fun.arrows_modules.image#map`, `fun.arrows_modules.coimage#map`, `fun.arrows_modules.coimage_image_comparison#map`
- Methods (6): `meth.kernel`, `meth.arrow_coker`, `meth.arrow_ker`, `meth.arrow_im`, `meth.arrow_coim`, `meth.arrow_coimage_image_comparison`

##### `cat.arrows_sets`

Operations and functor actions with no registration:

- Classifier-forget and constructor-induced actions (source is this category) (2): `action:{"constructorMap":["ctor.arrow",{"functor":"fun.sets.whole_subset"}]}`, `action:{"constructorMap":["ctor.arrow",{"functor":"fun.sets.whole_subset"}]}#map`

##### `cat.based_module`

Operations and functor actions with no registration:

- Functor actions (source is this category) (4): `fun.based_module.to_free_cover`, `fun.coord.from_based_module`, `fun.based_module.to_free_cover#map`, `fun.coord.from_based_module#map`

##### `cat.based_module_indexed`

Operations and functor actions with no registration:

- Functor actions (source is this category) (2): `fun.based_module.forget`, `fun.based_module.forget#map`

##### `cat.bilin_forms_over_rings`

Operations and functor actions with no registration:

- Functor actions (source is this category) (2): `fun.bilin_forms.values`, `fun.bilin_forms.values#map`

##### `cat.boolean_algebras`

Operations and functor actions with no registration:

- Element operations (5): `op.boolean_algebras.union`, `op.boolean_algebras.inter`, `op.boolean_algebras.diff`, `op.boolean_algebras.symm_diff`, `op.boolean_algebras.subset`
- Functor actions (source is this category) (2): `fun.boolean_algebras.forget`, `fun.boolean_algebras.forget#map`

Constructors (named objects):

- No registration names the object as its input form (1): `obj.boolean_algebras.power_set`

##### `cat.cardinals`

Operations and functor actions with no registration:

- Functor actions (source is this category) (2): `fun.cardinals.to_cardinalities`, `fun.cardinals.to_cardinalities#map`

Inclusions, literal forms and graph forms: `lit.cardinals` (literal)

##### `cat.commutative_monoids`

Operations and functor actions with no registration:

- Functor actions (source is this category) (2): `fun.commutative_monoids.monoid`, `fun.commutative_monoids.monoid#map`

##### `cat.coord`

Operations and functor actions with no registration:

- Functor actions (source is this category) (2): `fun.coord.forget`, `fun.coord.forget#map`

##### `cat.coord_lattice`

Operations and functor actions with no registration:

- Functor actions (source is this category) (4): `fun.coord_lattice.to_coord`, `fun.coord_lattice.to_integral`, `fun.coord_lattice.to_coord#map`, `fun.coord_lattice.to_integral#map`

##### `cat.core_groups`

Operations and functor actions with no registration:

- Cell components (1): `cell.core_groups.automorphisms_units#component`
- Classifier-forget and constructor-induced actions (source is this category) (2): `action:{"constructorMap":["ctor.core",{"functor":"fun.groups.monoid"}]}`, `action:{"constructorMap":["ctor.core",{"functor":"fun.groups.monoid"}]}#map`
- Functor actions (source is this category) (6): `fun.core_groups.automorphisms`, `fun.core_groups.endomorphisms`, `fun.core_groups.centers`, `fun.core_groups.automorphisms#map`, `fun.core_groups.endomorphisms#map`, `fun.core_groups.centers#map`

##### `cat.core_modules_r`

Operations and functor actions with no registration:

- Cell components (1): `cell.core_modules_r.automorphisms_units#component`
- Classifier-forget and constructor-induced actions (source is this category) (2): `action:{"constructorMap":["ctor.core",{"functor":"fun.modules.fibre_inclusion"}]}`, `action:{"constructorMap":["ctor.core",{"functor":"fun.modules.fibre_inclusion"}]}#map`
- Functor actions (source is this category) (8): `fun.modules.rank`, `fun.core_modules_r.automorphisms`, `fun.core_modules_r.endomorphisms`, `fun.modules.annihilator`, `fun.modules.rank#map`, `fun.core_modules_r.automorphisms#map`, `fun.core_modules_r.endomorphisms#map`, `fun.modules.annihilator#map`

##### `cat.core_pointed_sets`

Operations and functor actions with no registration:

- Cell components (1): `cell.core_pointed_sets.stabilizer_ambient#component`
- Classifier-forget and constructor-induced actions (source is this category) (2): `action:{"constructorMap":["ctor.core",{"functor":"fun.pointed_sets.projection"}]}`, `action:{"constructorMap":["ctor.core",{"functor":"fun.pointed_sets.projection"}]}#map`
- Functor actions (source is this category) (2): `fun.core_pointed_sets.stabilizer`, `fun.core_pointed_sets.stabilizer#map`

##### `cat.core_sets`

Operations and functor actions with no registration:

- Cell components (1): `cell.core_sets.automorphisms_units#component`
- Classifier-forget and constructor-induced actions (source is this category) (2): `action:{"constructorMap":["ctor.core",{"functor":"fun.sets.whole_subset"}]}`, `action:{"constructorMap":["ctor.core",{"functor":"fun.sets.whole_subset"}]}#map`
- Functor actions (source is this category) (6): `fun.sets.cardinality`, `fun.core_sets.automorphisms`, `fun.core_sets.endomorphisms`, `fun.sets.cardinality#map`, `fun.core_sets.automorphisms#map`, `fun.core_sets.endomorphisms#map`

##### `cat.core_subobjects_modules_r`

Operations and functor actions with no registration:

- Classifier-forget and constructor-induced actions (source is this category) (2): `action:{"constructorMap":["ctor.core",{"functor":"fun.subobjects_modules.forget"}]}`, `action:{"constructorMap":["ctor.core",{"functor":"fun.subobjects_modules.forget"}]}#map`
- Functor actions (source is this category) (2): `fun.subobjects_modules.rank`, `fun.subobjects_modules.rank#map`

##### `cat.core_subobjects_sets`

Operations and functor actions with no registration:

- Classifier-forget and constructor-induced actions (source is this category) (2): `action:{"constructorMap":["ctor.core",{"functor":"fun.subobjects_sets.domain"}]}`, `action:{"constructorMap":["ctor.core",{"functor":"fun.subobjects_sets.domain"}]}#map`
- Functor actions (source is this category) (8): `fun.subsets.point_predicates`, `fun.subsets.subset_predicates`, `fun.subsets.contains`, `fun.subsets.set_eq`, `fun.subsets.point_predicates#map`, `fun.subsets.subset_predicates#map`, `fun.subsets.contains#map`, `fun.subsets.set_eq#map`

##### `cat.countable_sets`

Operations and functor actions with no registration:

- Classifier-forget and constructor-induced actions (source is this category) (2): `action:{"classifierForget":"clf.sets.countable"}`, `action:{"classifierForget":"clf.sets.countable"}#map`

##### `cat.division_rings`

Operations and functor actions with no registration:

- Classifier-forget and constructor-induced actions (source is this category) (2): `action:{"classifierForget":"clf.division"}`, `action:{"classifierForget":"clf.division"}#map`

##### `cat.enumerated_sets`

Operations and functor actions with no registration:

- Classifier-forget and constructor-induced actions (source is this category) (2): `action:{"classifierForget":"clf.sets.enumerated"}`, `action:{"classifierForget":"clf.sets.enumerated"}#map`
- Functor actions (source is this category) (2): `fun.sets.enumerated_to_countable`, `fun.sets.enumerated_to_countable#map`

##### `cat.fields`

Operations and functor actions with no registration:

- Classifier-forget and constructor-induced actions (source is this category) (2): `action:{"classifierForget":"clf.commutative_rings.field"}`, `action:{"classifierForget":"clf.commutative_rings.field"}#map`

Constructors (named objects):

- No registration names the object as its input form (3): `obj.fields.rationals` (named in sage-modules; matched by rule in sage-set-limits, sage-symbolic), `obj.fields.reals` (matched by rule in sage-symbolic), `obj.fields.complexes` (matched by rule in sage-symbolic)

##### `cat.finite_projective_lattice`

Operations and functor actions with no registration:

- Functor actions (source is this category) (2): `fun.finite_projective_lattice.forget`, `fun.finite_projective_lattice.forget#map`

##### `cat.finite_projective_lattices_over_rings`

Operations and functor actions with no registration:

- Functor actions (source is this category) (2): `fun.finite_projective_lattices.to_bil`, `fun.finite_projective_lattices.to_bil#map`

##### `cat.finite_sets`

Operations and functor actions with no registration:

- Classifier-forget and constructor-induced actions (source is this category) (2): `action:{"classifierForget":"clf.sets.finite"}`, `action:{"classifierForget":"clf.sets.finite"}#map`
- Functor actions (source is this category) (2): `fun.sets.finite_to_countable`, `fun.sets.finite_to_countable#map`

Constructors (named objects):

- Input form of a registration (1): `obj.finite_sets.fin` (input of 2; named in sage, sage-power-set, sage-set-limits)

Inclusions, literal forms and graph forms: `graph.finite_sets` (graphLiteral)

##### `cat.finitelygeneratedmodules`

Operations and functor actions with no registration:

- Classifier-forget and constructor-induced actions (source is this category) (2): `action:{"classifierForget":"clf.modules_finitelygenerated"}`, `action:{"classifierForget":"clf.modules_finitelygenerated"}#map`

##### `cat.finiterankmodules`

Operations and functor actions with no registration:

- Classifier-forget and constructor-induced actions (source is this category) (2): `action:{"classifierForget":"clf.modules_finiterank"}`, `action:{"classifierForget":"clf.modules_finiterank"}#map`

##### `cat.fraction_field_perfect_finite_projective_lattice`

Operations and functor actions with no registration:

- Functor actions (source is this category) (2): `fun.fraction_field_perfect_finite_projective_lattice.forget`, `fun.fraction_field_perfect_finite_projective_lattice.forget#map`

##### `cat.free_cover_indexed`

Operations and functor actions with no registration:

- Functor actions (source is this category) (2): `fun.free_cover.forget`, `fun.free_cover.forget#map`

##### `cat.freemodules`

Operations and functor actions with no registration:

- Classifier-forget and constructor-induced actions (source is this category) (2): `action:{"classifierForget":"clf.modules_free"}`, `action:{"classifierForget":"clf.modules_free"}#map`

##### `cat.groups`

Operations and functor actions with no registration:

- Direct constructions (target is this category) (2): `con.automorphisms`, `con.automorphisms#map`
- Element operations (1): `op.groups.inverse`
- Functor actions (source is this category) (2): `fun.groups.monoid` (handled inside gap-groups), `fun.groups.monoid#map`
- Limits and colimits (1): `lim.groups.kernel`
- Named morphisms (3): `mor.groups.sign` (handled inside gap-groups), `mor.groups.identity` (handled inside gap-groups), `mor.groups.trivial` (handled inside gap-groups)

Constructors (named objects):

- Input form of a registration (3): `obj.groups.units` (input of 4; named in gap-groups), `obj.groups.symmetric` (input of 4; named in gap-groups), `obj.groups.cyclic` (input of 4; named in gap-groups)

##### `cat.hausdorff_topological_commutative_monoids`

Operations and functor actions with no registration:

- Functor actions (source is this category) (2): `fun.hausdorff_topological_commutative_monoids.additive_commutative_monoid`, `fun.hausdorff_topological_commutative_monoids.additive_commutative_monoid#map`

Constructors (named objects):

- No registration names the object as its input form (1): `obj.hausdorff_topological_monoids.power_series`

##### `cat.integral_forms`

Operations and functor actions with no registration:

- Functor actions (source is this category) (2): `fun.integral_forms.to_bil`, `fun.integral_forms.to_bil#map`

##### `cat.integral_lattice`

Operations and functor actions with no registration:

- Functor actions (source is this category) (2): `fun.integral_lattice.forget_form`, `fun.integral_lattice.forget_form#map`

Constructors (named objects):

- Input form of a registration (1): `obj.integral_lattice.e8` (input of 4; named in gap-groups, sage-modules)

##### `cat.integral_lattices`

Operations and functor actions with no registration:

- Functor actions (source is this category) (2): `fun.integral_lattices.to_bil`, `fun.integral_lattices.to_bil#map`

##### `cat.lattice`

Operations and functor actions with no registration:

- Functor actions (source is this category) (6): `fun.lattice.forget_form`, `fun.lattice.change_value`, `fun.lattice.base_change`, `fun.lattice.forget_form#map`, `fun.lattice.change_value#map`, `fun.lattice.base_change#map`

##### `cat.lattices_over_rings`

Operations and functor actions with no registration:

- Functor actions (source is this category) (2): `fun.lattices_over_rings.to_bil`, `fun.lattices_over_rings.to_bil#map`

##### `cat.linear_orders`

Operations and functor actions with no registration:

- Cell components (1): `cmp.linear_orders.carrier#component`
- Element operations (2): `op.linear_orders.le`, `op.linear_orders.lt`
- Functor actions (source is this category) (4): `fun.linear_orders.forget`, `fun.linear_orders.to_partial_orders`, `fun.linear_orders.forget#map`, `fun.linear_orders.to_partial_orders#map`

Constructors (named objects):

- No registration names the object as its input form (4): `obj.linear_orders.naturals` (matched by rule in sage-symbolic), `obj.linear_orders.integers` (matched by rule in sage-set-limits, sage-symbolic), `obj.linear_orders.rationals` (matched by rule in sage-set-limits, sage-symbolic), `obj.linear_orders.reals` (matched by rule in sage-symbolic)

##### `cat.module_points`

Operations and functor actions with no registration:

- Functor actions (source is this category) (2): `fun.module_points.projection`, `fun.module_points.projection#map`

##### `cat.modules_over_rings_ext`

Operations and functor actions with no registration:

- Functor actions (source is this category) (2): `fun.modules_ext.ring`, `fun.modules_ext.ring#map`

##### `cat.modules_total`

Operations and functor actions with no registration:

- Cell components (1): `cell.modules.additive_group_carrier#component`
- Functor actions (source is this category) (6): `fun.modules.underlying`, `fun.modules.additive_group`, `fun.modules.projection`, `fun.modules.underlying#map`, `fun.modules.additive_group#map`, `fun.modules.projection#map`

##### `cat.monoids`

Operations and functor actions with no registration:

- Direct constructions (target is this category) (2): `con.endomorphisms`, `con.endomorphisms#map`
- Element operations (2): `op.monoids.mul`, `op.monoids.one`
- Functor actions (source is this category) (4): `fun.monoids.semigroup`, `fun.monoids.units`, `fun.monoids.semigroup#map`, `fun.monoids.units#map`
- Methods (1): `meth.units`

##### `cat.ordinals`

Operations and functor actions with no registration:

- Functor actions (source is this category) (2): `fun.ordinals.card`, `fun.ordinals.card#map`
- Named morphisms (4): `mor.ordinals.natural_sum_map`, `mor.ordinals.natural_product_map`, `mor.ordinals.natural_sum_list_map`, `mor.ordinals.natural_product_list_map`

Constructors (named objects):

- No registration names the object as its input form (7): `obj.ordinals.sum`, `obj.ordinals.product`, `obj.ordinals.power`, `obj.ordinals.natural_sum`, `obj.ordinals.natural_product`, `obj.ordinals.natural_sum_list`, `obj.ordinals.natural_product_list`

##### `cat.partial_orders`

Operations and functor actions with no registration:

- Element operations (1): `op.partial_orders.le`
- Functor actions (source is this category) (2): `fun.partial_orders.forget`, `fun.partial_orders.forget#map`

##### `cat.partially_ordered_sets`

Operations and functor actions with no registration:

- Functor actions (source is this category) (2): `fun.sets.partially_ordered_to_sets`, `fun.sets.partially_ordered_to_sets#map`

##### `cat.pointed_sets`

Operations and functor actions with no registration:

- Functor actions (source is this category) (2): `fun.pointed_sets.projection`, `fun.pointed_sets.projection#map`

##### `cat.quad_forms_over_rings`

Operations and functor actions with no registration:

- Functor actions (source is this category) (2): `fun.quad_forms.ring`, `fun.quad_forms.ring#map`

##### `cat.quad_module`

Operations and functor actions with no registration:

- Functor actions (source is this category) (4): `fun.quad_module.forget`, `fun.quad_module.change_value`, `fun.quad_module.forget#map`, `fun.quad_module.change_value#map`

##### `cat.quad_wform`

Operations and functor actions with no registration:

- Functor actions (source is this category) (4): `fun.quad_wform.value`, `fun.quad_wform.carrier`, `fun.quad_wform.value#map`, `fun.quad_wform.carrier#map`

##### `cat.quotients_modules_r`

Operations and functor actions with no registration:

- Functor actions (source is this category) (4): `fun.quotients_modules.projection`, `fun.quotients_modules.codomain`, `fun.quotients_modules.projection#map`, `fun.quotients_modules.codomain#map`
- Methods (2): `meth.quotient_projection`, `meth.quotient_codomain`

##### `cat.rings`

Operations and functor actions with no registration:

- Cell components (3): `cmp.rings.carrier#component`, `cell.rings.additive_monoid_carrier#component`, `cell.rings.multiplicative_monoid.semiring#component`
- Element operations (4): `op.rings.add` (handled inside sage-presentations, sage-symbolic), `op.rings.mul` (handled inside sage-presentations, sage-symbolic), `op.rings.pow` (handled inside sage-presentations, sage-symbolic), `op.rings.neg` (handled inside sage-presentations, sage-symbolic)
- Functor actions (source is this category) (8): `fun.rings.multiplicative_monoid` (handled inside gap-groups, sage-symbolic), `fun.rings.additive_group`, `fun.rings.additive_commutative_monoid`, `fun.rings.semiring`, `fun.rings.multiplicative_monoid#map`, `fun.rings.additive_group#map`, `fun.rings.additive_commutative_monoid#map`, `fun.rings.semiring#map`

Constructors (named objects):

- Input form of a registration (1): `obj.rings.integers_mod` (input of 2; named in gap, gap-groups, sage-modules, sage-presentations, sage-set-limits; matched by rule in sage-symbolic)
- No registration names the object as its input form (8): `obj.rings.integers` (named in gap-groups, sage-modules; matched by rule in sage-set-limits, sage-symbolic), `obj.rings.rationals` (named in gap-groups, sage-modules; matched by rule in sage-set-limits, sage-symbolic), `obj.rings.reals` (matched by rule in sage-symbolic), `obj.rings.complexes` (matched by rule in sage-symbolic), `obj.rings.polynomials`, `obj.rings.mv_polynomials`, `obj.rings.matrices`, `obj.rings.power_series`

##### `cat.schemes`

Constructors (named objects):

- No registration names the object as its input form (1): `obj.schemes.spec_base`

##### `cat.schemes_over_ring`

Constructors (named objects):

- No registration names the object as its input form (2): `obj.schemes_over.spec_polynomials`, `obj.schemes_over.spec_mv_polynomials`

##### `cat.semigroups`

Operations and functor actions with no registration:

- Classifier-forget and constructor-induced actions (source is this category) (2): `action:{"classifierForget":"clf.magmas.associative"}`, `action:{"classifierForget":"clf.magmas.associative"}#map`

##### `cat.semirings`

Operations and functor actions with no registration:

- Cell components (1): `cell.semirings.carrier#component`
- Element operations (3): `op.semirings.add` (handled inside sage-symbolic), `op.semirings.mul` (handled inside sage-symbolic), `op.semirings.pow` (handled inside sage-symbolic)
- Functor actions (source is this category) (4): `fun.semirings.forget`, `fun.semirings.monoid`, `fun.semirings.forget#map`, `fun.semirings.monoid#map`

Constructors (named objects):

- No registration names the object as its input form (1): `obj.semirings.naturals` (matched by rule in sage-symbolic)

##### `cat.sets.pair_diagrams`

Operations and functor actions with no registration:

- Functor actions (source is this category) (2): `fun.sets.pair_limit`, `fun.sets.pair_limit#map`

##### `cat.slice_sets`

Operations and functor actions with no registration:

- Functor actions (source is this category) (2): `fun.slice_sets.forget`, `fun.slice_sets.forget#map`

##### `cat.subobjects_bilin_module`

Operations and functor actions with no registration:

- Functor actions (source is this category) (4): `fun.subobjects_bilin_module.domain`, `fun.subobjects_bilin_module.inclusion`, `fun.subobjects_bilin_module.domain#map`, `fun.subobjects_bilin_module.inclusion#map`
- Methods (1): `meth.bilin_module.inclusion`

##### `cat.subobjects_groups`

Operations and functor actions with no registration:

- Direct constructions (target is this category) (2): `con.stabilizers`, `con.stabilizers#map`
- Functor actions (source is this category) (4): `fun.subobjects_groups.domain` (handled inside gap-groups), `fun.subobjects_groups.inclusion`, `fun.subobjects_groups.domain#map`, `fun.subobjects_groups.inclusion#map`
- Methods (1): `meth.inclusion`

Constructors (named objects):

- Input form of a registration (2): `obj.subgroups.alternating` (input of 3; named in gap-groups), `obj.subgroups.kernel` (input of 4; named in gap-groups)
- No registration names the object as its input form (3): `obj.subgroups.action_stabilizer`, `obj.subgroups.center`, `obj.subgroups.subgroup`

##### `cat.subobjects_modules_r`

Operations and functor actions with no registration:

- Functor actions (source is this category) (6): `fun.subobjects_modules.inclusion`, `fun.subobjects_modules.forget`, `fun.subobjects_modules.domain`, `fun.subobjects_modules.inclusion#map`, `fun.subobjects_modules.forget#map`, `fun.subobjects_modules.domain#map`
- Methods (3): `meth.submodule_inclusion`, `meth.submodule_domain`, `meth.subobject_dim`

Constructors (named objects):

- No registration names the object as its input form (1): `obj.subobjects_modules.span`

##### `cat.subobjects_sets`

Operations and functor actions with no registration:

- Functor actions (source is this category) (2): `fun.subobjects_sets.domain`, `fun.subobjects_sets.domain#map`
- Methods (2): `meth.contains`, `meth.set_eq`

##### `cat.torsion_free_modules`

Operations and functor actions with no registration:

- Classifier-forget and constructor-induced actions (source is this category) (2): `action:{"classifierForget":"clf.modules.torsion_free"}`, `action:{"classifierForget":"clf.modules.torsion_free"}#map`

##### `cat.totally_ordered_sets`

Operations and functor actions with no registration:

- Functor actions (source is this category) (2): `fun.sets.totally_ordered_to_sets`, `fun.sets.totally_ordered_to_sets#map`

##### `fam.modules(S)`

Operations and functor actions with no registration:

- Functor actions (source is this category) (3): `fun.modules.reindex`, `fun.modules.reindex#cartesian`, `fun.modules.reindex#map`

##### `total(clf.bilin_forms.even)`

Operations and functor actions with no registration:

- Classifier-forget and constructor-induced actions (source is this category) (2): `action:{"classifierForget":"clf.bilin_forms.even"}`, `action:{"classifierForget":"clf.bilin_forms.even"}#map`

##### `total(clf.bilin_forms.finite)`

Operations and functor actions with no registration:

- Classifier-forget and constructor-induced actions (source is this category) (2): `action:{"classifierForget":"clf.bilin_forms.finite"}`, `action:{"classifierForget":"clf.bilin_forms.finite"}#map`

##### `total(clf.bilin_forms.free)`

Operations and functor actions with no registration:

- Classifier-forget and constructor-induced actions (source is this category) (2): `action:{"classifierForget":"clf.bilin_forms.free"}`, `action:{"classifierForget":"clf.bilin_forms.free"}#map`

##### `total(clf.bilin_forms.lattice)`

Operations and functor actions with no registration:

- Classifier-forget and constructor-induced actions (source is this category) (2): `action:{"classifierForget":"clf.bilin_forms.lattice"}`, `action:{"classifierForget":"clf.bilin_forms.lattice"}#map`

##### `total(clf.bilin_forms.unimodular)`

Operations and functor actions with no registration:

- Classifier-forget and constructor-induced actions (source is this category) (2): `action:{"classifierForget":"clf.bilin_forms.unimodular"}`, `action:{"classifierForget":"clf.bilin_forms.unimodular"}#map`

##### `total(clf.bilin_forms.values)`

Operations and functor actions with no registration:

- Classifier-forget and constructor-induced actions (source is this category) (2): `action:{"classifierForget":"clf.bilin_forms.values"}`, `action:{"classifierForget":"clf.bilin_forms.values"}#map`

##### `total(clf.bilin_module.lattice)`

Operations and functor actions with no registration:

- Classifier-forget and constructor-induced actions (source is this category) (2): `action:{"classifierForget":"clf.bilin_module.lattice"}`, `action:{"classifierForget":"clf.bilin_module.lattice"}#map`

##### `total(clf.magmas.additive)`

Operations and functor actions with no registration:

- Classifier-forget and constructor-induced actions (source is this category) (2): `action:{"classifierForget":"clf.magmas.additive"}`, `action:{"classifierForget":"clf.magmas.additive"}#map`

##### `total(clf.magmas.commutative)`

Operations and functor actions with no registration:

- Classifier-forget and constructor-induced actions (source is this category) (2): `action:{"classifierForget":"clf.magmas.commutative"}`, `action:{"classifierForget":"clf.magmas.commutative"}#map`

##### `total(clf.magmas.inverse)`

Operations and functor actions with no registration:

- Classifier-forget and constructor-induced actions (source is this category) (2): `action:{"classifierForget":"clf.magmas.inverse"}`, `action:{"classifierForget":"clf.magmas.inverse"}#map`

##### `total(clf.magmas.multiplicative)`

Operations and functor actions with no registration:

- Classifier-forget and constructor-induced actions (source is this category) (2): `action:{"classifierForget":"clf.magmas.multiplicative"}`, `action:{"classifierForget":"clf.magmas.multiplicative"}#map`

##### `total(clf.magmas.unital)`

Operations and functor actions with no registration:

- Classifier-forget and constructor-induced actions (source is this category) (2): `action:{"classifierForget":"clf.magmas.unital"}`, `action:{"classifierForget":"clf.magmas.unital"}#map`

##### `total(clf.magmaswithtwooperations.distributive)`

Operations and functor actions with no registration:

- Classifier-forget and constructor-induced actions (source is this category) (2): `action:{"classifierForget":"clf.magmaswithtwooperations.distributive"}`, `action:{"classifierForget":"clf.magmaswithtwooperations.distributive"}#map`

##### `total(clf.sets.graded)`

Operations and functor actions with no registration:

- Classifier-forget and constructor-induced actions (source is this category) (2): `action:{"classifierForget":"clf.sets.graded"}`, `action:{"classifierForget":"clf.sets.graded"}#map`

Registered categories with no operation address and no named object in the catalogue (22): `cat.additive_magmas`, `cat.additive_semigroups`, `cat.cardinalities`, `cat.coord_indexed`, `cat.coslice_sets`, `cat.crystals`, `cat.definite_lattice`, `cat.endofunctors_sets`, `cat.even_integral_lattices`, `cat.even_lattice`, `cat.finite_free_lattice`, `cat.finite_free_lattices_over_rings`, `cat.free_cover`, `cat.ideals_r`, `cat.indefinite_lattice`, `cat.magmaswithtwooperations`, `cat.schemes_over`, `cat.subsets.point_predicates`, `cat.subsets.subset_predicates`, `cat.unimodular_lattice`, `cat.unimodular_lattices_over_rings`, `cat.walking_pair`


### 2.6 Registrations that overlap under the manifest rule

`api/manifest.md:191-195` of CONTRACT says that an exact-form registration and a category-wide registration have equal standing, and that an invocation to which both apply is ambiguous. Each row is one pair of registrations of one operation: one on a category address, one on a named form of that category. The kernel was not run to observe the outcome.

| Operation | Category-wide input | Backend of the category-wide registration | Exact input form of the same category | Backend of the exact registration |
| --- | --- | --- | --- | --- |
| `meth.cardinality` | `cat.subobjects_groups` | `gap-groups` | `obj.subgroups.alternating` | `gap-groups` |
| `meth.cardinality` | `cat.subobjects_groups` | `gap-groups` | `obj.subgroups.kernel` | `gap-groups` |
| `meth.cardinality` | `cat.sets` | `sage-set-limits` | `obj.sets.fin` | `sage` |
| `meth.cardinality` | `cat.sets` | `sage-set-limits` | `obj.sets.naturals` | `sage` |
| `meth.cardinality` | `cat.sets` | `sage-set-limits` | `obj.sets.positive_naturals` | `sage` |
| `meth.cardinality` | `cat.sets` | `sage-set-limits` | `obj.sets.primes` | `sage` |
| `meth.cardinality` | `cat.sets` | `sage-set-limits` | `obj.sets.integers` | `sage` |
| `meth.cardinality` | `cat.sets` | `sage-set-limits` | `obj.sets.rationals` | `sage` |
| `meth.cardinality` | `cat.sets` | `sage-set-limits` | `obj.sets.integers_mod` | `gap` |
| `meth.cardinality` | `cat.sets` | `sage-set-limits` | `obj.sets.integers_mod_power` | `gap` |
| `meth.cardinality` | `cat.sets` | `sage-set-limits` | `obj.sets.power_set` | `sage-power-set` |
| `meth.cardinality` | `cat.sets` | `sage-set-limits` | `obj.sets.permutations` | `gap-groups` |
| `meth.cardinality` | `cat.sets` | `sage-set-limits` | `obj.sets.f9_x` | `sage-presentations` |
| `meth.cardinality` | `cat.sets` | `sage-set-limits` | `obj.sets.f9_y` | `sage-presentations` |
| `meth.cardinality` | `cat.sets` | `sage-set-limits` | `obj.sets.units` | `gap-groups` |
| `prop.is_finite` | `cat.subobjects_groups` | `gap-groups` | `obj.subgroups.alternating` | `gap-groups` |
| `prop.is_finite` | `cat.subobjects_groups` | `gap-groups` | `obj.subgroups.kernel` | `gap-groups` |
| `prop.is_abelian` | `cat.subobjects_groups` | `gap-groups` | `obj.subgroups.kernel` | `gap-groups` |
| `prop.is_commutative` | `cat.subobjects_groups` | `gap-groups` | `obj.subgroups.alternating` | `gap-groups` |
| `prop.is_commutative` | `cat.subobjects_groups` | `gap-groups` | `obj.subgroups.kernel` | `gap-groups` |

### 2.7 Addresses that only `extension-ports.json` publishes

`extension-ports.json` publishes the default catalogue and six more modules (`provenance.additionalImports`). Its `operations`, `inputForms`, `objects`, `functors`, `entries` and `lifts` are supersets of those of `declared-ports.json`. No registration names an address of this table.

| Address only in `extension-ports.json` | Family | Owner category | Registrations |
| --- | --- | --- | --- |
| `fun.core_sets.two_subsets` | functor action (object) | `cat.core_sets` | 0 |
| `cmp.groups.cyclic_quotient_residue` | presentation comparison | `cat.groups` | 0 |
| `cmp.sets.fin_reversal` | presentation comparison | `cat.sets` | 0 |
| `meth.two_subsets` | method | `cat.sets` | 0 |
| `mor.sets.integer_square_bound_subset` | named morphism | `cat.sets` | 0 |
| `mor.sets.integer_square_bound_admitted` | named morphism | `cat.sets` | 0 |
| `mor.sets.cyclic_quotient_map` | named morphism | `cat.sets` | 0 |
| `mor.groups.cyclic_quotient_aut_by_unit` | named morphism | `cat.groups` | 0 |
| `mor.sets.successor_power_series_terms` | named morphism | `cat.sets` | 0 |
| `mor.modules.rectangular_linear_map` | named morphism | `cat.modules_r` | 0 |
| `mor.modules.row_linear_map` | named morphism | `cat.modules_r` | 0 |
| `mor.bilin_module.ordinary_kernel_inclusion` | named morphism | `cat.bilin_module` | 0 |
| `mor.bilin_module.degenerate_plane_map` | named morphism | `cat.bilin_module` | 0 |
| `mor.bilin_module.degenerate_plane_cone` | named morphism | `cat.bilin_module` | 0 |
| `mor.bilin_module.degenerate_plane_paired_cone` | named morphism | `cat.bilin_module` | 0 |
| `mor.bilin_module.pulled_back_forward` | named morphism | `cat.bilin_module` | 0 |
| `mor.bilin_module.pulled_back_backward` | named morphism | `cat.bilin_module` | 0 |
| `mor.core_sets.specified_iso` | named morphism | `cat.core_sets` | 0 |
| `mor.core_sets.fin_rev` | named morphism | `cat.core_sets` | 0 |
| `mor.sets.automorphism_forward` | named morphism | `cat.sets` | 0 |
| `mor.sets.automorphism_backward` | named morphism | `cat.sets` | 0 |
| `mor.groups.automorphism_forward` | named morphism | `cat.groups` | 0 |
| `mor.groups.automorphism_backward` | named morphism | `cat.groups` | 0 |
| `mor.modules.automorphism_forward` | named morphism | `cat.modules_r` | 0 |
| `mor.modules.automorphism_backward` | named morphism | `cat.modules_r` | 0 |
| `mor.sets.automorphism_evaluation` | named morphism | `cat.sets` | 0 |
| `mor.sets.automorphism_inverse_evaluation` | named morphism | `cat.sets` | 0 |
| `fun.core_sets.two_subsets#map` | functor action (map) | `cat.core_sets` | 0 |
| `lift.bilin_module.change_value_restriction#obj` | lift field (obj) | `cat.bilin_module` | 0 |
| `lift.bilin_module.change_value_restriction#hom` | lift field (hom) | `cat.bilin_module` | 0 |
| `lift.bilin_module.change_value_restriction#forward` | lift field (forward) | `cat.bilin_module` | 0 |
| `lift.bilin_module.change_value_restriction#backward` | lift field (backward) | `cat.bilin_module` | 0 |
| `lift.bilin_module.change_value_restriction#factor` | lift field (factor) | `cat.bilin_module` | 0 |
| `obj.linear_orders.fin_ordinary` | named object | `cat.linear_orders` | 0 |
| `obj.linear_orders.fin_reverse` | named object | `cat.linear_orders` | 0 |
| `obj.sets.two_subsets` | named object | `cat.sets` | 0 |
| `obj.sets.integer_square_bound` | named object | `cat.sets` | 0 |
| `obj.finite_sets.integer_square_bound` | named object | `cat.finite_sets` | 0 |
| `obj.sets.cyclic_quotient` | named object | `cat.sets` | 0 |
| `obj.groups.cyclic_quotient` | named object | `cat.groups` | 0 |
| `obj.fields.prime_residues` | named object | `cat.fields` | 0 |
| `obj.modules_r.restricted_regular` | named object | `cat.modules_r` | 0 |
| `obj.sets.rectangular_matrices` | named object | `cat.sets` | 0 |
| `obj.bilin_module.ordinary_kernel_restriction` | named object | `cat.bilin_module` | 0 |
| `obj.bilin_module.rational_diagonal_2_3` | named object | `cat.bilin_module` | 0 |
| `obj.bilin_module.degenerate_plane` | named object | `cat.bilin_module` | 0 |
| `obj.bilin_module.degenerate_plane_target` | named object | `cat.bilin_module` | 0 |
| `obj.bilin_module.degenerate_plane_with_dot` | named object | `cat.bilin_module` | 0 |

## 3. Evaluation that the kernel performs itself

### 3.1 State of the table

The table "Kernel computation (C22)" is at `tasks.md:93-106` of MAIN. `tasks.md:67` says that its rows state the source at `9165255`. The kernel branch is at `447469b`. 72 commits changed `CasCompiler/`, `CasRuntime/` and `CasCatalogue/` between the two. The column "At `447469b`" gives the place where the same code is now.

For the three rows of T033, the code at `447469b` is not the code that the row describes. No build and no test was run for this document. Confirm these three rows before a plan uses them.

C22 permits two kinds of owner for such an evaluation: a leaf that computes a published operation or predicate, and a proof procedure registered in `lean-categories`. The last column gives the mechanism that `tasks.md` requires.

### 3.2 The rows of the table

| # | Task | Location in `tasks.md` | At `447469b` | What the kernel does | Mathematical operation | Published row | Owner category | Mechanism that `tasks.md` requires |
| --- | --- | --- | --- | --- | --- | --- | --- | --- |
| 1 | T033 | `CasCompiler/Lower.lean:312-314` | `Lower.lean:895-902`; guards at `:2096-2111` | `whnfCore` runs before the eliminator guards. The row says that a closed `match`, recursor or `ite` is reduced in Lean. At `447469b` the call sets `iota := false`. | A closed computation that Lean can reduce: arithmetic of numerals, a greatest common divisor, a case distinction on data. | `op.semirings.*`, `op.rings.*`; `mor.sets.gcd` | `cat.semirings`, `cat.rings`; `cat.sets` for `mor.sets.gcd` | The no-implementation outcome that names the head. |
| 2 | T033 | `Lower.lean:552-555`, `:520-523` | `Lower.lean:2105-2111`, `:221-226`, `:1215-1219` | The row says that each constant with a definition is unfolded. At `447469b` a constant with no published operation ends in `noImplementation` (`:2111`), and `unfoldSourceApplication?` opens registered descriptors (`:1217-1219`). | The body of an operation that has no published row, evaluated by unfolding. | None | The category that owns the operation after `lean-categories` publishes it. | Unfold source definitions and registered derivation plans only. |
| 3 | T033 | `Lower.lean:393-397` | `Lower.lean:1187-1214` | The row says that `whnf` of a class instance gives a field. At `447469b` the code projects from a constructor application (`:1200-1205`) and gives `noImplementation` for a matcher or an eliminator (`:1206-1214`). | A structure field of an instance: the multiplication, the unit, the inverse, the scalar action. | `op.monoids.mul`, `op.monoids.one`, `op.groups.inverse`, `op.rings.*`, `op.modules.*` | `cat.monoids`, `cat.groups`, `cat.rings`, `cat.modules_r` | `unfoldDefinition?` to a constructor application; an eliminator gives no implementation. |
| 4 | T113 | `CasRuntime/Session.lean:157-186` | `Session.lean:268-298` (`compare`) | Reads both returned packets back into Lean terms (`:284-287`) and decides their equality with `Decide.decideProp` (`:295`). | Equality of two elements of one set. | `mor.sets.equality` (registered by `sage-symbolic`) | `cat.sets`. The carrier comes from the underlying-set action of the category of the values. | A published predicate lowered as a demand, or a procedure registered in `lean-categories`. |
| 5 | T113 | `Session.lean:117-124`; `CasCatalogue/Evaluation.lean:81-108` | `Session.lean:196-201` (`discharged`); `Evaluation.lean:81-110`, `:115-121` | After the registered evaluations, closes the goal with `Codec.conditionProof` or `mkDecideProof` (`Evaluation.lean:96-100`). A question with no registered literal form is decided by these alone. | Each operation of a decidable closed proposition: arithmetic in $\mathbb{N}$, $\mathbb{Z}$ and $\mathbb{Z}/n$, order comparison, equality, membership, primality, a quantifier over a finite type. | `op.semirings.add`, `mul`, `pow`; `op.rings.add`, `mul`, `neg`, `pow`; `op.linear_orders.le`, `lt`; `mor.sets.equality`; `meth.contains`; `mor.sets.nat_is_prime`; `mor.sets.gcd` | `cat.semirings`, `cat.rings`, `cat.linear_orders`, `cat.sets`, `cat.subobjects_sets` | A registered procedure closes the goal. With none, the question is a demand. |
| 6 | T021 | `CasRuntime/Literal.lean:17-28`, `:102-104` | Same lines (`constraintProof`) | Decides a propositional field of returned data: `whnf` of `decide` at transparency `all` (`:21`), then `mkDecideProof` (`:25`). | The condition of a subtype on a value: $k < n$ for `Fin n`, primality for the set of primes. | `op.linear_orders.lt`; `mor.sets.nat_is_prime` | `cat.linear_orders`, `cat.sets` | The evidence procedure registered with the admission of the type, in `lean-categories`. |
| 7 | T034 | `CasCompiler/SourceNumeral.lean:48-56` | `SourceNumeral.lean:51-59` (`numeralProof`) | Decides the domain obligation of a numeral by `whnf` of `mkDecide` (`:56-58`). | $k < n$ in $\mathbb{N}$. | `op.linear_orders.lt` on `obj.linear_orders.naturals` | `cat.linear_orders` | The evidence procedure of the numeral row (T119), in `lean-categories`. |
| 8 | T035 | `CasCompiler/ReadGraphRules.lean:67-71` | Same lines | `Decide.decisionProof` (`:69`) decides that a graph literal lists each element one time. | The list of the elements of a finite set, and equality of two of its elements. | `mor.sets.equality`. No row for the list of elements was found; the finite carrier is `obj.finite_sets.fin`. | `cat.finite_sets`, `cat.sets` | A registered evaluation on the graph-literal row, in `lean-categories`. |
| 9 | T068 | `CasCompiler/ReadSubsetNotation.lean:31-41` | Same lines (`:33`, `:34`, `:35`) | Host `Nat` arithmetic finds the common difference of a progression and decides the progression property. | $\le$, subtraction, addition and equality in $\mathbb{N}$. | `op.linear_orders.le`, `op.semirings.add`, `mor.sets.equality`. No subtraction row is in `operations`. | `cat.linear_orders`, `cat.semirings`, `cat.sets` | The published subtraction and the registered ellipsis definition. |
| 10 | T059 | `CasCompiler/SourceAdmission.lean:64-80`, `:108-109`; `CasCatalogue/Evaluation.lean:127-170`, `:201-275` | `SourceAdmission.lean:77-96` (`establish`), `:152-153`; `Evaluation.lean:127-170`, `:174-196`, `:201-275` | Reduces the goal before the registered evidence procedure runs. `plumbingValue` unfolds composites, identities, product projections and the application of a map. `evidencePresentation` runs `whnf` at transparency `all` on class dictionaries and carriers. `suppliedHomPresentation` normalizes the function of a closed map. | Composition of maps, application of a map to a point, the projections of a product, the structure fields of an instance. | No row for composition or application (the wire has `compose` and `apply`). `lim.sets.product` gives the projections. | `cat.sets`, and the categories of the instances | The registered `ObjectEntry.evidence`, stated on the term as read. A presentation step belongs to that procedure in `lean-categories`. |

### 3.3 The functions of the cited files

| File and lines at `447469b` | Function | What it does | Row above, or operation and owner |
| --- | --- | --- | --- |
| `CasCatalogue/Decide.lean:28` | `decideBudget` | Sets 20000 as the heartbeat budget of one decision (multiplied by 1000 at the call). | Not a computation. |
| `Decide.lean:37-49` | `kernelAccepts` | The Lean kernel type-checks a proof term in a copy of the environment. | A check. It computes when the proof term is a decision. |
| `Decide.lean:56-62`, `:66-71`, `:74-77` | `kernelDecides`, `decideProp`, `decisionProof` | Forms `of_decide_eq_true (Eq.refl true)` with `mkDecideProof`. The Lean kernel then evaluates the Mathlib `Decidable` instance. | Rows 4, 5, 8. |
| `CasCatalogue/Codec.lean:53` | `nat?` | `evalNat` evaluates a closed expression of $\mathbb{N}$ to a literal. | Arithmetic of $\mathbb{N}$: `op.semirings.*`, `cat.semirings`. |
| `Codec.lean:64-79` | `finiteDomain` | Lists the elements of a finite type from its `Fintype` instance, by `whnf` at transparency `all`. | The list of the elements of a finite set: `cat.finite_sets`. No published row was found. |
| `Codec.lean:93-297` | `conditionProofAux` | Assembles a proof from decision, reflexivity, function extensionality (`:216-229`), constructor congruence and case analysis over a non-recursive inductive type (`:263-296`). | Equality of two maps on a finite domain, and a quantifier over a finite set: `cat.sets`, `cat.finite_sets`. Row 5. |
| `Codec.lean:300-307` | `conditionProof` | Checks the assembled proof with `kernelAccepts`. | Row 5. |
| `Codec.lean:310-378` | `encode` | Writes a closed value as JSON. For a function field it applies the function to each element of the finite domain (`:315-323`). It reduces integers and lists by `whnf` (`:328-352`). | The graph of a map: `cat.sets`, `cat.finite_sets`. Arithmetic of $\mathbb{Z}$: `cat.rings`. |
| `Codec.lean:406-527` | `decodeAt` | Reads JSON as a Lean value. Decides each `input = key` to check a graph (`:424-428`). Decides each proof field of a constructor (`:502-517`). | Equality in the domain: `cat.sets`. The subtype conditions of row 6. |
| `CasCatalogue/Evaluation.lean:35-61` | `runProcedure` | Runs a procedure that `lean-categories` registers, on a goal. | Permitted by C22. The procedure belongs to `lean-categories`. |
| `Evaluation.lean:68-72` | `evaluationsOf` | Selects the registered evaluations whose literal form occurs in the proposition. | Not a computation. |
| `Evaluation.lean:81-110`, `:115-121` | `evaluatedDecides`, `decideEvaluated` | Runs the registered evaluations, then closes the goal with `Codec.conditionProof` or `mkDecideProof`. | Row 5. |
| `Evaluation.lean:127-170` | `plumbingRoots`, `plumbingApplication`, `plumbingValue`, `normalizedValue` | Unfolds the heads of a namespace list (`CasCatalogue`, `LeanCategories`, `CategoryTheory`, `TypeCat`, `DFunLike`, `FunLike`, `Function`, `id`, `Prod.fst`, `Prod.snd`, `Prod.map`, `inferInstance`, `inferInstanceAs`) and reduces. | Row 10. |
| `Evaluation.lean:174-196` | `suppliedHomPresentation` | Reduces the function of a closed map by `whnf` at transparency `all`. | Row 10. |
| `Evaluation.lean:201-275` | `evidencePresentation` | Reduces supplied class dictionaries and carriers by `whnf` at transparency `all`, then calls `suppliedHomPresentation`. | Row 10. |

### 3.4 Call sites that the table does not list

- Searched: the non-test `.lean` files of `CasCompiler/`, `CasRuntime/` and `CasCatalogue/` at `447469b`, with `git grep`, for the names `decideProp`, `decideEvaluated`, `evaluatedDecides`, `conditionProof`, `mkDecideProof`, `decisionProof`, `kernelDecides`, `kernelAccepts`, `runProcedure`, `evidencePresentation`, `normalizedValue`, `plumbingValue`.
- Found: two call sites in the new kernel that no row names, and the call sites of the old interpreter.
- Conclusion: the two sites below are the same kind of evaluation as row 7. This is an inference from the text of the code.
- Confidence: Medium. The search was by name.
- Gaps: other reductions (`whnf`, `reduce`, `evalNat`, `isDefEq` at transparency `all`) were not listed for the whole tree.

| Location at `447469b` | What the kernel does | Operation | Owner category |
| --- | --- | --- | --- |
| `CasCompiler/SourceLimit.lean:415-420` (`constructionIndex`) | `mkDecideProof` of `ordinal < bound` for an index of type `Fin n` of a diagram. | $k < n$ in $\mathbb{N}$: `op.linear_orders.lt` | `cat.linear_orders` |
| `CasCompiler/SourceRing.lean:69-73` | `Decide.decisionProof` of `index < bound` for the index of a ring generator. | $k < n$ in $\mathbb{N}$: `op.linear_orders.lt` | `cat.linear_orders` |

The old interpreter in `CasCatalogue/` calls the same functions: `Realize.lean` (`:506`, `:513`, `:531`, `:577`, `:597`, `:981`, `:1537-1539`, `:1893`, `:2038`, `:2521-2522`, `:2807-2808`, `:2855-2861`, `:2894-2915`, `:2987`), `Language.lean` (`:818`, `:924-926`, `:4477`), `StructuredResult.lean` (`:405`, `:436`), `Semantic.lean` (`:180`), `EquationData.lean` (`:247-286`), `ConstructionData.lean` (`:94`), `FunctorActionData.lean` (`:86`). `tasks.md:198-212` (T051, T064) removes that path.

### 3.5 Kernel evaluation by owner category

| Owner | Evaluation that the kernel performs today |
| --- | --- |
| `cat.sets` | Equality of two elements (rows 4, 5, 8, 9; `Codec.decodeAt`). Application and composition of maps and the projections of a product (row 10). The graph of a map (`Codec.encode`). Greatest common divisor and primality, which the catalogue registers as named maps of sets (rows 1, 5, 6). |
| `cat.finite_sets` | The list of the elements of a finite carrier (row 8; `Codec.finiteDomain`; the case analysis of `Codec.conditionProofAux`). |
| `cat.linear_orders` | $<$ and $\le$ in $\mathbb{N}$ (rows 5, 6, 7, 9; `SourceLimit.lean:415-420`; `SourceRing.lean:69-73`). |
| `cat.semirings` | Arithmetic of $\mathbb{N}$ (rows 1, 5, 9; `Codec.nat?`). |
| `cat.rings` | Arithmetic of $\mathbb{Z}$ and $\mathbb{Z}/n$ (rows 1, 5; `Codec.encode`). |
| `cat.monoids`, `cat.groups`, `cat.modules_r` | The structure fields that the lowerer reads from an instance (row 3). |
| `cat.subobjects_sets` | Membership (row 5). |
| A procedure registered in `lean-categories` | Rows 6, 7, 8 and 10 require a registered evidence or evaluation procedure. Rows 4 and 5 permit one. |

## 4. Protocol and SDK

### 4.1 What the backends use

| Fact | Evidence |
| --- | --- |
| Each program imports `cas_port` from `PYTHONPATH`. The kernel supplies the directory. | `AGENTS.md:163-165` of LEAVES; `api/manifest.md:65-75` of CONTRACT |
| The leaves repository pins no contract revision. | `lakefile.toml:1-5` (no dependency); `AGENTS.md:168` ("Every `require` tracks `main`") |
| Each program calls `serve` with four positional arguments: backend name, engine version, adapter version, handlers. | `sage_backend.py:82-83`, `gap_backend.py:65-66`, `sage_power_set.py:96`, `sage_set_limits.py:327-330`, `sage_discriminant.py:59-60`, `sage_fin_rev.py:51`, `gap_groups.py:318-325`, `sage_modules.py:90-93`, `sage_presentations.py:349-355`, `sage_bilinear_lift.py:148-153`, `sage_symbolic.py:649-672` |
| That call is the v1 signature `serve(backend, backend_version, adapter_version, ops, protocol=1)`. No program passes `protocol`. | `python/cas_port.py:821` at `ef3771d` |
| The ready frame has `op`, `protocol: 1`, `backend`, `backend_version`, `adapter_version`, `capabilities`. | `python/cas_port.py:829-831` at `ef3771d` |
| Seven programs import `serve` only. Four import `point_invocation`, `serve`, `value_data`. | `serve` only: `sage_backend.py:19`, `gap_backend.py:22`, `sage_power_set.py:22`, `sage_discriminant.py:6`, `gap_groups.py:15`, `sage_modules.py:15`, `sage_bilinear_lift.py:15`. Three names: `sage_fin_rev.py:7`, `sage_set_limits.py:33`, `sage_presentations.py:15`, `sage_symbolic.py:39` |
| No program returns `deferred_data`, and no program imports another SDK reader (`lift_input`, `method_invocation`, `construction_invocation`, `typed_map`). | The import lines above |
| The contract revisions that the leaf author recorded are `3c2159b`, `c603ede`, `c6e78eb` and `3382e4e`. The last is dated 2026-10-21, with catalogue `ee957329`. | `DEFECTS.md:7-9`, `:166`, `:206`, `:263`, `:433-434` |
| All 115 pairs (operation, input) are addresses of the catalogue at mathematics `3f8aedf`. | Section 2, by program |

### 4.2 Where v2 is

| Revision | SDK that it ships |
| --- | --- |
| Contract `main`, `ef3771d` (CONTRACT) | v1. `python/cas_port.py:821`: `serve(..., protocol=1)`. No `api/python-sdk.md`, no `python/cas_session.py`, no `pyproject.toml`. |
| Contract `integration/kernel-v1-20261106`, `a0417b0` | v2, contract `cas-computation/2`. `api/python-sdk.md`, `python/cas_session.py` (630 lines), `pyproject.toml`, `uv.lock`. |
| `lake-manifest.json` of `lean-cas-dsl` `main` | Pins contract `f0431be` (v1; an ancestor of `ef3771d`). |
| `lake-manifest.json` of the kernel branch of `lean-cas-dsl` | Pins contract `a0417b0` (v2). |

The two contract branches divide at `f0431be`. The local contract kernel branch has 17 commits after it. Contract `main` has 2. In the local clone, `origin/integration/kernel-v1-20261106` is `dcb9a15`, one commit behind `a0417b0`; that commit adds `routine-observations/1`. GitHub was not queried. Commit `5a5635a` of the contract kernel branch removes the v1 bridge. `declared-ports.json` has the same `provenance` on the two branches.

`contracts/computational-runtime.md` of MAIN is the v2 design. `tasks.md:490` (T028) owns the publication of the released contract and SDK. `tasks.md:552` (T104) owns the migration of the leaves.

### 4.3 What v2 requires and the work in the backends

| Item | v1 as the backends use it | v2 (`api/python-sdk.md` at `a0417b0`; `computational-runtime.md`) | Work |
| --- | --- | --- | --- |
| Entry point | `serve(backend, backend_version, adapter_version, ops)` | `cas_port.serve(backend, backend_version, operations)` (`cas_port.py:864`, `cas_session.py:607`) | Remove the adapter-version argument from the 11 calls. With four arguments the v2 function raises `TypeError` at start. |
| Announcement | `protocol: 1`, `adapter_version`, `capabilities` | `{"op":"ready","protocol":2,"contract":"cas-computation/2","features":[...],"backend","backend_version"}` (`python-sdk.md:28-35`) | The SDK writes it. |
| Negotiation | None | The kernel sends `hello`; the SDK acknowledges. There is no downgrade to v1: the outcome is `unavailable/incompatible_protocol` (`computational-runtime.md:50-52`). | The SDK does it. A v1 program does not start a computation. |
| Request | `{request_id, op, args}`; the handler receives `args` | `{protocol, request_id, op, input, args, scope_id}` (`python-sdk.md:43-44`); `cas_session.request_input()` gives the input address | A handler can select its case from the admitted input address. Today each handler reads the `ctor` of the argument. |
| Reply | `{request_id, status, value}` | Exactly `request_id`, `status`, `value`, `exports` (`python-sdk.md:45-48`) | The SDK writes it. |
| Opaque values | `sage-set-limits` makes tokens by hand (`sage_set_limits.py:235`, `:251-256`) and answers `apply` of a token under `lim.sets.product` (`:239-240`, `:259-269`) | `cas_session.export(handler, captures)`; the kernel calls `$cas.invoke_export`; each token is in the `exports` table with its captures; `$cas.discard` revokes (`python-sdk.md:103-129`, `:169-177`) | Rewrite the projections of the symbolic product as exports. One program. |
| Kernel services | No program uses `deferred_data` | `deferred_data` stays. A generator handler yields `cas_session.suspend(calls, captures)` and the kernel resumes it with the results (`python-sdk.md:131-167`). A child with no implementation gives `{"ctor":"noImplementation","args":[op, input]}` in its slot (`computational-runtime.md:190`). | Optional. A category implementation can request an operation of another category in place of a private copy (section 1.4). |
| Errors | Each exception becomes `status: "error"` | The same, and `ComputationError(kind, message)`, `UnsupportedOperation(operation)` (`python-sdk.md:17-21`) | None required. |
| Engine routine record | The routine is named in comments | Optional feature `routine-observations/1`, at `a0417b0` only: `cas_session.invoke_routine(routine, *args)` records the delegated call (`python-sdk.md:50-87`) | Optional. It records what section 1.2 gives by hand. |
| Dependencies | Standard library | Python `>= 3.12`, `pydantic >= 2.14.3` (`pyproject.toml`); `cas_port.py:17` uses a `type` statement | The interpreter that runs the program needs them. After `engine_python.py:49-53` that interpreter is the engine interpreter (`CAS_SAGE_PYTHON`, `CAS_GAP_PYTHON`). |
| JSON | `json.dumps` defaults | Finite numbers only; a repeated object key is refused (`cas_port.py:811-832` at `a0417b0`) | None found. |
| Manifest | Three fields | Three fields, and optional `preferredRoutes` with `name`, `receiver`, `route` (constitution C6) | None required. |

One more fact concerns the request form, not the SDK version. `api/kernel-service.md:92-98` of CONTRACT gives the complete method request as `{"ctor": method_id, "args": [residual actions..., method functor], "receiver": actual_input}`. Two programs read the `receiver` member (`gap_groups.py:26-27`, `sage_modules.py:22-23`). The `meth.cardinality` and `prop.is_finite` handlers of `sage`, `gap`, `sage-power-set`, `sage-set-limits`, `sage-discriminant` and `sage-presentations` read the argument as the object descriptor itself. I infer from the code that they do not accept the complete method request; this was not run. `kernel-service.md:127-131` lets a kernel permit the raw receiver form when the residual route is empty.

`sage_bilinear_lift.py:41-57` reads the `liftInput` envelope by hand. The SDK has `lift_input`, `lift_parameters` and `lift_images` for it (`cas_port.py:529-630` at `ef3771d`).

## 5. Rules that LEAVES states for leaf authors

File names with no repository are files of LEAVES. `INTENT.md` is the same file in LEAVES and CONTRACT.

### 5.1 Permitted inputs

| Rule | Source |
| --- | --- |
| A leaf author writes against the contract and the catalogue on `main`. | `AGENTS.md:140` |
| The package depends on the leaf contract and on `lean-categories` only. Each operation that a leaf names is a row of the catalogue. | `AGENTS.md:147-148` |
| The author is blind to the tests. Nothing in the package depends on the acceptance suite, runs it or can reach it. | `AGENTS.md:140-141`, `:153-157`; `README.md:67-70` |
| Acceptance requirements, kernel source references and harness observations are outside the permitted inputs of a leaf author. | `DEFECTS.md:87-92` |
| An assignment can limit the inputs to the released contract, the native-engine APIs and the source of the leaf role. To read catalogue source outside that assignment was recorded as a conduct defect. | `DEFECTS.md:165-170`, `:205-208` |
| Engines: the shared math container (Sage, GAP, Julia/Oscar, Macaulay2, Singular), SymPy, published research code. | `AGENTS.md:3-6`, `:121-122` |
| The engine interpreters are `CAS_GAP_PYTHON` and `CAS_SAGE_PYTHON`; the default is `.venv/bin/python` of the workspace. | `AGENTS.md:163-166`; `README.md:63`; `backends/engine_python.py:20-26` |

### 5.2 What a leaf does

| Rule | Source |
| --- | --- |
| A leaf is a registration: an operation that is formal in `lean-categories`, an input form, and an opaque implementation of the declared result form. | `AGENTS.md:109-112`; `README.md:3-7` |
| A registration has exactly three fields. Other fields of a manifest carry no meaning. | `README.md:9-12`; CONTRACT `README.md:17-21`, `api/manifest.md:43-48` |
| Wire, do not write: declared input form, engine input, engine routine, engine result, declared result form. The leaf owns that translation and the choice of routine, and nothing else. | `AGENTS.md:121-125` |
| Each computation names the engine and the routine that it calls. | `AGENTS.md:126-127`; `README.md:13-16` |
| Engine values stay private. Only a value of the declared result form crosses the port. | `AGENTS.md:133-134` |
| A case that the program does not support fails explicitly. | `README.md:45-46` |
| A leaf that needs a new category, method, placement, forwarding or edge has found a defect upstream. The mathematics is formalized in `lean-categories` first. | `AGENTS.md:158-160`; `README.md:74` |
| A leaf that finds kernel work in itself reports the gap upstream. A leaf changes when that exposes a deficiency of the contract, the kernel or `lean-categories`, and the commit names the deficiency. | `AGENTS.md:129-132`, `:161-162`; `README.md:71-72` |
| All leaves live in the leaves repository. | `AGENTS.md:146` |
| A violation of the model is recorded as a defect, not worked around. | `AGENTS.md:8-15` |
| An encoding that the contract does not fix is the choice of the leaf. It is evidence of nothing, and the contract form replaces it. | `DEFECTS.md:449-450` |

### 5.3 What a leaf must not do

| Rule | Source |
| --- | --- |
| No hand-rolled algorithm. New algorithmic code is written only when no existing system supplies the computation, and the leaf says so with the evidence. | `AGENTS.md:126-128` |
| No kernel machinery: dispatch, placement, propagation, composition, refinement and caching are the kernel's. | `AGENTS.md:129-132` |
| No mathematics and no Lean. | `AGENTS.md:92-93`, `:112-113`; `README.md:6`; `INTENT.md:1046`, `:1063` |
| No semantic authority: a leaf does not decide what a value is, which values are equal, what holds of them, or which operations an object has. | `AGENTS.md:90-91` |
| No proof, denotation, identification of values, decision evidence, status, trust level, certificate or checker. Nothing reads such a thing from a leaf. | `AGENTS.md:33-37`, `:149-151` |
| No computation that can be carried out entirely in Lean. | `AGENTS.md:57-61`, `:151-152` |
| No mechanism that raises the trust or the acceptance signal of the leaf. | `AGENTS.md:67-76` |
| No edit of the contract, the kernel or `lean-categories`. | `AGENTS.md:141`; CONTRACT `README.md:38-39` |
| No change of a leaf to make a test pass. | `AGENTS.md:154-155`; `README.md:68-69` |
| The orchestrator does not write, port or polish a leaf. | `AGENTS.md:142-143` |
| The leaves in the repository are quarantined and are to be rewritten, not ported. | `AGENTS.md:143-145` |
| No leaf-specific forwarding of an inherited method. | `INTENT.md:1655`, `:1704` |
| The applicability of a backend does not narrow the mathematical domain of an operation. | `INTENT.md:1661`, `:1706` |
| A leaf does not create a category, declare that its object is a group, say which operations an object has, create its own notion of subgroup, stabilizer, kernel, cardinality or basis, change the mathematical type of a result, or insert an inheritance or placement edge. A backend object does not become the public value. | `INTENT.md:1694-1716`, `:1622` |
| Overlapping registrations are avoided: an exact form and a category address of one operation have equal standing, and an invocation to which both apply is ambiguous. | CONTRACT `api/manifest.md:191-195` |

### 5.4 What the repository checks

`justfile:9-11` checks that `leaves.json` is JSON and that each program compiles. `AGENTS.md:168` says that the commit and push tiers compile nothing. `specimens/README.md:3-7` and `:22-24` describe four bad leaves on `meth.cardinality` and `obj.sets.fin`: no registration, a wrong answer, a malformed answer, and a program that exits with code 73.

## 6. Surprises

1. **One backend, several categories.** `gap-groups` holds 37 registrations whose operations the catalogue gives to `cat.sets` (16), `cat.magmas` (19) and `cat.arrows_groups` (2). Its input forms are in `cat.groups`, `cat.sets`, `cat.subobjects_groups`, `cat.bil_wform`, `cat.integral_lattice` and `cat.arrows_groups`. It answers commutativity of the lattices $A_n$ and $E_8$ from `AbelianGroup([0]*n)` with a literal rank (`gap_groups.py:54-57`). `sage-symbolic` holds 19 registrations that the catalogue gives to `cat.sets`; their declaring modules are number systems, polynomials, linear algebra, calculus, real limits, differentials and power sets (section 2.3).
2. **One operation, many backends.** `meth.cardinality` is in 8 programs and `prop.is_finite` in 4. The same lowering table from a named set to a Sage parent is in three programs (section 1.5).
3. **Hand-rolled algorithms.** `lim.sets.pullback` filters a Cartesian product in Python (`sage_set_limits.py:320-321`). `lift.bilin_module.restrict#obj` restricts the pairing point by point (`sage_bilinear_lift.py:92-108`).
4. **A cokernel that is a name.** `colim.bil_w_form.cokernel` checks that the input is the diagram $A_n \to A_n^\vee$ with the zero arrow, discards the Smith form, and answers the two catalogue names `obj.bil_wform.root_lattice_a_discriminant` and `mor.bil_wform.root_lattice_a_to_discriminant` (`sage_discriminant.py:41-50`).
5. **A rank that is a literal.** `meth.rank` on $E_8$ is `FreeModule(ZZ, 8).rank()` (`sage_modules.py:52`, `:71`).
6. **Element operations have no registration.** Ring arithmetic runs only inside the point decoders of `sage-presentations` and `sage-symbolic` (section 1.4). The example `2 * 3 = 6 in ℤ` of `tasks.md:17` has no registered `op.rings.mul`.
7. **Overlap.** Section 2.6 lists the pairs of registrations that are ambiguous under `api/manifest.md:191-195`. The largest group is `meth.cardinality` on `cat.sets` (`sage-set-limits`) with each `meth.cardinality` on a named set.
8. **Two addresses, one function.** `prop.is_abelian` and `prop.is_commutative` call `abelianness` (`gap_groups.py:321-322`); the two rows name one classifier, `clf.magmas.commutative`. `meth.group_arrow_kernel` and `fun.arrows_groups.kernel` call `kernel` (`gap_groups.py:323-324`); the functor is the functor of the method.
9. **Models of $\mathbb{R}$ and $\mathbb{C}$ differ between programs.** `sage_backend.py:44-45` uses the floating-point fields `RR` and `CC`. `sage_symbolic.py:56` uses the symbolic ring for points and `:89-92` uses `AA` and `QQbar` for polynomial coefficients. `mor.sets.equality` answers `bool(x == y)` (`sage_symbolic.py:561`); on the symbolic ring `False` also means "not proved".
10. **Contract `main` is v1.** The v2 SDK is on the contract kernel branch only (section 4.2).
11. **`tasks.md` and the catalogue differ on binders.** `tasks.md:87` says that `bind.sets.limit`, `bind.sets.limit_at_infinity` and `bind.sets.power_series_sum` are not operations of the published catalogue. `operations` of `declared-ports.json` at mathematics `3f8aedf` holds all eight binders, and LEAVES registers `bind.sets.limit` and `bind.sets.limit_at_infinity`.
12. **The T033 rows describe an older source** (section 3.1).
13. **Two documents differ on the old leaves.** `AGENTS.md:143-145` of LEAVES says that the present leaves are quarantined and are rewritten, not ported. `tasks.md:552` (T104) says that the retained leaf registrations move into the category implementations and migrate to the v2 contract.
14. **`DEFECTS.md` counts are old.** `DEFECTS.md:104` gives ten programs and 96 registrations, and `:265` gives 94. `leaves.json` has 11 programs and 115 registrations. `README.md:17-61` does not list `sage_discriminant.py` and `sage_fin_rev.py`.

## Files

| File | Content |
| --- | --- |
| `existing-leaves.md` | This document. |
| `existing-leaves.json` | The 115 registrations as records: `operation`, `input`, `backend`, `file`, `line`, `function`, `engine`, `routine`, `routine_line`, `category`, `family`, `owner_detail`, `input_category`, `handrolled`, `handrolled_kind`, `handrolled_quote`, `leaf_held_mathematics`, `manifest_line`. `handrolled` is `true` for `partial`, `yes` and `lookup`. |
| `existing-leaves.categories.json` | Each owner category with its operation addresses, registrations, named objects and other constructors, and the overlaps of section 2.6. |
| `existing_leaves_build.py`, `existing_leaves_catalogue.py`, `existing_leaves_implementations.py`, `existing-leaves.prose.md` | The program and the text that make the three files above. `existing_leaves_implementations.py` holds the function, line and routine of each registration, as read in the backend programs. The program checks that each function is defined at the stated line. Run: `python3 -I -B existing_leaves_build.py LEAVES CONTRACT OUT`. |
