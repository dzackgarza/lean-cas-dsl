# Spike inventory: the computations and features of the first spike (snapshot of 2026-11-25)

The first days of lean-cas-dsl were a spike that scoped the functionality of the first product. This record lists every computation and every user-visible feature of that spike, with its source. For each computation it names the workload statements that carry it, or it proposes the statement that the computation needs. The record reads fixed revisions and is not kept current. `spike-inventory.json` holds the same data, with the catalogue rows, the routes and the evidence of each proposed statement. `category-scope.md` uses this record to scope the category implementations.

## Sources and revisions

| Input | Revision | Part read |
| --- | --- | --- |
| `SPEC.md`, the guiding specification of the spike | `73bfb11` | all 344 lines |
| The live acceptance notebook `notebooks/categorical-cas.ipynb` | `9c7d438`, its last revision (`978ce76` removed it) | all code cells and their outputs; the markdown cells in part |
| `notebooks/demo.ipynb`, `notebooks/boundaries.ipynb`, `notebooks/python-control.ipynb` | `32e6872`, the last spike commit | all cells (163, 29, 1) |
| `tests/test_e2e.py` (2200 lines), `tests/roundtrip.py` (603 lines) | `32e6872` | all lines |
| `CasDslTests/*.lean`: Core, Eval, Transport, CanonicalMaps, Latex, Codec, Membership, Wording, Std, Extension, Denote (3672 lines) | `32e6872` | all lines |
| The 156 spike commits | `eca90be` to `32e6872` (author dates 2026-07-30 to 2026-08-06) | all subjects; the bodies of `47bce16`, `0fb26b9`, `ca9798c`, `69bceb9`, `3e8011c`, `79ec602`, `d506cb7` |
| Workload statements | `workload-routes.json` (snapshot of 2026-11-25); the K3 and K14 files on `integration/kernel-v1-20261106` | identifiers and texts of the 287 statements and the 18 file statements |
| Catalogue | lean-cas-dsl-leaf-contracts `33a514c`, `api/extension-ports.json` (mathematics `3f8aedf`) | the rows of the proposed statements |

Source notation in the tables: `S:L` is line L of `SPEC.md` at `73bfb11`; `A`N is cell N of the acceptance notebook at `9c7d438`; `D`N, `B`N and `PC`N are cell N of `demo.ipynb`, `boundaries.ipynb` and `python-control.ipynb` at `32e6872` (cells count from 0); `E:L` and `R:L` are lines of `tests/test_e2e.py` and `tests/roundtrip.py` at `32e6872`; `Core:L` and the other file names are lines of `CasDslTests/<name>.lean` at `32e6872`. The JSON spells each source in full. `rx:` abbreviates the prefix `reconstructed_extensions_20261024.` of the extension statements. In the tables `¦` stands for `|`, which a Markdown table cell cannot hold.

## Method

**Rows.** A row is one distinct computation: an operation applied to an input, with a result. A wrong-answer check of the same computation, a second spelling of it, and another value of the same operation on the same kind of input stay in the row; the column "Spike computation" names them. A boundary case that the spike pinned on purpose (the gcd at zero, a negative prime, a double root, an empty set, a unit in a factorization) has a row of its own. A line of `SPEC.md` is a computation of the inventory also when the spike refused it (rows E06 to E08).

**Carried.**

| Value | Meaning |
| --- | --- |
| full | A workload statement asks the same operation on the same kind of input. |
| partial | A statement carries a part; a proposed statement covers the rest. |
| none | No workload statement carries the computation; the row has a proposed statement. |
| typing judgement | The carrying statement is a settled question: elaboration settles it, and no implementation computes it. |

**Proposed statements.** Each proposed statement is written in the notation of the workload files, with the bindings that it uses. Its catalogue rows come from the text matcher of `workload-routes.json` (`workload-routes-scripts/textmatch.py`), and its categories from the route rules R1 to R4 of that record (`route.py`). The matcher reads a name by its surface name in the catalogue, and it misreads some forms: `|·|` as the complex modulus where it is a cardinality, `map … to` as a change of coefficients where it is an inclusion or a truncation, `ℤ[3]` as a polynomial ring, `∖` as a set difference. The hand corrections follow the recorded readings of the nearest workload statement (for example `fun.sets.cardinality` for `|·|`, as in `sets.card.*`). The field `evidence` of each proposed statement in the JSON gives its correction and the reason. A row that a proposed statement needs and the catalogue lacks is in the column "Missing catalogue row"; `category-scope.md` lists these rows with their descriptions.

**Spike ceilings.** A ceiling is a request outside `SPEC.md` that the spike refused and documented as a limit: for example $\sqrt{2} + \sqrt{5}$, the determinant over $\mathbb{Z}/5$, an uncountable cardinal. A ceiling is not a computation of the spike, so it is not V1 by the definition of `category-scope.md`. Each ceiling has a proposed statement, so that its version can follow the membership rule when the classified Sage coverage (#20, #21, #23) reaches it.

**Features.** A feature is behaviour that is not a computation in a category: the language, display, provenance and discovery commands, the canonical-map audit, approximation tolerances, error reporting, dispatch, and notebook and installation behaviour. Each feature maps to the functional requirements (FR) and user stories (US) of `spec.md` that cover it, or to "none". The mapping gives an installation feature no priority over other work.

**Statements of the K3 and K14 files.** `milestones.json` records the 18 statements of `b0-required-positives.cas.proposed` and `b0-formed-positives.cas.proposed` by their categories only. The category scope needs their rows. The section "Rows of the K3 and K14 statements" gives them: the text match for 9 statements, and a hand correction for the other 9, each with its reason. The categories of all 18 routes equal those of `milestones.json`.

## Counts

| Quantity | Count |
| --- | ---: |
| Computations | 157 |
| Carried by a workload statement | 92 |
| Partly carried (a statement and a proposed statement) | 9 |
| No statement (a proposed statement) | 56 |
| Of the carried ones: carried by a typing judgement only (no computation) | 14 |
| SPEC.md lines that the spike refused | 3 |
| Proposed statements for computations | 94 |
| Spike ceilings (refusals outside SPEC.md) | 18 |
| Non-category features | 38 |
| Catalogue rows that a computation needs and the catalogue lacks | 14 |
| Catalogue rows that only a ceiling needs and the catalogue lacks | 4 |

## Computations

### Exact number systems

| ID | Spike computation | Result | Sources | Statements | Carried |
| --- | --- | --- | --- | --- | --- |
| N01 | `assert 2 + 3 = 5` | `true` | S:8; A2; D3; E:104; Eval:362 | `numbers.integers.sum` | full |
| N02 | `assert 2 + 3 = 0 in ℤ/5` | `true` | S:9; A3; D5; E:105; Eval:363 | `numbers.zmod5.sum` | full |
| N03 | `assert gcd(84, 30) = 6 (also (84).gcd(30))` | `true` | S:10; A10; D17; D19; E:133; E:2049; R:279 | `numbers.gcd` | full |
| N04 | `gcd(0, -7)` | `7` | R:281 | no statement | none |
| N05 | `360.factor() (written (360).factor())` | `2³ · 3² · 5` | S:12; A6; D13; D16; E:120; E:2045; R:138; Core:910 | `factorization.prime_factors`, `factorization.multiplicity_two`, `factorization.multiplicity_three`, `factorization.multiplicity_seven` | full |
| N06 | `factor_int(-12)` | `(-1) · 2² · 3` | R:144 | no statement | none |
| N07 | `assert ℤ ⊆ ℚ and ℚ ⊆ ℝ and ℝ ⊆ ℂ (and ℕ ⊆ ℤ, ℕ ⊆ ℂ, ℤ ⊆ ℝ, ℚ ⊆ ℂ)` | `true; ℝ ⊆ ℚ, ℚ ⊆ ℤ and ℤ ⊆ ℤ/5 false` | S:15; A121; D56; E:1264; E:917; Eval:632 | `numbers.containments`, `numbers.containments.transitive` | full (typing judgement) |
| N08 | `assert -3 ∈ ℤ` | `true` | S:17 | `numbers.membership.negative` | full (typing judgement) |
| N09 | `assert 7/3 ∈ ℚ (also 7/3 \in ℚ)` | `true` | S:18; D146; E:2061 | `fractions.member` | full (typing judgement) |
| N10 | `assert √2 ∈ ℝ` | `true` | S:19; A123; D53; E:1322; Eval:647 | `fractions.sqrt_member` | full (typing judgement) |
| N11 | `assert 2 + 2i ∈ ℂ` | `true` | S:20; A125; D10; D54; E:1323; Eval:648 | no statement | none |
| N12 | `assert z.re() = 2` | `true` | S:26; E:1343; Eval:655 | `numbers.complex.re` | full |
| N13 | `assert z.im() = 2` | `true` | S:27; E:1344; Eval:656 | `numbers.complex.im` | full |
| N14 | `assert z.bar() = 2 - 2i` | `true` | S:28; A128; E:1345; Eval:657 | `numbers.complex.bar` | full |
| N15 | `assert z · z.bar() = 8` | `true` | S:29; A129; E:1346; Eval:658 | `numbers.complex.norm` | full |
| N16 | `assert ¦z¦ = 2√2` | `true (exact surd, never a decimal)` | S:30; A132; D49; E:1348; Eval:659 | `numbers.complex.abs`, `fractions.modulus` | full |
| N17 | `map √2 to ℝ/O(1/10^{10}) (also ε = 1/10², 1/2⁵³, 1/3; values 1/3, 3, 1/√2, −√2)` | `1.4142135623 + O(1/10^{10}), with the exact source and the requested and achieved tolerances` | S:37; A149; D51; E:1504; E:1545; E:1617; R:406; R:426; Core:311 | `factorization.approximation` | partial |
| N18 | `√8, √9, √(1/2), √(−4)` | `2√2, 3, (1/2)√2, 2i` | E:1328; E:1335; Eval:670; Core:230 | no statement | none |
| N19 | `√2 · √2, (1 + √2)(1 − √2), (√2)², 1/√2` | `2, −1, 2, (1/2)√2` | E:1337; E:1386; E:1736; Core:247; Core:249 | no statement | none |
| N20 | `assert √2 ∉ ℚ; assert 2 + 2i ∉ ℝ` | `true` | A124; E:1325; Eval:651 | no statement | none |
| N21 | `s2 := √2 in ℝ: s2.re(), s2.im(), s2.bar(), ¦s2¦; ¦1 − √2¦` | `√2, 0, √2, √2; √2 − 1` | Eval:675; Core:979; Core:986 | no statement | none |
| N22 | `1 + 1/2 (ℤ and ℚ joined along ℤ ⊆ ℚ)` | `3/2` | CanonicalMaps:290 | no statement | none |
| N23 | `2^10, (1/2)^0, 10^{3}, 2^{3}, 1/10^{2}` | `1024, 1, 1000, 8, 1/100` | E:1734; E:1743; Eval:1044; Core:201 | no statement | none |
| N24 | `map n to ℤ/7 for n = 360; 7 in ℤ/5` | `3; 2` | A29; E:817; CanonicalMaps:277 | `rx:complete.rx05.additive_map_sample`, `rx:complete.rx05.multiplicative_map_sample` | full |
| N25 | `ℤ[3], ℤ[4], ℚ[2], ℚ[3] (adopted Denumerable.ofNat order)` | `−2, 2, −1/2, 1` | E:542; E:544; E:1773; Core:363; Core:393; A68; A70 | no statement | none |
| N26 | `cardinalities of named domains: ¦ℤ/6¦, ¦(ℤ/3)²¦, ¦Mat₂(ℤ/3)¦, ¦ℚ[x]¦, ¦ℚ³¦, ¦ℤ¦` | `6, 9, 81, ℵ₀, ℵ₀, ℵ₀` | Core:346; E:1306 | `sets.card.z4_cubed`, `sets.card.z7`, `sets.card.integers` | partial |
| N27 | `let rr := 3 in ℝ; map 3 to ℂ` | `3 ∈ ℝ; 3` | D57; D58; E:1288 | no statement | none |
| N28 | `is_prime on ℕ: 7, 8, 2¹²⁷ − 1; 13 ∈ primes, 15 ∉ primes` | `true, false, true; true, true` | A119; D152; E:1094; E:1011; R:291; R:301 | `ellipses.prime`, `ellipses.not_prime` | full |
| N29 | `is_prime on ℤ: −7, 0, 1` | `true, false, false` | R:297 | no statement | none |

### Finite sets

| ID | Spike computation | Result | Sources | Statements | Carried |
| --- | --- | --- | --- | --- | --- |
| F01 | `let A := {1, 2, 3} in 𝒫(ℤ); let B := {3, 4, 5} in 2^ℤ; assert A in 𝒫(ℤ); assert A ⊆ ℤ` | `checked power-set ascription; true` | S:48; S:49; A102; D96; E:858; E:909; E:912; Eval:764 | no statement | none |
| F02 | `assert A ∪ B = {1, 2, 3, 4, 5}` | `true` | S:51; A89; D97; E:870; Core:554; Eval:739 | `finite_sets.union` | full |
| F03 | `assert A ∩ B = {3}` | `true` | S:52; A90; D97; E:871; Eval:740 | `finite_sets.intersection` | full |
| F04 | `assert A \ B = {1, 2}` | `true` | S:53; A91; D97; E:872; Eval:741 | `finite_sets.difference` | full |
| F05 | `assert A △ B = {1, 2, 4, 5}` | `true` | S:54; A92; D97; E:873; Eval:742 | `finite_sets.symmetric_difference` | full |
| F06 | `assert ¦A¦ = 3 (also ¦{1, 2, 3}¦, ¦{1, 2, 2, 3}¦)` | `true` | S:56; A94; D98; E:886; E:480; Eval:744 | `finite_sets.card` | full |
| F07 | `assert ¦A × B¦ = 9` | `true` | S:57; A96; D98; E:887; Core:596; Eval:745 | `finite_sets.card_product` | full |
| F08 | `assert ¦𝒫(A)¦ = 2^¦A¦ (also ¦2^{1, 2, 3}¦, ¦𝒫(ℤ/10)¦)` | `true; 8; 1024` | S:58; A97; D98; E:888; E:1746; E:1089; Core:598; Eval:746 | `finite_sets.card_power_set` | partial |
| F09 | `assert 2 ∈ A` | `true` | S:63; A99; D100; E:903; Eval:748 | `finite_sets.member` | full |
| F10 | `assert 4 ∉ A (also 4 ∉ {1, 2, 3})` | `true` | S:64; A100; D7; D100; E:904; Eval:749 | `finite_sets.not_member` | full |
| F11 | `assert A ⊆ A ∪ B` | `true` | S:65; A101; D100; E:905; Eval:750 | `finite_sets.subset_union` | full |
| F12 | `assert A ∩ B ⊆ A` | `true` | S:66; D100; E:906; Eval:751 | `finite_sets.intersection_subset` | full |
| F13 | `assert A ∪ B ∉ 𝒫(A)` | `true` | E:910; Eval:766 | no statement | none |
| F14 | `let dup := {1, 2, 2, 3} in 𝒫(ℤ); dup = {1, 2, 3}` | `true; ¦dup¦ = 3` | E:477 | no statement | none |
| F15 | `bounded progressions {1, 3, ..., 9}, {1, 2, ..., 9999}` | `the finite progression` | Eval:370; E:1755 | no statement | none |
| F16 | `∑ and ∏ over explicit finite sets: ∑{1,2,3} a, ∏{1,2,3} a, ∑{} a, ∏{} a, ∑ a², ∏ 2a, ∑{1/2, 1/3} a, ∑ and ∏ over {√2, −√2}` | `6, 6, 0, 1, 14, 48, 5/6, 0, −2` | Eval:992; Eval:999; Eval:1003; Eval:1006; Core:805 | no statement | none |

### Set comprehensions

| ID | Spike computation | Result | Sources | Statements | Carried |
| --- | --- | --- | --- | --- | --- |
| C01 | `let S := {n ∈ ℤ ¦ n² ≤ 20}; assert S in 𝒫(ℤ)` | `true` | S:73; S:74; A104; D102; E:936; Eval:781 | `comprehension.typed` | full (typing judgement) |
| C02 | `assert S = {-4, -3, -2, -1, 0, 1, 2, 3, 4} (also {n ∈ ℤ ¦ n² ≤ 4})` | `true` | S:76; A105; D102; E:938; E:1969; Eval:784 | `comprehension.elements` | full |
| C03 | `assert ¦S¦ = 9` | `true` | S:77; A106; D102; E:939; Eval:785 | `comprehension.card` | full |
| C04 | `assert 4 ∈ S; assert 5 ∉ S; assert -4 ∈ S` | `true` | E:941; Eval:787 | no statement | none |
| C05 | `empty comprehensions {n ∈ ℤ ¦ n − n < 0}, {n ∈ ℕ ¦ 0·n > 0}` | `{}` | E:1076; Eval:817 | no statement | none |
| C06 | `let E := {2n ¦ n ∈ ℕ}; assert E in 𝒫(ℕ)` | `true` | S:82; S:83; A108; D103; E:965; Eval:792 | `comprehension.image_typed` | full (typing judgement) |
| C07 | `assert 8 ∈ E (also 10¹² ∈ E, 10¹² + 1 ∉ E)` | `true` | S:85; A109; A112; D103; E:968; E:972; Eval:795 | `comprehension.even_member` | full |
| C08 | `assert 9 ∉ E` | `true` | S:86; A110; E:969; Eval:796 | `comprehension.odd_not_member` | full |
| C09 | `assert ¦E¦ = ℵ₀` | `true` | S:87; A111; D103; E:970; Eval:797 | `comprehension.even_card` | full |
| C10 | `let e: ℕ → ℕ := n ↦ 2n (renamed m2); assert e(ℕ) = E` | `true` | S:89; S:90; A114; D104; E:983; Eval:805 | `comprehension.image_apply` | full |
| C11 | `assert e.image() = E` | `true` | S:91; A115; D104; E:984; Eval:806 | `comprehension.image_method` | full |
| C12 | `{e(n) ¦ n ∈ ℕ, 0 ≤ n < 6}` | `{0, 2, 4, 6, 8, 10}` | S:93; S:94; A116; D106; E:994; Eval:809 | no statement | none |
| C13 | `{7 ¦ n ∈ ℕ}, {p.deg() ¦ n ∈ ℕ}` | `{7}, {3}` | E:1060; Eval:822 | no statement | none |
| C14 | `{2, 4} ⊆ E; A ⊆ E` | `true; false` | Core:584; E:977 | no statement | none |
| C15 | `{a ∈ ℚ ¦ r(a) = 0}; 0 ∈ {a ∈ ℚ ¦ r(a) = 1}` | `{1}; true` | E:1963; E:1966 | no statement | none |

### Functions

| ID | Spike computation | Result | Sources | Statements | Carried |
| --- | --- | --- | --- | --- | --- |
| H01 | `let h := t ↦ t² + 1 in ℝ → ℝ; let hp(t) := t^2 + 1 in R->R; assert h = hp` | `true` | S:101; S:102; S:103; A75; D108; E:620; Eval:390 | `functions.extensional` | full |
| H02 | `assert h(0) = 1` | `true` | S:104; A76; D109; E:625; Eval:391 | `functions.at_zero` | full |
| H03 | `assert h(3) = 10` | `true` | S:105; A77; D109; E:626; Eval:392 | `functions.at_three` | full |
| H04 | `assert h(-t) = h(t)` | `true` | S:106; A79; D111; E:635; Eval:393 | `functions.even` | full |
| H05 | `(f ∘ g)(2) for f = t², g = t³` | `64` | E:731; Eval:434 | no statement | none |
| H06 | `m2(3); fa(3) for fa: ℕ → ℕ := n ↦ n²` | `6; 9` | E:788; Eval:440; D148; E:2063 | no statement | none |
| H07 | `let k(t) = t + 7 in ℤ/5 → ℤ/5; k(4); k(t)` | `1 ∈ ℤ/5; t + 2` | E:795; E:805; Eval:441 | no statement | none |

### Polynomials

| ID | Spike computation | Result | Sources | Statements | Carried |
| --- | --- | --- | --- | --- | --- |
| P01 | `let p(x) := x³ − 2x + 1 in ℤ[x]; assert x ∈ ℤ[x]` | `true` | S:113; S:115; A14; E:190; Eval:503 | `polynomials.variable` | full (typing judgement) |
| P02 | `assert p ∈ ℤ[x]` | `true` | S:116; A15; E:191; Eval:505 | `polynomials.member` | full (typing judgement) |
| P03 | `assert p.deg() = 3` | `true` | S:117; A17; E:206; Eval:517 | `polynomials.degree` | full |
| P04 | `assert p(1) = 0` | `true` | S:118; D23; Eval:375 | `polynomials.root` | full |
| P05 | `p.factor()` | `(x − 1)(x² + x − 1)` | S:120; S:121; A18; E:178; R:180 | `polynomials.factors` | full |
| P06 | `q := map p to ℂ[x]; q.factor()` | `(x − 1)(x − (−1 + √5)/2)(x − (−1 − √5)/2)` | S:122; S:123; S:124; A136; A137; E:1433; R:205 | `factorization.over_complexes` | full |
| P07 | `let q := x ↦ x² − 2 in ℚ[x]; assert q(√2) = 0` | `true` | S:129; S:130; E:1425; Eval:707 | `polynomials.at_sqrt2` | full |
| P08 | `assert q(-√2) = 0` | `true` | S:131; E:1426; Eval:708 | `polynomials.at_minus_sqrt2` | full |
| P09 | `assert q.roots() ⊆ ℂ - ℚ (the spike: q.roots() = {} in ℚ, and qc.roots() ⊆ ℂ − ℚ for qc = map q to ℂ[x])` | `true` | S:132; A146; A147; E:1456; E:1462 | `polynomials.irrational_roots`, `polynomials.no_rational_roots` | full |
| P10 | `map p to ℚ[x]; its factorization and q(1) = 0` | `(x − 1)(x² + x − 1); true` | A19; A20; A21; E:180; E:181; E:183; R:150; CanonicalMaps:276 | `polynomials.degree_over_rationals` | partial |
| P11 | `p ∈ ℚ[x]; 1/2 ∉ ℤ[x]; 1/2 ∈ ℚ[x]; x + 1/2 ∉ ℤ[x]` | `true` | E:192; E:193; Eval:507; Eval:509; Eval:514 | no statement | none |
| P12 | `roots in the coefficient ring: p.roots() over ℤ, (x² − 3x + 2).roots() and (2x − 1).roots() over ℚ` | `{1}; {1, 2}; {1/2}` | A23; D25; E:412; E:424; E:448; R:311; R:328 | no statement | none |
| P13 | `roots with multiplicity: (x − 1)²; ¦dbl.roots()¦` | `{1, 1}; 2` | D34; D35; E:453; E:456; R:332; Core:488 | no statement | none |
| P14 | `roots over ℂ: (map q to ℂ[x]).roots(); x − √2; x − i; x² + 1; x − (1 + 2i)` | `{√2, −√2}; {√2}; {i}; {i, −i}; {1 + 2i}` | A144; E:1459; E:1461; E:1483; E:1490; R:240; R:244; R:249 | no statement | none |
| P15 | `p₅ = x⁵ − x⁴ − x³ + x² − 2x + 2 over ℤ, ℚ, ℂ: roots, factors, ¦roots¦, ∑ and ∏ of the roots` | `{1} in ℤ and ℚ; (x − 1)(x² − 2)(x² + 1); five roots {±√2, 1, ±i} in ℂ; ∑ = 1; ∏ = −2` | D21; D25; D27; D30; D31; D38; D39; D45 | no statement | none |
| P16 | `pc := map p to ℂ[x]; pc ∈ ℂ[x]; pc.deg(); pc(1), pc((−1 ± √5)/2)` | `true; 3; 0, 0` | A139; A140; D42; D43; E:1439; Eval:690 | no statement | none |
| P17 | `factorizations with a unit: 2x² − 2 over ℚ; the constant 1; −2x − 2 over ℤ` | `2(x − 1)(x + 1); 1; (−1)·2·(x + 1)` | E:1152; E:1159; R:191; Core:930 | no statement | none |
| P18 | `polynomial arithmetic and substitution: (1 + 2x)(1 + 3x); p(2); pin(x) + 1 at 2; 2x² at 3; 3 − x at 1` | `1 + 5x + 6x²; 5; 5; 18; 2` | Eval:42; Eval:376; Eval:973; E:222; Eval:593 | no statement | none |

### Differentials

| ID | Spike computation | Result | Sources | Statements | Carried |
| --- | --- | --- | --- | --- | --- |
| D01 | `let X := Spec ℚ[x] in Schemes/ℚ` | `X := Spec ℚ[x]` | S:140; A192; E:233; Eval:539 | `schemes.affine_line` | full (typing judgement) |
| D03 | `assert f ∈ ℚ[x]` | `true` | S:152; Eval:541 | `differentials.member` | full (typing judgement) |
| D04 | `assert f.deg() = 2` | `true` | S:153; E:217; Eval:528 | `differentials.degree` | full |
| D05 | `assert f(2) = 15` | `true` | S:154; E:216; Eval:529 | `differentials.at_two` | full |
| D06 | `assert d(f) = (6x + 1) dx (and d(f) ≠ 6x + 1)` | `true` | S:156; A195; A198; D86; E:247; Eval:542 | `differentials.differential` | full |
| D07 | `assert (d/dx)(f) = 6x + 1` | `true` | S:157; A196; D88; E:248; Eval:543 | `differentials.derivative` | full |

### Indefinite integration

| ID | Spike computation | Result | Sources | Statements | Carried |
| --- | --- | --- | --- | --- | --- |
| I01 | `kernel(d/dx : ℚ[x] → ℚ[x])` | `ℚ` | S:170; S:171; A200; D92; E:258; Eval:560 | no statement | none |
| I02 | `∫ f dx; assert ∫ f dx = x³ + (1/2)x² + x + ℚ` | `x³ + (1/2)x² + x + ℚ` | S:176; S:177; S:178; A201; A202; D90; E:276; E:278; Eval:562 | `integration.primitives` | full |
| I03 | `assert ∫ f dx = x³ + (1/2)x² + x + 7 + ℚ` | `true (any representative)` | A203; E:280; Eval:565 | no statement | none |
| I04 | `assert ¦∫ f dx¦ = ℵ₀` | `true` | E:283; Eval:569 | no statement | none |
| I05 | `let Fs := {h ∈ ∫ f dx ¦ h(0) = 0} in 𝒫(ℚ[x]); assert Fs.cardinality() = 1` | `true; Fs = {x³ + (1/2)x² + x}` | S:184; S:185; A205; A206; D94; E:286; E:287; Eval:571 | `integration.normalized_count`, `integration.normalized` | full |
| I06 | `let F := Fs[0] in ℚ[x]; assert F(x) = x³ + (1/2)x² + x` | `the unique member of Fs` | S:186; S:188; A207; A208; D94; E:288; E:289; Eval:574; Eval:576 | no statement | none |
| I07 | `assert d(F) = f dx` | `true` | S:189; A209; D94; E:290; Eval:577 | `integration.differential` | full |
| I08 | `assert (d/dx)(F) = f` | `true` | S:190; E:291; Eval:578 | `integration.derivative` | full |
| I09 | `F ∈ ∫ f dx; F(0)` | `true; 0` | Eval:580; S:184 | `integration.at_zero` | partial |
| I10 | `Gs := {h ∈ ∫ f dx ¦ h(0) = 5}; G := Gs[0]` | `G = x³ + (1/2)x² + x + 5` | Eval:585 | no statement | none |

### Elementary calculus

| ID | Spike computation | Result | Sources | Statements | Carried |
| --- | --- | --- | --- | --- | --- |
| L01 | `assert lim_{t → 0} sin(t)/t = 1` | `true` | S:197; A211; D132; E:313; R:493 | `calculus.limit_sinc` | full |
| L02 | `assert lim_{t → ∞} 1/t = 0` | `true` | S:198; A212; D132; E:314; R:498 | `calculus.limit_infinity` | full |
| L03 | `lim_{t → ∞} sin(t)` | `does not converge (structured refusal)` | E:327; R:512 | no statement | none |
| L04 | `assert ∫₀¹ t² dt = 1/3` | `true` | S:203; A213; D134; E:335; R:523 | `calculus.integral_square` | full |
| L05 | `assert ∫₀^π sin(t) dt = 2` | `true` | S:204; A214; D134; E:336; R:527 | `calculus.integral_sine` | full |
| L06 | `let f := t ↦ e^t in ℝ → ℝ; Tf := f.taylor_expansion(0) in ℝ[[t]]; assert Tf ∈ ℝ[[t]]` | `true` | S:209; S:211; S:212; A218; A219; D136; E:347; E:348 | `calculus.taylor_exp` | full (typing judgement) |
| L07 | `map Tf to ℝ[[t]]/(t^6); [t³]Tf, [t⁵]Tf` | `1 + t + (1/2)t² + (1/6)t³ + (1/24)t⁴ + (1/120)t⁵ + O(t⁶); 1/6, 1/120` | S:213; S:214; A221; D136; E:350; E:360; R:540 | no statement | none |
| L08 | `let g: ℝ → ℝ := t ↦ sin(t); Tg := g.taylor_expansion(0) in ℝ[[t]]; assert Tg ∈ ℝ[[t]]` | `true` | S:219; S:220; S:221; A223; E:365; E:367 | `calculus.taylor_sin` | full (typing judgement) |
| L09 | `map Tg to ℝ[[t]]/(t^8)` | `t − (1/6)t³ + (1/120)t⁵ − (1/5040)t⁷ + O(t⁸)` | S:222; S:223; A224; D137; E:368; R:547 | no statement | none |

### Vectors and matrices

| ID | Spike computation | Result | Sources | Statements | Carried |
| --- | --- | --- | --- | --- | --- |
| M01 | `let M := [1, 2; 3, 4] in Mat₂(ℚ); v := (1, 2); b := (5, 11); assert M*v = b (also M v, M(v); and v = (1, 0), b = (1, 3))` | `true` | S:230; S:233; S:234; S:239; A39; D75; E:1794; Eval:856; Core:650 | `matrices.product`, `matrices.juxtaposition`, `matrices.application` | full |
| M02 | `assert M.det() = -2 (also det [0, 1; 1, 0] = −1, det of the zero 3×3 matrix = 0)` | `true` | S:240; A35; D65; E:503; R:344; Core:733 | `matrices.det` | full |
| M03 | `assert M.rank() = 2` | `true` | S:241; A46; D69; E:1839 | `matrices.rank` | full |
| M04 | `assert M.ker() = {0}` | `true; M.ker() = {0} ≤ ℚ²` | S:242; A47; A48; D70; D71; E:1844 | `matrices.kernel` | full |
| M05 | `M⁻¹ (also M.inverse())` | `[−2, 1; 3/2, −1/2]` | S:247; S:248; A34; D67; E:501; E:1799; R:346 | `inverses.value` | full |
| M06 | `assert M⁻¹ b = v` | `true` | S:254; A40; E:1795 | `inverses.solve` | full |
| M07 | `assert M⁻¹(M v) = v` | `true` | S:255; A41; E:1796 | `inverses.left` | full |
| M08 | `assert M(M⁻¹ b) = b` | `true` | S:256; A42; E:1797 | `inverses.right` | full |
| M09 | `assert M.trace() = 5` | `true` | A49 | `matrices.trace` | full |
| M10 | `charpoly of [0, −2; 1, 3]` | `x² − 3x + 2` | R:369; Core:846 | `matrices.charpoly` | full |
| M11 | `inverse of the singular [1, 2; 2, 4]` | `refused: not invertible` | R:351 | no statement | none |
| M12 | `vectors add: v + b, b − v, ∑_{u ∈ {v, b}} u (∏ refused: no product of vectors)` | `(6, 13), (4, 9), (6, 13)` | E:2002; E:2004; Core:531 | no statement | none |
| M13 | `trace over ℤ/5: [1, 2; 3, 4] in Mat₂(ℤ/5)` | `0` | E:1934; E:1935 | no statement | none |

### Subspaces and spans

| ID | Spike computation | Result | Sources | Statements | Carried |
| --- | --- | --- | --- | --- | --- |
| W01 | `let W := span_QQ{u₁, u₂} \leq ℚ³ in QQ-Mod; assert W.dim() = 2` | `true` | S:263; S:264; S:266; S:269; A166; D120; E:1859; Eval:901 | `subspaces.dim` | full |
| W02 | `assert (1, 1, 2) ∈ W` | `true` | S:270; A167; D120; E:1860; Eval:902 | `subspaces.member` | full |
| W03 | `assert (1, 1, 0) ∉ W` | `true` | S:271; A168; D120; E:1861; Eval:903 | `subspaces.not_member` | full |
| W04 | `let φ: ℚ³ → ℚ := (a, b, c) ↦ a + b − c; assert W = ker φ` | `true` | S:276; S:278; A173; A174; D122; E:2189; E:2190; Core:760 | `subspaces.kernel` | partial |
| W05 | `span normal form: span{u₁, u₂, (1, 1, 2)} = W, span{(1, 1, 2), (0, 1, 1)} = W, span{(1, 0, 0), (0, 1, 1)} ≠ W` | `true` | A170; A171; E:1896; E:1897; Eval:908; Core:691 | no statement | none |
| W06 | `span{u₁} ⊆ W; ¦W¦` | `true; ℵ₀` | E:1895; E:1898; Eval:918; Eval:920 | no statement | none |
| W07 | `the trivial subspace span{(0, 0)} ≤ ℚ²: dim, ¦·¦, = {0}` | `0, 1, true` | Eval:923; Core:742 | no statement | none |
| W08 | `φ((1, 1, 2)), φ((1, 1, 0)); φq(vq) for φq: QQ^3 → QQ` | `0, 2; 0` | D123; E:2192; E:2094 | no statement | none |
| W09 | `fh: ℚ³ → ℚ³ := (x, y, z) ↦ (2x + 3y + z, x − y, 3z − x): fh((1, 0, 0)), (fh ∘ fh)((1, 0, 0)), ker fh, im fh; φ ∘ fh` | `(2, 1, −1); (6, 1, −5); {0}; span of the standard basis; (x, y, z) ↦ 4x + 2y − 2z` | D126; D127; D128; D129; D130; E:2196; Core:761; Core:769 | no statement | none |

### A composed computation

| ID | Spike computation | Result | Sources | Statements | Carried |
| --- | --- | --- | --- | --- | --- |
| K01 | `let r(x) := x³ − 2x + 1 in ℚ[x]; let roots := {a ∈ ℂ ¦ r(a) = 0} in 𝒫(ℂ); assert ¦roots¦ = 3` | `true` | S:285; S:286; S:288; A176; A177; A179; D139; E:1950 | `composed.root_count` | full |
| K02 | `assert 1 ∈ roots` | `true` | S:289; A180; D139; E:1951 | `composed.root_one` | full |
| K03 | `assert ∑_{a ∈ roots} a = 0` | `true` | S:290; A182; D139; E:1952 | `composed.root_sum` | partial |
| K04 | `assert ∏_{a ∈ roots} a = -1` | `true` | S:291; A183; D139; E:1953 | `composed.root_product` | partial |
| K05 | `roots (the root set itself)` | `{−1/2 − (1/2)√5, −1/2 + (1/2)√5, 1}` | A178; D139; E:1956 | no statement | none |
| K06 | `let C := r.companion_matrix(); assert C.charpoly() = r` | `true; C = [0, 0, −1; 1, 0, 2; 0, 1, 0]` | S:296; S:298; A185; A187; D140; E:1913; E:1915; R:376; Core:890 | `composed.charpoly` | full |
| K07 | `assert C.det() = -1` | `true` | S:299; A188; D140; E:1916; R:384 | `composed.det` | full |
| K08 | `assert C.trace() = 0` | `true` | S:300; A189; D140; E:1917 | `composed.trace` | full |
| K09 | `let f(t) = t^2 in RR->RR; let g(t) = t^3 in RR->RR; assert (f ∘ g)(t) = t^6` | `true` | S:306; S:307; S:308; A85; D113; E:730; Eval:430 | `composed.composition` | full |

### Ellipses

| ID | Spike computation | Result | Sources | Statements | Carried |
| --- | --- | --- | --- | --- | --- |
| E01 | `let X := {0, 1, 2, ...}; assert X = \NN` | `true` | S:316; S:317; A64; D142; D145; E:534; E:2058 | `ellipses.naturals` | full |
| E02 | `let Y := {0, 2, 4, ...}; assert Y = {2n ¦ n in \NN} (and 8 ∈ Y, 9 ∉ Y)` | `true` | S:318; S:319; A66; A67; D142; E:536; E:2060 | `ellipses.evens` | full |
| E03 | `assert Y = 2\NN (and X ≠ 2ℕ)` | `true` | S:320; D142; E:957; E:2154; E:2156 | `ellipses.multiples` | full |
| E04 | `let f: NN -> NN := n ↦ n^2; let Z := {n in \NN ¦ f(n) \in 2\NN} (2 ∈ Z, 3 ∉ Z)` | `Z presented by its guard` | S:321; S:322; E:2165 | `ellipses.even_square`, `ellipses.odd_square`, `ellipses.squares_even` | full |
| E05 | `let primes := {n in \NN ¦ n.is_prime() }` | `a set decided on membership` | S:323; D152; E:1009 | `ellipses.prime`, `ellipses.not_prime` | full |
| E06 | `let R := CC[x_0, x_1, ..., x_9]` | `spike refused (reserved spelling, not implemented)` | S:329; B21; D154; E:2108 | `several_variables.variable`, `several_variables.last_variable` | full (typing judgement); spike refused |
| E07 | `assert R in Algebras/CC` | `spike refused` | S:330; E:2117 | `algebras.polynomials_several` | full (typing judgement); spike refused |
| E08 | `assert R.dimension() is 10` | `spike refused` | S:331; E:2120 | `several_variables.dimension` | full; spike refused |
| E09 | `let f(t) = ∑_{n ∈ \NN} n^2 t^n \in ZZ[[t]]; assert [t^2]f = 4 (also [t³]f, [t⁰]f)` | `true; 9, 0` | S:338; S:343; A226; A229; D149; D150; D156; E:383; Eval:612 | `series.coefficient_two`, `series.coefficient_three`, `series.coefficient_zero`, `series.coefficient_four` | full |
| E10 | `map f to ZZ[[t]] / O(t^5)` | `t + 4t² + 9t³ + 16t⁴ + O(t⁵)` | S:339; S:340; A228; D156; E:386 | no statement | none |

### Modules

| ID | Spike computation | Result | Sources | Statements | Carried |
| --- | --- | --- | --- | --- | --- |
| R01 | `let F := ℤ/4 in CyclicModules(ℤ) (and in Modules(ℤ)); F.annihilator() (also ℤ/12)` | `(4); (12)` | A51; A52; D77; D78; E:514; E:523; Core:1046 | no statement | none |
| R02 | `F.cardinality() for F = ℤ/4 as ℤ-module (through the underlying set); 2 ∈ F` | `4; true` | A54; A56; D79; E:583; E:585; Transport:248; Transport:309 | `rx:complete.rx06.restricted_cardinality` | partial |
| R03 | `F.set_eq({0, 1, 2, 3}) (and bare F = {0, 1, 2, 3} false)` | `true` | A58; A59; D82; B6; B7; E:604; E:608; Transport:343 | no statement | none |

### Sets of numbers

| ID | Spike computation | Result | Sources | Statements | Carried |
| --- | --- | --- | --- | --- | --- |
| Q01 | `ℂ − ℚ: √2 ∈, 2 + 2i ∈, 1 ∉, 1/2 ∉; {√2, −√2} ⊆ ℂ − ℚ` | `true` | E:1467; E:1468; Eval:713; Eval:719; Core:1020 | no statement | none |
| Q02 | `ℚ[[t]] ⊆ ℝ[[t]]; ℝ[[t]] ⊆ ℚ[[t]]` | `true; false` | E:2177; E:2180 | no statement | none |
| Q03 | `X.cardinality() for X = {0, 1, 2, ...}; ℤ.cardinality()` | `ℵ₀; ℵ₀` | A71; E:546; E:1306 | `sets.card.naturals`, `sets.card.integers` | full |


## Proposed statements

The proposed statements of the rows with the value "none" or "partial". A typing judgement is marked; it needs no computation.

| ID | Proposed statement | Bindings | Categories on the route | Missing catalogue row | Note |
| --- | --- | --- | --- | --- | --- |
| N04.1 | `assert gcd(0, -7) = 7` | — | magmas, monoids, rings, semigroups, sets | — | The gcd at zero and at a negative argument; the result is not negative. |
| N06.1 | `assert (-12 in ℤ ∖ 0).factors() = {2, 3}` | — | magmas, monoids, rings, semigroups, sets | `missing.ufd_factorization` | The unit −1 is part of the result; no row factors an integer. |
| N11.1 | `assert 2 + 2 · i ∈ ℂ` | — | rings, sets (typing judgement) | — | `numbers.cas` checks it only in the binding `let z := 2 + 2 · i in ℂ`. A typing judgement. |
| N17.1 | `assert ¦approximate(√2, 1/10^{10}) - √2¦ < 1/10^{10}` | — | linear_orders, magmas, monoids, rings, semigroups, sets | `missing.real_approximation` | `factorization.approximation` decides ¦√2 − 1.4142135623¦ < 10⁻¹⁰ for a given decimal; no statement asks for the approximation. |
| N18.1 | `assert sqrt(8) = 2 · sqrt(2)` | — | magmas, monoids, rings, semigroups, sets | — | — |
| N18.2 | `assert sqrt(9) = 3` | — | magmas, monoids, rings, semigroups, sets | — | — |
| N18.3 | `assert sqrt(-4) = 2 · i` | — | magmas, monoids, rings, semigroups, sets | `missing.complex_sqrt` | √ of a negative rational is a chosen complex root. |
| N19.1 | `assert sqrt(2) · sqrt(2) = 2` | — | magmas, monoids, rings, semigroups, sets | — | — |
| N19.2 | `assert (1 + sqrt(2)) · (1 - sqrt(2)) = -1` | — | magmas, monoids, rings, semigroups, sets | — | — |
| N20.1 | `assert √2 ∉ ℚ` | — | magmas, monoids, rings, semigroups, sets | — | — |
| N20.2 | `assert 2 + 2 · i ∉ ℝ` | — | magmas, monoids, rings, semigroups, sets | — | — |
| N21.1 | `assert s2.im() = 0` | `let s2 := sqrt(2) in ℝ` | magmas, monoids, rings, semigroups, sets | — | — |
| N21.2 | `assert ¦1 - sqrt(2)¦ = sqrt(2) - 1` | — | magmas, monoids, rings, semigroups, sets | — | — |
| N22.1 | `assert 1 + 1/2 = 3/2` | — | magmas, monoids, rings, semigroups, sets | — | — |
| N23.1 | `assert 2^10 = 1024` | — | magmas, monoids, rings, semigroups, sets | — | — |
| N23.2 | `assert (1/2)^0 = 1 in ℚ` | — | magmas, monoids, rings, semigroups, sets | — | — |
| N25.1 | `assert ℤ[3] = -2` | — | enumerated_sets, magmas, monoids, rings, semigroups, semirings, sets | `missing.denumerable_enumeration` | User Story 4.4 and FR-034 require the adopted order; no workload statement asks for it. The notebook at 9c7d438 shows the superseded zigzag order. |
| N25.2 | `assert ℚ[2] = -1/2` | — | enumerated_sets, magmas, monoids, rings, semigroups, semirings, sets | `missing.denumerable_enumeration` | — |
| N26.1 | `assert ¦Mat₂(ℤ/3)¦ = 81` | — | cardinals, commutative_rings, core_sets, magmas, monoids, rings, semigroups, sets | — | — |
| N26.2 | `assert ¦ℚ[x]¦ = ℵ₀` | — | cardinals, commutative_rings, core_sets, magmas, monoids, rings, semigroups, sets | — | — |
| N27.1 | `assert (map 3 to ℂ) = 3 in ℂ` | — | magmas, monoids, rings, semigroups, sets | — | An inclusion of the number systems applied to an element. |
| N29.1 | `assert m.is_prime()` | `let m := -7 in ℤ` | magmas, monoids, rings, semigroups, sets | `missing.ufd_prime` | The ruling that −7 is prime ((−7) = (7)) makes primality a UFD notion on ℤ. |
| N29.2 | `assert (1).is_prime() = false` | — | semirings, sets | — | — |
| F01.1 | `assert A in 𝒫(ℤ)` | `let A := {1, 2, 3} in 𝒫(ℤ)`<br>`let B := {3, 4, 5} in 2^ℤ` | rings, sets (typing judgement) | — | `finite_sets.cas` has the two bindings and no statement about them. A typing judgement. |
| F08.1 | `assert ¦𝒫(A)¦ = 2^¦A¦` | `let A := {1, 2, 3} in 𝒫(ℤ)`<br>`let B := {3, 4, 5} in 2^ℤ` | cardinals, core_sets, magmas, monoids, rings, semigroups, sets | `missing.cardinal_power` | `finite_sets.card_power_set` writes the right side as 8; SPEC.md writes the power of a cardinal. |
| F08.2 | `assert ¦𝒫(ℤ/10)¦ = 1024` | — | cardinals, core_sets, magmas, monoids, rings, semigroups, sets | — | — |
| F13.1 | `assert A ∪ B ∉ 𝒫(A)` | `let A := {1, 2, 3} in 𝒫(ℤ)`<br>`let B := {3, 4, 5} in 2^ℤ` | boolean_algebras, magmas, monoids, rings, semigroups, sets | — | — |
| F14.1 | `assert {1, 2, 2, 3} = {1, 2, 3} in 𝒫(ℤ)` | — | magmas, monoids, rings, semigroups, sets | — | — |
| F15.1 | `assert {1, 3, ..., 9} = {1, 3, 5, 7, 9}` | — | semirings, sets | — | — |
| F16.1 | `assert ∑_{a ∈ {1, 2, 3}} a = 6` | — | magmas, monoids, rings, semigroups, sets | — | — |
| F16.2 | `assert ∏_{a ∈ {}} a = 1` | — | magmas, monoids, rings, semigroups, sets | — | — |
| F16.3 | `assert ∑_{a ∈ {1, 2, 3}} (a^2) = 14` | — | magmas, monoids, rings, semigroups, sets | — | — |
| C04.1 | `assert 4 ∈ S` | `let S := {n ∈ ℤ ¦ n² ≤ 20}` | linear_orders, magmas, monoids, rings, semigroups, sets | — | — |
| C04.2 | `assert 5 ∉ S` | `let S := {n ∈ ℤ ¦ n² ≤ 20}` | linear_orders, magmas, monoids, rings, semigroups, sets | — | — |
| C05.1 | `assert {n ∈ ℤ ¦ n - n < 0} = {}` | — | linear_orders, magmas, monoids, rings, semigroups, sets | — | — |
| C12.1 | `assert {m2(n) ¦ n ∈ ℕ, 0 ≤ n < 6} = {0, 2, 4, 6, 8, 10}` | `let m2 : ℕ → ℕ := n ↦ 2n` | linear_orders, semirings, sets | — | The image of the bounded subset {n ∈ ℕ ¦ 0 ≤ n < 6} under m2. |
| C13.1 | `assert {7 ¦ n ∈ ℕ} = {7}` | — | semirings, sets | — | The image of a constant map. |
| C14.1 | `assert {2, 4} ⊆ E` | `let E := {2n ¦ n ∈ ℕ}` | boolean_algebras, semirings, sets | — | — |
| C15.1 | `assert {a ∈ ℚ ¦ r(a) = 0} = {1}` | `let r(x) := x³ - 2x + 1 in ℚ[x]` | commutative_rings, magmas, monoids, rings, semigroups, sets | — | The solution set of a polynomial equation in the coefficient field; over ℂ it is `composed.root_count`. |
| H05.1 | `assert (f ∘ g)(2) = 64` | `let f(t) := t^2 in ℝ → ℝ`<br>`let g(t) := t^3 in ℝ → ℝ` | magmas, monoids, rings, semigroups, sets | — | — |
| H06.1 | `assert m2(3) = 6` | `let m2 : ℕ → ℕ := n ↦ 2n` | semirings, sets | — | — |
| H07.1 | `assert k(4) = 1` | `let k(t) := t + 7 in ℤ/5 → ℤ/5` | magmas, monoids, rings, semigroups, sets | — | — |
| H07.2 | `assert k(t) = t + 2` | `let k(t) := t + 7 in ℤ/5 → ℤ/5` | magmas, monoids, rings, semigroups, sets | — | — |
| P10.1 | `assert ((map p to ℚ[x]) in ℚ[x] ∖ 0).factors() = {x - 1, x² + x - 1}` | `let p(x) := x³ - 2x + 1 in ℤ[x]` | commutative_rings, magmas, monoids, rings, semigroups, sets | — | The statement reads the coefficient change through the degree; the factorization over ℚ has no statement. |
| P11.1 | `assert p ∈ ℚ[x]` | `let p(x) := x³ - 2x + 1 in ℤ[x]` | commutative_rings, rings, sets (typing judgement) | — | — |
| P11.2 | `assert 1/2 ∉ ℤ[x]` | — | commutative_rings, magmas, monoids, rings, semigroups, sets | — | — |
| P12.1 | `assert (p in ℤ[x] ∖ 0).roots() = {1}` | `let p(x) := x³ - 2x + 1 in ℤ[x]` | commutative_rings, magmas, monoids, rings, semigroups, sets | — | — |
| P12.2 | `assert (sp in ℚ[x] ∖ 0).roots() = {1, 2}` | `let sp := x ↦ x² - 3x + 2 in ℚ[x]` | commutative_rings, magmas, monoids, rings, semigroups, sets | — | — |
| P13.1 | `assert ¦(dbl in ℚ[x] ∖ 0).roots()¦ = 2` | `let dbl(x) := x² - 2x + 1 in ℚ[x]` | cardinals, commutative_rings, core_sets, magmas, monoids, rings, semigroups, sets | `missing.root_multiset` | With the catalogue's root set the count is 1; the spike's result is the multiset of Mathlib `Polynomial.roots`. |
| P14.1 | `assert ((map q to ℂ[x]) in ℂ[x] ∖ 0).roots() = {√2, -√2}` | `let q := x ↦ x² - 2 in ℚ[x]` | commutative_rings, magmas, monoids, rings, semigroups, sets | — | — |
| P14.2 | `assert (ps in ℂ[x] ∖ 0).roots() = {√2}` | `let ps := x ↦ x - √2 in ℂ[x]` | commutative_rings, magmas, monoids, rings, semigroups, sets | — | — |
| P15.1 | `assert (p5 in ℤ[x] ∖ 0).factors() = {x - 1, x² - 2, x² + 1}` | `let p5(x) := x^5 - x^4 - x^3 + x^2 - 2x + 2 in ℤ[x]` | commutative_rings, magmas, monoids, rings, semigroups, sets | — | — |
| P15.2 | `assert ¦{a ∈ ℂ ¦ p5(a) = 0}¦ = 5` | `let p5(x) := x^5 - x^4 - x^3 + x^2 - 2x + 2 in ℤ[x]` | cardinals, commutative_rings, core_sets, magmas, monoids, rings, semigroups, sets | — | — |
| P15.3 | `assert ∏_{a ∈ ((map p5 to ℂ[x]) in ℂ[x] ∖ 0).roots()} a = -2` | `let p5(x) := x^5 - x^4 - x^3 + x^2 - 2x + 2 in ℤ[x]` | commutative_rings, magmas, monoids, rings, semigroups, sets | — | — |
| P16.1 | `assert (map p to ℂ[x])((-1 + √5)/2) = 0` | `let p(x) := x³ - 2x + 1 in ℤ[x]` | commutative_rings, magmas, monoids, rings, semigroups, sets | — | — |
| P17.1 | `assert (lr in ℚ[x] ∖ 0).factorization().unit() = 2` | `let lr(x) := 2x² - 2 in ℚ[x]` | commutative_rings, magmas, monoids, rings, semigroups, sets | — | — |
| P18.1 | `assert (1 + 2x) · (1 + 3x) = 1 + 5x + 6x² in ℤ[x]` | — | commutative_rings, magmas, monoids, rings, semigroups, sets | — | — |
| P18.2 | `assert p(2) = 5` | `let p(x) := x³ - 2x + 1 in ℤ[x]` | commutative_rings, magmas, monoids, rings, semigroups, sets | — | — |
| I01.1 | `assert kernel(d/dx : ℚ[x] → ℚ[x]) = ℚ` | `let f := x ↦ 3x² + x + 1 in ℚ[x]` | arrows_modules_r, commutative_rings, magmas, modules_r, monoids, rings, semigroups, sets, subobjects_modules_r | `missing.derivative_linear` | — |
| I03.1 | `assert ∫ f dx = x³ + (1/2)x² + x + 7 + ℚ` | `let f := x ↦ 3x² + x + 1 in ℚ[x]` | commutative_rings, magmas, monoids, rings, semigroups, sets | — | — |
| I04.1 | `assert ¦∫ f dx¦ = ℵ₀` | `let f := x ↦ 3x² + x + 1 in ℚ[x]` | cardinals, commutative_rings, core_sets, magmas, monoids, rings, semigroups, sets | — | — |
| I06.1 | `assert F = x³ + (1/2)x² + x` | `let f := x ↦ 3x² + x + 1 in ℚ[x]`<br>`let Fs := {h ∈ ∫ f dx ¦ h(0) = 0} in 𝒫(ℚ[x])`<br>`let F := Fs[0] in ℚ[x]` | commutative_rings, magmas, monoids, rings, semigroups, sets | — | `differentials.cas` binds F as the literal x³ + (1/2)x² + x; User Story 2.1 needs the selected member. |
| I09.1 | `assert F ∈ ∫ f dx` | `let f := x ↦ 3x² + x + 1 in ℚ[x]`<br>`let F := x³ + (1/2)x² + x in ℚ[x]` | commutative_rings, magmas, monoids, rings, semigroups, sets | — | — |
| I10.1 | `assert Gs = {x³ + (1/2)x² + x + 5}` | `let f := x ↦ 3x² + x + 1 in ℚ[x]`<br>`let Gs := {h ∈ ∫ f dx ¦ h(0) = 5} in 𝒫(ℚ[x])` | commutative_rings, magmas, monoids, rings, semigroups, sets | — | — |
| L03.1 | `assert (t ↦ sin(t) in ℝ → ℝ) ∉ ConvergentAtInfinity` | — | sets | — | The limit is partial; its domain is `obj.sets.convergent_maps_at_infinity`. |
| L07.1 | `assert [t^3]Tf = 1/6` | `let f := t ↦ exp(t) in ℝ → ℝ`<br>`let Tf := (f in C^∞).taylor_expansion(0)` | commutative_rings, magmas, monoids, rings, semigroups, sets | — | `calculus.taylor_exp` asserts only the membership Tf ∈ ℝ[[t]]. |
| L07.2 | `assert (map Tf to ℝ[[t]]/(t^6)) = 1 + t + (1/2)t² + (1/6)t³ + (1/24)t⁴ + (1/120)t⁵` | `let f := t ↦ exp(t) in ℝ → ℝ`<br>`let Tf := (f in C^∞).taylor_expansion(0)` | commutative_rings, magmas, monoids, rings, semigroups, sets | `missing.series_truncation` | — |
| L09.1 | `assert [t^7]Tg = -1/5040` | `let g := t ↦ sin(t) in ℝ → ℝ`<br>`let Tg := (g in C^∞).taylor_expansion(0)` | commutative_rings, magmas, monoids, rings, semigroups, sets | — | — |
| L09.2 | `assert (map Tg to ℝ[[t]]/(t^8)) = t - (1/6)t³ + (1/120)t⁵ - (1/5040)t⁷` | `let g := t ↦ sin(t) in ℝ → ℝ`<br>`let Tg := (g in C^∞).taylor_expansion(0)` | commutative_rings, magmas, monoids, rings, semigroups, sets | `missing.series_truncation` | — |
| M11.1 | `assert [1, 2; 2, 4] ∉ Mat₂(ℚ)ˣ` | — | commutative_rings, magmas, monoids, rings, semigroups, sets | `missing.matrix_inverse_domain` | — |
| M12.1 | `assert v + b = (6, 13)` | `let M := [1, 2;           3, 4]  in Mat₂(ℚ)`<br>`let v := (1, 2) in ℚ²`<br>`let b := (5, 11) in ℚ²` | additive_monoids, magmas, monoids, rings, semigroups, sets | — | — |
| M12.2 | `assert ∑_{u ∈ {v, b}} u = (6, 13)` | `let M := [1, 2;           3, 4]  in Mat₂(ℚ)`<br>`let v := (1, 2) in ℚ²`<br>`let b := (5, 11) in ℚ²` | additive_monoids, magmas, monoids, rings, semigroups, sets | — | — |
| M13.1 | `assert N.trace() = 0` | `let N := [1, 2; 3, 4] in Mat₂(ℤ/5)` | commutative_rings, magmas, monoids, rings, semigroups, sets | — | — |
| W04.1 | `assert W = ker φ` | `let u₁ := (1, 0, 1) in ℚ³`<br>`let u₂ := (0, 1, 1) in ℚ³`<br>`let W := span({u₁, u₂})`<br>`let φ : ℚ³ → ℚ := (a, b, c) ↦ a + b - c` | additive_groups, arrows_modules_r, commutative_rings, fields, groups, magmas, modules_r, modules_total, monoids, rings, semigroups, sets, subobjects_modules_r | `missing.linear_map_from_formula` | `subspaces.kernel` writes the kernel of the matrix N = [1, 1, −1; 0, 0, 0; 0, 0, 0]; the map φ given by its formula has no statement. |
| W05.1 | `assert span({u₁, u₂, (1, 1, 2)}) = W` | `let u₁ := (1, 0, 1) in ℚ³`<br>`let u₂ := (0, 1, 1) in ℚ³`<br>`let W := span({u₁, u₂})` | commutative_rings, fields, magmas, monoids, rings, semigroups, sets | — | — |
| W05.2 | `assert span({(1, 1, 2), (0, 1, 1)}) = W` | `let u₁ := (1, 0, 1) in ℚ³`<br>`let u₂ := (0, 1, 1) in ℚ³`<br>`let W := span({u₁, u₂})` | commutative_rings, fields, magmas, monoids, rings, semigroups, sets | — | — |
| W06.1 | `assert span({u₁}) ⊆ W` | `let u₁ := (1, 0, 1) in ℚ³`<br>`let u₂ := (0, 1, 1) in ℚ³`<br>`let W := span({u₁, u₂})` | boolean_algebras, commutative_rings, fields, magmas, monoids, rings, semigroups, sets | — | — |
| W06.2 | `assert ¦W¦ = ℵ₀` | `let u₁ := (1, 0, 1) in ℚ³`<br>`let u₂ := (0, 1, 1) in ℚ³`<br>`let W := span({u₁, u₂})` | cardinals, commutative_rings, core_sets, fields, magmas, monoids, rings, semigroups, sets | — | — |
| W07.1 | `assert Wzero.dim() = 0` | `let Wzero := span({(0, 0)})` | additive_monoids, commutative_rings, fields, magmas, monoids, rings, semigroups, semirings, sets | — | — |
| W07.2 | `assert ¦Wzero¦ = 1` | `let Wzero := span({(0, 0)})` | additive_monoids, cardinals, commutative_rings, core_sets, fields, magmas, monoids, rings, semigroups, sets | — | — |
| W08.1 | `assert φ((1, 1, 0)) = 2` | `let φ : ℚ³ → ℚ := (a, b, c) ↦ a + b - c` | magmas, monoids, rings, semigroups, sets | `missing.linear_map_from_formula` | — |
| W09.1 | `assert (fh ∘ fh)((1, 0, 0)) = (6, 1, -5)` | `let fh : ℚ³ → ℚ³ := (x, y, z) ↦ (2x + 3y + z, x - y, 3z - x)` | magmas, monoids, rings, semigroups, sets | `missing.linear_map_from_formula` | — |
| W09.2 | `assert ker fh = {0}` | `let fh : ℚ³ → ℚ³ := (x, y, z) ↦ (2x + 3y + z, x - y, 3z - x)` | additive_groups, additive_monoids, arrows_modules_r, groups, magmas, modules_r, modules_total, monoids, rings, semigroups, sets, subobjects_modules_r | `missing.linear_map_from_formula` | — |
| W09.3 | `assert im fh = span({(1, 0, 0), (0, 1, 0), (0, 0, 1)})` | `let fh : ℚ³ → ℚ³ := (x, y, z) ↦ (2x + 3y + z, x - y, 3z - x)` | additive_groups, arrows_modules_r, commutative_rings, fields, groups, magmas, modules_r, modules_total, monoids, rings, semigroups, sets, subobjects_modules_r | `missing.linear_map_from_formula` | — |
| K03.1 | `assert ∑_{a ∈ roots} a = 0` | `let r(x) := x³ - 2x + 1 in ℚ[x]`<br>`let roots := {a ∈ ℂ ¦ r(a) = 0} in 𝒫(ℂ)` | commutative_rings, magmas, monoids, rings, semigroups, sets | — | `composed.root_sum` sums over ((map r to ℂ[x]) in ℂ[x] ∖ 0).roots(); the spike sums over the solution set `roots`. |
| K04.1 | `assert ∏_{a ∈ roots} a = -1` | `let r(x) := x³ - 2x + 1 in ℚ[x]`<br>`let roots := {a ∈ ℂ ¦ r(a) = 0} in 𝒫(ℂ)` | commutative_rings, magmas, monoids, rings, semigroups, sets | — | As K03. |
| K05.1 | `assert roots = {1, (-1 + √5)/2, (-1 - √5)/2}` | `let r(x) := x³ - 2x + 1 in ℚ[x]`<br>`let roots := {a ∈ ℂ ¦ r(a) = 0} in 𝒫(ℂ)` | commutative_rings, magmas, monoids, rings, semigroups, sets | — | — |
| E10.1 | `assert (map f to ℤ[[t]]/(t^5)) = t + 4t² + 9t³ + 16t⁴` | `let f := ∑_{n ∈ ℕ} n² · t^n in ℤ[[t]]` | commutative_rings, magmas, monoids, rings, semigroups, semirings, sets | `missing.series_truncation` | The coefficients up to t⁴ are `series.coefficient_*`; the truncation map has no statement. |
| R01.1 | `assert F.annihilator() = (4)` | `let F := ℤ/4 in Modules(ℤ)` | core_modules_r, ideals_r, magmas, modules_r, monoids, rings, semigroups, sets | `missing.module_annihilator_value`, `missing.cyclic_module_object` | — |
| R02.1 | `assert 2 ∈ F` | `let F := ℤ/4 in Modules(ℤ)` | magmas, modules_r, monoids, rings, semigroups, sets | `missing.cyclic_module_object` | RX-06 asks the cardinality of the finite ℤ-module ℤ/5 through its underlying set. |
| R03.1 | `assert F.set_eq({0, 1, 2, 3})` | `let F := ℤ/4 in Modules(ℤ)` | core_subobjects_sets, magmas, modules_r, monoids, rings, semigroups, sets, subobjects_sets, subsets.subset_predicates | `missing.cyclic_module_object` | — |
| Q01.1 | `assert √2 ∈ ℂ - ℚ` | — | boolean_algebras, magmas, monoids, rings, semigroups, sets | — | — |
| Q01.2 | `assert 1 ∉ ℂ - ℚ` | — | boolean_algebras, magmas, monoids, rings, semigroups, sets | — | — |
| Q02.1 | `assert ℚ[[t]] ⊆ ℝ[[t]]` | — | commutative_rings, magmas, monoids, rings, semigroups, sets | `missing.power_series_inclusion` | — |

## Spike ceilings

| ID | Spike request | Spike refusal | Sources | Requirement | Proposed statement |
| --- | --- | --- | --- | --- | --- |
| X01 | `√2 + √5` | two quadratic fields: a gap, not an approximation | A134; E:1383; Core:179 | FR-078 | `assert (√2 + √5)^2 = 7 + 2 · sqrt(10)` |
| X02 | `√(1 + √2)` | the square root of a non-rational number is not approximated | E:1388 | none | `assert sqrt(1 + sqrt(2))^2 = 1 + sqrt(2)` |
| X03 | `apz.approximate(1/1000) for apz = 2 + 2i` | NoImplementation: only real values are routed | E:1661; A156 | FR-078 | `assert ¦approximate(2 + 2 · i, 1/1000) - (2 + 2 · i)¦ < 1/1000` |
| X04 | `det and charpoly over ℤ/5: [1, 2; 3, 4] in Mat₂(ℤ/5)` | NoImplementation (the deliberate gap) | A234; B28; D162; E:557; E:1936; E:1938 | none | `assert N.det() = 3`<br>`assert N.charpoly() = x² + 3 in (ℤ/5)[x]` |
| X05 | `ℤ ∪ A; 𝒫(A) ∪ A` | NoImplementation: union is routed for explicit finite sets only | E:923; E:925 | none | `assert ℤ ∪ A = ℤ` |
| X06 | `¦ℝ¦, ℝ.cardinality(), ¦ℂ − ℚ¦, ¦2^ℕ¦, ¦𝒫(ℕ)¦` | uncountable: the slice cannot state the cardinal | E:897; E:1302; E:1469; Core:605 | none | `assert ¦ℝ¦ = 2^ℵ₀` |
| X07 | `¦primes¦` | a guard says nothing about size | E:1016 | none | `assert ¦primes¦ = ℵ₀` |
| X08 | `sine(0), recip(2) for symbolic bodies` | evaluation at a point is not implemented for symbolic bodies | B10; B11; E:658; E:662 | none | `assert sine(0) = 0`<br>`assert recip(2) = 1/2` |
| X09 | `(x⁵ − 1).factor() over ℂ` | not_expressible: roots of degree 4 over ℚ | E:1445; R:225 | none | `assert ¦((map pf to ℂ[x]) in ℂ[x] ∖ 0).factors()¦ = 5` |
| X10 | `p.is_prime() for p ∈ ℤ[x] (irreducibility)` | NoImplementation | E:1106 | none | `assert (p in ℤ[x] ∖ 0).is_irreducible() = false` |
| X11 | `zpoly.gcd(zpoly) in ℤ[x]` | NoImplementation | E:685 | none | `assert gcd(x² + 1, x² + 1) = x² + 1 in ℤ[x]` |
| X12 | `{n² ¦ n ∈ ℕ}; {n² ¦ n ∈ ℕ, n.is_prime()}; quadratic and two-sided images` | not an arithmetic progression; the head is not the binder | E:1023; E:1026; Eval:291 | none | `assert 9 ∈ {n² ¦ n ∈ ℕ}` |
| X13 | `{n ∈ ℤ ¦ n² ≥ 20}; a guard bound past the test cap; ¦𝒫(ℤ/5000)¦` | infinite; too many candidates; too large | E:1020; E:1086; E:1090 | FR-010 | `assert 5 ∈ {n ∈ ℤ ¦ n² ≥ 20}`<br>`assert ¦{n ∈ ℤ ¦ n² ≤ 10000000000}¦ = 200001` |
| X14 | `im φ for φ: ℚ³ → ℚ; nonlinear and affine multi-binder bodies` | no span presentation; disclosed gap | Core:766; E:1978; E:1982 | none | `assert φn((1, 2, 3)) = 5` |
| X15 | `AA^2(QQ); CC[x_0, x_1]; (3).dimension()` | reserved spellings refuse by name | B22; E:2097; E:2115; E:2120 | none | `assert Spec ℚ[x, y] in Schemes/ℚ` |
| X16 | `2ℝ (scaling image of ℝ)` | no image presentation | E:959 | none | `assert 2ℝ = ℝ` |
| X17 | `lim_{t → 0} arctan(t); bodies outside {sin, cos, exp, …}` | outside the closed vocabulary | E:321; E:673; R:504; Codec:117 | none | `assert lim_{t → 0} arctan(t) = 0` |
| X18 | `map Tg to ℝ[[t]]/(t^40)` | past the 12-term ceiling | E:374 | FR-010 | `assert [t^39]Tg = -1/20397882081197443358640281739902897356800000000` |

## Features that are not computations in a category

| ID | Kind | Feature | Sources | Requirement | Note |
| --- | --- | --- | --- | --- | --- |
| G01 | error reporting | `assert` decides a proposition with the outcomes true, false, unknown and error; only true commits the cell; a false or unknown assertion fails it | S:3; D1; A1; E:108; E:166 | FR-001, FR-029, US1 | — |
| G02 | language | A bare proposition displays its truth value (`gcd(84, 30) = 6` gives true; false is a successful cell; unknown displays) | D19; E:152 | FR-001, FR-029 | — |
| G03 | language | `and` conjoins assertions, commits once, and names the failed conjunct | S:15; D7; E:1276; E:1993 | FR-001 | — |
| G04 | language | Definitions: `let x := e in D` with a checked ascription, `let p(x) := e in D` with an indeterminate binder, bare `NAME := expr [in D]`, and `let x: T := e in C` with both ascriptions | S:3; D2; D40; D59; E:2026; E:2139 | FR-001 | — |
| G05 | language | Reserved notation: `e` (Euler's number) and `i` (imaginary unit) cannot be rebound; `d` and `π` are constants a binding may shadow; `--` begins a comment | D2; D9; B2; B3; E:398; E:708; E:1758 | none | No requirement states the reservation; FR-002 and FR-008 cover the meaning of i and e. |
| G06 | language | Spelling aliases: NN ZZ QQ RR R CC, the backslash family (\NN \in \leq \mapsto), ¦-> and \mapsto for ↦, -> for →, `is` for =, `in` for ∈, Mod(QQ) and QQ-Mod, QQ^3 for ℚ³, 2^ℤ for 𝒫(ℤ) | S:102; S:266; S:316; S:334; D143; E:2052; E:2074; E:2084 | none | The catalogue `notations` fields own the kernel spellings; the workloads keep `is` (several_variables.dimension). |
| G07 | language | Precedence: a superscript binds tighter than the implicit product (`3x²` is `3·(x²)`); unary minus stays out of it; the braced exponent `x^{k}`; a parenthesized receiver `(360).factor()`; the prefix spelling `gcd(84, 30)` of a method | S:12; E:209; E:1739; E:2040; E:131 | none | — |
| G08 | language | Binder scope: comprehension, function and ∑ binders are local and publish nothing; a binding wins over the indeterminate and over the prefix-method reading | E:763; E:779; E:842; E:1110; E:1768 | FR-003 | — |
| G09 | display | LaTeX-first display: each result emits one bundle with text/latex (inline, ASCII math mode) and text/plain; no text/latex where a value has no natural form (truth values, non-ASCII binders, the ℤ/4 module); assertions and diagnostics stay textual | Latex:1; E:1126; E:1165; E:1187; E:1219 | FR-038, US8 | — |
| G10 | display | Display conventions: rational coefficients `(1/2)x^2`; a series by its rule ends in `…` and a truncation in `O(t^n)`; a vector is the tuple `(1, 2)`; a span shows its reduced basis and its ambient space; a product and a power set are denoted, not listed; a 1-form shows `dx` | S:341; E:384; E:1803; E:1866; E:891; E:261 | FR-038 | — |
| G11 | display | A value payload `application/vnd.casdsl.value+json` beside the display (a multiset, a progression, an approximation with its exact source; a denoted set has none) | E:1243; E:1518 | FR-027, US12 | — |
| G12 | display | Choice disclosures in notation on the result they qualify: the branch cut of the `√` spelling, the fixed embedding $\bar{\mathbb{Q}} \hookrightarrow \mathbb{C}$ of the roots and factors in $\mathbb{C}[x]$ | D38; D49; E:1328; E:465 | FR-038, FR-016, US8 | — |
| G13 | display | Advisory notes on results, for example `p does not split over ℤ: it has 1 of its 3 roots there (with multiplicity)` | D25; E:410 | FR-038, FR-005 | — |
| G14 | provenance | `#explain_route`: the inheritance path as a chain of maps, the Mathlib anchor of the operation, the backend routine and its documentation link, in mathematical wording | D14; D15; D80; E:124; Wording:95 | FR-038, US8 | — |
| G15 | discovery | `#capabilities`: each method with its declaring category, anchor and implemented routes | D157; D158 | FR-037, US8 | — |
| G16 | discovery | `#capability_gaps`: methods that are available and have no implementation for a presentation | D159; A231; E:564 | FR-037, US8 | — |
| G17 | canonical-map audit | `#canonical_maps`: the registered identifications that drive ⊆, ∈, `map … to` and coercion, each with its documentation; a defective (two-way or doubled) registration is a loud error | D160; A31; E:821; CanonicalMaps:196 | FR-037, FR-002 | The kernel reads inclusions as catalogue rows (`incl.sets.*`); no requirement names a listing command. |
| G18 | error reporting | NoImplementation: a structured gap that names the operation, the object, the inheritance path and the routes considered; the mathematics stays available | B26; B28; D161; Eval:315 | FR-013, FR-029, US10 | — |
| G19 | error reporting | Refusals by name: held spellings, a truncation target that is not a ring, ℝ/O(ε) that is not a quotient, a morphism ascribed as an object, a lambda without ascription, domains that do not compose, an argument outside the domain, a shape mismatch of matrix and vector, a symbolic body at a point | B0; E:734; E:1579; E:1815; E:2101; E:2125 | FR-029 | — |
| G20 | approximation tolerance | Approximation semantics: the exact source is kept; the requested and the achieved tolerances travel with the decimal; $\varepsilon$ must be a positive rational; an unmeetable $\varepsilon$ is a capability failure that names it; no arithmetic on approximations; two approximations compare as unknown; the decimal is checked against its bound | S:34; E:1518; E:1555; E:1566; E:1623; E:1637; Codec:125; R:395 | FR-011, US4 | — |
| G21 | language | Bare `=` is bound to one category: `F = {0, 1, 2, 3}` is false for the module `F`; the set question is `set_eq` through the underlying set | B4; D81; Transport:317 | FR-016, FR-019, US3 | — |
| G22 | inheritance | Methods inherited along category inclusions and transported along a preferred forgetful functor (`UnderlyingSet` from modules to sets); two applicable routes are an ambiguity, not a choice | D76; A53; Core:90; Transport:117; Transport:147 | FR-019, FR-023, FR-017, FR-064, US3, US5 | — |
| G23 | inheritance | One arithmetic: ∑ and ∏ fold the same + and × that the binary operators use, attached to the structure of the elements | Core:522 | FR-023 | — |
| G24 | mathematical authority | Mathlib anchors: each category and method names its Mathlib meaning; registered memberships and inclusions must be discharged by Mathlib; availability is checked against Mathlib at each call | Membership:24; Denote:1 | FR-012 | The kernel takes this authority from lean-categories, not from checks in the kernel. |
| G25 | extension | A contributed term production with its translator (`tripleof x` is 3·x) extends the surface without an edit to the core grammar | Extension:188 | none | — |
| G26 | dispatch | Executors keyed by (backend, operation); operation signatures checked when a route registers; a nullary operation refuses an argument | Core:1077; Core:1144 | FR-028, FR-013 | — |
| G27 | error reporting | The wire codec rejects malformed frames (bad magnitude, zero denominator, a shape that contradicts its size, an unknown tag, a symbol outside the vocabulary); the Sage adapter announces its capabilities and answers an unknown operation as unsupported | Codec:165; R:125; R:465 | FR-029, US6 | — |
| G28 | answer checks | Replies checked against the request: factorizations multiplied back, roots evaluated, charpoly, determinant and companion matrix checked | Core:829; Core:901 | FR-029, FR-030 | FR-014 gives checkers no correctness authority; the kernel now observes kernel behaviour and independent expectations assess answers. |
| G29 | notebook behaviour | The notebook is a document: each output is the result of the visible prefix; an edit re-runs the cell and the cells below (↻); an upstream failure stops the run; a failed cell commits nothing | D0; E:570 | US7, FR-034, FR-036 | — |
| G30 | notebook behaviour | Notebook re-execution gate: stored outputs must equal a live document-order run, byte-stable, with timing metadata kept | commit 3801718; commit ddcf982; commit a23ee30 | FR-034, FR-039, FR-043 | — |
| G31 | notebook behaviour | End-to-end acceptance through the real Jupyter protocol against the installed `casdsl` kernelspec | E:1 | FR-034, US7 | — |
| G32 | installation | Install of the Jupyter kernelspec (`nbdsl_kernel.install --project . --prelude-module CasDsl.Notebook --name casdsl`) and the sync-kernel recipe that restarts stale kernels | E:9; commit c3d1551; commit e860c6b; commit 42e4c01 | FR-039 | FR-094 to FR-098 cover the launch of the Sage interpreter; no requirement names the kernelspec install. |
| G33 | installation | The Sage adapter runs as a separate process started by `sage -python backends/sage_adapter.py`; a missing `sage` is a loud failure | R:556 | FR-094, FR-095, FR-097 | — |
| G34 | notebook behaviour | A control notebook on a plain Python kernel | PC0 | none | — |
| G35 | language | An ordinary Lean command in a cell still elaborates as Lean | Eval:1072 | none | — |
| G36 | display | Emitted prose speaks mathematics: no internal vocabulary, no issue citations in diagnostics | Wording:105; commit 4948a46; commit 375a6f6 | FR-037, FR-038 | — |
| G37 | language | Plain numbers are naturally elements of $\mathbb{Z}$: a bare numeral is read in $\mathbb{Z}$ unless an ascription selects another domain | S:45 | FR-002 | The workload readings keep this convention (assumption A1 of `workload-routes.md`). |
| G38 | display | `d` displays the universal relative differential $d : \mathcal{O}_X \to \Omega^1_{X/S}$ and its coordinate form $\mathbb{Q}[x] \to \Omega^1_{\mathbb{Q}[x]/\mathbb{Q}} \cong \mathbb{Q}[x]\,dx$; the integral displays as a coset of the kernel of $d/dx$ | S:142; S:161; S:181; A194; E:243; E:302 | FR-006, FR-007, FR-037 | — |

## Rows of the K3 and K14 statements

| Statement | Catalogue rows | Correction |
| --- | --- | --- |
| `lattices.rank.e8` | `lit.cardinals`, `meth.rank`, `obj.integral_lattice.e8`, `obj.sets.naturals` | `.rank()` of a lattice is `meth.rank`; the matrix rank is the other row of the name. |
| `units.rationals.three_inverse` | `fun.monoids.units`, `fun.rings.multiplicative_monoid`, `meth.units`, `mor.sets.divide`, `mor.sets.equality`, `num.rings`, `obj.rings.rationals`, `obj.sets.rationals`, `op.groups.inverse` | ℚˣ is the image of ℚ under `fun.monoids.units`; the inverse is `op.groups.inverse` (milestones.md). |
| `refinement.finite_product_card` | `cat.finite_sets`, `lim.sets.product`, `lit.cardinals`, `meth.cardinality`, `obj.rings.integers_mod`, `obj.sets.fin` | text match |
| `groups.kernel.sign_card` | `fun.arrows_groups.kernel`, `fun.sets.cardinality`, `fun.subobjects_groups.domain`, `lit.cardinals`, `meth.group_arrow_kernel`, `mor.groups.sign`, `obj.groups.cyclic`, `obj.groups.symmetric` | `ker()` of a group map is `meth.group_arrow_kernel`; `¦·¦` is `fun.sets.cardinality` (milestones.md). |
| `groups.kernel.trivial_card` | `fun.arrows_groups.kernel`, `fun.sets.cardinality`, `fun.subobjects_groups.domain`, `lit.cardinals`, `meth.group_arrow_kernel`, `mor.groups.trivial`, `obj.groups.cyclic`, `obj.groups.symmetric` | As `groups.kernel.sign_card`. |
| `groups.kernel.identity_card` | `fun.arrows_groups.kernel`, `fun.sets.cardinality`, `fun.subobjects_groups.domain`, `lit.cardinals`, `meth.group_arrow_kernel`, `mor.groups.identity`, `obj.groups.symmetric` | As `groups.kernel.sign_card`. |
| `groups.alternating.three_card` | `lit.cardinals`, `meth.cardinality`, `obj.subgroups.alternating` | text match |
| `groups.abelian.cyclic_three` | `cat.groups`, `obj.groups.cyclic`, `prop.is_abelian` | text match |
| `groups.abelian.symmetric_three` | `cat.groups`, `mor.sets.equality`, `obj.groups.symmetric`, `obj.sets.truth_values`, `prop.is_abelian` | text match |
| `presentations.f9.forward_generator` | `cmp.f9.translation`, `fun.commutative_rings.ring`, `mor.sets.equality`, `num.rings`, `obj.commutative_rings.f9_x`, `obj.commutative_rings.f9_y`, `obj.sets.f9_x`, `obj.sets.f9_y`, `op.rings.add` | `F9translation` is `cmp.f9.translation`, as in RX-07 (milestones.md). |
| `presentations.f9.inverse_generator` | `cmp.f9.translation`, `fun.commutative_rings.ring`, `mor.sets.equality`, `num.rings`, `obj.commutative_rings.f9_x`, `obj.commutative_rings.f9_y`, `obj.sets.f9_x`, `obj.sets.f9_y`, `op.rings.add`, `op.rings.neg` | As the forward generator. |
| `presentations.f9.forward_constant` | `cmp.f9.translation`, `fun.commutative_rings.ring`, `mor.sets.equality`, `mor.sets.f9_x_constants`, `mor.sets.f9_y_constants`, `num.rings`, `obj.commutative_rings.f9_x`, `obj.commutative_rings.f9_y` | As the forward generator. |
| `presentations.f9.inverse_constant` | `cmp.f9.translation`, `fun.commutative_rings.ring`, `mor.sets.equality`, `mor.sets.f9_x_constants`, `mor.sets.f9_y_constants`, `num.rings`, `obj.commutative_rings.f9_x`, `obj.commutative_rings.f9_y` | As the forward generator. |
| `formed.card.hyperbolic_fixed` | `lit.cardinals`, `meth.cardinality`, `obj.bilin_module.bilinear_form`, `obj.modules.regular`, `obj.sets.bilinear_maps`, `obj.sets.integers`, `obj.sets.vectors`, `op.rings.add`, `op.rings.mul` | text match |
| `formed.card.hyperbolic_variable` | `lit.cardinals`, `meth.cardinality`, `obj.bil_wform.formed`, `obj.modules.regular`, `obj.sets.bilinear_maps`, `obj.sets.integers`, `obj.sets.vectors`, `op.rings.add`, `op.rings.mul` | text match |
| `formed.card.zero_rank_zero` | `lit.cardinals`, `meth.cardinality`, `num.rings`, `obj.bilin_module.bilinear_form`, `obj.modules.regular`, `obj.sets.bilinear_maps`, `obj.sets.integers`, `obj.sets.vectors` | text match |
| `formed.pairing.hyperbolic` | `mor.sets.equality`, `mor.sets.formed_pairing`, `num.rings`, `obj.bil_wform.formed`, `obj.modules.regular`, `obj.rings.integers`, `obj.sets.bilinear_maps`, `obj.sets.integers`, `obj.sets.vectors`, `op.rings.add`, `op.rings.mul`, `op.rings.neg` | text match |
| `formed.pairing.scaled_hyperbolic` | `mor.sets.equality`, `mor.sets.formed_pairing`, `num.rings`, `obj.bil_wform.formed`, `obj.modules.regular`, `obj.rings.integers`, `obj.sets.bilinear_maps`, `obj.sets.integers`, `obj.sets.vectors`, `op.rings.add`, `op.rings.mul`, `op.rings.neg` | text match |

## Findings

1. Most lines of `SPEC.md` have a statement in the permanent workload files: 92 of the 157 computations are carried in full. The permanent files restate the spike's sections with new statements around them (the prime factors and multiplicities of 360, the matrix trace and charpoly, the lattices).
2. The permanent files carry some spike computations only by a typing judgement or by a changed input. `calculus.taylor_exp` and `calculus.taylor_sin` assert only $T_f \in \mathbb{R}[[t]]$; the Taylor coefficients and both truncations of `SPEC.md` have no statement (L07, L09, E10). `differentials.cas` binds $F$ as the literal $x^3 + \tfrac{1}{2}x^2 + x$, so the selection of the unique member of $F_s$ (User Story 2.1) has no statement (I06). `subspaces.kernel` uses a matrix in place of the map $\varphi$ (W04). `composed.root_sum` and `composed.root_product` sum over the roots of a polynomial in place of the solution set $\{a \in \mathbb{C} \mid r(a) = 0\}$ (K03, K04).
3. Several spike computations need a catalogue row that the catalogue does not have: the approximation of a real number, the factorization and primality of an integer, the root multiset of a polynomial, the enumeration of a denumerable set in the adopted order, the truncation of a power series, cardinal exponentiation, a linear map given by a formula, and $d/dx$ as a linear map.
4. The enumeration of $\mathbb{Z}$ and $\mathbb{Q}$ in the adopted `Denumerable.ofNat` order (N25) is a V1 requirement of User Story 4.4 and FR-034, and no workload statement asks for it.
5. Three lines of `SPEC.md` §Ellipses were refused by the spike (E06 to E08): the polynomial ring in ten indeterminates, its membership in $\mathbf{Alg}_{\mathbb{C}}$ and its Krull dimension. The workloads carry them, so they are V1 computations although the spike did not compute them.
