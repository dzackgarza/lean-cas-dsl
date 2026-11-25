# Correction rows audit A

Snapshot. Kernel source: branch `integration/kernel-v1-20261106` at `fc7fdf8` (committed content only, read with `git show` and `git grep`). Rows: working copy of `specs/001-categorical-research-language/tasks.md` on `main`, which state the source at `9165255`. Read date: 2026-11-25. Nothing was built or run. No verdict uses a test result; where a test module is named, only its existence was read.

Verdict words: HOLDS, MOVED, CHANGED, REPAIRED, NOT DETERMINED, as the request defines them. A line range that still overlaps the code is HOLDS with the current lines; a range that no longer overlaps is MOVED.

## Files read

Read in full at `fc7fdf8`: `CasRuntime/Session.lean`, `CasRuntime/Literal.lean`, `CasRuntime/KernelState.lean`, `CasRuntime/Realization.lean`, `CasRuntime/Execute.lean`, `CasCatalogue/Decide.lean`, `CasCatalogue/Evaluation.lean`, `CasCatalogue/TestSuite.lean`, `CasCatalogue/InterpretationFailure.lean`, `CasCompiler/SourceNumeral.lean`, `CasCompiler/SourceAdmission.lean`, `CasCompiler/SourceRing.lean`, `CasCompiler/SourceLimit.lean`, `CasCompiler/SourceMethod.lean`, `CasCompiler/ReadGraphRules.lean`, `CasCompiler/ReadSubsetNotation.lean`, `CasCompiler/ReadNumeralRules.lean`, `CasCompiler/ReadDispatch.lean`, `CasCompiler/ReadNamed.lean`, `CasCompiler/Syntax.lean`.

Read in part (line ranges): `CasCompiler/Lower.lean` 195-300, 380-560, 700-965, 1150-1330, 1955-2130; `CasCompiler/Layout.lean` 60-185, 540-575; `CasRuntime/Environment.lean` 100-125, 205-217, 770-830, 985-1050, 1115-1145; `CasRuntime/RoutedMethod.lean` 245-330, 385-440, 496-715; `CasRuntime/Point.lean` 96-200; `CasCompiler/SourcePropertyQualification.lean` 1-125; `CasCompiler/Surface.lean` 160-215, 535-556; `CasCompiler/SourceTypeOrigin.lean` 355-410; `CasCompiler/ReadMember.lean` 30-140, 185-210; `CasCompiler/CategoricalPointFamily.lean` 262-300; `CasCompiler/SourceTuple.lean` 20-70; `CasRuntime/SessionEndpointTests.lean` 8-69; `CasRuntime/ResultCodec.lean` 184-222; `CasRuntime/NativeMapEndpoints.lean` 1-70; `benchmarks/question_identity.lean` 1-30. Every other file was seen only through `git grep` hit lines.

Also read: Lean 4.33.0 `src/lean/Lean/Meta/WHNF.lean` 640-720 (the toolchain that the branch pins), for the behaviour of `whnfCore` with `iota := false`. Old revision `9165255`: `Lower.lean` 300-320, 385-402, 498-560; `Realization.lean` 153-160, 194-210, 240-256; `KernelState.lean` 34-44; `Environment.lean` 105-124; `Execute.lean` 36-58; the five `keepTrialAmbiguity` sites.

## Counts

| Verdict | Rows |
| --- | --- |
| HOLDS | 8 |
| MOVED | 6 |
| CHANGED | 3 |
| REPAIRED | 4 |
| NOT DETERMINED | 1 |
| Total | 22 |

## Kernel computation (C22)

| Row | Verdict | Current location | Evidence |
| --- | --- | --- | --- |
| T033, `Lower.lean:312-314` (`whnfCore` before the eliminator guards) | REPAIRED | `CasCompiler/Lower.lean:895-902`; guards at `:2096-2111` and `:1206-1214` | `{ config with zeta := false, zetaDelta := false, iota := false, proj := .yes })` (`:899`). Lean 4.33.0 `WHNF.lean:685`: `unless cfg.iota do return e` stands before the matcher, recursor, quotient and auxiliary-definition steps. The reduction that remains is beta and projection of a constructor application. The test module of the required mechanism exists: `CasRuntime/UnpublishedOperationTests.lean:24-39` (`Nat.gcd 84 30` through `#cas`). |
| T033, `Lower.lean:552-555`, `:520-523` (every constant with a definition is unfolded) | CHANGED | `CasCompiler/Lower.lean:2105-2111` (repaired part); `:846-857`, `CasCompiler/Layout.lean:137-142` (remaining part) | Repaired: `throwStratum .noImplementation m!"{name} has no published operation"` (`:2111`); the `unfoldProjInst?` branch is gone (`:2070-2076`). Remaining: `if let some expanded ← unfoldSourceApplication? parent then` (`:855`) opens one unregistered definition under a projection when its body is the expected constructor; `inputProjectionHead` opens every definition at a head: `let some (.defnInfo declaration) := (← getEnv).find? name` (`Layout.lean:140`), used at `Lower.lean:1157` and `:1198`. Neither authority of the row (`BindingRole.definition`, `CheckedComputationDerivation`) is checked there. The defect class remains in this narrower form. |
| T033, `Lower.lean:393-397` (full `whnf` of a class instance) | REPAIRED | `CasCompiler/Lower.lean:1194-1214` | `let normalizedParent ← frame.context.inputProjectionSource value` (`:1198`), then `projectCore?` (`:1203`). `Layout.lean:94-98`: "Recursors, quotient eliminators, matchers and opaque declarations remain computation boundaries". An eliminator at the head: `throwStratum .noImplementation m!"{declaration} is a match with no published operation"` (`:1208`). No `whnf` of a value remains in `field`; the `whnf` at `:1190` is of the type. |
| T113, `Session.lean:157-186` (`compare`) | MOVED | `CasRuntime/Session.lean:264-298` | `match ← Decide.decideProp (← mkEq first second) with` (`:295`). The packets are read back at `:284-287` (`ScalarLiteral.readAt`, `ScalarLiteral.read`). |
| T113, `Session.lean:117-124`, `Evaluation.lean:81-108` | MOVED | `CasRuntime/Session.lean:193-201`; `CasCatalogue/Evaluation.lean:81-110` | `Evaluation.decideEvaluated proposition` (`Session.lean:201`); `none => mkDecideProof condition` (`Evaluation.lean:100`), after `Codec.conditionProof` (`:97`). |
| T021, `Literal.lean:17-28`, `:102-104` | HOLDS | same lines | `let decision ← withTransparency .all <| whnf (← mkDecide condition)` (`:21`). Callers: `Materialize.lean:643` (admission), `Session.lean:286-287`, `ChildCall.lean:57`, `Point.lean:532`. |
| T034, `SourceNumeral.lean:48-56` | HOLDS | `CasCompiler/SourceNumeral.lean:50-59` | `unless (← withAtLeastTransparency .default <| whnf decision).isConstOf ``Bool.true do` (`:57`), then `mkDecideProof proposition` (`:59`). The same function closes an equality obligation by conversion: `isDefEq arguments[1]! arguments[2]!` and `mkEqRefl` (`:52-55`). The explicit `using (proof(…))` form is read at `:75-79`. |
| T035, `ReadGraphRules.lean:67-71` | HOLDS | same lines | `let some proof ← CasCatalogue.Decide.decisionProof obligation` (`:69`). |
| T068, `ReadSubsetNotation.lean:31-41` | HOLDS | `:31-42` | `let difference := second - first` (`:34`); `y = x + difference` (`:35`). |
| T059, `SourceAdmission.lean:64-80`, `:108-109`; `Evaluation.lean:127-170`, `:201-275` | MOVED | `CasCompiler/SourceAdmission.lean:77-96`, `:149-153`; `CasCatalogue/Evaluation.lean:127-170`, `:201-275` (same) | `let presented ← Evaluation.evidencePresentation (← semanticState) closed` (`SourceAdmission.lean:85`); `else Evaluation.normalizedValue (← zetaReduce (← instantiateMVars read))` (`:153`); `else withTransparency .all <| whnf e` (`Evaluation.lean:231`); `plumbingRoots` (`:127-129`). |

### Required mechanism, C22 rows

- Row 1: the mechanism is met. Remove the row.
- Row 2: the mechanism is still right. The row must name the remaining sites. A decision is necessary there: `Functor.comp F G` under `.obj` is an unregistered definition, and the code opens it as "structural code" (`Lower.lean:848-852`). The row as written forbids that; no governing text that I read permits it.
- Row 3: the mechanism is met. Remove the row. The unfolding step of this path is the `Layout.lean:137-142` site of row 2.
- Rows 4 to 10: the mechanisms are still right. Row 6 must name the four callers, because the admission caller is only one of them.

### Proposed replacement rows (TASKS layout)

| Task | Location | Defect | Required mechanism |
| --- | --- | --- | --- |
| T033 | `CasCompiler/Lower.lean:846-857`; `CasCompiler/Layout.lean:137-142` (callers `Lower.lean:1157`, `:1198`) | The parent of a projection is opened by its definition when it is not a registered declaration: one unregistered definition whose body is the expected constructor (`unfoldSourceApplication?`), and every definition at the head in `inputProjectionHead`. The definition is not checked to be a `BindingRole.definition` binding or a `CheckedComputationDerivation` plan. The application tail is repaired: a constant with no published operation ends in no implementation (`Lower.lean:2105-2111`). | Unfold only `BindingRole.definition` bindings and `CheckedComputationDerivation` plans. A class instance is opened to its constructor application and projected; any other unregistered definition under a projection gives the no-implementation outcome that names it. |
| T113 | `CasRuntime/Session.lean:264-298` | `compare` reads both returned packets back into Lean terms (`:284-287`) and decides their equality with `Decide.decideProp` (`:295`). No leaf and no registered procedure takes part. | The equality is a published predicate lowered as a demand, or a proof procedure registered in **M**; with neither, no implementation. |
| T113 | `CasRuntime/Session.lean:193-201`; `CasCatalogue/Evaluation.lean:81-110` | After the registered evaluations, the goal is closed by `Codec.conditionProof` or `mkDecideProof` (`Evaluation.lean:94-101`). A question in which no registered literal form occurs is decided by these alone. `mkDecideProof` evaluates a Mathlib `Decidable` instance by Lean reduction; C22 permits only a procedure registered in **M**. | A registered procedure closes the goal. The registered evaluations never close a goal, so the closing procedure is a missing input upstream. Without it the question is a demand. |
| T021 | `CasRuntime/Literal.lean:17-28`, `:102-104`; callers `Materialize.lean:643`, `Session.lean:286-287`, `ChildCall.lean:57`, `Point.lean:532` | A propositional field of returned data is decided by `whnf` of `decide` at transparency `all`. The field is a mathematical condition on the value (for example primality in a subtype), not layout, scope or owner. | The registered evidence procedure of the type's admission. With none, the returned value is not read back as a Lean term. |
| T034 | `CasCompiler/SourceNumeral.lean:50-59` | A numeral's domain obligation (`k < n`) is decided by Lean reduction of a `Decidable` instance; an equality obligation is closed by conversion and `Eq.refl` (`:52-55`). | The registered evidence procedure of the numeral row (T119 supplies the evidence field upstream). The explicit `using (proof(…))` form stays accepted when the source writes it. |
| T059 | `CasCompiler/SourceAdmission.lean:77-96`, `:149-153`; `CasCatalogue/Evaluation.lean:127-170`, `:201-275` | The goal given to the registered evidence procedure is first reduced in Lean (`whnf` at transparency `all`, and unfolding selected by a hard-coded namespace list). This reduction is a proof step that the kernel wrote. | The registered `ObjectEntry.evidence` stated on the term as read. A presentation step that a procedure needs belongs to that procedure in **M**. |
| T036 | `CasCompiler/SourceRing.lean:67-73` | The index of an indexed generator (`x_i` of `R[x_0, …]`) is admitted by `Decide.decisionProof` of `i < n`, and the proof is put in `Fin.mk`. | The registered evidence procedure of the generator row's index, or the registered naming of the variables. With neither, no reading. |
| T048 | `CasCompiler/SourceLimit.lean:415-420` | For a shape with index `Fin n`, `K.leg(j)` forms `⟨j, _⟩` with `mkDecideProof` of `j < n`. | The registered naming of shape objects (T123) supplies the object of the shape and its evidence. |

## Fallbacks and merged outcomes (C13)

| Row | Verdict | Current location | Evidence |
| --- | --- | --- | --- |
| T027, `Session.lean` (`Outcome.ofException`, `Outcome.fails`) | CHANGED | `CasRuntime/Session.lean:17-85`; `CasCatalogue/TestSuite.lean:53-80`, `:169-171` | `Outcome` now has `noImplementation` and `ambiguousRealization` beside `gap` (`:20-22`), and `Outcome.stratum?` gives each its stratum (`:63-70`). The kind is still merged: `.gap _, .noImplementation _, .ambiguousRealization _ => "gap"` (`:33`). An unread source form: `if CasCatalogue.Exception.isUnsupportedSource error then return .gap message` (`:77`), with no stratum, and `Outcome.fails` is false for it (`:59-60`). The suite report row has `kind` and `detail` only (`TestSuite.lean:53-80`); the stratum reaches only the notebook cell failure (`TestSuite.lean:372`, `NotebookSession.lean:59`) and inspection (`Inspect.lean:269`). `scripts/accept_files.sh:165` fixes the kinds `holds`, `gap`, `unavailable`. `.gap` also holds four computed-question outcomes (`Session.lean:282`, `:291`, `:298`, `:319`). The defect class remains at the driver boundary. |
| T027, `KernelState.lean:39-41`; `Realization.lean:157-158`, `:246`, `:250` | MOVED | `CasRuntime/KernelState.lean:39-41` (same); `CasRuntime/Realization.lean:218-220`, `:371`, `:375` | `none => pure (".", "{}")` (`KernelState.lean:41`); `none => pure ("all", #[])` (`Realization.lean:219`); `(derivations[index]?.getD #[])` (`:371`), `(rows[node.val]?.getD #[])` (`:375`). The absent inputs start at `Session.lean:108-117` (`installedManifest` returns `none` when the default path is absent) and `:129-132`. |
| T027, `Environment.lean:117-121` | MOVED | `CasRuntime/Environment.lean:791-796`, in `checkDependencies` (`:776`) | `throwError "the runtime value has a different retained dependent reference"` (`:796`): no stratum, so `Outcome.ofException` gives `.internal` (`Session.lean:85`). The same form at `:996-1000`, `:1013-1014`, `:1020-1027`, `:1032-1036`, `:1118-1123`, `:1125-1129`, `:1137-1138`. A missing value that has a recorded outcome is attributed to its definition (`Session.lean:703-706`, `:781-790`). |
| T113, T027, `Session.lean:199-205`; `CasCompiler/Syntax.lean` | CHANGED | `CasRuntime/Session.lean:303-324`; `CasRuntime/Literal.lean:140-160` | A registered property reply is `Option Bool`, and `none` is accepted: `.ok none => .gap "the property observation returned no decision"` (`Session.lean:319`). A published predicate reply must still be a Boolean: `other => return .malformed s!"{other.compress}: a predicate requires a Boolean answer"` (`:324`). `CasCompiler/Syntax.lean` (read in full) has no `unknown` form; `truthCase?` reads `True` and `False` only (`Session.lean:328-339`). The unknown answer of a property is merged into the kind `gap`. |
| T010, T022, `Execute.lean:41-55` | MOVED | `CasRuntime/Execute.lean:45-59`; `CasRuntime/Transaction.lean:342` | `.ok (.pending _), .ok .running =>` then `match ← waiter.wait with` (`Execute.lean:53-57`); `if cell.claims.contains occurrence then return .ok .running` (`Transaction.lean:342`). No guard was found (searched `Transaction.lean`, `Occurrence.lean`, `Execute.lean`, `Kernel.lean`, `Demand.lean`, `Scope.lean`, `Invocation.lean` for cycle, reentr, itself, wait on). |
| T030, T031, T034, T048, trial readings (`keepTrialAmbiguity`) | REPAIRED | `ReadNamed.lean:166-187`; `ReadNumeralRules.lean:30-33`; `SourceAdmission.lean:272-289`, `:416-419`; `SourceLimit.lean:329-334` | No trial catches a failure. "Not applicable" is a typed result: `.error _ => pure ()` with `catch error => original.restore; throw error` (`ReadNamed.lean:173-178`); `return (← sourceNumeral? context.categoryOf number expected).isSome` (`ReadNumeralRules.lean:31`); `return (← present row).isSome` (`SourceLimit.lean:333`). `keepTrialAmbiguity` has no caller: only its definition remains (`CasCatalogue/InterpretationFailure.lean:29-31`), and `plan.md:321` still describes it. |

### Required mechanism, C13 rows

- Row 1: still right. The mechanism now has a smaller object: `Outcome` tells the three cases apart; the kind and the report row do not.
- Row 2: still right as written. Consequence to settle in the plan: the kernel checks of Part 1 "use a protocol peer or an empty manifest". After the repair such a check must name an explicit empty manifest; an absent one fails. This is an inference from the text of TASKS, not a reading of the tests.
- Row 3: still right.
- Row 4: still right for predicates and for the source form. The property path needs its own statement: the unknown answer exists and must have an outcome of its own.
- Row 5: still right.
- Row 6: the mechanism is met at the five sites. Remove the row, delete the dead definition, and add the row below.

### Proposed replacement rows (TASKS layout)

| Task | Location | Defect | Required mechanism |
| --- | --- | --- | --- |
| T027 | `CasRuntime/Session.lean:30-38`, `:59-60`, `:74-85`; `CasCatalogue/TestSuite.lean:53-80`, `:169-171`; `scripts/accept_files.sh:165` | `Outcome` separates an unread source form (`gap`, no stratum), no implementation and an ambiguous realization, but `Outcome.kind` gives `gap` for all three, and the report row of the suite has no stratum. An unread source form does not fail; it is kernel work, not a missing leaf. `gap` also holds "no scalar comparison", "not decided in Lean" and "the property returned no decision". | An outcome kind, or a stratum in the report row, that the drivers read: an unread source form is told from a missing implementation and from an ambiguous realization. |
| T027 | `CasRuntime/KernelState.lean:39-41`; `Realization.lean:218-220`, `:371`, `:375`; `Session.lean:108-117`, `:129-132` | An absent manifest becomes `{}` and an absent profile becomes `all`. | Fail on a missing manifest or profile. A check with no leaf names an explicit empty manifest. |
| T027 | `CasRuntime/Environment.lean:791-796` (and `:996-1000`, `:1020-1027`, `:1118-1129`) | A dependent reference that is missing or different raises an error with no stratum, so the statement is reported as `internal`, except when the missing binding has a recorded outcome. | The stratum of the cause: a malformed reply, or no implementation when one constructor binder has several input roles. |
| T113, T027 | `CasRuntime/Session.lean:303-324`; `CasCompiler/Syntax.lean` | A predicate reply must be a Boolean. A property reply may be `none`, and that answer is reported with the kind `gap`. `assert P = unknown` has no source form, although C6 names the `unknown` outcome. | A decision with three values, for predicates and properties, with its own outcome and its source form. |
| T010, T022 | `CasRuntime/Execute.lean:45-59`; `Transaction.lean:342` | A demand for an occurrence that is running waits for its completion, so a demand whose operands reach its own occurrence would wait on itself. Reach from the lowerer is not established. | Refuse such a demand as `unavailable`. |
| T055, T056 | `CasCompiler/CategoricalPointFamily.lean:277-291` (callers `CategoricalPointSource.lean:134`, `SourceLimit.lean:174`, `CasRuntime/Point.lean:160`, `:653`) | New since `9165255`. `carrierFamily?` reads three different results as "no carrier family": a route family that is not finite (`:280`), an unsupported-source failure and a semantic ambiguity of the carrier preparation (`:288-291`). The caller then takes the whole-family form. | The ambiguity is raised. The nonfinite family uses the supplied comparison (T056). Only a category with no route to sets has no carrier family. |

The owner of the last row is my assignment from the task definitions (T055: selection at every competing binding; T056: nonfinite route families). The row is not in TASKS.

## Released contract rules with no implementation

| Row | Verdict | Current location | Evidence |
| --- | --- | --- | --- |
| T061, T026, `SourceMethod.lean:21-43` (one address at the owner) | REPAIRED | `CasRuntime/RoutedMethod.lean:385-430`, `:506-515`, `:613-678`; `CasRuntime/Realization.lean:339-405` | A boundary for each position of the route: `let categories := #[route.source] ++ route.steps.map (·.target)` (`RoutedMethod.lean:396`). Selection over all of them before any prefix runs: `profile.selectMethod manifest route.family.entry.id (route.boundaries.map (·.forms))` (`:509-510`); none and several: `throwStratum .noImplementation` and `throwStratum .ambiguousRealization` (`Realization.lean:389-390`). The request: `let edges := (route.family.route.refs.extract offset count).push (.functor route.family.functor.id)` (`:622`), one descriptor for each (`:669-672`). `SourceMethod.lean:21-43` now holds `methodReceiver` and `sourceMethodChoices`, which form the method through `RoutedMethodFamily`. Limit: `CasContract/Port.lean:205-222` of the contract package and `CasCompiler/RoutedMethodFamily.lean` were not read; the verdict is against the row's Required mechanism. |
| T042, T061, `Demand.lean:104-106`; consumer `SessionEndpointTests.lean:57` | NOT DETERMINED (location MOVED) | `CasRuntime/Point.lean:100-151`, `:668`; `CasRuntime/ResultCodec.lean:191-200`; consumer `CasRuntime/SessionEndpointTests.lean:56-67` | `Demand.lean` has no map-action code now (one hit for endpoint, image, map: `:153`). The request is the categorical point invocation: `let source ← categoricalInput kernel request context graph nativeSource supplied.source` (`Point.lean:127`), with `nativeSource`, `nativeTarget` the ends of the family's arrow (`:124`). The consumer still observes an end that is a descriptor of the source arrow: `unless slot.binding.value == coneValue.value do` (`SessionEndpointTests.lean:66`). Not read: whether `supplied.source` and `supplied.target` are computed object images (`CategoricalPointFamily.request?`, `CategoricalPointSource.lean`), and where the reply is admitted (`PreparedMapResult.forSource`). Those three reads decide the row. |

Required mechanism: row 1 is met by the code that was read; remove the row after a reading of the contract text. Row 2: the mechanism stays; only the location is known to be stale.

Proposed replacement for row 2, location only:

| Task | Location | Missing rule | Required mechanism |
| --- | --- | --- | --- |
| T042, T061 | `CasRuntime/Point.lean:100-151`, `:668`; consumer `CasRuntime/SessionEndpointTests.lean:56-67` | The request of a functor's map action carries the source arrow and its source endpoints. The contract (`api/manifest.md:168-169` of the contract package) requires both already computed image endpoints. Not confirmed at `fc7fdf8`: the request has `source` and `target` inputs at the ends of the family's arrow; their producer was not read. | The two object images are computed first and go in the request. The reply is admitted at those images. |

## Acceptance drivers that name absent files

| Row | Verdict | Current location | Evidence |
| --- | --- | --- | --- |
| T004, T029, T040, `scripts/ci_kernel_candidate.py:468` | HOLDS | same line | `['cas-registry-export', 'cas-axiom-audit', 'cas-harness', 'cas-question-export']]` (`:468`). `lakefile.lean` defines `cas-registry-export` (`:94`), `cas-harness` (`:99`), `cas-axiom-audit` (`:105`) only. |
| T063, T071, `scripts/ci_kernel_candidate.py:1036-1039` | HOLDS | `:1035-1038` | `source = root / 'CasAcceptance/Kernel' / (module + '.lean')` (`:1038`). `git ls-tree` of `CasAcceptance/Kernel` at `fc7fdf8` lists no file. The claim about `origin/work/kernel-v1-20261023` was not checked. |
| T103, `benchmarks/question_identity.lean:16-18` | HOLDS | same lines | `let mut scope : CasCatalogue.Language.Scope := {}` (`:16`); `for item in CasCatalogue.Language.items text do` (`:18`); the only imports are `CasCatalogue.TestSuite` (`:7-8`). `TestSuite.lean:7-18` imports no `Language`, `FileItems` or `Realize`; `items` is in `CasCatalogue/FileItems.lean:14`. |
| T041, `scripts/probes/rx_lift_runtime.lean` | HOLDS | `:3`, `:66`, `:122`, `:131` | `import CasCatalogue.Realize` (`:3`); `Realize.prepare scope statement (some stages)` (`:122`). No `KernelSession` or `CasRuntime` name occurs in the file. |

The States of the four rows are still right. For row 2, write `:1035-1038`.

## Kernel-side decisions that the C22 table does not list

Slice searched: the non-test files of `CasCompiler/` and `CasRuntime/` at `fc7fdf8` (`*Tests.lean` excluded), with `CasCatalogue/Decide.lean`, `Evaluation.lean` and `TestSuite.lean`. Patterns: `mkDecideProof`, `decisionProof`, `decideProp`, `Decide.`, `mkDecide`, `of_decide`, `withTransparency`, `.all`, `Meta.reduce`, `whnfD`, `whnfI`, `evalExpr`, `evalNat`, `native_decide`, `simp`, `norm_num`, `omega`, tactic runners, and the numeral forms `isNatLit?`, `getNat`, `toNat`, `mkNatLit`, `rawNatLit`. Each hit was read at its line; the surrounding function was read where the list below quotes it.

| File:line | What it computes | Owner (by the task definitions in TASKS) |
| --- | --- | --- |
| `CasCompiler/SourceRing.lean:67-73` (known) | `Decide.decisionProof` of `index < bound` for the indexed generator `x_i`; the proof goes in `Fin.mk`. Quote: `let some proof ← CasCatalogue.Decide.decisionProof proposition` (`:71`). | T036 (indeterminates, indexed binders) |
| `CasCompiler/SourceLimit.lean:415-420` (known) | `mkDecideProof` of `ordinal < bound` for `K.leg(j)` at a shape `Fin n`. Quote: `let proof ← try mkDecideProof below` (`:418`). | T048, with T123 (names of shape objects) |
| `CasCompiler/Surface.lean:179-188` (`sourceFiniteIndices`) | Compares the declared arity with the number of pattern components by conversion (`isDefEq arity (mkNatLit count)`, `:180`), then builds each `Fin` index with a decision proof: `mkApp3 (mkConst ``of_decide_eq_true) bound (mkApp2 (mkConst ``Nat.decLt) literal (mkNatLit count)) eagerReflBoolTrue` (`:186-187`). Callers `Surface.lean:207` (`sourceComponentValues`), `SourcePattern.lean:40`. | T031 (destructured binders); the tuple and pattern row of T035, T048 |
| `CasCompiler/SourcePropertyQualification.lean:98-111` | For `X in <property category>`: the class proposition `property X` is reduced with `Meta.reduce` at transparency `all` (`:104-105`) and proved by instance search (`synthInstance? normalized`, `:106`); no instance gives `invalid` (`:107`). A mathematical property of an object is decided by Lean reduction and instance search. | T057, with T135 (proof procedures of the registered properties) |
| `CasCompiler/SourceTypeOrigin.lean:369-385` (`trySourceInstance`) | When instance search fails, each argument of the class goal is reduced with `Meta.reduce` at transparency `all`, types included (`:377-379`), and the search runs again. A value in a class argument is evaluated by Lean. | T030 (reader, selected dictionaries); T059 where the instance is a domain condition |
| `CasCompiler/SourceNumeral.lean:52-55` | An equality obligation of a numeral row is closed by `isDefEq` and `Eq.refl`. It is in the function of the T034 row, outside the lines that the row describes. | T034 |
| `CasCompiler/SourceTuple.lean:35-41` | `whnf expected`, `whnf domain` (default transparency), then the declared `Fin n` arity is compared with the number of components by conversion (`isDefEq index.getAppArgs[0]! (mkNatLit components.size)`, `:40`). An arity that is an expression is evaluated by Lean. | T035 |
| `CasCompiler/SourceRing.lean:85-112` | Host `Nat` arithmetic on the digits of variable names expands `x_0, ..., x_9`: `for middle in [first + 1:last] do` (`:110`), after `(String.ofList digits).toNat!` (`:90`). It is notation expansion of an ellipsis, the class of the T068 row. | T036, with T137 (the meaning of an ellipsis) |
| `CasCompiler/SourceLimit.lean:361` | `withTransparency .all <| whnf indexType`: a type is normalized to find the inductive type of a shape index. It is a type, not a value; it serves the constructor-order selection that the row of T048 in "Meaning or route" already names. | T048 |

Not counted as decisions: conversion checks at transparency `all` that compare types or whole families and produce no value: `LiftFamily.lean:125`, `LimitInterface.lean:61`, `:84`, `:92`, `:99`, `:118`, `Surface.lean:550`, `SourceTypeOrigin.lean:383`, `SourcePropertyQualification.lean:36`, `:44`, `:94`, `SourceSubobject.lean:27`, `Elaborate.lean:266`, `CasRuntime/ResultCodec.lean:218`. For `LiftFamily.lean` and `LimitInterface.lean` only the hit lines were read.

- Searched: the slice and patterns above.
- Found: the nine sites of the table; no `decide` tactic, no `native_decide`, no `simp`, `norm_num` or `omega` call in the slice.
- Conclusion: I believe the list is complete for the named patterns in the slice. It is an inference for decisions made by plain `isDefEq` at default transparency, which the patterns do not find.
- Confidence: Medium.
- Gaps: `isDefEq` on values at default transparency (many sites); `CasCatalogue/Codec.lean` (`conditionProof`), which `Evaluation.lean:97` calls and which was not read; the files seen only by grep.

## Adjacent facts found while reading (not in my tables)

- `CasCompiler/SourcePropertyQualification.lean:112-120` forms a refined object (`FullSubcategory.mk`) for an explicit property qualification and checks its inclusion. The T057 row of "Meaning or route" says that no code applies a refinement. That row needs a reading by its owner.
- `plan.md:321` describes `keepTrialAmbiguity` as the current mechanism.
