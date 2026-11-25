# Rows audit C: "Meaning or route" rows, reader forms, state notes, removal table

Snapshot. Kernel source: branch `integration/kernel-v1-20261106` at tip `fc7fdf8` (2026-11-25), committed content only, read with `git show` and `git grep`. Rows: working copy of `specs/001-categorical-research-language/tasks.md` on `main` (it has uncommitted edits and its line numbers moved during this audit). No build and no test was run. A verdict is a reading of the source.

Paths are relative to the repository. `CasCompiler/` is omitted from a path when the file is in that directory.

## Counts

| Verdict | "Meaning or route" rows (19) | "Unreached code" T030 row (1) |
| --- | --- | --- |
| HOLDS | 1 | 0 |
| MOVED | 9 | 0 |
| CHANGED | 6 | 1 |
| REPAIRED | 3 | 0 |
| NOT DETERMINED | 0 | 0 |

## "Meaning or route selected by something other than the formal rule" rows

| # | Row (task; first words of location) | Verdict | Current location | Evidence (quoted line) | Required mechanism still right? |
| --- | --- | --- | --- | --- | --- |
| 1 | T061; `SourceMethod.lean:23-24` | REPAIRED (reader) | `RoutedMethodReturn.lean:29-36`, `:191-204`; `RoutedMethodFamily.lean:270-288` | `let rows := state.lifts.filter (fun row => row.kind == .subobjects && row.edge == edge)` (`RoutedMethodReturn.lean:33`); `families := families.push (← RoutedMethodFamily.forRouteWithReturns route entry rows)` (`RoutedMethodFamily.lean:273`) | Yes, and it is implemented. The rejection stays only when a route edge has no `.subobjects` lift row (`RoutedMethodFamily.lean:288`). The source must be the registered arrow construct and the result is the subobjects construct, both found by semantics name (row 12). NOT CHECKED: how the lowerer and the runtime execute the return (`family.returns` is read outside the compiler only at `CasRuntime/Observation.lean:112`). |
| 2 | T056; `SourceMethod.lean:70-71` … | MOVED | See replacement | `\| throwUnsupportedSource "method inheritance requires its supplied uniform comparison"` (`RoutedMethodFamily.lean:265`) | Yes. |
| 3 | T061, T075; `SourceMethod.lean:45-57` | MOVED | `SourceMethod.lean:16-28`; `RoutedMethodFamily.lean:119-123` | `mkLambdaFVars #[receiver] (← functorObject complete input target)` (`RoutedMethodFamily.lean:123`) | Yes. |
| 4 | T055; `SourceCarrier.lean:200-207` | CHANGED | Consumers: `SourceMemberChoice.lean:156-173`; `SourceMethod.lean:118-122`, `:213-217`; `ReadMember.lean:82-87`; `SourceMember.lean:101-105`; `PropertyFamily.lean:142`; `RoutedMethodFamily.lean:319`; `SourceCarrier.lean:200-207`. Non-consumers: `SourceOperation.lean` (whole file), `SourceNumeral.lean` (whole file), `SourceCarrier.lean:145-147` | `let some route := routes[0]?` (`SourceCarrier.lean:147`, in `sourceCarrier`, after `sourceRouteAgreements`) | Yes. The defect class stays for element operations, numerals and carriers. Methods, properties, member families, the competition of member kinds, named views and division now consume the preference. |
| 5 | T055, T056, T060; `Resolve.lean`, `Equality.lean` | CHANGED | `ReadCellRules.lean:27-35`; `SourceCell.lean:43-226`; `SourceCarrier.lean:68-103`; `FamilyConversion.lean:15-32`; `CasCompiler.lean:9-10` | `unless ← isDefEq (← inferType first) (← inferType other) <&&> isDefEq first other do` (`SourceCarrier.lean:81`) | Partly. `component(…)` and `inverse_component(…)` now read, through the new `SourceCell.lean`, not through `Resolve.lean`. `Resolve.lean` and `Equality.lean` are imported only by the aggregate `CasCompiler.lean` and by test modules. No agreement gate reads `state.cells`: agreement is definitional equality or a supplied equality proof. |
| 6 | T055; `ReadMember.lean:42-66` | REPAIRED | `ReadMember.lean:147-187` (collection), `:54-118` (completion, preference, agreement or ambiguity) | `"several declared member readings accept this complete selected receiver"` (`ReadMember.lean:117`) | Implemented. Note: properties compete only when the call has no arguments (`:177`). |
| 7 | T030, T055; `ReadOperation.lean:136-152` | REPAIRED | `ReadOperation.lean:156-213`; `SourceOperation.lean:175-232` | `"juxtaposition has several declared readings of its original operands"` (`ReadOperation.lean:213`) | Implemented. Note: a trial that returns an applicability error is dropped (`:179`, `:186`); an exception of a trial propagates (`:193-195`). |
| 8 | T059; `SourceAdmission.lean:291-306` | MOVED | `SourceAdmission.lean:387-405`; `ReadOperation.lean:58-76` | `\| _ => return distinct[0]?` (`SourceAdmission.lean:405`); `let mut domain := hints[0]?` (`ReadOperation.lean:61`) | Yes. |
| 9 | T048; `SourceLimit.lean:95-135` | CHANGED | `SourceLimit.lean:245-292`, `:335-336`; `CreationFamily.lean:195-207` | `let #[(lift, target, row)] := candidates` (`SourceLimit.lean:261`); `if let some created ← sourceCreatedLimit? state shape selected maps then return some created` (`:336`, under `if candidates.isEmpty`) | Implemented: every lift and row pair, one or ambiguity, any shape, the diagram constructor from `entry.standardization`. One part of the old text stays: the created reading is formed only when no row of the maps' own category accepts. |
| 10 | T048; `SourceLimit.lean:39-45` | MOVED | `SourceLimit.lean:67-73`, `:91`, `:360-424` | `else pure (← sourceCarrier left, ← sourceCarrier right)` (`:72`); `let some index := alternatives[ordinal]?` (`:422`) | Yes. `constructionCases` (`:360-396`) now also enumerates constructors with fields and a `Discrete` index. |
| 11 | T035, T036, T075; `ReadNamed.lean`, `ReadRingNotation.lean` … | HOLDS | `Vec` `ReadNamed.lean:236`; `Poly`, `MvPoly`, `PowerSeries`, `coefficient`, `∫` `ReadRingNotation.lean:50`, `:57`, `:59`, `:33`, `:41`; `Units` `ReadSubsetNotation.lean:50`; `𝒫`, `sqrt`, `derivative` `ReadPowerRules.lean:43`, `:49`, `:41`, `:62`; `abs`, `cardinality` `ReadMemberRules.lean:32`, `:35`; `image` `ReadMember.lean:162`; `/` `SourceDivision.lean:29`; `leg` `ReadProjection.lean:25`; `lim` `ReadBinderNotation.lean:35` | `registered (mkIdentFrom source `Poly) #[⟨source.raw[0]⟩]` (`ReadRingNotation.lean:50`) | Yes. More literals of the same kind: `𝒫_fin` (`ReadSubsetNotation.lean:52`), `∞` (`ReadRingNotation.lean:39`), `d` (`ReadNameRules.lean:52`, `ReadPowerRules.lean:59`). `lim`, the definite `∫`, `∑` and `∏` are matched against `BinderEntry.token` (`SourceAdmission.lean:211`). |
| 12 | T061; `SourceMethod.lean:49` | CHANGED | `SourceMethod.lean:20`; `SourceConstruction.lean:34-35`; `RoutedMethodReturn.lean:126-129`, `:172`; `SourceSubobject.lean:25`, `:46`; `PublishedSource.lean:222-223`; `CasRuntime/RoutedMethod.lean:17-18`, `:290-293` | `unless constructor.semantics == ``CasCatalogue.Constructors.subobjects do return none` (`SourceSubobject.lean:46`) | The class stays and is wider: three constructors (arrow, core, subobjects). T134 names arrow and core only. |
| 13 | T036; `SourceRing.lean:217` | MOVED | `SourceRing.lean:219`, `:264-267`, `:291` | `let own ← mkAppM ``CategoryTheory.Under.mk #[← mkAppM ``CategoryTheory.CategoryStruct.id #[ring]]` (`:267`) | Yes. |
| 14 | T035; `SourceSubset.lean:90-93` | MOVED | `SourceSubset.lean:97-104`; `Lower.lean:2048-2050` | `unless row.type == ``Finset do` (`SourceSubset.lean:97`); `if name == ``List.toFinset then` (`Lower.lean:2048`) | Yes. |
| 15 | T034; `SourceNumeral.lean:196-200` | MOVED | `SourceNumeral.lean:367-369` | `if expected.headBeta.isConstOf ``Nat then` (`:367`) | Yes. NOT CHECKED: whether the expected type of an element of the registered natural numbers reaches this branch as a bare `Nat` (it depends on the catalogue row). |
| 16 | T035, T048; `SourceTuple.lean:28-88` | MOVED | `SourceTuple.lean:30-99`; `SourcePattern.lean:29-50` | `if type.isAppOfArity ``Prod 2 then pure ``Prod.mk` (`SourceTuple.lean:84`) | Yes. `PSigma` is a further native key (`SourceTuple.lean:86`, `SourcePattern.lean:44`). The limit universal family exists (`LimitUniversalFamily.lean`); tuple and pattern reading do not use it. |
| 17 | T059; `ReadEquationRules.lean:43-59` | MOVED | `ReadEquationRules.lean:39-59`; `ReadDispatch.lean:28-43`; `ReadNamed.lean:143-153` | `left := ⟨← sourcePointValue left.value none, none⟩` (`ReadEquationRules.lean:47`); `if judgement.category.any (·.role == .object) then sourceCarrier judgement` (`ReadDispatch.lean:32`) | Yes. One more case of the same class: a morphism read as its carrier function where a function type is expected (`ReadDispatch.lean:40-43`). |
| 18 | T057; `SourceMethod.lean:128-159` | CHANGED | `SourceMethod.lean:141-176`; `PropertyFamily.lean:69-73`; `SourcePropertyQualification.lean:70-147` | `let proposition ← mkAppM ``CasCatalogue.Classifier.Holds #[classifierValue, image]` (`PropertyFamily.lean:72`); `let some evidence ← synthInstance? normalized` (`SourcePropertyQualification.lean:106`) | Yes. A property name is still `Classifier.Holds`. New: an explicit qualification to a property category forms the refined object, keeps the inclusion (`.classifierForget`) and the `Holds` proof, for a proof-only classifier (`:37-39`). The proof is Lean instance search after full reduction, not a registered procedure. `refinementRealization` is read only by `CasCatalogue/Registry.lean:203`, `:397`. |
| 19 | T057; `SourceMember.lean:121-155` | CHANGED | `SourceMember.lean:251-304`, `:184-228` | `for choice in choices do` / `for slot in [:count] do` (`:265-266`); `\| _ => throwSemanticAmbiguity s!"several registered morphisms {name} leave this set"` (`:304`) | Partly implemented. "First fit" is gone: every slot and every refinement of the exact base is tried, and several distinct results are ambiguous. The refining object is formed with its registered identification (`memberRefinement?`). The slot is still found by a search with unification; no registration states it. |

### Proposed replacement text (column layout of TASKS)

Rows 1, 6 and 7: remove the row.

```
| T056 | `CasCompiler/RoutedMethodFamily.lean:67-68`, `:240-241`, `:264-265`; `SourceMethod.lean:162-163`; `PropertyFamily.lean:39-40`, `:140-141`; `SourceOperation.lean:116-117`, `:140-141`, `:195-196`; `SourceCarrier.lean:59-60`, `:194-195`; `SourceNumeral.lean:305-306`, `:403-404`; `SourceDivision.lean:40-41`; `CasRuntime/Inspect.lean:294-295` | A route family that is not finite is unsupported for methods, properties, operations, juxtaposition, carriers, views, numerals, division and operation discovery. `CategoricalPointFamily.lean:280` gives "no carrier family" for such a family with no error. | The supplied uniform comparison of C6. For the cycle of sets and their subobjects it is the comparison of T138. |
| T061, T075 | `CasCompiler/SourceMethod.lean:16-28`; `RoutedMethodFamily.lean:119-123` | A morphism receiver is wrapped as an object of the registered arrow category, and only the object action of the inherited method is formed. The arrow action `P(F(f))` is not implemented. | `Functor.map` of the composite. |
| T055 | `CasCompiler/SourceOperation.lean:348-498`; `SourceNumeral.lean:365-486`; `SourceCarrier.lean:145-147` | A declared preferred route is consumed for methods, properties, member families, the competition of member kinds, named structural views and division. Element operations, numerals and carriers do not consume it; `sourceCarrier` takes `routes[0]` after the whole-family agreement. | The C6 preference at every competing binding. |
| T055, T056, T060 | `CasCompiler/Resolve.lean`, `Equality.lean`; `SourceCarrier.lean:68-103`; `FamilyConversion.lean:15-32` | `component(…)` and `inverse_component(…)` are read through `SourceCell.lean`. The composition, whiskering, coherence and equality mechanisms of `Resolve.lean` and `Equality.lean` have no caller outside tests. The agreement gates accept definitional equality or a supplied equality proof; a registered comparison cell is never consumed for agreement. | Connect the agreement gate to the registered comparison cells with their transports. Connect or delete the unreached mechanisms. |
| T059 | `CasCompiler/SourceAdmission.lean:387-405`; `ReadOperation.lean:58-76` | With no unique common set, the first operand's set is used. | Ambiguity. |
| T048 | `CasCompiler/SourceLimit.lean:335-336` | A created limit is formed only when no registered presentation of the maps' own category accepts the maps. | State whether the presentation of the own category is the first binding. If it is not, the created reading competes with it. |
| T048 | `CasCompiler/SourceLimit.lean:67-73`, `:91`, `:360-424` | `X × Y` with operands of different categories reads both as carriers. For an index type that is a finite enumeration, `K.leg(j)` selects the `j`-th alternative in Lean declaration order (constructors, then their field choices), which no registration states. | `X × Y` with operands of different categories is ambiguous unless the source writes an explicit view, which then selects the category. `K.leg(j)` uses the registered naming of shape objects (T123). |
| T061 | `CasCompiler/SourceMethod.lean:20`; `SourceConstruction.lean:34-35`; `RoutedMethodReturn.lean:126-129`, `:172`; `SourceSubobject.lean:25`, `:46`; `PublishedSource.lean:222-223`; `CasRuntime/RoutedMethod.lean:17-18`, `:290-293` | Three constructor rows (arrow, core, subobjects) are selected by the name of their semantics declaration. | The registered universal data of the arrow, core and subobjects constructors (T134; its text names arrow and core only). |
| T036 | `CasCompiler/SourceRing.lean:219`, `:264-267`, `:291` | Element application has a case for `Under` and builds the own-ring algebra in the compiler. | The application row's argument object from the registry. |
| T035 | `CasCompiler/SourceSubset.lean:97-104`; `Lower.lean:2048-2050` | One literal type (`Finset`) is read; the lowerer has a case for `List.toFinset`. | `SubsetLiteralEntry.type` used generically. |
| T034 | `CasCompiler/SourceNumeral.lean:367-369` | (defect text unchanged) | (mechanism text unchanged) |
| T035, T048 | `CasCompiler/SourceTuple.lean:30-99`; `SourcePattern.lean:29-50` | Tuples and patterns are keyed on native `Prod`, `Sigma`, `PSigma` and `Fin n → X`; (rest unchanged) | The selected limit's universal map. |
| T059 | `CasCompiler/ReadEquationRules.lean:39-59`; `ReadDispatch.lean:28-43`; `ReadNamed.lean:143-153` | An operand is read differently so that the outer form applies (an atom as a whole subset, an object as its carrier, a morphism as its carrier function, a global element as its point). C6 does not let a surrounding operation change the reading of an argument. | (mechanism text unchanged) |
| T057 | `CasCompiler/SourceMethod.lean:141-176`; `PropertyFamily.lean:69-73`; `SourcePropertyQualification.lean:70-147` | A property name is read as `Classifier.Holds`. An explicit qualification to a property category forms the refined object with its inclusion and its `Holds` proof, for a proof-only classifier; the proof is Lean instance search after full reduction, not a registered procedure. `refinementRealization` is read by the registry export only. | The registered refinement of an object from a proof, and the proof procedure of the property (T135). |
| T057 | `CasCompiler/SourceMember.lean:251-304` | When no morphism leaves the set directly, the selected source object and each registered refinement of its base are tried in every explicit parameter slot by unification; several distinct results are ambiguous. The slot is found by search. | The registration states which parameter the refining object fills. |
```

## Source forms of `CasCompiler/Syntax.lean` and their reader rule

Verdict for the "Unreached code" T030 row: CHANGED. Five of the eight listed forms read now.

| Form (`Syntax.lean` line) | Reader rule at the tip |
| --- | --- |
| `component(…)` (`:140`) | Yes: `ReadCellRules.lean:29-31` |
| `inverse_component(…)` (`:142`) | Yes: `ReadCellRules.lean:32-34` |
| `map X along id` without arguments (`:126`) | Yes: `ReadLiftRules.lean:24-27` |
| `map X back along id` (`:127`) | Yes: `ReadLiftRules.lean:28-31` |
| `M⁻¹` (`:176`, no applied arguments) | Yes: `ReadOperationRules.lean:50-51` |
| `binder(…)` (`:148`) | No. `casSelectedBinder` occurs only in `Syntax.lean`. |
| `composite_lift(…)` (`:139`) | No. `casCompositeLift` occurs only in `Syntax.lean`. |
| `map p to S[x]` (`:125`) | No. `casMap` occurs only in `Syntax.lean`. |
| A decimal numeral, `scientific` (`:44`) | No. Not in the TASKS list; it had no rule at `9165255` also. |
| `M⁻¹(v)` (`:176`, applied form) | No rule by reading: the pattern `$operand:cas_term⁻¹` has the optional arguments absent, and no rule tests the kind `casInverse`. This is an inference from quotation matching; nothing was run. |
| `proof(…)` as a term of its own (`:65`) | No rule of its own. It is read as evidence inside `… using (…)`, `lift(…)`, `factor(…)` and `assert … using (…)`. |

Every other `cas_term` form and every `cas_stmt` form of `Syntax.lean` has a rule in the `Read*Rules.lean` and `Read*Notation.lean` files or in `ReadSession.lean:318-354`, `:362-385`. A matrix literal with no expected type ends in the unsupported-source error (`ReadApplicationRules.lean:32`).

Proposed row:

```
| T030 | Source forms declared in `CasCompiler/Syntax.lean` with no reader rule: `binder(…)`, `composite_lift(…)`, `map p to S[x]`, a decimal numeral (`scientific`), `M⁻¹(v)` (the applied form) | Each ends in the unsupported-source error (`ReadApplicationRules.lean:38-39`). Owners by capability: T046 (`composite_lift`), T036 (`map p to S[x]`). |
```

## State notes

### "T030, T031, T035 state at `9165255`"

| Statement | Truth at `fc7fdf8` |
| --- | --- |
| All three stay unchecked. | True in TASKS. |
| `let f(x, y, …) := e` reads. | True: `ReadSession.lean:338-342`. Test file: `SourceLetArgumentsTests.lean`. |
| `a is b` and `p and q` inside a term read. | True: `ReadEquationRules.lean:81-93`. Test file: `SourceEqualityFormTests.lean`. |
| `m(X)` for a registered method or property reads. | True: `ReadNameRules.lean:30-43`. Test file: `SourceMethodCallTests.lean`. |
| `X ⊆ Y` for named sets is a settled typing judgement, also in a conjunction. | True: `ReadSession.lean:158-199`, `:349-353`. Test: `CasRuntime/SessionComputationTests.lean:210-220`. |
| A named map on a product with several arguments reads; a global element is read at its declared source. | True: `ReadApplication.lean:68-81`, `:85-102`. Test file: `SourceProductArgumentTests.lean`. |
| A trial reading keeps an ambiguity that a candidate raises. | The behaviour is stronger now: a trial propagates every exception and drops only an explicit applicability error (`ReadOperation.lean:189-195`, `ReadNamed.lean:168-178`, `ReadMember.lean:63-79`, `SourceAdmission.lean:274-282`). The helper `keepTrialAmbiguity` has no caller; only its definition is left (`CasCatalogue/InterpretationFailure.lean:29`). |
| The forms without a rule are in the "Source forms" row. | The row needs the new list above. |

The commit identifiers of the note were not checked.

### "T027 state at `9165255`"

| Statement | Truth at `fc7fdf8` |
| --- | --- |
| T027 stays unchecked. | True in TASKS. |
| An unknown name is invalid source. | True: `Surface.lean:245-247`, `:286`, `:302` (`throwStratum .invalid` with `unknownSourceNameTag`). |
| A use of a definition that did not read has that definition's outcome. | True: `CasRuntime/Session.lean:104-106`, `:769-778`. |
| A missing runtime value is attributed by the identity of its binding. | True: `CasRuntime/Environment.lean:210-215`; `CasRuntime/Session.lean:252`, `:703-706`, `:779-790`. |
| Open: the rows of "Fallbacks and merged outcomes" and the fault-mode tests. | NOT CHECKED (those rows are outside this audit). Seen while reading `Session.lean`: `Outcome` has the constructors `noImplementation` and `ambiguousRealization`, both with the kind `gap` and with their own value in `Outcome.stratum?` (`:17-38`, `:63-70`); an unsupported source form is `.gap` with no stratum (`:77`); a gap does not fail (`:59-60`). |

## Removal of the old path (T051, T064)

Method: all `import` lines of the committed `.lean` files at the tip (`import`, `public import`, `meta import` counted alike), closed transitively inside the repository. Packages outside the repository (`CasContract`, `LeanCategories`, `Worker`) are not followed.

### Production closures

| Root | `CasCatalogue` modules in the closure |
| --- | --- |
| `CasRuntime.Session` | `Admission`, `Codec`, `Decide`, `EquationData`, `Evaluation`, `GraphData`, `InterpretationFailure`, `Registry`, `Resolve` |
| `CasDsl` (through the aggregate `CasCatalogue.lean`) | The nine above, and `Acceptance`, `AcceptanceSyntax`, `CellCall`, `CellSyntax`, `NotebookSession`, `QuestionIdentity`, `ResolveSyntax`, `Semantic`, `TestSuite`, `Trace` |
| In neither closure | `Realize`, `ElementData`, `ComputationalData`, `ConstructionData`, `LiftedSubobjectData`, `FunctorActionData`, `StructuredResult`, `Language`, `FileItems` |

How the old modules enter the closure of `CasRuntime.Session`: `CasCatalogue.Admission` is imported by `CasCompiler/SourceMethod.lean:8`, `CategoricalPointFamily.lean:3`, `PublishedPorts.lean:6`, `PublishedSource.lean:20`, `CasRuntime/ManifestAdmission.lean:4`, `Point.lean:8`, `Presentation.lean:5`, `RoutedMethod.lean:7`. `Admission.lean:7` imports `CasCatalogue.Resolve`. `CasCatalogue/Evaluation.lean:7` imports `Codec`; `Codec.lean:8` imports `EquationData`.

### Statements of the section

| Statement of TASKS | Truth at `fc7fdf8` |
| --- | --- |
| `CasCatalogue/TestSuite.lean` imports only `CasRuntime.Session` and `CasCompiler.Parse`. | Changed. It imports `CasRuntime.Session`, `CasRuntime.Inspect`, `CasCompiler.Parse`, `CasTools.QuestionObservation`, `Worker.Cell`, `Worker.Output` (`:7-18`). It imports no old reader module directly. |
| `#resolve`, `#methods` and `cell%` still answer from `CasCatalogue/Resolve.lean`. | The aggregate still imports `Resolve`, `ResolveSyntax`, `CellSyntax`, `CellCall` (`CasCatalogue.lean:9-10`, `:17-18`). The command bodies were NOT CHECKED. |
| The aggregate no longer imports `Language`, `Realize`, `Codec` or `Admission`. | True for its direct imports. `Codec`, `EquationData`, `Admission` and `Resolve` are in its closure through `CasRuntime.Session`. |
| Each step edits the import list of `CasGates/KernelPurity.lean`. | True: that file imports every module of the six steps. |
| `CasCatalogue/Acceptance.lean` and `AcceptanceSyntax.lean` define commands that nothing uses. | Importers: `CasCatalogue.lean:7-8`, `AcceptanceSyntax.lean:7-8`, `CasGates/KernelPurity.lean:4-5`. Use of the commands NOT CHECKED. |

### Replacement table

| Step | Modules | Production importers | Test modules and probes | Scripts, benchmarks and other files |
| --- | --- | --- | --- | --- |
| 1 | `Realize`, `ElementData` | None. (`Realize.lean:15` imports `ElementData`.) | `CasAcceptance/RegistrationProbes.lean`; `CasCatalogue/ElementDataProbes.lean`, `ProofIdentityProbes.lean`, `QuestionProbes.lean`, `StructuredReconstructionProbes.lean`, `StructuredResultProbes.lean` | `scripts/probes/rx_lift_runtime.lean`, `rx_lift_reader_preflight.lean`; `scripts/ci_kernel_candidate.py`; `scripts/test_question_provenance.py`; `specs/observations/2026-10-03/cached-polynomial-reuse.lean`, `polynomial-reuse.lean` |
| 2 | `ComputationalData`, `ConstructionData`, `LiftedSubobjectData`, `FunctorActionData`, then `StructuredResult` | None. (All are imported by `Realize.lean:11-17`; `StructuredResult` also by `ComputationalData.lean:5`, `LiftedSubobjectData.lean:5`.) | `CasAcceptance/StructuredComparisonProbes.lean`, `ReindexExecutionProbes.lean`; `CasCatalogue/ConstructionDataProbes.lean`, `LiftedSubobjectDataProbes.lean`, `FunctorActionDataProbes.lean` | None found |
| 3 | `Language`, `FileItems` | None. (`Language` is imported by `ElementData.lean:7`, `Realize.lean:7`.) | `CasAcceptance/SelectedStructureProbes.lean`; `CasCatalogue/BinderReaderProbes.lean`, `ConstructionLegReaderProbes.lean`, `ContextualSubsetProbes.lean`, `EvidencePresentationProbes.lean`, `ParameterStructureProbes.lean`, `PresentationReaderProbes.lean`, `SelectedCarrierProbes.lean`, `StructuredParameterProbes.lean` | `benchmarks/semantic_reading.lean`; `scripts/probes/rx_lift_runtime.lean`, `rx_lift_reader_preflight.lean` (`FileItems`) |
| 4 | `Admission`; `Codec`, `EquationData` | `Admission`: the eight kernel modules named above, in the closure of `CasRuntime.Session`. `Codec`: `CasCatalogue/Evaluation.lean:7`. `EquationData`: `Codec.lean:8`. | `CasCatalogue/ImageFormProbes.lean` (`Admission`), `CodecConditionProbes.lean` (`Codec`), `EquationDataProbes.lean` (`EquationData`) | `scripts/ci_kernel_candidate.py` (names `CasCatalogue.Admission`) |
| 5 | `Semantic`, `Trace` | `CasCatalogue.lean:19`, `:22` (closure of `CasDsl`); `Semantic.lean:9` imports `Trace` | `CasAcceptance/AdjunctionProbes.lean`, `ColimitProbes.lean`, `LiftLimitProbes.lean`, `LimitProbes.lean`, `PropsProbes.lean`, `ResolveProbes.lean`; `CasCatalogue/ResolutionFailureProbes.lean` | `custodian/adversarial.sh` (names `CasCatalogue/Semantic`) |
| 6 | `Resolve`, `ResolveSyntax`, `CellSyntax`, `CellCall` | `Resolve`: `CasCatalogue/Admission.lean:7` (closure of `CasRuntime.Session`), `Semantic.lean:7`, `ResolveSyntax.lean:7`, `CellSyntax.lean:7`, `CasCatalogue.lean:17`. The other three: `CasCatalogue.lean:9-10`, `:18`; `CellCall.lean:7` imports `CellSyntax`. | `CasAcceptance/ClosureProbes.lean`, `CohereProbes.lean`, `LiftProbes.lean`, `ResolveProbes.lean` (`ResolveSyntax`), `CellProbes.lean` (`CellCall`); `CasDslTests/Cells.lean` imports only `CasDsl.Notebook` (its use of the commands NOT CHECKED) | `notebooks/demo.ipynb` (`#resolve`, `#methods`, `cell%`) |
| Keep or move out of `CasCatalogue/` | `TestSuite`, `Decide`, `Evaluation`, `InterpretationFailure`, `Registry`, `QuestionIdentity`; also present at the tip: `NotebookSession`, `GraphData` | `GraphData`: `CasRuntime/CallablePacket.lean:4`. `NotebookSession`: `CasCatalogue.lean:21`. `QuestionIdentity`: `CasTools/QuestionObservation.lean:5`, which `TestSuite.lean:10` imports. | — | `benchmarks/question_identity.lean` imports only `CasCatalogue.TestSuite` |

Every module of steps 1 to 6 is also imported by the gate `CasGates/KernelPurity.lean`.

### Differences from the TASKS table

- Step 4: `Admission` is not blocked by `ImageFormProbes` alone. Eight kernel modules import it, so it is in the production closure of `CasRuntime.Session` and of `CasDsl`. `EquationData` is in that closure also, through `Codec`.
- Step 6: `Resolve` is in the production closure of `CasRuntime.Session`, through `Admission.lean:7`. Step 6 therefore depends on the removal of the `Admission` imports of step 4.
- Step 1: `benchmarks/question_identity.lean` imports only `TestSuite`; it is not an importer of `Realize`. Two more importers of `Realize` exist: `specs/observations/2026-10-03/cached-polynomial-reuse.lean` and `polynomial-reuse.lean`.
- The text about `TestSuite.lean` imports is out of date (six imports).
- `NotebookSession` and `GraphData` are not in the "Keep or move" row.

## Files read in full at the tip

`CasCompiler/`: `SourceMethod`, `RoutedMethodFamily`, `RoutedMethodReturn`, `SourceMemberChoice`, `SourceCarrier`, `SourceOperation`, `SourceNumeral`, `SourceDivision`, `SourceAdmission`, `SourceMember`, `SourceLimit`, `SourceRing`, `SourceSubset`, `SourceTuple`, `SourcePattern`, `SourceConstruction`, `SourceSubobject`, `SourceCell`, `SourcePropertyQualification`, `PropertyFamily`, `FamilyConversion`, `Syntax`, `Read`, `ReadExpression`, `ReadContext`, `ReadSession`, `ReadDispatch`, `ReadOperation`, `ReadMember`, `ReadNamed`, `ReadApplication`, `ReadAdmission`, `ReadSubset`, `ReadProjection`, and every `Read*Rules.lean` and `Read*Notation.lean` file. `CasRuntime/Session.lean`. `CasCatalogue/InterpretationFailure.lean`. Aggregates `CasDsl.lean`, `CasCatalogue.lean`, `CasRuntime.lean`, `CasCompiler.lean`, `CasAcceptance.lean`.

Read in part or by search only: `Lower.lean`, `Surface.lean`, `Resolve.lean`, `Equality.lean`, `CreationFamily.lean`, `CategoricalPointFamily.lean`, `PublishedSource.lean`, `SourceRoutes.lean`, `CasRuntime/RoutedMethod.lean`, `CasRuntime/Inspect.lean`. A claim that depends on these files is limited to the quoted lines. `lakefile.lean` was not read.
