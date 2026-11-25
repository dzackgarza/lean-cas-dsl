# Audit B: correction rows against the committed kernel source

## Scope and method

| Item | Value |
| --- | --- |
| Kernel branch | `integration/kernel-v1-20261106` |
| Tip read | `fc7fdf8` (2026-11-25 10:03:31 +0000) |
| Revision that the rows state | `9165255` (2026-11-20), an ancestor of the tip, 111 commits behind |
| Task list read | working tree of `specs/001-categorical-research-language/tasks.md` on `main` (it has uncommitted edits) |
| Source read | committed content only (`git archive` of the tip and of `9165255`) |
| Builds, tests, `lake`, `lean` | none |

A verdict comes from the source text only. No verdict uses a test result.
"Lines" are lines of the file at `fc7fdf8`.

## Counts

| Verdict | Table A | Table B | Total |
| --- | --- | --- | --- |
| HOLDS | 2 | 0 | 2 |
| MOVED | 8 | 0 | 8 |
| CHANGED | 4 | 5 | 9 |
| REPAIRED | 8 | 1 | 9 |
| NOT DETERMINED | 0 | 0 | 0 |
| Total | 22 | 6 | 28 |

## Table A: "Selected data recovered after the fact (C5, C23)"

| # | Row (tasks, first words of location) | Verdict | Current location | Evidence quote |
| --- | --- | --- | --- | --- |
| A1 | T048, T007, `SourceLimit.lean` (three formation functions) | REPAIRED | `Elaborate.lean:52-88` (fields `presentation`, `diagram`, `interface`); `SourceLimit.lean:117-122`, `:229-236`, `:349-355`; `LimitInterface.lean:88-101`, `:146-148` | `let dataConstructor ← row.dataConstructor.mapM (prepareDataConstructor row diagram)` (`LimitInterface.lean:147`) |
| A2 | T048, `SourceLimit.lean:239-258` | REPAIRED | `SourceLimit.lean:433-469` | `let index ← constructionIndex indexType ordinal` (`:446`) |
| A3 | T032, `Lower.lean:253-266`, `:236-241` | CHANGED | `Lower.lean:668-670` (named element); `Lower.lean:1440-1456` (admission) | `let some admitted := value.find? (·.getAppFn.isConstOf declaration)` (`:1453`) |
| A4 | T032, `Lower.lean:267-272` | REPAIRED | `Lower.lean:693-701` | `application (mkAppN (.mdata data native.getAppFn) native.getAppArgs)` (`:700`) |
| A5 | T032, `Lower.lean:69-73`, `:505-511` | REPAIRED | `Lower.lean:187-193`, `:767-772`, `:2051` | `throwError "the registered source declaration {declaration} lost its selected source address"` (`:772`) |
| A6 | T032, `Lower.lean:76-86`, `:399`, `:529` | REPAIRED | `Lower.lean:197-207`, `:268-277`, `:291-357`, `:688-692` | `throwError "the selected descriptor lost its original registered address"` (`:355`) |
| A7 | T032, `Lower.lean:148-162` | CHANGED | `Lower.lean:430-458`, `:462-483`; `CasRuntime/Value.lean:271-282`, `:1164-1183` | `let some value := marks[key]? \| throw "the source lost a retained occurrence mark"` (`Value.lean:281`) |
| A8 | T031, `Lower.lean:277-283` | REPAIRED | `Lower.lean:702-718` | `("args", .arr #[toJson s!"{binding.id.session}:{binding.id.serial}"])` (`:717`) |
| A9 | T059, T075, `SourceOperation.lean:19-79`; `Surface.lean:43-52`, `:80-91` | MOVED | `SourceOperation.lean:22-111`; `Surface.lean:47-56`, `:136-147` | `if let some candidate ← refinementDomain state entry expected then` (`SourceOperation.lean:109`) |
| A10 | T059, T075, `SourceCarrier.lean:268-335` | MOVED | `SourceCarrier.lean:279-349` | `unless ← withoutModifyingState <\| isDefEq carrier.value expected do continue` (`:337`) |
| A11 | T059, `SourceCarrier.lean:168-179` | HOLDS | `SourceCarrier.lean:168-179`; callers `ReadApplication.lean:108`, `SourceDivision.lean:34` | `if ← withoutModifyingState (isDefEq objects type) then found := found.push entry` (`:175`) |
| A12 | T035, T036, T059, `SourceAdmission.lean:22-56` and five more | MOVED | `SourceAdmission.lean:23-72`, `:294-310`; `SourceRing.lean:33-82`, `:165-197`; `SourceSubset.lean:20-42`; `SourceMember.lean:141-180`, `:232-304`, `:311-376` | `unless ← withReducible (isDefEq object type) do return false` (`SourceAdmission.lean:31`) |
| A13 | T059, `SourceAdmission.lean:36-38`, `:209-211` | MOVED | `SourceAdmission.lean:37-39`, `:308-310` | `\| _ => return type` (`:39`); `\| _ => return none` (`:310`) |
| A14 | T036, T057, `ReadNamed.lean:193-214`; `ReadAnnotationRules.lean:82-95` | MOVED | `ReadNamed.lean:238-259`; `ReadAnnotationRules.lean:64-105` | `let rows := state.objects.filter (·.name == derived entry.name)` (`ReadNamed.lean:250`) |
| A15 | T055, `ReadApplication.lean:83-86` | MOVED | `ReadApplication.lean:118-124` | `let head := function.consumeMData.getAppFn.constName?` (`:120`) |
| A16 | T055, `SourceMethod.lean:120-121` and four more | MOVED | `SourceMethod.lean:70-71`; `SourceOperation.lean:487-496`; `SourceCarrier.lean:158-159`, `:216-217`; `SourceNumeral.lean:210`, `:291`; `SourceMemberChoice.lean:182` | `(reprStr (families.map fun family => (family.entry.id, family.route.refs)))) value` (`SourceMethod.lean:71`) |
| A17 | T059, `SourceDivision.lean:78-80` | MOVED | `SourceDivision.lean:86-91` | `entry.admission.isSome && units.getAppFn.constName? == some entry.declaration` (`:90`) |
| A18 | T043, T044, `SourceLift.lean:106-153` | HOLDS | `SourceLift.lean:106-153` (the file has no change since `9165255`) | `let some value := (← id.getDecl).value?` (`:139`), then "the selected lift application has no definition" (`:140`) |
| A19 | T009, T042, `Environment.lean:111-121`, `:185-188` | CHANGED | `Environment.lean:272-405`, `:776-1155`, `:1353-1431` | `return ← isDefEq original specified` (`:1431`) |
| A20 | T038, T042, `Session.lean:275`, `:301-310`; `Invocation.lean:62`, `:71-92` | CHANGED | `Session.lean:605`, `:641-645`; `Invocation.lean:252-273` | `let observed := if computed then session.observed.insert entry.id else session.observed` (`Session.lean:645`) |
| A21 | T038, `Session.lean:288-297`; `Lower.lean:277-278` | REPAIRED | `Session.lean:100-103`, `:207-215`, `:616-617`, `:626-634`, `:656-657`, `:669-670` | `return some (outcome.withDetail s!"{name} has no computed value: {outcome.detail}")` (`:214`) |
| A22 | T038, T085, `TestSuite.lean:216-222`, `:123-131` | REPAIRED | `TestSuite.lean:357-375`; `Session.lean:145-155`; `NotebookSession.lean:25-39` | `liftCoreM (KernelSession.install run.session)` (`TestSuite.lean:375`) |

### Notes for Table A

**A1.** The three formation functions (`sourceBinaryLimit`, `sourceCreatedLimit?`, `sourceNamedLimit`) fill `presentation`, `diagram` and `interface`. `interface.dataConstructor` and `interface.standardization` have consumers: `CasCompiler/ConstructorPorts.lean:36`, `:43`, `CreationFamily.lean:199`, `:247`, `LimitFamily.lean:52-55`, `:114`. The note at TASKS line 406, item (4), says that rows T048, T007 are not confirmed. The source confirms the repair.

**A2.** The function contains no `isDefEq` on a candidate. The presentation comes from the application that formation retained (`sourceApplication? selection.declaration cone`, `:438`). The apex end is set to the receiver by position (`:456`). Two facts remain and belong to other rows: the function reads the presentation from the term envelope and not from `selection.presentation` (T117); the shape object is the ordinal-th constructor of the index type (`constructionIndex`, `:403-424`; T123).

**A3.** A named element now reads the application that the reader retained (`sourceApplication?`, `SourceReference.lean:41-51`; no subterm search). In `admission` the first-subterm search remains. It is a check: the found application must have exactly the parameters of the point family (`:1455`). The element comes from the retained position (`:1449`). Defect class: absent for a named element; present as a check in `admission`. The required mechanism is still correct for `admission`.

**A4, A5, A6.** With no mark, a registered declaration is an error (`:767-772`). `computationRefs` and `descriptorIds` are deleted. `isRegisteredComputation` and `isRegisteredDescriptor` return membership only. Remainder for A6: the membership scan of ten tables still permits the unfolding of an unmarked registered constant below a projection (`Lower.lean:1215-1221`) and of a declared endpoint (`:1081`). It selects no address.

**A7.** A mark with no value is now an error (`Value.lean:274`, `:281`, `:1176-1178`; called at `Lower.lean:475-478`). A binding with no retained value and with a definition contributes the references of its definition (`Lower.lean:444-447`). A binding with neither a value nor a definition, and a variable outside the binding context, still return no reference and no error (`:448`, `:449`). That case is a formal parameter. The owner of the row decides if this remainder is a defect.

**A9.** The owner of an element operand still comes from its native type: head match (`Surface.lean:53`), scan of `ObjectEntry.refines` (`SourceOperation.lean:107-109`), `isDefEq` (`:44-46`). New since `9165255`: named arguments of the base are retained (`alignSourceArguments?`, `:38-41`) and the comparison has a reference mark (`:59-60`). `SourceCategoryRole` has only `object` and `morphism` (`Elaborate.lean:29-32`), so a judgement cannot state an element owner. NOT CHECKED: each element rule for `category := none`.

**A10.** New since `9165255`: a retained object origin is read before the shape of the hint (`sourceObjectOrigin?`, `:306-310`). The shape fallback (`elementTypeOrigin`, `:279-290`, `:304`) and the acceptance by definitional equality (`:337`, `:342-343`) remain.

**A12.** `sourceAdmissionDomain?` now reads a retained object reference first (`SourceAdmission.lean:46-51`), then the head-matched registered domain (`:55-59`), then the scan (`:60-72`). The fallback of `sourceMorphismFrom?` now uses `memberSourceObjects` (`SourceMember.lean:141-180`), which reads a retained origin first; the old search `type.find? (·.isConstOf base.declaration)` is deleted. The scans by native type remain in every listed function.

**A14.** `relatedObject` (`X ∖ 0`, `Spec A`) selects by the composed name and returns the carrier selection (`ReadNamed.lean:258-259`). Only the rule `X in C/Y` returns carrier `none` (`ReadAnnotationRules.lean:100`). This was also true at `9165255`.

**A16.** This row states the same fact as row "T117, T055" of "Occurrences and selections carried in term metadata", which already has the current locations. Readers of the strings are tests only: `SourceCarrierTests.lean:70`, `:261`; `SourceMemberCompetitionTests.lean:193-194`; `SourceMethodPreferenceTests.lean:26-27`; `CasRuntime/SessionPreferenceTests.lean:51`. NOT CHECKED: the content of `SourceNumeral.lean` and `SourceMemberChoice.lean` (lines found by search).

**A19.** Two mechanisms:
- `checkDependencies` (`:776-1155`) no longer compares a binding with a field by `isDefEq`. It aligns the type family of the field with the expected type by expression shape (`dependencyTerms`, `:272-405`), resolves the aligned term to a `(BindingId, projection path)` (`dependencyReference`, `:236-250`, used at `:1002`) and compares the supplied binding of that reference (`:1017-1027`). A definitional-equality step remains for closed fragments and supplies no pairing (`:389-393`).
- `retainsSourceReference` (`:1353-1431`) accepts an operand that is not a mark, a variable or a projection when its role source is definitionally equal to the specified source (`:1429-1431`).
Defect class: present at `:1429-1431`; present in another form in `dependencyTerms` (the pairing of slot and term is recovered from the shape of two types). I read lines 93-1160 and 1244-1470 of this file. Lines 1-92, 1161-1243 and 1471-1764 are NOT CHECKED.

**A20.** Every definition with a computed value keeps the value (`Session.lean:642-644`); the counter no longer decides retention. The counter still decides `observed` (`:605`, `:641`, `:645`), which decides if a later question is computed or discharged in Lean (`:184-201`). `invokeExport` does not move the counter (`Invocation.lean:252-273`); the eight other invoke functions do (`:76`, `:105`, `:129`, `:154`, `:177`, `:200`, `:225`, `:247`). Defect class (decision by a dispatch count, not by the producer of the value): present for `observed`.

**A21.** A failed definition is recorded with its outcome by `BindingId`. Each later executable use returns that outcome before lowering. `Lower.lean:707-712` still lowers a `.definition` binding that has no retained value; after the session gate this applies to a definition of `Prop` or `Sort` type or over an unsupplied parameter (`Session.lean:611-615`).

**A22.** `#cas` reads the session from the Environment (`KernelSession.current?`, `TestSuite.lean:361`), forks it or starts one, and installs the session after the statement (`:375`). A suite file is one session (`:279-283`, `:167`). A notebook has one session and forks it for each cell (`NotebookSession.lean:25-39`).

### Replacement rows for Table A (layout of TASKS)

| Task | Location | Defect | Required mechanism |
| --- | --- | --- | --- |
| T032 | `CasCompiler/Lower.lean:1452-1456` | In `admission`, the registered admission application is found as the first subterm of the point family with the declaration at its head. It is used to check the argument telescope. A named element reads the application that the reader retained (`:669`). | The reader passes the admission application itself. |
| T032 | `CasCompiler/Lower.lean:437-449` | `captured` returns no reference and no error for a context binding that has neither a retained value nor a definition (`:448`) and for a variable outside the binding context (`:449`). A mark with no value is an error (`CasRuntime/Value.lean:281`). | Fail on a lost selection. |
| T059, T075 | `CasCompiler/SourceOperation.lean:22-111`; `Surface.lean:47-56`, `:136-147` | For an element operation the registered object and its refined structure are recovered from the operand's native type by head match, a scan of `ObjectEntry.refines` and `isDefEq`. Named arguments of the base are retained. Cause: a judgement has no element owner (`SourceCategoryRole` is `object` or `morphism`). | Keep the element's owner (object, category, carrier selection) in `NativeSourceJudgement`, as `SourceTypeOrigin.annotateSourceType` does for carriers. |
| T059, T075 | `CasCompiler/SourceCarrier.lean:279-349` | An element owner is read from a retained type or object origin when the hint has one. Without one, it is recovered from the shape of the hint type (`:304`) and accepted by definitional equality (`:337`). | As above. |
| T059 | `CasCompiler/SourceCarrier.lean:168-179` (callers `ReadApplication.lean:108`, `SourceDivision.lean:34`) | The category of a parameter is found by a scan of all categories for a matching object type. | The declaration's typed parameter. |
| T035, T036, T059 | `CasCompiler/SourceAdmission.lean:23-72`, `:294-310`; `SourceRing.lean:33-82`, `:165-197`; `SourceSubset.lean:20-42`; `SourceMember.lean:141-180`, `:232-304`, `:311-376` | One family of scans: "the registered object, admission, generator, power object or morphism whose family is this native type". `sourceAdmissionDomain?` and `memberSourceObjects` read a retained reference first and scan when there is none. | The selected object reaches its consumer. |
| T059 | `CasCompiler/SourceAdmission.lean:37-39`, `:308-310` | Several matching registered objects give the same result as none. | Report the ambiguity. |
| T036, T057 | `CasCompiler/ReadNamed.lean:238-259`; `ReadAnnotationRules.lean:64-105` | `X ∖ 0` and `Spec A` select a target by a composed name string (`ReadNamed.lean:250`). `X in C/Y` selects the category by the composed name `C/` (`ReadAnnotationRules.lean:69`) and returns the refined object with carrier `none` (`:100`), so its registered identification is dropped. | `ObjectEntry.notations` for the form, on the registered constructions of T136; `objectCarrierSelection` for the identification. |
| T055 | `CasCompiler/ReadApplication.lean:118-124` | The surface name for the preferred-route lookup is recovered from the head declaration, first hit. | The name that the reader selected. |
| T055 | `CasCompiler/SourceMethod.lean:70-71`; `SourceOperation.lean:487-496`; `SourceCarrier.lean:158-159`, `:216-217`; `SourceNumeral.lean:210`, `:291`; `SourceMemberChoice.lean:182` | Selected routes, refinements and the preferred route are kept as `repr` strings in metadata. Four test files read `carrierRoutes` and `preferredRoute`; no other code reads any of them. Same fact as row "T117, T055" of the metadata table. | Route and preference as retained data that the lowerer consumes. |
| T059 | `CasCompiler/SourceDivision.lean:86-91` | The admitted subobject of a divisor is recognized by head constant. | The division row's typed second factor. |
| T009, T042 | `CasRuntime/Environment.lean:1429-1431`; `:272-405`, `:776-1155` | An operand that is not a marked occurrence, a variable or a projection is accepted when its role source is definitionally equal to the specified source (`:1430-1431`). The dependency check pairs a prefix slot of a field with a context binding by `BindingId` and projection path (`:1002`, `:1017-1027`), after it aligns the type family of the field with the expected type by expression shape (`dependencyTerms`). | The `BindingId` or role identity of the dependency, retained with the field at formation. |
| T038, T042 | `CasRuntime/Session.lean:605`, `:641-645`; `Invocation.lean:252-273` | Every definition with a computed value keeps it (`:642-644`). A dispatch counter still decides if the definition is observed, that is, if a later question about it is computed or discharged in Lean (`:645`, `:184-201`). An export invocation does not move the counter. | Decide the observation by the value's producer. |

Rows A1, A2, A4, A5, A6, A8, A21, A22: remove (the table removes a repaired row). Row A18: no change.

## Table B: "Second interpreter and construction-specific execution (C23)"

| # | Row (tasks, first words of location) | Verdict | Current location | Evidence quote |
| --- | --- | --- | --- | --- |
| B1 | T022, T023, T032, `ChildCall.lean:49-125` | CHANGED | `CasRuntime/ChildCall.lean:36-123`; `CasCompiler/PublishedSource.lean:1443-1537` | `Elab.Term.withSynthesize do PublishedSource.prepare source call` (`ChildCall.lean:122`) |
| B2 | T042, T043, `Demand.lean:86-99`, `:106` | CHANGED | `CasRuntime/Demand.lean:246-269`; `CasCompiler/RecordAction.lean:89-109`, `:133-180` | `let inputs ← kernel.recordInputs evaluateSource request family transaction action` (`Demand.lean:264`) |
| B3 | T043, `ManifestAdmission.lean:26-33` and five more | CHANGED | `SourceLift.lean:172-177`, `:204`; `LiftFamily.lean:15-30`, `:67-103`; `Program.lean:116`; `Lower.lean:606`, `:1675-1692`; `RecordAction.lean:163-180`; `ManifestAdmission.lean:86-88`; `Demand.lean:255-256` | `let address := s!"{family.lift.raw}#{field.projection.getString!}"` (`RecordAction.lean:166`) |
| B4 | T026, `Realization.lean:198-206` | REPAIRED | `CasRuntime/Realization.lean:309-327`; caller `Demand.lean:255-256` | `profile.allowsRegistration target registration).map (index, ·)).flatten` (`Realization.lean:317`) |
| B5 | T026, T032, `Demand.lean:107-124`; `Program.lean:15-43`, `:64-67` | CHANGED | `Demand.lean:161-186`, `:203-208`, `:271-296`; `Program.lean:49-74`, `:112-115`; `Realization.lean:331`, `:354` | `let mut term := plan.betaRev parameters.reverse (preserveMData := true)` (`Demand.lean:285`) |
| B6 | T042, `Demand.lean:69` | CHANGED | `CasCompiler/RecordAction.lean:114-128`, `:167-179` | `for field in layout.fields.extract 0 count do` (`RecordAction.lean:120`) |

### Notes for Table B

**B1.** See "Provider-requested path" below.

**B2.** A registered family now receives the earlier fields that the selected field declares: `SourceLayout.actionInputs` → `nativeInputs` reads `field.precedingDependencies` (`RecordAction.lean:89-99`, `:142-146`), and the runtime evaluates those inputs for every selected registration (`Demand.lean:264-269`). The stated defect is absent. One dependent-record path for every boundary does not exist: `RecordAction.prepare` has a case for a computation reference, `.limitUniversal`, `.creation` and `.lift` (`:142-180`), and `Kernel.reach` sends `.limit`, `.creation`, `.point`, `.objectAction`, `.property`, `.routedMethod`, `.presentation` and `.application` to separate prepared invocations (`Demand.lean:116-245`). Defect class (construction-kind cases in execution): present.

**B3.** Published lift addresses now come from the fields of the record (`LiftFamily.projections`, `LiftFamily.lean:67-81`; `forAddress?`, `:85-103`; `ManifestAdmission.lean:86-88`). The hard-coded names in `ManifestAdmission` are deleted. Remaining: the reader's lift members are the literal names `obj`, `hom`, `forward`, `backward` (`SourceLift.lean:172-177`) and the factor projection (`:204`); `LiftPort` has the two cases `computation` and `factor` (`LiftFamily.lean:15-30`); `ProgramBoundary.lift` (`Program.lean:116`); `liftFamily` in the lowerer (`Lower.lean:606`, `:1675-1692`); the lift case of `RecordAction.prepare` (`:163-180`). `selectLift` is now a registration-only selector with a profile target, used for every family that has no derivation (`Realization.lean:309-327`).

**B4.** `selectLift` takes the profile and a `ProfileTarget` and filters with `allowsRegistration`. The lift caller passes `.lift id` (`Demand.lean:255-256`). `RealizationProfile.prepare` validates a `lift` rule (`Realization.lean:225-236`) and its registrations (`:265-270`).

**B5.** The second sentence of the row is false at the tip. `SourceProgram.forTarget` has the caller `Realization.lean:354`. `SourceProgram.instantiate` (`Program.lean:68-74`) uses `withPrerequisites` and `PrerequisiteSlot` and has the callers `Demand.lean:163`, `:205`, `:272` and `RoutedMethod.lean:699`. `Realization.derivation` carries a `SourceProgram` (`Realization.lean:331`). The first sentence holds in part: the compiler instantiates the plan with the selected prerequisite families; the runtime applies the plan to the marked parameters, projects the field path and applies the arguments, and sends the term to the lowerer (`Demand.lean:271-296`; the same for a point at `:161-186` and an object action at `:203-208`). `ProgramBoundary.target` and `.prerequisite` have a producer in tests only (`OperationalTests.lean:24`, `:41`, `:49`). NOT CHECKED: the body of `RoutedMethod.lean:682-699` (found by search).

**B6.** `Kernel.earlierOutputs` is deleted. Its rule is now `orderedInputs` in the compiler and applies to the lift boundary only: each earlier wire field for a computation port (`RecordAction.lean:168`), each computational field of the lift's computation for the factor port (`:169-179`). A registered family uses `precedingDependencies` (`:89-99`). The source comment gives the released lift packet as the reason ("cas-leaf-contracts api/wire-examples.md, prescribed lifts and separate factor", `:111-113`). NOT CHECKED: that contract. If the contract prescribes the ordered prefix, the required mechanism of this row disagrees with the released contract for a lift, and the row needs a decision.

### Replacement rows for Table B (layout of TASKS)

| Task | Location | Defect | Required mechanism |
| --- | --- | --- | --- |
| T022, T023, T032 | `CasCompiler/PublishedSource.lean:1443-1537` (entry), `:1499-1514` (lift and family addresses), `:190-286` (method); `CasRuntime/ChildCall.lean:36-123` | `Kernel.child` passes its frame to the compiler entry `PublishedSource.prepare`; the runtime builder and `childOperand` are deleted. Remaining: (a) the entry has one application builder for each kind of address, beside the rules of the reader; the reader uses only `namedApplicable` of that module (`ReadNamed.lean:130`). (b) An operation, functor, construction or morphism address is applied at the wire parameters; the reader's `sourceOperation` (owner, routes, family agreement) does not run. (c) A child lift call marks the `LiftFamily` and forms no `CasCompiler.selection` (reader: `SourceLift.lean:102-103`, `:170-171`, `:180`), so the earlier fields that `RecordAction.orderedInputs` requires are demanded again. (d) The C6 gate runs for a method (`:214`); it is not checked for a property. | One producer for each family, used by the reader rule and by the published entry. A child lift call keeps the selection of the lift application that it continues. |
| T042, T043 | `CasCompiler/RecordAction.lean:133-180`; `CasRuntime/Demand.lean:116-269` | A registered family receives its declared earlier fields (`field.precedingDependencies`). `RecordAction.prepare` has one case for each of: computation reference, universal family, creation, lift. `Kernel.reach` has a separate prepared invocation for eight more boundary kinds. | One dependent-record path, driven by `FieldLayout.precedingDependencies`, for every boundary. |
| T043 | `CasCompiler/SourceLift.lean:172-177`, `:204`; `LiftFamily.lean:15-30`; `Program.lean:116`; `Lower.lean:606`, `:1675-1692`; `RecordAction.lean:163-180`; `CasRuntime/Demand.lean:255-256` | The reader's lift members are the literal names `obj`, `hom`, `forward`, `backward` and the factor projection. `LiftPort`, `ProgramBoundary.lift`, the lowerer's `liftFamily` and the lift case of `RecordAction.prepare` are separate from the registered-family path. Published lift addresses come from the record's fields (`LiftFamily.lean:67-103`). | The ordinary dependent-record boundary for the published `MonoLiftComputation`; reader members derived from its record layout. |
| T026, T032 | `CasRuntime/Demand.lean:161-186`, `:203-208`, `:271-296`; `CasRuntime/RoutedMethod.lean:682-699`; `CasCompiler/Program.lean:112-115` | The compiler instantiates the derivation plan (`SourceProgram.instantiate`, `Program.lean:68-74`). The runtime applies the plan to the marked parameters, projects the field path and applies the arguments, in four places. `ProgramBoundary.target` and `.prerequisite` have no producer outside tests. | The compiler forms the applied plan at the retained parameters, path and arguments. Connect or delete the two boundary constructors. |
| T042, T043 | `CasCompiler/RecordAction.lean:114-128`, `:167-179` | For a lift boundary each earlier wire field is an input; a factor takes each computational field of the lift's computation. A registered family uses `field.precedingDependencies`. The source cites the released lift packet as the reason. | `field.precedingDependencies` (data model: per-field dependencies, not a blanket owner). Compare with the released lift packet before the change. |

Row B4: remove.

## Provider-requested path against C23

C23, "Every public request uses the same mathematical preparation boundary": an initial source call, a deferred call and a provider-requested call use the common source-governed operation selection, dependent application and interface preparation; the runtime resolves scoped operands, invokes the prepared computation and retains the result; the runtime does not rebuild the mathematical application; reuse of only the final lowerer is not sufficient.

Files read in full for this section: `CasRuntime/ChildCall.lean` (126 lines), `CasCompiler/PublishedSource.lean` (1540 lines).

### Path

1. A deferred group and a suspension call `kernel.child` (`Invocation.lean:331`, `:305`).
2. `Kernel.child` (`ChildCall.lean:36-123`) opens the scope of the parent request and makes a `PublishedSourceContext` of callbacks.
3. The compiler forms the term: `PublishedSource.prepare source call` (`ChildCall.lean:121-122`; `PublishedSource.lean:1443-1537`).
4. `evaluateSource` lowers and executes the term (`ChildCall.lean:123`). It is `lowerTerm` with the ordinary executor (`Kernel.lean:15-52`), the same function that `Kernel.run` uses for an initial statement (`Kernel.lean:65-69`).

### What the runtime does

The runtime supplies callbacks only (`ChildCall.lean:54-120`): resolution of a scoped reference (`retained`), a scalar literal reader, evaluation and marking of an operand (`bind`, `rebind`), the category inputs of a receiver (`methodParameters`), comparison of a supplied value with a declared input (`checkInput`), form and owner admission (`admitMethod`, `admitProperty`, `admitPoint`, `admitCategorical`), the field of a retained record by wire index (`projection`), and the retained cone and creation owner. `childOperand` and the runtime application builder of `9165255` are deleted. The statement "the runtime builds the dependent application" is false at the tip.

### How the operation is selected

The address string selects the operation. Each lookup requires one owner:

| Address kind | Selection | Lines of `PublishedSource.lean` |
| --- | --- | --- |
| `$cas.project`, `$cas.apply` | the retained value | `:1458-1472` |
| action edge, functor with receiver | `PublishedPorts.edge?`, functor id | `:1473-1479`, `:1264-1296` |
| method | method id, then the route below | `:1480-1481`, `:190-286` |
| property | property id | `:1482-1483`, `:288-308` |
| point (`ctor = "apply"`) | `pointOwner`: component, cartesian, morphism, application, binder, functor map, action | `:1484-1485`, `:1004-1160` |
| component, presentation, creation, universal, raw limit | their published-port lookups | `:1486-1497` |
| lift port | `LiftFamily.forAddress?` | `:1499-1501` |
| operation, construction, functor, morphism | `PublishedPorts.family?` | `:1503-1514` |

No surface name is resolved on this path. The provider gives a published address and the complete parameters.

### Who builds the dependent application

The compiler. The shared producers are `applySourceArguments`, `applySourceDataArguments` and `elabSourceApplication` (`SourceTypeOrigin.lean:472-532`), called by `explicit` and `complete` (`PublishedSource.lean:145-161`), and the family producers (`RoutedMethodFamily.applyAt`, `PropertyFamily.forReceiver`, `CategoricalPointFamily`, `SourceActionFamily`, `LimitFamily`, `nativeSourceCell`). The reader's rules do not call `prepare`. The reader uses one function of the module, `namedApplicable` (`ReadNamed.lean:130`). `PublishedSource.lean` has its own builder for each kind of address, for example `mapValue` (`:933-986`), `rawLimit` (`:1165-1262`) and `validateSymbolicCore` (`:706-846`).

### Route resolution, receiver admission and the C6 gate

| Check | Method | Property | Operation, functor, construction, morphism address | Lift port |
| --- | --- | --- | --- | --- |
| Route resolution | `RoutedMethodFamily.atSource`, the producer of the reader (`SourceMethod.lean:52`); the action descriptors of the packet must name one first-hit family (`:207-210`) | `PropertyFamily.forReceiver` (`:305-306`); NOT CHECKED inside | none; the declaration is applied at the wire parameters (`:1513-1514`) | none |
| C6 competing-routes gate | runs: `family.agreements` (`:214`; `RoutedMethodFamily.lean:316-329`): a declared preferred route is enforced, and each other surviving family needs a whole-family agreement or the request is a semantic ambiguity | NOT CHECKED: `PropertyFamily.lean:142`, `:148` call `preferredRoute?` and `sourceRouteAgreements`; I did not read the function that holds them | does not run; no name is resolved | does not run |
| Receiver admission | runs: typed read at the declared receiver type (`:232`), then `admitMethod` (`:239`; `ChildCall.lean:78-80`) | runs: `registry.rejects` (`:293`), then `admitProperty` (`:307`; `ChildCall.lean:81-85`) | each operand is read at its declared type with `checkRegisteredDomains` (`:92-96`) | the same |

Differences between the method path here and the reader: the agreement evidence is every `Prop` local of the context (`:211-213`), where the reader passes the carrier comparisons of the receiver (`SourceMethod.lean:88-89`); the reader also lets member kinds compete (`sourceMemberPreference`, `checkSourceMemberSelections`, `SourceMethod.lean:118-127`).

The reader's operation path (`sourceOperation`, `SourceOperation.lean:348-498`: element owner, routes, family agreement, refinement cone, transports) has no part in a child call on an operation address.

### Does a child lift call form a selection

No. The lift branch forms `family.mark (complete head parameters)` (`PublishedSource.lean:1499-1501`). The mark holds the kind `LiftFamily`, the lift id and the port (`LiftFamily.lean:107-110`). It holds no `CasCompiler.selection`. The reader gives each selected lift application a selection name (`SourceLift.lean:102-103`) and puts it on every record action (`selectRecordActions`, `:170-171`; `selectedField`, `:180`). The lift branch reads no `bindings` from the provider; the universal branch does (`:1310-1359`).

Consequence (inference from the code read, medium confidence; `Transaction.lean` is NOT CHECKED): `PreparedRequest.selection` comes from the lowering frame (`Lower.lean:179`), and the frame gets a selection only below a selected-field node (`Lower.lean:560`). A child lift term has no such node, so `RecordAction.prepare` receives `family.selection = none` (`Demand.lean:90-91`) and does not mark the earlier field inputs (`RecordAction.lean:81-83`). The runtime evaluates those inputs as new source terms (`Demand.lean:100-104`). The earlier fields then get new occurrences. The row's sentence "A child lift call forms no selection, so earlier fields get fresh occurrences" holds.

### Result against C23

| C23 statement | State at `fc7fdf8` |
| --- | --- |
| The runtime does not rebuild the mathematical application | satisfied: the compiler builds the term |
| The runtime resolves scoped operands, invokes, retains | satisfied: callbacks only |
| Common final lowerer and executor | satisfied |
| Common dependent application | partly: shared application elaborator and family producers; a separate builder for each kind of address in `PublishedSource.lean` |
| Common source-governed operation selection | partly: shared for a method; address lookup with no route for an operation, functor, construction or morphism; not checked for a property |
| Direct and provider-requested calls keep the same selected operation and dependent inputs | not satisfied for a lift: no selection, earlier fields demanded again |

## The 2026-11-17 paragraph: three statements

| # | Statement | Truth at `fc7fdf8` | Evidence |
| --- | --- | --- | --- |
| 1 | In `CasCompiler/SourceLimit.lean`, `sourceLimitLeg?` selects endpoint representatives by definitional equality. | False | `SourceLimit.lean:433-469` has no `isDefEq`. The index is `constructionIndex indexType ordinal` (`:446`); the apex end is set to the receiver by position (`:456`). |
| 1a | (The formation of a limit now retains its row and cone in the judgement and in the binding; the apex recognition `limitApex?` is deleted.) | True, and incomplete | The selection also retains the presentation, the diagram, the interface and the construction name (`Elaborate.lean:52-88`). `limitApex?` occurs in no `.lean` file of the branch; it occurs in `research.md:78` and `tasks.md:61`, `:478`. |
| 2 | In `CasRuntime/ChildCall.lean`, `Kernel.child` builds the mathematical application of a provider-requested operation inside the runtime. | False | `ChildCall.lean:121-123`: the compiler entry `PublishedSource.prepare` forms the term. |
| 3 | `scripts/probes/rx_lift_runtime.lean` runs the original RX-LIFT statements through `CasCatalogue.Realize`. | True | No change since `9165255`. `:3` `import CasCatalogue.Realize`; `:66` `Realize.Harness.load`; `:122` `Realize.prepare scope statement (some stages)`; `:131` `Realize.evaluatePrepared harness question`. |

## Observations outside the rows

These are facts seen during the reading. They are not verdicts on a row.

- `CasCompiler/SourceLimit.lean:418`: the bound of a `Fin n` index ordinal is decided with `mkDecideProof`.
- `CasRuntime/Session.lean:611`: a definition of `Sort` type gets no retained value; `Lower.lean:884` lowers a type as an object. Each later use lowers the definition again (`Lower.lean:707-712`).
- `CasCatalogue/TestSuite.lean:366`: a `#cas` command with no installed session starts a session. Only `withSession` (`:251`) and the notebook (`NotebookSession.lean:73-75`) close a session.
- `CasCompiler/Lower.lean` holds diagnostic `dbg_trace` lines for named declarations (`:770-771`, `:797-903`, `:1147-1247`, `:2052-2068`).

## Files read

Tip `fc7fdf8`, in full: `CasRuntime/ChildCall.lean`, `Demand.lean`, `Invocation.lean`, `Session.lean`, `Realization.lean`, `ManifestAdmission.lean`, `Kernel.lean`, `ExecutionContext.lean`; `CasCompiler/PublishedSource.lean`, `Lower.lean`, `SourceLimit.lean`, `SourceLift.lean`, `SourceOperation.lean`, `SourceCarrier.lean`, `SourceDivision.lean`, `SourceAdmission.lean`, `SourceRing.lean`, `SourceSubset.lean`, `SourceMember.lean`, `SourceMethod.lean`, `ReadNamed.lean`, `ReadAnnotationRules.lean`, `ReadApplication.lean`, `RecordAction.lean`, `Program.lean`, `LiftFamily.lean`, `LimitInterface.lean`, `PublishedPorts.lean`, `SourceReference.lean`, `SelectedField.lean`; `CasCatalogue/TestSuite.lean`, `NotebookSession.lean`; `scripts/probes/rx_lift_runtime.lean`.

Tip, in part: `CasRuntime/Environment.lean` (93-1160, 1244-1470), `CasRuntime/Value.lean` (170-359, 1090-1204), `CasCompiler/Surface.lean` (40-179), `CasCompiler/Elaborate.lean` (20-149), `CasCompiler/RoutedMethodFamily.lean` (225-339).

`9165255`, in full: `CasCompiler/Lower.lean`, `LiftFamily.lean`, `Program.lean`; `CasRuntime/ChildCall.lean`, `Demand.lean`, `Invocation.lean`, `ManifestAdmission.lean`. In part: `Session.lean`, `Environment.lean`, `Realization.lean`, `SourceOperation.lean`, `Surface.lean`, `SourceAdmission.lean`, `SourceMember.lean`, `ReadNamed.lean`.

Constitution (`main` checkout): lines 385-739 (C5, C6, C7, C8, C23).

NOT CHECKED: `CasRuntime/RoutedMethod.lean`, `Transaction.lean`, `PreparedRequest.lean` (two lines by search); `CasCompiler/PropertyFamily.lean`, `SourceNumeral.lean`, `SourceMemberChoice.lean`, `SourceTypeOrigin.lean` (line numbers by search); the element reader rules; the released leaf contract.
