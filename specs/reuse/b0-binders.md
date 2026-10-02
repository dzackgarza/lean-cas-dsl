# Reuse record: `b0-binders`

The kernel's one binder path (`CasCatalogue.Language.bind`, `readArguments`), which replaces the
cases `definite`, `bigOperator`, `formalSeries?` and the `lim` refusal (`specs/binders.md`).

## Queries
- `search "binder notation big operator"`: Iris `big_op.v` (folds with built-in binders over lists,
  maps and sets), Mathlib `Finset.sum` / `tsum` notation: each a notation for one operation, defined
  with it; none reads a notation through a table of rows whose operations it does not know;
- `search "elaborate binder notation unify arguments"`, `search "Finset.sum notation delaborator"`,
  `search "tsum notation"`: notation and delaborators for fixed operations only;
- Lean `Meta.forallMetaTelescopeReducing`, `isDefEq`, `saveState`/`restoreState`: the unification
  of a row's parameters with the arguments, and asking it without committing to it.

## Owner
- `lean-categories`: the binder rows (`BinderEntry`; `bind.sets.integral`, `bind.sets.finite_sum`,
  `bind.sets.finite_product`, `bind.sets.limit`, `bind.sets.limit_at_infinity`,
  `bind.sets.real_series`, `bind.sets.complex_series`, `bind.sets.power_series_sum`), each with its
  operation, domain, and the object of maps the operation is total on with its admission and
  evidence; the registry validator `validateBinder`.
- The kernel's existing generic machinery: `recognize` (an object by declaration identity),
  `atStage` (a term at a stage, the variable its generic element), `admit` (an admission with its
  registered evidence), `applyTo` (a registered family applied to elements), `coerceTo` (along
  registered inclusions).

## New code
The reading rule itself, which no dependency supplies: select the rows whose operation takes the
arguments, read the body at the row's domain, select by the codomain of the body's map, admit the
map into the operation's source, apply the operation. `numeralElement?` (a numeral's element asked
without failing) and `admitInto` (an admission over the object row) factor existing kernel code.
