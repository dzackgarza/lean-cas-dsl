import json
import re
from pathlib import Path

HERE = Path(__file__).resolve().parent

INPUTS = {
    "workload_routes": "workload-routes.json",
    "milestones": "milestones.json",
    "scaffolding": "scaffolding.json",
    "existing_leaves": "existing-leaves.json",
    "spike_inventory": "spike-inventory.json",
    "engine_survey": "engine-survey.md",
}

FAMILY = {
    "cat.sets": "Sets",
    "cat.core_sets": "Sets",
    "cat.subobjects_sets": "Sets",
    "cat.core_subobjects_sets": "Sets",
    "cat.subsets.point_predicates": "Sets",
    "cat.subsets.subset_predicates": "Sets",
    "cat.finite_sets": "Finite, countable, enumerated sets",
    "cat.enumerated_sets": "Finite, countable, enumerated sets",
    "cat.countable_sets": "Finite, countable, enumerated sets",
    "cat.boolean_algebras": "Boolean algebras, power sets",
    "cat.cardinals": "Cardinals",
    "cat.cardinalities": "Cardinals",
    "cat.partial_orders": "Order structures",
    "cat.linear_orders": "Order structures",
    "cat.magmas": "Magmas, semigroups, monoids",
    "cat.semigroups": "Magmas, semigroups, monoids",
    "cat.monoids": "Magmas, semigroups, monoids",
    "cat.commutative_monoids": "Magmas, semigroups, monoids",
    "cat.additive_monoids": "Magmas, semigroups, monoids",
    "cat.additive_commutative_monoids": "Magmas, semigroups, monoids",
    "cat.groups": "Groups",
    "cat.additive_groups": "Groups",
    "cat.core_groups": "Groups",
    "cat.subobjects_groups": "Groups",
    "cat.arrows_groups": "Groups",
    "cat.semirings": "Semirings",
    "cat.rings": "Rings, commutative rings",
    "cat.commutative_rings": "Rings, commutative rings",
    "cat.fields": "Fields",
    "cat.modules_r": "Modules",
    "cat.modules_total": "Modules",
    "cat.core_modules_r": "Modules",
    "cat.subobjects_modules_r": "Modules",
    "cat.arrows_modules_r": "Modules",
    "cat.core_subobjects_modules_r": "Modules",
    "cat.ideals_r": "Modules",
    "cat.algebras": "Algebras",
    "cat.hausdorff_topological_commutative_monoids": "Polynomial rings",
    "cat.bil_wform": "Bilinear and quadratic modules",
    "cat.bilin_module": "Bilinear and quadratic modules",
    "cat.arrows_bilin_module": "Bilinear and quadratic modules",
    "cat.integral_lattice": "Lattices (quadratic forms)",
    "cat.schemes_over_ring": None,
}

CALCULUS_ROWS = {
    "bind.sets.limit",
    "bind.sets.limit_at_infinity",
    "bind.sets.integral",
    "bind.sets.real_series",
    "bind.sets.complex_series",
    "mor.sets.taylor_expansion",
    "mor.sets.real_sin",
    "mor.sets.real_cos",
    "mor.sets.real_exp",
    "mor.sets.smooth_continuous",
    "mor.sets.smooth_derivative",
}

KIND = [
    ("obj.", "object constructor"),
    ("con.", "construction"),
    ("fun.", "functor (object and morphism actions)"),
    ("forget[", "classifier forget (object and morphism actions)"),
    ("prop.", "property"),
    ("clf.", "classifier"),
    ("cmp.", "comparison (presentation or cell)"),
    ("cell.", "comparison (presentation or cell)"),
    ("lift.", "lift"),
    ("fib.", "fibration"),
    ("adj.", "adjunction"),
    ("ctor.arrow(", "image of a functor under Arr (object and morphism actions)"),
    ("ctor.core(", "image of a functor under Core (object and morphism actions)"),
    ("ctor.", "constructor"),
    ("cat.", "category"),
    ("op.", "operation"),
    ("mor.", "operation"),
    ("meth.", "operation"),
    ("num.", "operation"),
    ("lit.", "operation"),
    ("pow.", "operation"),
    ("bind.", "operation"),
    ("lim.", "operation"),
    ("colim.", "operation"),
    ("incl.", "operation"),
    ("graph.", "operation"),
]


def load(name):
    with open(HERE / INPUTS[name], encoding="utf-8") as handle:
        return json.load(handle)


def kind(row):
    for prefix, label in KIND:
        if row.startswith(prefix):
            return label
    raise ValueError(f"no kind for catalogue row {row}")


def survey_families():
    text = (HERE / INPUTS["engine_survey"]).read_text(encoding="utf-8")
    start = text.index("## Recommendation summary")
    end = text.index("\n## ", start + 1)
    families = {}
    for line in text[start:end].splitlines():
        cells = [c.strip() for c in line.strip().strip("|").split("|")]
        if len(cells) != 4 or cells[0] in ("Family", "---"):
            continue
        families[cells[0]] = {
            "primary": cells[1],
            "fallback": cells[2],
            "engines_needed": cells[3],
        }
    return families


def parse_why(why):
    owners, params = {}, {}
    for cat, reasons in why.items():
        for reason in reasons:
            match = re.match(r"R1 owner of (\S+)$", reason)
            if match:
                owners.setdefault(match.group(1), set()).add(cat)
            match = re.match(r"R1 declared parameter of (\S+)$", reason)
            if match:
                params.setdefault(match.group(1), set()).add(cat)
    return owners, params


def structural_order(scaffolding, milestones):
    layers = {c["id"]: c for c in scaffolding["categories"]}
    position = {}
    for index, ms in enumerate(milestones["milestones"]):
        for cat in ms["categories"]:
            assert cat not in position, cat
            position[cat] = (index, ms["task"], ms["milestone"], ms["part"])

    def rank(cat):
        entry = layers.get(cat)
        if entry is None:
            return None
        if entry["layer"] is not None:
            return entry["layer"]
        return entry["inferredLayerWithInputs"]

    def key(cat):
        index = position[cat][0] if cat in position else len(milestones["milestones"])
        r = rank(cat)
        return (index, -1 if r is None else r, cat)

    return key, position, layers


def edges_between(scaffolding):
    out = []
    for edge in scaffolding["edges"]:
        if edge["edge"] == "fun.sets.whole_subset":
            continue
        out.append((edge["edge"], edge["source"], edge["target"], edge["kind"]))
    return out


def main():
    target = HERE / "category-scope.json"
    workload = [
        r for r in load("workload_routes") if r["source"] in ("permanent", "extension")
    ]
    milestones = load("milestones")
    scaffolding = load("scaffolding")
    leaves = load("existing_leaves")
    spike = load("spike_inventory")
    survey = survey_families()
    key, position, layers = structural_order(scaffolding, milestones)
    edges = edges_between(scaffolding)
    nonstructural = {}
    for c in scaffolding["categories"]:
        for f in c["nonStructuralFunctorsOut"]:
            nonstructural[f["functor"]] = (c["id"], f["target"])

    kernel_v1 = set()
    for ms in milestones["milestones"]:
        kernel_v1.update(ms["v1_statements"])
    spike_carried = {}
    for comp in spike["computations"]:
        for sid in comp["statements"]:
            spike_carried.setdefault(sid, []).append(comp["id"])

    statements = {}
    for r in workload:
        sid = r["id"]
        settled = r["question_kind"] == "settled"
        if sid in spike_carried or sid in kernel_v1:
            version = "V1"
        else:
            version = "V2"
        basis = []
        if sid in spike_carried:
            basis.append("spike computation " + ", ".join(spike_carried[sid]))
        if sid in kernel_v1:
            basis.append("kernel V1 statement")
        if not basis:
            basis.append("full-B0 statement (#19)")
        statements[sid] = {
            "version": version,
            "class": r["source"] + " workload statement",
            "statement": r["statement"],
            "computed": not settled,
            "rows": r["rows"],
            "categories": r["categories"],
            "why": r["why"],
            "basis": basis,
        }
    for b in spike["full_b0_file_routes"]:
        statements[b["id"]] = {
            "version": "V2",
            "class": "full-B0 file statement",
            "statement": b["statement"],
            "computed": True,
            "rows": b["rows"],
            "categories": b["categories"],
            "why": b["why"],
            "basis": ["full-B0 statement (#19), " + b["file"]],
        }
    for comp in spike["computations"]:
        for p in comp["proposed"]:
            statements[p["id"]] = {
                "version": "V1",
                "class": "proposed statement",
                "statement": p["statement"],
                "computed": not p["typing_judgement"],
                "rows": p["rows"],
                "categories": p["categories"],
                "why": p["why"],
                "basis": ["spike computation " + comp["id"]],
            }
    for ceil in spike["ceilings"]:
        for p in ceil["proposed"]:
            statements[p["id"]] = {
                "version": None,
                "class": "spike ceiling",
                "statement": p["statement"],
                "computed": not p["typing_judgement"],
                "rows": p["rows"],
                "categories": p["categories"],
                "why": p["why"],
                "basis": ["spike ceiling " + ceil["id"]],
            }
    missing_ids = [s for s in kernel_v1 if s not in statements]
    assert not missing_ids, missing_ids

    owners, params = {}, {}
    for s in statements.values():
        o, p = parse_why(s["why"])
        for row, cats in o.items():
            owners.setdefault(row, set()).update(cats)
        for row, cats in p.items():
            params.setdefault(row, set()).update(cats)

    def registered(cats):
        return [c for c in cats if c.startswith("cat.")]

    def route_edges(cats):
        cats = set(cats)
        return [(e, s, t) for e, s, t, _ in edges if s in cats and t in cats]

    def home(row):
        if row in nonstructural:
            source, target = nonstructural[row]
            candidates = registered([source, target])
        else:
            candidates = registered(
                sorted(owners.get(row, set()) | params.get(row, set()))
            )
        assert candidates, f"no owner category for {row}"
        return max(candidates, key=key)

    edge_ends = {e: (s, t) for e, s, t, _ in edges}

    rows = {}
    route_count = {}
    for sid, s in statements.items():
        if s["version"] is not None and s["computed"]:
            for cat in s["categories"]:
                route_count.setdefault(cat, {"V1": set(), "V2": set()})[
                    s["version"]
                ].add(sid)
        needed = [(r, home(r)) for r in s["rows"]] + [
            (e, src) for e, src, _ in route_edges(s["categories"])
        ]
        for row, cat in needed:
            entry = rows.setdefault(
                row,
                {
                    "home": cat,
                    "statements": {
                        "V1": set(),
                        "V2": set(),
                        "ceiling": set(),
                        "settled": set(),
                    },
                },
            )
            assert entry["home"] == cat
            if not s["computed"]:
                entry["statements"]["settled"].add(sid)
            elif s["version"] is None:
                entry["statements"]["ceiling"].add(sid)
            else:
                entry["statements"][s["version"]].add(sid)

    by_home = {}
    for row, entry in rows.items():
        by_home.setdefault(entry["home"], []).append(row)

    regs = {}
    for reg in leaves:
        cats = registered([reg["category"], reg["input_category"]])
        if reg["operation"] in rows:
            cats.append(rows[reg["operation"]]["home"])
        cat = max(cats, key=key)
        regs.setdefault(cat, []).append(
            {
                k: reg[k]
                for k in (
                    "operation",
                    "input",
                    "backend",
                    "engine",
                    "routine",
                    "file",
                    "line",
                )
            }
        )

    categories = sorted(set(by_home) | set(route_count), key=key)
    out_categories = []
    for cat in categories:
        row_entries = []
        for row in sorted(by_home.get(cat, []), key=lambda r: (kind(r), r)):
            e = rows[row]["statements"]
            version = "V1" if e["V1"] else "V2" if e["V2"] else None
            row_entries.append(
                {
                    "row": row,
                    "kind": kind(row),
                    "catalogue_owners": sorted(edge_ends[row])
                    if row in edge_ends
                    else sorted(owners.get(row, set())),
                    "parameter_categories": sorted(params.get(row, set())),
                    "version": version,
                    "statements": {k: sorted(v) for k, v in e.items() if v},
                    "engine_family": "Calculus" if row in CALCULUS_ROWS else None,
                }
            )
        family = FAMILY.get(cat)
        assert cat in FAMILY, f"no engine family recorded for {cat}"
        families = sorted(
            ({family} | {r["engine_family"] for r in row_entries}) - {None}
        )
        for f in families:
            assert f in survey, f
        counts = route_count.get(cat, {"V1": set(), "V2": set()})
        ms = position.get(cat)
        out_categories.append(
            {
                "id": cat,
                "name": layers[cat]["name"] if cat in layers else None,
                "layer": layers[cat]["layer"] if cat in layers else None,
                "inferred_layer": layers[cat]["inferredLayerWithInputs"]
                if cat in layers
                else None,
                "built_from": [i["target"] for i in layers[cat]["inferredInputs"]]
                if cat in layers
                else [],
                "milestone": {"task": ms[1], "name": ms[2], "part": ms[3]}
                if ms
                else None,
                "engine_families": [{"family": f, **survey[f]} for f in families],
                "rows": [r for r in row_entries if r["version"] is not None],
                "ceiling_only_rows": [
                    r
                    for r in row_entries
                    if r["version"] is None and r["statements"].get("ceiling")
                ],
                "settled_only_rows": [
                    r["row"]
                    for r in row_entries
                    if r["version"] is None and not r["statements"].get("ceiling")
                ],
                "counts": {
                    "V1_rows": sum(1 for r in row_entries if r["version"] == "V1"),
                    "V2_rows": sum(1 for r in row_entries if r["version"] == "V2"),
                    "V1_statements": len(counts["V1"]),
                    "V2_statements": len(counts["V2"]),
                    "statements": len(counts["V1"] | counts["V2"]),
                },
                "registrations": sorted(
                    regs.get(cat, []),
                    key=lambda r: (r["operation"], r["input"], r["backend"]),
                ),
            }
        )

    unplaced = sorted(set(regs) - set(categories))
    result = {
        "inputs": INPUTS,
        "generated_by": "category_scope.py",
        "rules": {
            "versions": {
                "V1": "a workload statement that carries a computation of the spike inventory, a statement proposed by the inventory for a spike computation, or a kernel V1 statement of milestones.json (the 134 extension statements and the 15 K1 identifiers)",
                "V2": "every other statement of #19 (K1 to K14): the other permanent statements and the 18 statements of the K3 and K14 files",
                "V3": "the classified Sage coverage of #20, #21 and #23; a row joins a category's V3 by the same membership rule when tasks T140 to T147 produce the classified statements; no statement exists yet",
            },
            "row_version": "the first version of a computed statement that needs the row; a typing judgement (question kind settled, or a proposed typing judgement) computes nothing and gives no version",
            "rows_of_a_statement": "its catalogue rows, and the structural functors and classifier forgets of scaffolding.json whose two ends are on its route",
            "home_category": "the latest category, in the structural order, among the catalogue owners and the declared parameter categories of the row (both ends of a functor); a structural functor or classifier forget belongs to its source",
            "structural_order": "the order of the milestones of milestones.json (which applies the layers of scaffolding.json and the rule of plan.md for the categories with no chain), then the layer (or the inferred layer with inputs), then the identifier",
            "registrations": "a registration of existing-leaves.json belongs to the latest of its operation's home category, its operation's category and its input's category",
        },
        "counts": {
            "statements": {
                v: sum(
                    1
                    for s in statements.values()
                    if s["version"] == v and s["computed"]
                )
                for v in ("V1", "V2")
            },
            "settled_statements": sum(
                1
                for s in statements.values()
                if not s["computed"] and s["version"] is not None
            ),
            "ceiling_statements": sum(
                1 for s in statements.values() if s["version"] is None
            ),
            "categories": len(out_categories),
            "rows": {
                v: sum(c["counts"][v + "_rows"] for c in out_categories)
                for v in ("V1", "V2")
            },
        },
        "categories": out_categories,
        "registrations_without_category_entry": {c: regs[c] for c in unplaced},
        "statements": {
            sid: {
                k: s[k]
                for k in (
                    "version",
                    "class",
                    "statement",
                    "computed",
                    "categories",
                    "basis",
                )
            }
            for sid, s in sorted(statements.items())
        },
        "missing_catalogue_rows": spike["missing_catalogue_rows"],
    }
    with open(target, "w", encoding="utf-8") as handle:
        json.dump(result, handle, ensure_ascii=False, indent=1)
        handle.write("\n")


if __name__ == "__main__":
    main()
