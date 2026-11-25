"""Complete native creation interfaces for original occurrence/continuation controls.

The original set-limit provider computes the target cone. This peer exercises
native record transport and owned continuations; it implements no pullback
algorithm, mathematical definition, or native proof.
"""

from __future__ import annotations

import json
import sys
from pathlib import Path

from cas_port import input_ref
from cas_session import export, proxy, serve

configuration = json.loads(sys.argv[1])
creation_count = 0


def observe(label, context, captures):
    record = {
        "label": label,
        "prepared_role": context.get("prepared_role"),
        "kind": context.get("kind"),
        "arguments": context.get("arguments", []),
        "parameter_count": len(context.get("parameters", [])),
        "captures": [value.reference() for value in captures],
    }
    with Path(configuration["log"]).open("a", encoding="utf-8") as log:
        log.write(json.dumps(record) + "\n")


def native_interface(label, captures):
    """Lease the actual native interface; every later use keeps its supplied inputs."""

    def invoke(context):
        assert context["kind"] == "dependent"
        observe(label, context, captures)
        role = context["prepared_role"]
        if role.startswith("project:"):
            assert context["arguments"] == []
            return native_interface(label + "/" + role, captures)
        # Only actual native applications introduce these new input positions.
        assert context["arguments"]
        arguments = [proxy(input_ref(["arguments", index]))
                     for index in range(len(context["arguments"]))]
        return native_interface(label + "/application", [*captures, *arguments])

    return export(invoke, captures)


def creation(context):
    global creation_count
    assert context["prepared_role"] == ""
    assert context["arguments"] == []
    assert context["argument_layouts"] == []
    assert context["bindings"] == []
    parameters = context["parameters"]
    assert len(parameters) >= 4
    diagram = parameters[3]
    assert diagram["ctor"] == "cospan" and len(diagram["args"]) == 2
    # The diagram packet is structural; its original declared fields are typed
    # inputs. No invented whole-D reference or fixed source constant is decoded.
    captures = [proxy(input_ref(["parameters", index])) for index in (0, 1, 2)]
    captures.extend(proxy(input_ref(["parameters", 3, "args", index])) for index in range(2))
    captures.extend(proxy(input_ref(["parameters", index])) for index in range(4, len(parameters)))
    mode = ("inline", "owned", "repeat", "missing")[min(creation_count, 3)]
    creation_count += 1
    observe("creation:" + mode, context, captures)
    if mode == "owned":
        return native_interface("complete-created-root", captures)

    # Original native data-field order:
    # LiftsToLimit = [LiftableCone, makesLimit]
    # LiftableCone = [liftedCone, validLift]
    # Cone = [pt, pi]; Iso = [hom, inv]. Native proof fields have no reply slot.
    cone = [native_interface("source-apex", captures),
            native_interface("source-cone-pi", captures)]
    comparison = [native_interface("validLift-hom", captures),
                  native_interface("validLift-inv", captures)]
    liftable = [cone, comparison]
    if mode == "missing":
        return [liftable]
    return [liftable, native_interface("source-makesLimit", captures)]


serve("creation-invocation-peer", "0", {
    "lift.finite_sets.pullbacks": creation,
})
