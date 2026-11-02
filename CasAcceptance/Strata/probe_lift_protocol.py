"""Protocol scaffolding for actual selected/composed lift dispatch.

Every returned token is an arbitrary data-flow witness. This program implements
no mathematics and supplies no correctness evidence. The kernel probe checks
framing, ordered dependencies and ownership using the public contract helpers.
"""

import itertools
import sys

from cas_port import lift_factor_input, lift_input, lift_parameters, serve, typed_map


serials = itertools.count()


def envelope(name, *arguments):
    return {"ctor": name, "args": list(arguments)}


def token(operation):
    return envelope("opaqueData", f"{operation}: actual reply {next(serials)}")


def implementation(operation):
    def call(packet):
        lift_parameters(packet)
        if operation.endswith("#factor"):
            _, _, _, _, outputs, _, cone = lift_factor_input(packet, operation)
            domain, _, _ = typed_map(cone)
            return envelope("typedMap", domain, outputs[0], token(operation))
        kind, _, action, source, base, outputs = lift_input(packet, operation)
        if kind == "liftInput":
            source = source["args"][0]
        field = operation.rsplit("#", 1)[1]
        if field == "obj":
            return token(operation)
        if field == "hom":
            return envelope("typedMap", outputs[0], source, token(operation))
        image = envelope("functorAction", action, outputs[0])
        apex = base["args"][0]
        if field == "forward":
            return envelope("typedMap", image, apex, token(operation))
        return envelope("typedMap", apex, image, token(operation))

    return call


if __name__ == "__main__":
    serve("lift-probe", "0", "0.1.0", {
        operation: implementation(operation) for operation in sys.argv[1:]
    })
