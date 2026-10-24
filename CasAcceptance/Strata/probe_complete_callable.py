"""Protocol-only complete-callable witnesses; no mathematical answers or laws."""

import itertools
import sys
import uuid

from cas_port import opaque_data, point_invocation, presentation_invocation, serve, value_data


process = uuid.uuid4().hex
serials = itertools.count()
wrong_endpoints = "--wrong-endpoints" in sys.argv[1:]


def implementation(operation):
    def call(request):
        if request.get("ctor") == "presentationApply":
            _, _, source, target, argument = presentation_invocation(request)
        else:
            _, _, _, domain, source, target, argument = point_invocation(request, operation)
            if domain != source:
                raise ValueError("whole-callable observation changed the original full domain")
        if argument != {"ctor": "identity", "args": [source, source]}:
            raise ValueError("whole-callable observation substituted a point or sample")
        token = opaque_data(f"{process}:{next(serials)}")
        if wrong_endpoints:
            source, target = target, source
            if source == target:
                source = {"ctor": "objectProduct", "args": [source, source]}
        return value_data({"ctor": "typedMap", "args": [source, target, token]})

    return call


if __name__ == "__main__":
    serve("complete-callable-probe", "0", "0.1.0", {
        operation: implementation(operation) for operation in sys.argv[1:]
        if not operation.startswith("--")
    })
