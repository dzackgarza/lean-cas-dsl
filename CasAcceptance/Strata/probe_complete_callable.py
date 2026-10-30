"""Protocol-only complete-callable witnesses; no mathematical answers or laws."""

import itertools
import sys
import uuid

from cas_port import (
    action_invocation, opaque_data, point_invocation, presentation_invocation,
    serve, value_data,
)


process = uuid.uuid4().hex
serials = itertools.count()
issued = set()
object_images = []
wrong_endpoints = "--wrong-endpoints" in sys.argv[1:]
bare_reply = "--bare-reply" in sys.argv[1:]


def fresh():
    token = f"{process}:{next(serials)}"
    issued.add(token)
    return opaque_data(token)


def tokens(data):
    if isinstance(data, dict):
        if data.get("ctor") == "opaqueData":
            yield data["args"][0]
        else:
            for child in data.values():
                yield from tokens(child)
    elif isinstance(data, list):
        for child in data:
            yield from tokens(child)


def implementation(operation):
    def call(request):
        if any(token not in issued for token in tokens(request)):
            raise ValueError("the complete callable received another session's data")
        if operation.startswith("action:"):
            action_invocation(request, operation)
            result = fresh()
            object_images.append(result)
            return value_data(result)
        if request.get("ctor") == "presentationApply":
            _, _, source, target, argument = presentation_invocation(request)
        else:
            _, _, _, domain, source, target, argument = point_invocation(request, operation)
            if domain != source:
                raise ValueError("whole-callable observation changed the original full domain")
        if argument != {"ctor": "identity", "args": [source, source]}:
            raise ValueError("whole-callable observation substituted a point or sample")
        if object_images and (source not in object_images or target not in object_images):
            raise ValueError("the component did not reuse its actually computed full endpoints")
        token = fresh()
        if bare_reply:
            if wrong_endpoints:
                raise ValueError("a bare protocol witness has no replaceable endpoint fields")
            return token
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
