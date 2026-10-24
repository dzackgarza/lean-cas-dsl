"""Exercise the published package resolver and startup helper under real workspace layouts.

Usage: python3 scripts/test_contract_package_paths.py CONTRACT_CHECKOUT [LEAN]
Run with the compiled public contract on LEAN_PATH, for example from `lake env`.
Every manifest and dependency fixture is temporary. No backend or CAS answers are used.
"""

from __future__ import annotations

import json
import os
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile


PACKAGE = "cas_leaf_contracts"
PROBE = """module
import CasContract.Port
meta import CasContract.Port
open Lean

public def main (arguments : List String) : IO Unit := do
  let [package] := arguments
    | throw <| IO.userError "expected one package name"
  let directory ← CasCatalogue.Backend.packageDir package
  IO.println (toJson directory.toString).compress
"""
STARTUP = "import cas_port; cas_port.serve('package-path-smoke', '0', '0', {})"


def manifest(package: str = PACKAGE, *, name: str = "consumer", **entry) -> dict:
    return {"name": name, "packages": [{"name": package, "type": "git", **entry}]}


def install_helper(destination: Path, helper: Path) -> None:
    (destination / "python").mkdir(parents=True, exist_ok=True)
    shutil.copy2(helper, destination / "python" / "cas_port.py")


def resolve(lean: str, probe: Path, directory: Path, package: str,
            override: Path | None) -> subprocess.CompletedProcess:
    environment = os.environ.copy()
    # Preserve imports when Lake supplied paths relative to the original workspace.
    if environment.get("LEAN_PATH"):
        environment["LEAN_PATH"] = os.pathsep.join(
            str(Path(path).resolve()) for path in environment["LEAN_PATH"].split(os.pathsep)
        )
    environment.pop("CAS_LEAF_CONTRACT_PATH", None)
    if override is not None:
        environment["CAS_LEAF_CONTRACT_PATH"] = str(override)
    return subprocess.run(
        [lean, "--run", str(probe), package], cwd=directory, env=environment,
        text=True, capture_output=True, check=False, timeout=30,
    )


def start_helper(directory: Path, resolved: Path) -> None:
    environment = os.environ.copy()
    environment["PYTHONPATH"] = str(resolved / "python")
    result = subprocess.run(
        [sys.executable, "-c", STARTUP], cwd=directory, env=environment,
        input=b"", capture_output=True, check=True, timeout=10,
    )
    length, separator, payload = result.stdout.partition(b"\n")
    if not separator or not length.isdigit() or int(length) != len(payload):
        raise AssertionError("the resolved helper did not emit one complete ready frame")
    ready = json.loads(payload)
    if ready.get("op") != "ready" or ready.get("backend") != "package-path-smoke":
        raise AssertionError(f"the resolved helper did not start: {ready}")


def main() -> None:
    if not 2 <= len(sys.argv) <= 3:
        raise SystemExit(__doc__)
    helper = (Path(sys.argv[1]) / "python" / "cas_port.py").resolve(strict=True)
    lean_name = sys.argv[2] if len(sys.argv) == 3 else "lean"
    executable = shutil.which(lean_name)
    if executable is None:
        raise SystemExit(f"Lean executable not found: {lean_name}")
    lean = str(Path(executable).resolve(strict=True))
    with tempfile.TemporaryDirectory(prefix="cas-contract-package-") as temporary:
        root = Path(temporary)
        probe = root / "PackagePath.lean"
        probe.write_text(PROBE, encoding="utf-8")
        cases = []

        def add(label: str, content: dict | str | None, target: str | Path | None,
                *, package: str = PACKAGE, override: Path | None = None,
                failure: str | None = None) -> None:
            directory = root / label
            directory.mkdir()
            if content is not None:
                (directory / "lake-manifest.json").write_text(
                    content if isinstance(content, str) else json.dumps(content),
                    encoding="utf-8",
                )
            resolved = None if target is None else (directory / target).resolve()
            if resolved is not None:
                install_helper(resolved, helper)
            cases.append((label, directory, package, override, resolved, failure))

        add("default-git", manifest(), f".lake/packages/{PACKAGE}")
        add("configured-relative", {**manifest(), "packagesDir": "vendor"},
            f"vendor/{PACKAGE}")
        absolute_packages = root / "absolute-packages"
        add("configured-absolute", {**manifest(), "packagesDir": str(absolute_packages)},
            absolute_packages / PACKAGE)
        add("git-subdirectory", {**manifest(subDir="public/contract"), "packagesDir": "vendor"},
            f"vendor/{PACKAGE}/public/contract")
        add("path-relative", {**manifest(type="path", dir="../relative-contract"),
                              "packagesDir": "ignored-packages"}, "../relative-contract")
        absolute_contract = root / "absolute-contract"
        add("path-absolute", manifest(type="path", dir=str(absolute_contract)), absolute_contract)
        add("root-package", {"name": PACKAGE, "packages": []}, ".")
        override = root / "overridden-contract"
        add("explicit-override", "not a valid manifest", override, override=override)
        other = "other_package"
        add("override-is-contract-only", manifest(package=other), f".lake/packages/{other}",
            package=other, override=override)
        add("legacy-directory", None, f".lake/packages/{PACKAGE}")
        add("missing-package", {"name": "consumer", "packages": []}, None,
            failure=f"Lake package {PACKAGE} is absent")
        # An unrelated root can even contain a helper; it still is not the dependency.
        install_helper(root / "missing-package", helper)
        add("invalid-manifest", "not a valid manifest", None,
            failure="cannot read the Lake package manifest")

        for label, directory, package, override, expected, failure in cases:
            result = resolve(lean, probe, directory, package, override)
            if failure is not None:
                if result.returncode == 0 or failure not in result.stdout + result.stderr:
                    raise AssertionError(f"{label}: expected explicit resolution failure; {result}")
                continue
            if result.returncode != 0:
                raise AssertionError(f"{label}: resolver failed: {result.stdout}{result.stderr}")
            observed = (directory / json.loads(result.stdout.strip())).resolve()
            if observed != expected:
                raise AssertionError(f"{label}: resolved {observed}, expected {expected}")
            start_helper(directory, observed)
        print(f"PASS: {len(cases)} package layouts/failures, including real public-helper startup")


if __name__ == "__main__":
    main()
