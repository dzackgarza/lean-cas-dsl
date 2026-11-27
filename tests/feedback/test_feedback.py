"""Real public-command regressions for current source-to-result feedback.

Run from the compatible kernel checkout with just test-feedback.
An optional unittest selector runs only the requested regression.
The probes retain their sources, reports and diagnostics under timing/logs/feedback-tests.
"""
from __future__ import annotations

import datetime
from decimal import Decimal
import gzip
import hashlib
import json
import math
import os
import signal
import shutil
import subprocess
import sys
import tempfile
import time
import unittest
from pathlib import Path
from unittest.mock import patch

type JsonValue = None | bool | int | float | str | list[JsonValue] | dict[str, JsonValue]

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT / "scripts"))
from application_log import dumps_exact_json, loads_application_event
from acceptance_inputs import SOURCE_REVISION
from feedback_checkout import retain_checkout, restore_checkout


TIMING_FIELDS = {
    "run_id", "parent_run", "utc_start", "seconds", "status", "revision", "dirty",
    "environment", "target", "input_sha256", "log_path", "log_sha256",
}


def read_log(path: Path) -> str:
    if path.suffix == ".gz":
        with gzip.open(path, "rt") as source:
            return source.read()
    return path.read_text()


def current_acceptance_result() -> dict:
    current = json.loads((ROOT / ".tmp/accept-current.json").read_text())
    return json.loads((ROOT / current["result"]).read_text())


def process_children(pid: int) -> set[int]:
    children = set()
    for path in Path(f"/proc/{pid}/task").glob("*/children"):
        try:
            children.update(int(child) for child in path.read_text().split())
        except (FileNotFoundError, ProcessLookupError):
            continue
    return children


class FeedbackRecordTests(unittest.TestCase):
    def setUp(self) -> None:
        directory = ROOT / "timing/logs/feedback-tests"
        directory.mkdir(parents=True, exist_ok=True)
        self.control = Path(tempfile.mkdtemp(prefix="module-record-", dir=directory))
        self.checkout = self.control / "checkout"
        subprocess.run(["git", "clone", "--shared", "--no-checkout", "--quiet",
                        str(ROOT), str(self.checkout)], check=True)
        self.revision = subprocess.check_output(
            ["git", "-C", str(self.checkout), "rev-parse", "HEAD"], text=True).strip()
        self.feedback_pending = False
        self.addCleanup(self.retain_feedback_checkout)
        for name in [".gitignore", "justfile", "lean-toolchain", "scripts/feedback.sh",
                     "scripts/container.sh", "scripts/feedback_records.py",
                     "scripts/application_log.py", "scripts/acceptance_inputs.py",
                     "scripts/check_acceptance_permanent.py"]:
            target = self.checkout / name
            target.parent.mkdir(parents=True, exist_ok=True)
            shutil.copy2(ROOT / name, target)
        for name in ["FeedbackPass", "FeedbackFail"]:
            shutil.copy2(ROOT / f"tests/feedback/fixtures/{name}.lean",
                         self.checkout / f"{name}.lean")
        manifest = json.loads((ROOT / "lake-manifest.json").read_text())
        manifest.update(name="feedback_records", packages=[])
        (self.checkout / "lake-manifest.json").write_text(json.dumps(manifest) + "\n")
        configuration = (ROOT / "lakefile.lean").read_text()
        marker = "script «feedback-context» do\n"
        self.assertEqual(configuration.count(marker), 1)
        context_script = marker + configuration.split(marker, 1)[1]
        (self.checkout / "lakefile.lean").write_text(
            "import Lake\nopen Lake DSL\npackage feedback_records\n"
            "lean_lib FeedbackPass\nlean_lib FeedbackFail\n\n" + context_script)
        image_digest = os.environ.get("CAS_FEEDBACK_IMAGE_DIGEST", "")
        self.assertRegex(image_digest, r"^sha256:[0-9a-f]{64}$")
        self.environment = {
            "lean": subprocess.check_output(
                ["lean", "--version"], cwd=self.checkout, text=True).strip(),
            "image_digest": image_digest,
        }
        self.log = self.control / "public-loop.log"

    def retain_feedback_checkout(self) -> None:
        self.assertFalse(self.feedback_pending,
                         "the feedback run did not finalize; its checkout is retained in place")
        retain_checkout(self.checkout, self.revision, ["lean-toolchain", "scripts/feedback.sh"])

    def wait_feedback_finished(self) -> None:
        deadline = time.monotonic() + 60
        while time.monotonic() < deadline:
            records = self.checkout / "timing/modules.jsonl"
            contexts = list((self.checkout / "timing/logs").glob("*/context.json"))
            if len(contexts) == 1 and records.is_file():
                result = contexts[0].with_name("result.json")
                events = contexts[0].with_name("events.jsonl")
                try:
                    rows = records.read_text().splitlines()
                    terminal = events.read_text().splitlines()
                    if (result.is_file() and len(rows) == 1 and terminal
                            and json.loads(terminal[-1]).get("event") == "run.finished"):
                        row = json.loads(rows[0])
                        if (self.checkout / row["log_path"]).is_file():
                            self.run_directory = contexts[0].parent
                            self.feedback_pending = False
                            return
                except (FileNotFoundError, json.JSONDecodeError):
                    pass
            time.sleep(0.01)
        self.fail(f"the actual run did not finalize its row and gzip log: {self.log.read_text()}")

    def run_feedback(self, module: str, interrupted: bool = False) -> int:
        hold = self.checkout / "feedback-record-hold"
        ready = self.checkout / "feedback-record-ready"
        if interrupted:
            hold.write_text("hold the actual consumer until SIGTERM\n")
        self.started_at = datetime.datetime.now(datetime.timezone.utc)
        self.started_clock = time.monotonic()
        with self.log.open("w") as output:
            process = subprocess.Popen(
                ["just", "loop", module], cwd=self.checkout, stdout=output,
                stderr=subprocess.STDOUT, start_new_session=True)
            self.feedback_pending = True
            finalization_waited = False
            try:
                if interrupted:
                    observed = None
                    deadline = time.monotonic() + 300
                    while process.poll() is None and time.monotonic() < deadline:
                        if ready.is_file():
                            pending = [process.pid]
                            descendants = set()
                            natives = []
                            while pending:
                                pid = pending.pop()
                                if pid in descendants:
                                    continue
                                proc = Path(f"/proc/{pid}")
                                try:
                                    descendants.add(pid)
                                    pending.extend(process_children(pid) - descendants)
                                    arguments = (proc / "cmdline").read_bytes().decode().split("\0")
                                    if ((proc / "comm").read_text().strip() == "lean"
                                            and (proc / "cwd").resolve() == self.checkout
                                            and any((self.checkout / argument).resolve() ==
                                                    self.checkout / f"{module}.lean"
                                                    for argument in arguments if argument.endswith(".lean"))):
                                        natives.append((pid, arguments, os.getpgid(pid)))
                                except (FileNotFoundError, ProcessLookupError):
                                    continue
                            if natives:
                                self.assertEqual(len(natives), 1, self.log.read_text())
                                pid, arguments, group = natives[0]
                                self.assertIn(group, descendants)
                                self.assertEqual(os.getpgid(group), group)
                                self.assertEqual(Path(f"/proc/{group}/cwd").resolve(), self.checkout)
                                self.assertEqual(ready.read_text(), "feedback passing module entered\n")
                                observed = {"pid": pid, "command": arguments,
                                            "group": group, "signal": signal.SIGTERM,
                                            "monotonic_ns": time.monotonic_ns()}
                                (self.control / "interruption.json").write_text(
                                    json.dumps(observed, indent=2) + "\n")
                                os.killpg(process.pid, signal.SIGTERM)
                                break
                        time.sleep(0.01)
                    if observed is None and process.poll() is None:
                        try:
                            os.killpg(process.pid, signal.SIGTERM)
                        except ProcessLookupError:
                            pass
                status = process.wait(timeout=300)
                finalization_waited = True
                self.wait_feedback_finished()
                if interrupted:
                    self.assertIsNotNone(observed, self.log.read_text())
            finally:
                try:
                    if process.poll() is None:
                        try:
                            os.killpg(process.pid, signal.SIGTERM)
                        except ProcessLookupError:
                            pass
                        try:
                            process.wait(timeout=30)
                        except subprocess.TimeoutExpired:
                            os.killpg(process.pid, signal.SIGKILL)
                            process.wait(timeout=30)
                    if not finalization_waited:
                        self.wait_feedback_finished()
                finally:
                    hold.unlink(missing_ok=True)
        self.finished_at = datetime.datetime.now(datetime.timezone.utc)
        return status

    def assert_record(self, module: str, status: str) -> bytes:
        rows = [json.loads(line) for line in
                (self.checkout / "timing/modules.jsonl").read_text().splitlines()]
        self.assertEqual(len(rows), 1)
        row = rows[0]
        self.assertEqual(set(row), TIMING_FIELDS)
        context = json.loads((self.run_directory / "context.json").read_text())
        result = json.loads((self.run_directory / "result.json").read_text())
        runs = [json.loads(line) for line in
                (self.checkout / "timing/runs.jsonl").read_text().splitlines()]
        self.assertEqual(runs, [result])
        self.assertEqual(context["context_status"], "complete")
        self.assertEqual(context["targets"], [module])
        self.assertEqual(context["sources"], [f"{module}.lean"])
        self.assertEqual(context["dependencies"], [])
        self.assertEqual(len(context["resolution"]["packages"]), 1)
        self.assertEqual(Path(context["resolution"]["packages"][0]["path"]).resolve(), self.checkout)
        self.assertEqual(row["run_id"], context["run"])
        self.assertEqual(row["parent_run"], context["parent_run"])
        self.assertEqual(row["revision"], self.revision)
        self.assertEqual(row["dirty"], context["dirty"])
        self.assertIs(row["dirty"], True)
        self.assertEqual(row["environment"], self.environment)
        self.assertEqual(row["environment"], {
            key: context["environment"][key] for key in ("lean", "image_digest")})
        self.assertEqual(row["target"], module)
        self.assertEqual(row["status"], status)
        original = ROOT / f"tests/feedback/fixtures/{module}.lean"
        source = self.checkout / f"{module}.lean"
        self.assertEqual(source.read_bytes(), original.read_bytes())
        self.assertEqual(row["input_sha256"], hashlib.sha256(original.read_bytes()).hexdigest())
        self.assertEqual(row["input_sha256"], context["inputs"][f"{module}.lean"])
        steps = [json.loads(path.read_text()) for path in
                 (self.run_directory / "steps").glob("*.json")]
        build = [step for step in steps if step["phase"] == "build"]
        executed = [step for step in steps if step["phase"] == "execution"]
        self.assertEqual(len(build), 1)
        self.assertIn(f"+{module}:deps", build[0]["command"])
        self.assertEqual(build[0]["status"], 0)
        self.assertEqual(len(executed), 1)
        self.assertIn(f"{module}.lean", executed[0]["command"])
        self.assertEqual(executed[0]["source"], f"{module}.lean")
        self.assertEqual(row["utc_start"], executed[0]["utc"])
        self.assertEqual(row["seconds"], executed[0]["seconds"])
        started = datetime.datetime.fromisoformat(row["utc_start"])
        self.assertEqual(started.utcoffset(), datetime.timedelta(0))
        self.assertLessEqual(self.started_at, started)
        self.assertLessEqual(started, self.finished_at)
        self.assertIsInstance(row["seconds"], (int, float))
        self.assertTrue(math.isfinite(row["seconds"]))
        self.assertGreater(row["seconds"], 0)
        self.assertLessEqual(row["seconds"], time.monotonic() - self.started_clock)
        log = self.checkout / row["log_path"]
        self.assertEqual(log, self.run_directory / "output.log.gz")
        self.assertEqual(row["log_path"], result["log"])
        self.assertEqual(row["log_path"], context["log"])
        self.assertEqual(row["log_sha256"], hashlib.sha256(log.read_bytes()).hexdigest())
        self.assertFalse(log.with_suffix("").exists())
        raw = gzip.decompress(log.read_bytes())
        self.assertTrue(raw)
        events = [json.loads(line) for line in
                  (self.run_directory / "events.jsonl").read_text().splitlines()]
        self.assertEqual(events[0]["event"], "run.started")
        self.assertEqual(events[-1]["event"], "run.finished")
        self.assertEqual(result["interruption_signal"], "TERM" if status == "interrupted" else None)
        self.assertEqual(result["status"], 143 if status == "interrupted" else executed[0]["status"])
        if status == "pass":
            self.assertEqual(executed[0]["status"], 0)
        elif status == "fail":
            self.assertNotEqual(executed[0]["status"], 0)
        else:
            self.assertFalse(executed[0]["complete"])
        return raw

    def test_passing_module_writes_one_row(self) -> None:
        self.assertEqual(self.run_feedback("FeedbackPass"), 0, self.log.read_text())
        raw = self.assert_record("FeedbackPass", "pass")
        self.assertEqual(raw.count(b"feedback passing module entered"), 1)
        self.assertEqual(raw.count(b"feedback passing module finished"), 1)

    def test_failing_module_writes_fail(self) -> None:
        self.assertNotEqual(self.run_feedback("FeedbackFail"), 0, self.log.read_text())
        raw = self.assert_record("FeedbackFail", "fail")
        self.assertIn(b"feedback failing module reached execution", raw)

    def test_terminated_run_writes_interrupted(self) -> None:
        self.assertNotEqual(self.run_feedback("FeedbackPass", interrupted=True), 0,
                            self.log.read_text())
        raw = self.assert_record("FeedbackPass", "interrupted")
        self.assertEqual(raw.count(b"feedback passing module entered"), 1)
        self.assertNotIn(b"feedback passing module finished", raw)


class FeedbackTests(unittest.TestCase):
    def test_application_log_codec_preserves_exact_values(self) -> None:
        mantissa = 1234567890123456789012345678901234567890123456789
        expected = Decimal("123456789012.3456789012345678901234567890123456789")
        document = {"schema": 2, "session": "codec", "sequence": 0, "parents": [],
                    "monotonicMilliseconds": 0, "event": "codec.value", "data": {
                        "root": 6, "nodes": [
                            ["num", mantissa, 37], ["str", "quoted \"value\"\nλ"],
                            ["bool", True], ["null"],
                            ["obj", [["number", 0], ["text", 1], ["flag", 2], ["empty", 3]]],
                            ["arr", [4, 4]], ["obj", [["items", 5]]]]}}
        decoded = loads_application_event(json.dumps(document, ensure_ascii=False))
        first, second = decoded["data"]["items"]
        self.assertIs(first, second, "decoding expanded a repeated complete JSON object")
        self.assertEqual(first["number"].as_tuple(), expected.as_tuple())
        self.assertEqual(first["text"], 'quoted "value"\nλ')
        encoded = dumps_exact_json(decoded)
        self.assertEqual(json.loads(encoded, parse_float=Decimal), decoded)
        self.assertEqual(loads_application_event(dumps_exact_json({**decoded, "schema": 1})),
                         {**decoded, "schema": 1})
        for root, value in [(0, expected), (1, first["text"]), (2, True), (3, None),
                            (4, first), (5, [first, second])]:
            with self.subTest(root=root):
                wire = {**document, "data": {**document["data"], "root": root}}
                actual = loads_application_event(json.dumps(wire, ensure_ascii=False))
                self.assertEqual(actual["data"], value)
                legacy = {**actual, "schema": 1}
                self.assertEqual(loads_application_event(dumps_exact_json(legacy)), legacy)
        for graph, message in [
            ({"root": 0, "nodes": [["null"]], "extra": None}, "root and node table"),
            ({"root": 0, "nodes": [["arr", [0]]]}, "forward"),
            ({"root": 1, "nodes": [["null"], ["obj", [["x", 0], ["x", 0]]]]},
             "duplicate"),
            ({"root": True, "nodes": [["null"]]}, "root"),
            ({"root": 0, "nodes": [["bool", 1]]}, "constructor"),
            ({"root": 0, "nodes": [["num", 1, -1]]}, "constructor"),
        ]:
            with self.subTest(graph=graph), self.assertRaisesRegex(ValueError, message):
                loads_application_event(json.dumps({**document, "data": graph}))

    def collect_trace(self, context_file: Path, shared_setup: float, directory: Path) -> tuple[int, dict]:
        result = subprocess.run(
            [sys.executable, "-c",
             "import json, sys\n"
             "from pathlib import Path\n"
             "sys.path.insert(0, sys.argv[1])\n"
             "from feedback_records import collect_computations\n"
             "from application_log import dumps_exact_json\n"
             "summary = collect_computations(Path(sys.argv[2]), float(sys.argv[3]))\n"
             "print(dumps_exact_json(summary))\n"
             "raise SystemExit(0 if summary['complete'] else 1)\n",
             str(ROOT / "scripts"), str(context_file), str(shared_setup)],
            cwd=directory, stdout=subprocess.PIPE, stderr=subprocess.STDOUT, text=True, check=False)
        (directory / "collector.log").write_text(result.stdout)
        summary = context_file.with_name("computation-summary.json")
        self.assertTrue(summary.is_file(), result.stdout)
        return result.returncode, json.loads(summary.read_text())

    def assert_run_records(self, record: dict, module: str, completed: bool) -> dict:
        run = (ROOT / record["log"]).parent
        self.assertEqual(run.parent, ROOT / "timing/logs")
        self.assertTrue((run / "output.log.gz").is_file())
        self.assertTrue((run / "context.json").is_file())
        events = [json.loads(line) for line in (run / "events.jsonl").read_text().splitlines()]
        self.assertEqual(events[0]["event"], "run.started")
        self.assertEqual(events[-1]["event"], "run.finished")
        modules = [json.loads(line) for line in (ROOT / "timing/modules.jsonl").read_text().splitlines()]
        selected = [entry for entry in events
                    if entry.get("run") == record["run"] and entry.get("module") == module]
        self.assertTrue(selected, "the current module has no durable timing record")
        result = selected[-1]
        self.assertEqual(result["complete"], completed)
        self.assertEqual(result["revision"], record["revision"])
        self.assertEqual(result["environment"], record["environment"])
        self.assertEqual(result["context"], str((run / "context.json").relative_to(ROOT)))
        if completed:
            self.assertEqual(selected[0]["event"], "module.started")
            self.assertEqual(result["event"], "module.finished")
            self.assertEqual(result["status"], 0)
            source = ROOT / result["source"]
            self.assertEqual(result["input_sha256"], hashlib.sha256(source.read_bytes()).hexdigest())
            self.assertGreater(result["seconds"], 0)
            self.assertAlmostEqual(result["inclusive_seconds"],
                                   result["seconds"] + result["shared_setup_seconds"])
        else:
            self.assertEqual(result["event"], "module.not_run")
            self.assertIsNone(result["seconds"])
            self.assertIsNone(result["status"])
        compact = [entry for entry in modules
                   if entry.get("run_id") == record["run"] and entry.get("target") == module]
        self.assertEqual(len(compact), 1)
        row = compact[0]
        self.assertEqual(set(row), TIMING_FIELDS)
        self.assertEqual(row["revision"], record["revision"])
        self.assertEqual(row["parent_run"], record["parent_run"])
        self.assertEqual(row["environment"], {
            key: record["environment"][key] for key in ("lean", "image_digest")})
        self.assertEqual(row["status"], "pass" if completed else
                         "interrupted" if record.get("interruption_signal") else "fail")
        self.assertEqual(row["input_sha256"], record["inputs"].get(result["source"]))
        self.assertEqual(row["log_path"], record["log"])
        self.assertEqual(row["log_sha256"],
                         hashlib.sha256((ROOT / row["log_path"]).read_bytes()).hexdigest())
        if completed:
            self.assertEqual(row["utc_start"], result["utc"])
            self.assertEqual(row["seconds"], result["seconds"])
        ignored = subprocess.run(
            ["git", "check-ignore", str(run.relative_to(ROOT))], cwd=ROOT,
            stdout=subprocess.PIPE, text=True, check=False)
        self.assertEqual(ignored.returncode, 0, f"raw timing logs are not ignored: {ignored.stdout}")
        tracked = subprocess.run(
            ["git", "check-ignore", "timing/modules.jsonl", "timing/acceptance.jsonl",
             "timing/computations.jsonl"], cwd=ROOT, stdout=subprocess.PIPE, text=True, check=False)
        self.assertEqual(tracked.returncode, 1, f"timing records are ignored: {tracked.stdout}")
        return result

    def test_argument_failures_have_current_durable_records(self) -> None:


        reason = "Record the original invalid focused selection before native work"
        combined = "CasRuntime.LiteralTests CasRuntime.NativeFieldPrefixTests"
        controls = [
            (["loop", ""], [], "", "select at least one test module; an empty selection cannot run"),
            (["slow", reason, combined], [combined], reason, f"not a local Lean module: {combined}"),
        ]
        records = ROOT / "timing/runs.jsonl"
        for arguments, targets, expected_reason, diagnostic in controls:
            with self.subTest(command=arguments):
                previous = len(records.read_text().splitlines()) if records.exists() else 0
                result = subprocess.run(
                    ["just", *arguments], cwd=ROOT, stdout=subprocess.PIPE,
                    stderr=subprocess.STDOUT, text=True, check=False)
                self.assertEqual(result.returncode, 2, result.stdout)
                self.assertIn(f"feedback: {diagnostic}", result.stdout)
                rows = [json.loads(line) for line in records.read_text().splitlines()[previous:]]
                current = [row for row in rows
                           if row.get("command") == ["scripts/feedback.sh", *arguments]]
                self.assertEqual(len(current), 1, result.stdout)
                record = current[0]
                self.assertEqual(record["kind"], arguments[0])
                self.assertEqual(record["reason"], expected_reason)
                self.assertEqual(record["targets"], targets)
                self.assertEqual(record["sources"], [])
                self.assertEqual(record["acceptance"], [])
                self.assertEqual(record["status"], 2)
                self.assertEqual(record["execution_status"], 2)
                self.assertEqual(record["context_status"], "pending")
                self.assertFalse(record["attempted"])
                self.assertEqual(record["attempted_sources"], [])
                self.assertTrue(all(phase["status"] is None and phase["seconds"] == 0
                                    for phase in record["phases"].values()))
                run = (ROOT / record["context"]).parent
                self.assertEqual(run.parent, ROOT / "timing/logs")
                context = json.loads((run / "context.json").read_text())
                self.assertEqual(context["command"], ["scripts/feedback.sh", *arguments])
                self.assertEqual(context["targets"], targets)
                self.assertEqual(context["utc"], record["utc"])
                self.assertEqual(context["started_monotonic_ns"], record["started_monotonic_ns"])
                self.assertEqual(json.loads((run / "result.json").read_text()), record)
                events = [json.loads(line) for line in (run / "events.jsonl").read_text().splitlines()]
                self.assertEqual([event["event"] for event in events], ["run.started", "run.finished"])
                self.assertEqual(events[0]["utc"], context["utc"])
                self.assertTrue(all(event["run"] == record["run"] for event in events))
                self.assertEqual(events[-1]["status"], 2)
                self.assertEqual(list((run / "steps").glob("*.json")), [])
                self.assertEqual(record["computations"]["records"], 0)
                self.assertEqual(record["computations"]["logs"], [])
                log = read_log(ROOT / record["log"])
                self.assertIn(f"feedback: {diagnostic}", log)
                self.assertIn(f"{arguments[0]}: execution status 2; status 2", log)

    def test_native_preparation_failure_retains_actual_diagnostic(self) -> None:
        directory = ROOT / "timing/logs/feedback-tests"
        directory.mkdir(parents=True, exist_ok=True)
        control = Path(tempfile.mkdtemp(prefix="native-preparation-failure-", dir=directory))
        checkout = control / "checkout"
        for name in ["justfile", "lean-toolchain", "scripts/feedback.sh", "scripts/container.sh",
                     "scripts/feedback_records.py", "scripts/application_log.py",
                     "scripts/acceptance_inputs.py", "scripts/check_acceptance_permanent.py"]:
            target = checkout / name
            target.parent.mkdir(parents=True, exist_ok=True)
            shutil.copy2(ROOT / name, target)
        manifest = json.loads((ROOT / "lake-manifest.json").read_text())
        manifest["packages"] = []
        manifest["name"] = "feedback_preparation_failure"
        (checkout / "lake-manifest.json").write_text(json.dumps(manifest) + "\n")
        marker = "native feedback preparation failure control"
        (checkout / "lakefile.lean").write_text(
            "import Lake\nopen Lake DSL\npackage feedback_preparation_failure\n"
            f"#eval (throw (IO.userError {json.dumps(marker)}) : IO Unit)\n")
        (checkout / "PreparationFailure.lean").write_text("#check Nat\n")
        result = subprocess.run(["just", "loop", "PreparationFailure"], cwd=checkout,
                                capture_output=True, text=True, check=False, timeout=120)
        output = result.stdout + result.stderr
        (control / "public-loop.log").write_text(output)
        self.assertNotEqual(result.returncode, 0, output)
        self.assertIn(marker, output)
        record = json.loads((checkout / "timing/runs.jsonl").read_text().splitlines()[-1])
        self.assertEqual(record["status"], result.returncode)
        self.assertEqual(record["context_status"], "pending")
        self.assertGreater(record["preparation_seconds"], 0)
        self.assertFalse(record["attempted"])
        self.assertTrue(all(phase["status"] is None for phase in record["phases"].values()))
        self.assertIn(marker, read_log(checkout / record["log"]))
        run = (checkout / record["context"]).parent
        events = [json.loads(line) for line in (run / "events.jsonl").read_text().splitlines()]
        self.assertEqual(events[0]["event"], "run.started")
        self.assertEqual(events[-1]["event"], "run.finished")

    def test_dependencies_follow_resolved_package_selection(self) -> None:


        selected = json.loads(subprocess.check_output(
            ["lake", "--log-level=error", "run", "feedback-context"], cwd=ROOT, text=True))
        module = "CasCatalogue.FeedbackMissingConsumer"
        self.assertFalse((ROOT / (module.replace(".", "/") + ".lean")).exists())
        result = subprocess.run(["just", "loop", module], cwd=ROOT, check=False)
        self.assertEqual(result.returncode, 2)
        record = json.loads((ROOT / "timing/runs.jsonl").read_text().splitlines()[-1])
        self.assertEqual(record["targets"], [module])
        expected = {package["key"]: package for package in selected["packages"][1:]}
        actual = {package["key"]: package for package in record["dependencies"]}
        self.assertEqual(actual.keys(), expected.keys())
        for key, package in expected.items():
            with self.subTest(package=key):
                path = Path(package["path"]).resolve()
                self.assertEqual(actual[key]["path"], str(path))
                revision = subprocess.check_output(
                    ["git", "-C", str(path), "rev-parse", "HEAD"], text=True).strip()
                self.assertEqual(actual[key]["revision"], revision)
                self.assertEqual(actual[key]["matches_manifest_path"],
                                 str(path) == actual[key]["manifest_path"])
                configuration = Path(package["configuration"])
                self.assertEqual(actual[key]["configuration"], str(configuration.resolve()))
        self.assertEqual(record["resolution"], selected)
        self.assert_run_records(record, module, completed=False)

    def test_missing_consumer_invalidates_previous_report(self) -> None:
        module = "CasCatalogue.FeedbackMissingConsumer"
        source = module.replace(".", "/") + ".lean"
        self.assertFalse((ROOT / source).exists(), "the missing-source control must be absent")
        subprocess.run(
            ["just", "loop", "+CasCatalogue.TestSuite:leanArts", "ellipses"],
            cwd=ROOT, check=True,
        )
        report = ROOT / ".tmp/accept-run.json"
        previous = report.read_bytes()
        self.assertIn("ellipses.naturals", {row["id"] for row in json.loads(previous)})
        result = subprocess.run(["just", "loop", module, "ellipses"], cwd=ROOT, check=False)
        self.assertNotEqual(result.returncode, 0)
        self.assertFalse(report.exists(), "the missing consumer left an earlier report as current")
        record = json.loads((ROOT / "timing/runs.jsonl").read_text().splitlines()[-1])
        self.assertEqual(record["targets"], [module])
        self.assertEqual(record["status"], 2)
        self.assertFalse(record["attempted"])
        self.assertTrue(all(phase["status"] is None for phase in record["phases"].values()))
        self.assertIsNone(record["inputs"][source])
        self.assertEqual(Path(ROOT / record["log"]).with_name("prior-accept-run.json").read_bytes(),
                         previous)
        self.assert_run_records(record, module, completed=False)

    def test_warm_consumer_executes_again(self) -> None:
        manifest = ROOT / ".tmp/kernel-session-leaves.json"
        command = ["just", "loop", "CasRuntime.SessionTests"]
        if not manifest.exists():
            subprocess.run(command, cwd=ROOT, check=True)
        previous = manifest.stat().st_mtime_ns
        result = subprocess.run(command, cwd=ROOT, check=False)
        self.assertEqual(result.returncode, 0, "the original public consumer must pass")
        self.assertGreater(
            manifest.stat().st_mtime_ns,
            previous,
            "a warm loop replayed the previous elaboration instead of executing the consumer",
        )
        record = json.loads((ROOT / "timing/runs.jsonl").read_text().splitlines()[-1])
        self.assert_run_records(record, "CasRuntime.SessionTests", completed=True)
        summary = record["computations"]
        self.assertTrue(summary["complete"], summary["malformed"])
        all_rows = [json.loads(line) for line in
                    (ROOT / summary["record_file"]).read_text().splitlines()]
        direct = [row for row in all_rows if row["unit"] == "statement" and row["file_run"] is None]
        self.assertTrue(direct, "direct public session calls lost their computation records")
        originals = {}
        original_rejections = {}
        for log in summary["logs"]:
            events = [loads_application_event(line) for line in (ROOT / log).read_text().splitlines()]
            wrappers = {event["sequence"] for event in events if event["event"] == "computation.started"}
            for event in events:
                if (event["event"] == "statement.started" and
                        not any(parent in wrappers for parent in event["parents"])):
                    originals[(event["session"], event["sequence"])] = event
                elif (event["event"] == "statement.parseFailed" and
                        not any(parent in wrappers for parent in event["parents"])):
                    original_rejections[(event["session"], event["sequence"])] = event
        measured = {(row["session"], row["start"]["sequence"]): row for row in direct
                    if "start" in row}
        self.assertEqual(measured.keys(), originals.keys())
        self.assertTrue(any(row["setup_seconds"] > 0 for row in direct),
                        "retained direct definitions lost their later setup cost")
        steps = [json.loads(path.read_text()) for path in
                 (ROOT / record["context"]).parent.joinpath("steps").glob("*.json")]
        module_steps = [step for step in steps if step["phase"] == "execution"]
        self.assertEqual(len(module_steps), 1)
        rejected = {(row["session"], row["completion"]["sequence"]): row for row in direct
                    if row.get("parse_failure")}
        self.assertTrue(original_rejections, "the public consumer did not exercise a parse rejection")
        self.assertIn("let timingRejected :=",
                      {event["data"]["source"] for event in original_rejections.values()})
        self.assertEqual(rejected.keys(), original_rejections.keys(),
                         "a completed public parse rejection lost its computation record")
        self.assertEqual(len(rejected), sum(bool(row.get("parse_failure")) for row in direct))
        for key, row in rejected.items():
            event = original_rejections[key]
            data = event["data"]
            self.assertTrue(row["complete"])
            self.assertNotIn("start", row)
            self.assertEqual(row["completion"], event)
            self.assertEqual(row["outcome"], data)
            self.assertEqual(row["file"], "CasRuntime/SessionTests.lean")
            self.assertEqual(row["input_sha256"], record["inputs"][row["file"]])
            self.assertEqual(row["statement_sha256"],
                             hashlib.sha256(data["source"].encode()).hexdigest())
            self.assertEqual(row["step"], module_steps[0]["step"])
            self.assertEqual(data["kind"], "invalid")
            self.assertEqual(data["stratum"], "invalid")
            self.assertTrue(data["fails"])
            self.assertFalse(data["attempted"])
            self.assertFalse(data["published"])
            self.assertFalse(data["retainsSetup"])
            self.assertLessEqual(data["startedMonotonicMilliseconds"] + data["milliseconds"],
                                 event["monotonicMilliseconds"])
            self.assertEqual(row["execution_seconds"], data["milliseconds"] / 1000)
            self.assertEqual(row["setup_seconds"], data["cumulativeSetupMilliseconds"] / 1000)
            self.assertAlmostEqual(row["seconds"], row["execution_seconds"] + row["setup_seconds"])
            self.assertAlmostEqual(row["inclusive_seconds"], row["seconds"] +
                                   row["shared_setup_seconds"] + row["shared_worker_setup_seconds"] +
                                   row["shared_session_setup_seconds"])
        for key, row in measured.items():
            self.assertTrue(row["complete"])
            self.assertEqual(row["start"], originals[key])
            self.assertEqual(row["file"], "CasRuntime/SessionTests.lean")
            self.assertEqual(row["input_sha256"], record["inputs"][row["file"]])
            self.assertEqual(row["statement_sha256"],
                             hashlib.sha256(originals[key]["data"]["source"].encode()).hexdigest())
            self.assertEqual(row["step"], module_steps[0]["step"])
            self.assertEqual(row["shared_session_setup_seconds"],
                             row["session_preparation"]["data"]["milliseconds"] / 1000)
            self.assertAlmostEqual(row["inclusive_seconds"], row["execution_seconds"] +
                                   row["setup_seconds"] + row["shared_setup_seconds"] +
                                   row["shared_worker_setup_seconds"] + row["shared_session_setup_seconds"])
        fixture = (ROOT / "tests/runtime/application_log.cas").resolve()
        rows = [row for row in all_rows if Path(row["file"]).resolve() == fixture]
        self.assertTrue(rows, "the original public file lost its computation records")
        source_hash = hashlib.sha256(fixture.read_bytes()).hexdigest()
        for file_run in {row["file_run"] for row in rows}:
            observed = [row for row in rows if row["file_run"] == file_run]
            top = [row for row in observed if row["unit"] == "statement"]
            nested = [row for row in observed if row["unit"] == "nested_statement"]
            self.assertEqual(len(top), 6)
            self.assertEqual(len(nested), 2)
            self.assertIn("logging.direct", {row["id"] for row in top})
            self.assertIn("logging.nested", {row["id"] for row in nested})
            self.assertEqual(sorted(row["ordinal"] for row in nested), [0, 1])
            self.assertTrue(any(row["id"].startswith("(statement)") for row in nested),
                            "the nested definition lost its own measured record")
            by_key = {row["computation"]: row for row in observed}
            for row in observed:
                self.assertTrue(row["complete"])
                self.assertEqual(row["input_sha256"], source_hash)
                self.assertEqual(row["revision"], record["revision"])
                self.assertEqual(row["environment"], record["environment"])
                self.assertAlmostEqual(row["seconds"],
                                       row["execution_seconds"] + row["setup_seconds"])
                self.assertAlmostEqual(row["inclusive_seconds"], row["seconds"] +
                                       row["shared_setup_seconds"] + row["shared_worker_setup_seconds"] +
                                       row["shared_session_setup_seconds"])
            for row in nested:
                root = by_key[row["root_computation"]]
                self.assertEqual(row["parent_computation"], root["computation"])
                self.assertIn(root["start"]["sequence"], row["start"]["parents"])
                self.assertEqual(row["completion"]["parents"][-1], row["start"]["sequence"])
                self.assertEqual(row["outcome"], row["completion"]["data"])
                self.assertEqual(row["outcome"]["publication"], "pending enclosing cell")
                self.assertEqual(row["enclosing_outcome"], root["completion"]["data"]["result"])
                self.assertTrue(row["enclosing_published"])
                self.assertGreaterEqual(row["setup_seconds"], root["setup_seconds"])
            ordered = sorted(nested, key=lambda row: row["ordinal"])
            self.assertEqual(ordered[0]["preceding_setup_seconds"], 0)
            self.assertGreaterEqual(ordered[1]["preceding_setup_seconds"],
                                    ordered[0]["execution_seconds"])

        seeded = [row for row in direct if row.get("start", {}).get("data", {}).get("source") ==
                  "let timingPrepared := 17 + 29 in ℤ"]
        self.assertEqual(len(seeded), 1)
        seed = seeded[0]
        self.assertEqual(seed["outcome"]["kind"], "holds")
        self.assertTrue(seed["outcome"]["retainsSetup"])
        self.assertGreater(seed["execution_seconds"], 0)
        continued = sorted((row for row in rows if row["session"] == seed["session"] and
                            row["unit"] == "statement"), key=lambda row: row["ordinal"])
        self.assertEqual(len(continued), 6)
        self.assertEqual(len({row["file_run"] for row in continued}), 1)
        events = [loads_application_event(line) for line in
                  (ROOT / seed["source_log"]).read_text().splitlines()]
        file_starts = [event for event in events if event["event"] == "file.started" and
                       event["data"]["fileRun"] == continued[0]["file_run"]]
        self.assertEqual(len(file_starts), 1)
        file_setup = file_starts[0]["data"]["sharedFileSetupMilliseconds"]
        expected_setup = (seed["completion"]["data"]["cumulativeSetupMilliseconds"] +
                          seed["completion"]["data"]["milliseconds"] + file_setup)
        for row in continued:
            self.assertEqual(row["start"]["data"]["cumulativeSetupMilliseconds"], expected_setup)
            self.assertEqual(row["completion"]["data"]["setupMilliseconds"], expected_setup)
            self.assertEqual(row["completion"]["data"]["sharedFileSetupMilliseconds"], file_setup)
            self.assertEqual(row["setup_seconds"], expected_setup / 1000)
            if row["ordinal"] < 4:
                expected_setup += row["completion"]["data"]["executionMilliseconds"]
        later = [row for row in direct if row.get("start", {}).get("data", {}).get("source") ==
                 "assert timingPrepared = 46 in ℤ"]
        self.assertEqual(len(later), 1)
        self.assertEqual(later[0]["session"], seed["session"])
        self.assertEqual(later[0]["outcome"]["kind"], "holds")
        self.assertEqual(later[0]["setup_seconds"], expected_setup / 1000)



        selected = next(row for row in rows
                        if row["unit"] == "nested_statement" and row["id"] == "logging.nested")
        source_log = ROOT / selected["source_log"]
        original = source_log.read_bytes()
        missing = {selected["start"]["sequence"], selected["completion"]["sequence"]}
        lines = original.splitlines(keepends=True)
        retained = [line for line in lines if json.loads(line)["sequence"] not in missing]
        self.assertEqual(len(retained), len(lines) - 2)
        directory = ROOT / "timing/logs/feedback-tests"
        directory.mkdir(parents=True, exist_ok=True)
        control = Path(tempfile.mkdtemp(prefix="missing-child-pair-", dir=directory))
        copied_run = control / "run"
        copied_log = copied_run / "application" / source_log.name
        shutil.copytree((ROOT / record["context"]).parent / "application", copied_run / "application",
                        copy_function=lambda src, dst: shutil.copy2(src, dst)
                        if Path(src).name == source_log.name else os.link(src, dst))
        copied_log.write_bytes(b"".join(retained))
        context_file = copied_run / "context.json"
        context_file.write_bytes((ROOT / record["context"]).read_bytes())
        shutil.copytree((ROOT / record["context"]).parent / "steps", copied_run / "steps")
        shared_setup = record["preparation_seconds"] + record["phases"]["build"]["seconds"]
        original_record_size = (ROOT / "timing/computations.jsonl").stat().st_size
        status, damaged = self.collect_trace(context_file, shared_setup, control)
        self.assertNotEqual(status, 0)
        self.assertFalse(damaged["complete"])
        self.assertTrue(any("sequence" in failure for failure in damaged["malformed"]),
                        damaged["malformed"])
        self.assertTrue(all(not file["complete"] for file in damaged["files"]
                            if file["session"] == selected["session"]))
        survived = [json.loads(line) for line in
                    (copied_run / "computations.jsonl").read_text().splitlines()]
        enclosing = next(row for row in survived
                         if row["computation"] == selected["root_computation"])
        self.assertIn("completion", enclosing, "a sequence gap erased an actual later terminal result")
        self.assertEqual(source_log.read_bytes(), original)
        self.assertEqual((ROOT / "timing/computations.jsonl").stat().st_size, original_record_size)



        terminal_index = next(index for index, line in enumerate(lines)
                              if json.loads(line)["sequence"] == selected["completion"]["sequence"])
        wire = json.loads(lines[terminal_index])
        self.assertEqual(wire["schema"], 2, "the current native consumer did not use the graph transport")
        expanded = loads_application_event(lines[terminal_index])
        expected_rows = {row["computation"]: row for row in
                         (json.loads(line, parse_float=Decimal) for line in
                          (ROOT / summary["record_file"]).read_text().splitlines())}
        variants = [
            ("schema1", {**expanded, "schema": 1}, None),
            ("unknown-schema", {**wire, "schema": 3}, "unsupported application log schema"),
            ("forward-reference", {**wire, "data": {"root": 0, "nodes": [["arr", [0]]]}}, "forward"),
        ]
        for name, replacement, error in variants:
            with self.subTest(transport=name):
                control = Path(tempfile.mkdtemp(prefix=f"application-{name}-", dir=directory))
                copied_run = control / "run"
                copied_log = copied_run / "application" / source_log.name
                shutil.copytree((ROOT / record["context"]).parent / "application", copied_run / "application",
                                copy_function=lambda src, dst: shutil.copy2(src, dst)
                                if Path(src).name == source_log.name else os.link(src, dst))
                copied_lines = list(lines)
                copied_lines[terminal_index] = (dumps_exact_json(replacement) + "\n").encode()
                copied_log.write_bytes(b"".join(copied_lines))
                context_file = copied_run / "context.json"
                context_file.write_bytes((ROOT / record["context"]).read_bytes())
                shutil.copytree((ROOT / record["context"]).parent / "steps", copied_run / "steps")
                status, observed = self.collect_trace(context_file, shared_setup, control)
                if error is None:
                    self.assertEqual(status, 0)
                    self.assertTrue(observed["complete"], observed["malformed"])
                    restored = [json.loads(line, parse_float=Decimal) for line in
                                (copied_run / "computations.jsonl").read_text().splitlines()]
                    self.assertEqual({row["computation"] for row in restored}, set(expected_rows))
                    for row in restored:
                        self.assertTrue(row["complete"])
                        self.assertEqual(row["completion"]["data"],
                                         expected_rows[row["computation"]]["completion"]["data"])
                        for field in ("seconds", "execution_seconds", "setup_seconds",
                                      "shared_setup_seconds", "shared_worker_setup_seconds",
                                      "shared_session_setup_seconds", "inclusive_seconds"):
                            self.assertEqual(row[field], expected_rows[row["computation"]][field])
                else:
                    self.assertNotEqual(status, 0)
                    self.assertFalse(observed["complete"])
                    self.assertTrue(any(error in failure for failure in observed["malformed"]),
                                    observed["malformed"])
        self.assertEqual(source_log.read_bytes(), original)
        self.assertEqual((ROOT / "timing/computations.jsonl").stat().st_size, original_record_size)



    def test_module_and_statement_records_cover_public_run(self) -> None:

        module = "CasCompiler.ContextTests"
        result = subprocess.run(
            ["just", "loop", module, "ellipses"], cwd=ROOT,
            stdout=subprocess.PIPE, stderr=subprocess.STDOUT, text=True, check=False)
        record = json.loads((ROOT / "timing/runs.jsonl").read_text().splitlines()[-1])
        self.assertEqual(record["targets"], [module])
        self.assertEqual(record["acceptance"], ["ellipses"])
        self.assertEqual(record["status"], result.returncode, result.stdout)
        self.assertEqual(record["phases"]["build"]["status"], 0, result.stdout)
        self.assertEqual(record["phases"]["execution"]["status"], 0, result.stdout)
        self.assert_run_records(record, module, completed=True)
        acceptance = current_acceptance_result()
        self.assertEqual(acceptance["parent_run"], record["run"])
        self.assertEqual(acceptance["files"], ["ellipses"])
        self.assertEqual(acceptance["status"], record["phases"]["acceptance"]["status"],
                         result.stdout)


        self.assertEqual(record["execution_status"], acceptance["status"], result.stdout)
        expected_status = record["execution_status"] or int(
            record["over_limit"] or not record["computations"]["complete"])
        self.assertEqual(result.returncode, expected_status, result.stdout)
        self.assertTrue(acceptance["complete"])
        self.assertTrue(acceptance["timing_complete"])
        self.assertEqual(acceptance["context_status"], "complete")
        self.assertEqual(acceptance["revision"], record["revision"])
        self.assertEqual(acceptance["environment"], record["environment"])
        run = ROOT / acceptance["run"]
        self.assertEqual(run.parent, ROOT / "timing/logs")
        compact = [json.loads(line) for line in
                   (ROOT / "timing/acceptance.jsonl").read_text().splitlines()]
        compact = [row for row in compact if row.get("run_id") == run.name]
        self.assertEqual(len(compact), 1)
        self.assertEqual(set(compact[0]), TIMING_FIELDS)
        self.assertEqual(compact[0]["target"], "tests/acceptance/ellipses.cas")
        self.assertEqual(compact[0]["parent_run"], record["run"])
        self.assertEqual(compact[0]["revision"], acceptance["revision"])
        self.assertEqual(compact[0]["environment"], {
            key: acceptance["environment"][key] for key in ("lean", "image_digest")})
        self.assertEqual(compact[0]["status"], "fail" if acceptance["status"] else "pass")
        self.assertEqual(compact[0]["input_sha256"],
                         hashlib.sha256((ROOT / "tests/acceptance/ellipses.cas").read_bytes()).hexdigest())
        self.assertEqual(compact[0]["log_path"], acceptance["log"])
        self.assertEqual(compact[0]["log_sha256"],
                         hashlib.sha256((ROOT / compact[0]["log_path"]).read_bytes()).hexdigest())
        summary = acceptance["computations"]
        rows = [json.loads(line) for line in
                (ROOT / summary["record_file"]).read_text().splitlines()]
        self.assertTrue(rows)
        self.assertEqual(len(summary["files"]), 1)
        file_timing = summary["files"][0]
        self.assertEqual(compact[0]["seconds"],
                         (file_timing["completion"]["monotonicMilliseconds"] -
                          file_timing["begin"]["monotonicMilliseconds"]) / 1000)
        top = [row for row in rows if row["unit"] == "statement"]
        self.assertEqual(summary["files"][0]["statements"], len(top))
        self.assertEqual(summary["files"][0]["executed"], len(top))
        self.assertTrue(summary["files"][0]["complete"])
        expected = set(json.loads((run / "ellipses.inventory.json").read_text())["assertions"])
        self.assertLessEqual(expected, {row["id"] for row in rows})
        self.assertGreater(len(rows), len(expected), "successful setup definitions lost their records")
        source_hash = hashlib.sha256((ROOT / "tests/acceptance/ellipses.cas").read_bytes()).hexdigest()
        for row in rows:
            with self.subTest(computation=row["computation"]):
                self.assertTrue(row["complete"])
                self.assertEqual(row["file"], "tests/acceptance/ellipses.cas")
                self.assertEqual(row["input_sha256"], source_hash)
                self.assertEqual(row["revision"], record["revision"])
                self.assertEqual(row["environment"], acceptance["environment"])
                self.assertEqual(row["start"]["data"]["computation"], row["computation"])
                self.assertEqual(row["completion"]["data"]["computation"], row["computation"])
                self.assertGreaterEqual(row["seconds"], row["setup_seconds"])
                self.assertAlmostEqual(
                    row["inclusive_seconds"],
                    row["seconds"] + row["shared_setup_seconds"] + row["shared_worker_setup_seconds"] +
                    row["shared_session_setup_seconds"])
                self.assertTrue((ROOT / row["source_log"]).is_file())



        run_events = [json.loads(line) for line in (run / "events.jsonl").read_text().splitlines()]
        self.assertEqual(run_events[-1]["event"], "run.finished")
        self.assertEqual(run_events[-1]["status"], acceptance["status"])
        if acceptance["status"]:
            self.assertTrue(all(row["complete"] for row in rows))
            self.assertTrue(any(row["outcome"]["fails"] for row in top))



        worker_rows = [row for row in rows if row["worker"] is not None]
        self.assertTrue(worker_rows, "the public acceptance worker lost its declared identity")
        worker = worker_rows[0]["worker"]
        starts = [(path, json.loads(path.read_text())) for path in (run / "steps").glob("*.json")]
        starts = [(path, step) for path, step in starts
                  if step["phase"] == f"acceptance-worker{worker}"]
        self.assertEqual(len(starts), 1)
        start_path, original_start = starts[0]
        source_log = ROOT / worker_rows[0]["source_log"]
        original_log = source_log.read_bytes()
        events = [loads_application_event(line) for line in original_log.splitlines()]
        self.assertEqual(events[0]["data"]["feedbackWorker"], worker)
        first_file = min(event["monotonicMilliseconds"] for event in events
                         if event["event"] == "file.begin")
        directory = ROOT / "timing/logs/feedback-tests"
        directory.mkdir(parents=True, exist_ok=True)
        original_record_size = (ROOT / "timing/computations.jsonl").stat().st_size
        for fault, message in [("missing", "startup boundary"), ("late", "before its recorded start")]:
            with self.subTest(startup=fault):
                control = Path(tempfile.mkdtemp(prefix=f"worker-start-{fault}-", dir=directory))
                copied_run = control / "run"
                copied_log = copied_run / "application" / source_log.name
                copied_log.parent.mkdir(parents=True)
                copied_log.write_bytes(original_log)
                context_file = copied_run / "context.json"
                context_file.write_bytes((run / "context.json").read_bytes())
                if fault == "late":
                    altered = dict(original_start)
                    altered["started_monotonic_ns"] = (first_file + 1) * 1_000_000
                    target = copied_run / "steps" / start_path.name
                    target.parent.mkdir(parents=True)
                    target.write_text(json.dumps(altered) + "\n")
                status, damaged = self.collect_trace(
                    context_file, worker_rows[0]["shared_setup_seconds"], control)
                self.assertNotEqual(status, 0)
                self.assertFalse(damaged["complete"])
                self.assertTrue(any(message in failure for failure in damaged["malformed"]),
                                damaged["malformed"])
                survived = [json.loads(line) for line in
                            (copied_run / "computations.jsonl").read_text().splitlines()]
                self.assertTrue(survived)
                for row in survived:
                    self.assertFalse(row["complete"])
                    self.assertIsNone(row["shared_worker_setup_seconds"])
                    self.assertIsNone(row["inclusive_seconds"])
                    self.assertIn("completion", row, "missing setup erased actual completed execution")
        self.assertEqual(source_log.read_bytes(), original_log)
        self.assertEqual(json.loads(start_path.read_text()), original_start)
        self.assertEqual((ROOT / "timing/computations.jsonl").stat().st_size, original_record_size)



    def test_unread_source_form_keeps_its_failure_stratum(self) -> None:
        directory = ROOT / "timing/logs/feedback-tests"
        directory.mkdir(parents=True, exist_ok=True)
        control = Path(tempfile.mkdtemp(prefix="source-stratum-", dir=directory))
        log = control / "public-loop.log"
        with log.open("w") as output:
            result = subprocess.run(
                ["just", "loop", "+CasCatalogue.TestSuite:leanArts", "polynomials"],
                cwd=ROOT, stdout=output, stderr=subprocess.STDOUT, check=False)
        self.assertNotEqual(result.returncode, 0, log.read_text())
        rows = json.loads((ROOT / ".tmp/accept-run.json").read_text())
        selected = [row for row in rows
                    if row["file"] == "tests/acceptance/polynomials.cas"
                    and row["id"] == "polynomials.degree_over_rationals"]
        self.assertEqual(len(selected), 1)
        outcome = selected[0]
        self.assertEqual(outcome["kind"], "gap")
        self.assertEqual(outcome["stratum"], "unsupportedSource")
        self.assertTrue(outcome["fails"])
        self.assertIn("polynomials.cas:24:", log.read_text())
        self.assertTrue(all("stratum" in row for row in rows))
        recorded = current_acceptance_result()
        self.assertTrue(recorded["complete"], recorded)
        self.assertTrue(recorded["timing_complete"], recorded)
        self.assertNotEqual(recorded["status"], 0)



        base = control / "old-report.json"
        head = control / "current-report.json"
        legacy = {key: value for key, value in outcome.items()
                  if key not in {"stratum", "fails"}}
        base.write_text(json.dumps([legacy]))
        head.write_text(json.dumps([outcome]))
        comparison = subprocess.run(
            [sys.executable, "scripts/check_acceptance_regression.py", str(base), str(head)],
            cwd=ROOT, capture_output=True, text=True, check=False)
        (control / "comparison.log").write_text(comparison.stdout + comparison.stderr)
        self.assertEqual(comparison.returncode, 1, comparison.stdout + comparison.stderr)
        self.assertIn("unsupportedSource", comparison.stdout)
        explicit = {**legacy, "stratum": None, "fails": True}
        head.write_text(json.dumps([explicit]))
        comparison = subprocess.run(
            [sys.executable, "scripts/check_acceptance_regression.py", str(base), str(head)],
            cwd=ROOT, capture_output=True, text=True, check=False)
        (control / "explicit-failure.log").write_text(comparison.stdout + comparison.stderr)
        self.assertEqual(comparison.returncode, 1, comparison.stdout + comparison.stderr)

    def test_changed_extension_file_fails_before_execution(self) -> None:
        directory = ROOT / "timing/logs/feedback-tests"
        directory.mkdir(parents=True, exist_ok=True)
        extension = Path("tests/acceptance/proposals/"
                         "independent-extension-reconstruction-20261024/completion")
        checkpoint = extension / "source-checkpoint.json"
        original_checkpoint = (ROOT / checkpoint).read_bytes()


        for stem, authority in [("rx01-selected-orders", "source-checkpoint"),
                                ("rx02-complete-core-action", "added-blob")]:
            with self.subTest(stem=stem):
                control = Path(tempfile.mkdtemp(prefix="changed-extension-", dir=directory))
                checkout = control / "checkout"
                selected = extension / f"{stem}.cas"
                evidence = None
                try:
                    subprocess.run(
                        ["git", "clone", "--shared", "--no-checkout", "--quiet",
                         str(ROOT), str(checkout)], check=True)
                    cloned_head = subprocess.check_output(
                        ["git", "-C", str(checkout), "rev-parse", "HEAD"], text=True).strip()
                    original = (ROOT / selected).read_bytes()
                    files = ["justfile", "scripts/feedback.sh", "scripts/container.sh",
                             "scripts/feedback_records.py", "scripts/application_log.py",
                             "scripts/acceptance_inputs.py",
                             "scripts/check_acceptance_permanent.py",
                             str(checkpoint), str(selected)]
                    for name in files:
                        target = checkout / name
                        target.parent.mkdir(parents=True, exist_ok=True)
                        shutil.copy2(ROOT / name, target)
                    positive = control / "unchanged-input.json"
                    unchanged = subprocess.run(
                        [sys.executable, "scripts/acceptance_inputs.py", str(positive),
                         "--extension", stem], cwd=checkout, capture_output=True,
                        text=True, check=False)
                    (control / "unchanged-input.log").write_text(unchanged.stdout + unchanged.stderr)
                    self.assertEqual(unchanged.returncode, 0, unchanged.stdout + unchanged.stderr)
                    observed = json.loads(positive.read_text())["files"][0]
                    self.assertFalse(observed["admitted"])
                    self.assertTrue(observed["computing"])
                    self.assertEqual(observed["authority"]["kind"], authority)
                    self.assertEqual(observed["sha256"], hashlib.sha256(original).hexdigest())
                    (checkout / selected).write_bytes(original + b"\n-- changed-source guard control\n")
                    log = control / "public-loop.log"
                    with log.open("w") as output:
                        result = subprocess.run(
                            ["just", "loop", "--extension", stem], cwd=checkout,
                            stdout=output, stderr=subprocess.STDOUT, check=False)
                    self.assertNotEqual(result.returncode, 0, log.read_text())
                    self.assertIn("extension source changed", log.read_text())
                    record = json.loads(
                        (checkout / "timing/runs.jsonl").read_text().splitlines()[-1])
                    self.assertEqual(record["context_status"], "pending")
                    self.assertEqual(record["acceptance"], ["--extension", stem])
                    self.assertIsNone(record["phases"]["build"]["status"])
                    self.assertIsNone(record["phases"]["execution"]["status"])
                    self.assertFalse((checkout / ".tmp/accept-run.json").exists())
                    self.assertEqual((ROOT / selected).read_bytes(), original)
                finally:
                    if (checkout / ".git").is_dir():
                        evidence = retain_checkout(
                            checkout, SOURCE_REVISION, [str(checkpoint), str(selected)])
                self.assertIsNotNone(evidence)
                self.assertFalse((checkout / ".git").exists())
                retained = json.loads((evidence / "manifest.json").read_text())
                self.assertEqual(retained["state"], "retained")
                self.assertEqual(retained["git_state"]["head"], cloned_head)
                self.assertIsNone(retained["git_state"]["index_sha256"])
                self.assertEqual((evidence / "authority" / selected).read_bytes(), original)
                self.assertEqual((checkout / selected).read_bytes(),
                                 original + b"\n-- changed-source guard control\n")
                retained_path = str((checkout / selected).relative_to(ROOT))
                ignored = subprocess.run(
                    ["git", "check-ignore", "--", retained_path], cwd=ROOT,
                    capture_output=True, text=True, check=False)
                self.assertEqual(ignored.returncode, 0, ignored.stdout + ignored.stderr)
                self.assertEqual(ignored.stdout.splitlines(), [retained_path])
                indexed = subprocess.check_output(
                    ["git", "ls-files", "--stage", "--", retained_path], cwd=ROOT, text=True)
                self.assertFalse(indexed, "retained raw evidence entered the Git index")
                with tempfile.TemporaryDirectory(prefix="feedback-checkout-restore-") as temporary:
                    restored = Path(temporary) / "checkout"
                    restore_checkout(evidence, restored)
                    self.assertEqual((restored / selected).read_bytes(), (checkout / selected).read_bytes())
                    self.assertEqual((restored / "timing/runs.jsonl").read_bytes(),
                                     (checkout / "timing/runs.jsonl").read_bytes())
                    self.assertEqual(subprocess.check_output(
                        ["git", "-C", str(restored), "rev-parse", "HEAD"], text=True).strip(), cloned_head)
        self.assertEqual((ROOT / checkpoint).read_bytes(), original_checkpoint)

    def test_verified_checkout_retirement_failure_remains_restorable(self) -> None:
        directory = ROOT / "timing/logs/feedback-tests"
        directory.mkdir(parents=True, exist_ok=True)
        control = Path(tempfile.mkdtemp(prefix="checkout-retirement-", dir=directory))
        checkout = control / "checkout"
        source = Path("tests/acceptance/proposals/"
                      "independent-extension-reconstruction-20261024/completion/"
                      "source-checkpoint.json")
        subprocess.run(["git", "clone", "--shared", "--no-checkout", "--quiet",
                        str(ROOT), str(checkout)], check=True)
        (checkout / source).parent.mkdir(parents=True, exist_ok=True)
        original = (ROOT / source).read_bytes()
        (checkout / source).write_bytes(original)
        failure = OSError("retirement fault control")
        real_rmtree = shutil.rmtree

        def fail_retirement(path, *arguments, **keywords):
            if Path(path) == checkout / ".git":
                (checkout / ".git/HEAD").unlink()
                raise failure
            return real_rmtree(path, *arguments, **keywords)

        with self.assertRaises(OSError) as caught:
            with patch("feedback_checkout.shutil.rmtree", side_effect=fail_retirement):
                retain_checkout(checkout, SOURCE_REVISION, [str(source)])
        self.assertIs(caught.exception, failure)
        records = list(control.glob("checkout-evidence-*/manifest.json"))
        self.assertEqual(len(records), 1)
        evidence = records[0].parent
        observed = json.loads(records[0].read_text())
        self.assertEqual(observed["state"], "retirement-failed")
        self.assertIn("verified_ns", observed)
        self.assertTrue((checkout / ".git").is_dir())
        self.assertFalse((checkout / ".git/HEAD").exists())
        self.assertEqual((checkout / source).read_bytes(), original)
        with tempfile.TemporaryDirectory(prefix="feedback-retirement-restore-") as temporary:
            restored = Path(temporary) / "checkout"
            restore_checkout(evidence, restored)
            self.assertEqual((restored / source).read_bytes(), original)
            self.assertEqual(subprocess.check_output(
                ["git", "-C", str(restored), "rev-parse", "HEAD"], text=True).strip(),
                observed["git_state"]["head"])


        real_rmtree(checkout / ".git")
        self.assertEqual((checkout / source).read_bytes(), original)

    def test_extension_is_an_unchanged_kernel_observation(self) -> None:
        directory = ROOT / "timing/logs/feedback-tests"
        directory.mkdir(parents=True, exist_ok=True)
        control = Path(tempfile.mkdtemp(prefix="extension-observation-", dir=directory))
        source = Path("tests/acceptance/proposals/"
                      "independent-extension-reconstruction-20261024/completion/"
                      "rx01-selected-orders.cas")
        original = (ROOT / source).read_bytes()
        baseline = ROOT / "CasAcceptance/Permanent/admitted.json"
        admitted_before = baseline.read_bytes()
        log = control / "public-loop.log"
        with log.open("w") as output:
            result = subprocess.run(
                ["just", "loop", "--extension", source.stem], cwd=ROOT,
                stdout=output, stderr=subprocess.STDOUT, check=False)
        recorded = current_acceptance_result()
        self.assertTrue(recorded["complete"], log.read_text())
        self.assertTrue(recorded["timing_complete"], log.read_text())
        self.assertEqual(recorded["inputs"][str(source)], hashlib.sha256(original).hexdigest())
        rows = json.loads((ROOT / ".tmp/accept-run.json").read_text())
        self.assertTrue(rows)
        self.assertTrue(all(row["file"] == str(source) for row in rows))
        self.assertTrue(all(row["inputKind"] == "extension" and not row["admitted"]
                            and row["computing"] for row in rows))
        self.assertTrue(all("stratum" in row for row in rows))
        self.assertEqual(bool(result.returncode), any(row["fails"] for row in rows))
        run = ROOT / recorded["run"]
        plan = json.loads((run / "selection.json").read_text())
        self.assertEqual(len(plan["files"]), 1)
        selected = plan["files"][0]
        self.assertFalse(selected["admitted"])
        self.assertEqual({row["id"] for row in rows if not row["id"].startswith("(statement)")},
                         set(selected["assertions"]))
        self.assertIn(" computing\n", (run / "worker0.lean").read_text())
        self.assertEqual((ROOT / source).read_bytes(), original)
        self.assertEqual(baseline.read_bytes(), admitted_before)

class SuiteTests(unittest.TestCase):
    def setUp(self) -> None:
        directory = ROOT / "timing/logs/feedback-tests"
        directory.mkdir(parents=True, exist_ok=True)
        self.directory = Path(tempfile.mkdtemp(dir=directory))

    def run_suite(self, selection: Path) -> tuple[int, list[dict[str, JsonValue]]]:
        report = self.directory / "report.json"
        source = self.directory / "consumer.lean"
        source.write_text(
            "import LeanCategories.Catalogue\nimport CasCatalogue.TestSuite\n\n"
            f'#cas_tests "{selection.relative_to(ROOT)}" '
            f'reporting "{report.relative_to(ROOT)}"\n'
        )
        result = subprocess.run(
            ["bash", "-c",
             'source scripts/container.sh; incontainer just probe "$1"',
             "feedback-regression", str(source.relative_to(ROOT))],
            cwd=ROOT, stdout=subprocess.PIPE, stderr=subprocess.STDOUT, text=True, check=False,
        )
        (self.directory / "consumer.log").write_text(result.stdout)
        self.assertTrue(report.is_file(), f"the public command produced no report: {result.stdout}")
        return result.returncode, json.loads(report.read_text())

    def test_empty_selection_is_a_current_failure(self) -> None:
        selected = self.directory / "empty"
        selected.mkdir()
        status, report = self.run_suite(selected)
        self.assertNotEqual(status, 0, "an empty selected suite must not succeed")
        self.assertTrue(any(row["kind"] == "internal" and row["fails"] for row in report))

    def test_missing_input_is_infrastructure_failure(self) -> None:
        status, report = self.run_suite(self.directory / "missing.cas")
        self.assertNotEqual(status, 0)
        self.assertEqual(len(report), 1)
        self.assertEqual(report[0]["kind"], "internal")
        self.assertTrue(report[0]["fails"])

    def test_duplicate_assertions_preserve_rows_and_fail(self) -> None:

        original = (ROOT / "tests/acceptance/numbers.cas").read_text()
        assertion = next(item for item in original.split("\n\n")
                         if item.startswith("test numbers.integers.sum "))
        selected = self.directory / "duplicate.cas"
        selected.write_text(assertion + "\n\n" + assertion + "\n")
        status, report = self.run_suite(selected)
        self.assertNotEqual(status, 0, "duplicate named assertions must fail the public command")
        self.assertEqual(sum(row["id"] == "numbers.integers.sum" for row in report), 2)
        self.assertTrue(any(row["kind"] == "internal" and row["fails"] for row in report))



class AcceptanceFeedbackTests(unittest.TestCase):
    def test_interrupted_preparation_and_build_retain_elapsed_phase(self) -> None:
        directory = ROOT / "timing/logs/feedback-tests"
        directory.mkdir(parents=True, exist_ok=True)
        for phase, required in [("preparation", {"run", "feedback-context"}),
                                ("build", {"build", "CasCatalogue.TestSuite"})]:
            with self.subTest(phase=phase):
                control = Path(tempfile.mkdtemp(prefix=f"interrupted-{phase}-", dir=directory))
                log = control / "interrupted.log"
                stopped = False
                observed = None
                with log.open("w") as output:
                    process = subprocess.Popen(
                        ["scripts/accept_files.sh", "numbers"], cwd=ROOT,
                        stdout=output, stderr=subprocess.STDOUT, start_new_session=True)
                    try:
                        deadline = time.monotonic() + 300
                        while process.poll() is None and time.monotonic() < deadline:
                            pending = [process.pid]
                            descendants = set()
                            while pending:
                                pid = pending.pop()
                                if pid in descendants:
                                    continue
                                proc = Path(f"/proc/{pid}")
                                try:
                                    descendants.add(pid)
                                    pending.extend(process_children(pid) - descendants)
                                    arguments = (proc / "cmdline").read_bytes().decode().split("\0")
                                    if ((proc / "comm").read_text().strip() != "lake"
                                            or (proc / "cwd").resolve() != ROOT
                                            or not required.issubset(arguments)):
                                        continue
                                    group = os.getpgid(pid)
                                    if (group not in descendants or os.getpgid(group) != group
                                            or Path(f"/proc/{group}/cwd").resolve() != ROOT):
                                        continue
                                    os.kill(process.pid, signal.SIGSTOP)
                                    stopped = True
                                    owned = []
                                    native = [pid]
                                    while native:
                                        native_pid = native.pop()
                                        if native_pid in owned:
                                            continue
                                        try:
                                            if os.getpgid(native_pid) != group:
                                                continue
                                            os.kill(native_pid, signal.SIGSTOP)
                                            owned.append(native_pid)
                                            native.extend(process_children(native_pid) - set(owned))
                                        except (FileNotFoundError, ProcessLookupError):
                                            continue
                                    self.assertIn(pid, owned, f"the actual {phase} process escaped; see {log}")
                                    observed = {"phase": phase, "pid": pid, "command": arguments,
                                                "group": group, "owned": owned}
                                    (control / "interruption.json").write_text(json.dumps(observed, indent=2) + "\n")
                                    os.kill(process.pid, signal.SIGTERM)
                                    for native_pid in reversed(owned):
                                        try:
                                            os.kill(native_pid, signal.SIGTERM)
                                            os.kill(native_pid, signal.SIGCONT)
                                        except ProcessLookupError:
                                            continue
                                    os.kill(process.pid, signal.SIGCONT)
                                    stopped = False
                                    break
                                except (FileNotFoundError, ProcessLookupError):
                                    continue
                            if observed is not None:
                                break
                            time.sleep(0.01)
                        self.assertIsNotNone(observed, f"no actual {phase} process was reached; see {log}")
                        status = process.wait(timeout=60)
                    finally:
                        if stopped:
                            try:
                                os.kill(process.pid, signal.SIGCONT)
                            except ProcessLookupError:
                                pass
                        if process.poll() is None:
                            try:
                                os.killpg(process.pid, signal.SIGTERM)
                                os.killpg(process.pid, signal.SIGCONT)
                            except ProcessLookupError:
                                pass
                            try:
                                process.wait(timeout=30)
                            except subprocess.TimeoutExpired:
                                os.killpg(process.pid, signal.SIGKILL)
                                process.wait(timeout=30)
                self.assertEqual(status, 143, log.read_text())
                record = current_acceptance_result()
                self.assertEqual(record["status"], 143)
                self.assertEqual(record["unfinished_phase"], phase)
                self.assertFalse(record["complete"])
                self.assertGreater(record["preparation_seconds"], 0)
                self.assertGreaterEqual(record["build_seconds"], 0)
                if phase == "preparation":
                    self.assertEqual(record["build_seconds"], 0)
                    self.assertEqual(record["context_status"], "pending")
                else:
                    self.assertGreater(record["build_seconds"], 0)
                    self.assertEqual(record["context_status"], "complete")
                self.assertLessEqual(record["preparation_seconds"] + record["build_seconds"],
                                     record["seconds"])
                run = ROOT / record["run"]
                self.assertIn(f"Acceptance run: {record['run']}", log.read_text())
                self.assertTrue(read_log(run / "output.log.gz"))
                events = [json.loads(line) for line in (run / "events.jsonl").read_text().splitlines()]
                self.assertEqual(events[-1]["event"], "run.finished")
                self.assertEqual(events[-1]["unfinished_phase"], phase)
                self.assertFalse(any(event.get("phase", "").startswith("acceptance-worker")
                                     for event in events))

    def test_interrupted_worker_cannot_reuse_previous_results(self) -> None:

        subprocess.run(["scripts/accept_files.sh", "numbers"], cwd=ROOT, check=False)
        report = ROOT / ".tmp/accept-run.json"
        prior = [row for row in json.loads(report.read_text())
                 if Path(row["file"]).name == "numbers.cas"
                 and not row["id"].startswith("(statement)")]
        self.assertTrue(prior, "the first real selected execution must produce results")
        directory = ROOT / "timing/logs/feedback-tests"
        directory.mkdir(parents=True, exist_ok=True)
        log = Path(tempfile.mkdtemp(dir=directory)) / "interrupted.log"
        with log.open("w") as output:
            process = subprocess.Popen(
                ["scripts/accept_files.sh", "numbers"], cwd=ROOT,
                stdout=output, stderr=subprocess.STDOUT, start_new_session=True,
            )
            try:
                deadline = time.monotonic() + 300
                interrupted = False
                while process.poll() is None and time.monotonic() < deadline:
                    pending = [process.pid]
                    descendants = set()
                    while pending:
                        pid = pending.pop()
                        if pid in descendants:
                            continue
                        proc = Path(f"/proc/{pid}")
                        try:
                            descendants.add(pid)
                            pending.extend(process_children(pid) - descendants)
                            arguments = (proc / "cmdline").read_bytes().decode().split("\0")
                            workers = [arg for arg in arguments if arg.endswith("/worker0.lean")]
                            if ((proc / "comm").read_text().strip() == "lean"
                                    and (proc / "cwd").resolve() == ROOT and workers):
                                current = ROOT / Path(workers[0]).with_name("numbers.json")
                                self.assertFalse(current.exists(), "the interruption was too late")
                                os.kill(pid, signal.SIGTERM)
                                interrupted = True
                                break
                        except (FileNotFoundError, ProcessLookupError):
                            continue
                    if interrupted:
                        break
                    time.sleep(0.1)
                self.assertTrue(interrupted, f"no actual acceptance worker was reached; see {log}")
                status = process.wait(timeout=60)
            finally:
                if process.poll() is None:
                    os.killpg(process.pid, signal.SIGTERM)
                    process.wait(timeout=30)
        current = [row for row in json.loads(report.read_text())
                   if Path(row["file"]).name == "numbers.cas"
                   and not row["id"].startswith("(statement)")]
        with self.subTest("worker exit"):
            self.assertNotEqual(status, 0, f"the interrupted worker was reported successful; see {log}")
        with self.subTest("current selected result"):
            self.assertEqual(current, [], "the interrupted run inherited previous selected results")
        latest = current_acceptance_result()
        run = ROOT / latest["run"]
        self.assertEqual(run.parent, ROOT / "timing/logs")
        self.assertFalse(latest["complete"])
        self.assertNotEqual(latest["status"], 0)
        self.assertTrue((run / "output.log.gz").is_file())
        events = [json.loads(line) for line in (run / "events.jsonl").read_text().splitlines()]
        self.assertEqual(events[0]["event"], "run.started")
        self.assertTrue(any(entry["event"] == "phase.started" and
                            entry["phase"] == "acceptance-worker0" for entry in events))
        self.assertEqual(events[-1]["event"], "run.finished")


    def test_partial_report_cannot_reuse_complete_results(self) -> None:


        directory = ROOT / "timing/logs/feedback-tests"
        directory.mkdir(parents=True, exist_ok=True)
        log = Path(tempfile.mkdtemp(dir=directory)) / "partial.log"
        run: Path | None = None
        stopped = False
        removed_id = ""
        original_metadata = {}
        with log.open("w") as output:
            process = subprocess.Popen(
                ["scripts/accept_files.sh", "ellipses", "numbers"], cwd=ROOT,
                stdout=output, stderr=subprocess.STDOUT, start_new_session=True,
            )
            try:

                deadline = time.monotonic() + 900
                while process.poll() is None and time.monotonic() < deadline:
                    if run is None:
                        for line in log.read_text().splitlines():
                            if line.startswith("Acceptance run: "):
                                run = (ROOT / line.removeprefix("Acceptance run: ")).resolve()
                                self.assertEqual(run.parent, ROOT / "timing/logs")
                                break
                    if run is not None:
                        selected_workers = {
                            (run / f"worker{worker}.lean").resolve()
                            for worker in range(2)
                        }
                        pending = [process.pid]
                        descendants = set()
                        while pending:
                            pid = pending.pop()
                            if pid in descendants:
                                continue
                            proc = Path(f"/proc/{pid}")
                            try:
                                descendants.add(pid)
                                pending.extend(process_children(pid) - descendants)
                                arguments = (proc / "cmdline").read_bytes().decode().split("\0")
                                group = os.getpgid(pid)
                                if ((proc / "comm").read_text().strip() == "lean"
                                        and (proc / "cwd").resolve() == ROOT
                                        and group in descendants and os.getpgid(group) == group
                                        and Path(f"/proc/{group}/cwd").resolve() == ROOT
                                        and selected_workers.intersection(
                                            (ROOT / argument).resolve() for argument in arguments
                                            if argument.endswith(".lean"))):
                                    self.assertFalse(
                                        (run / "ellipses.json").exists(),
                                        f"the report appeared before the aggregation barrier; see {log}",
                                    )
                                    os.kill(process.pid, signal.SIGSTOP)
                                    stopped = True
                                    break
                            except (FileNotFoundError, ProcessLookupError):
                                continue
                    if stopped:
                        break
                    time.sleep(0.1)
                self.assertTrue(stopped, f"no actual acceptance worker was reached; see {log}")
                self.assertIsNotNone(run)
                assert run is not None
                while time.monotonic() < deadline:
                    state = next(
                        line.split()[1] for line in
                        Path(f"/proc/{process.pid}/status").read_text().splitlines()
                        if line.startswith("State:")
                    )
                    if state == "T":
                        break
                    time.sleep(0.01)
                else:
                    self.fail(f"the owning acceptance shell did not stop; see {log}")

                selected_report = run / "ellipses.json"
                while time.monotonic() < deadline:
                    try:
                        workers = [
                            json.loads((run / f"worker{worker}.status.json").read_text())
                            for worker in range(2)
                        ]
                        original = selected_report.read_bytes()
                        rows = json.loads(original)
                        break
                    except (FileNotFoundError, json.JSONDecodeError):
                        time.sleep(0.1)
                else:
                    self.fail(f"the actual workers did not finish before cleanup; see {log}")
                self.assertTrue(
                    all(worker["status"] == 0 for worker in workers),
                    f"the unmodified real consumers must finish before report corruption: {workers}",
                )
                expected = set(json.loads(
                    (run / "ellipses.inventory.json").read_text())["assertions"])
                named = [row for row in rows if not row["id"].startswith("(statement)")]
                self.assertEqual({row["id"] for row in named}, expected)
                self.assertEqual(len(named), len(expected), "the original report must be complete")
                self.assertTrue(named, "the real selected report must contain named assertions")
                (run / "ellipses.complete.json").write_bytes(original)
                removed_id = named[0]["id"]
                partial = [row for row in rows if row["id"] != removed_id]
                selected_report.write_text(json.dumps(partial, ensure_ascii=False, indent=1) + "\n")
                for name in ["selection.json", "worker0.status.json", "inputs.json", "manifest.sha256"]:
                    metadata = run / name
                    original_metadata[name] = metadata.read_bytes()
                    (run / (name + ".complete")).write_bytes(original_metadata[name])
                    metadata.write_bytes(b"{")

                os.kill(process.pid, signal.SIGCONT)
                stopped = False
                status = process.wait(timeout=max(1, deadline - time.monotonic()))
            finally:
                if stopped:
                    try:
                        os.kill(process.pid, signal.SIGCONT)
                    except ProcessLookupError:
                        pass
                if process.poll() is None:
                    try:
                        os.killpg(process.pid, signal.SIGTERM)
                    except ProcessLookupError:
                        pass
                    try:
                        process.wait(timeout=30)
                    except subprocess.TimeoutExpired:
                        try:
                            os.killpg(process.pid, signal.SIGKILL)
                        except ProcessLookupError:
                            pass
                        process.wait(timeout=30)

        current = json.loads((ROOT / ".tmp/accept-run.json").read_text())
        latest = current_acceptance_result()
        self.assertEqual(latest["run"], str(run.relative_to(ROOT)))
        self.assertNotEqual(status, 0, f"the partial selected report was accepted; see {log}")
        self.assertNotEqual(latest["status"], 0)
        self.assertFalse(latest["complete"], "a missing selected assertion is incomplete")
        for name in original_metadata:
            self.assertTrue(any(name in error for error in latest["metadata_errors"]),
                            f"the damaged metadata disappeared from the final result: {name}")
        self.assertEqual(latest["inputs"], json.loads(original_metadata["inputs.json"]))
        self.assertIsNone(latest["manifest_sha256"])
        self.assertIsNone(latest["workers"][0]["status"])
        self.assertIsNone(latest["workers"][0]["seconds"])
        actual_numbers = json.loads((run / "numbers.json").read_text())
        self.assertEqual({row["id"] for row in current if Path(row["file"]).name == "numbers.cas"},
                         {row["id"] for row in actual_numbers},
                         "damaged metadata erased the other file's completed outcomes")
        events = [json.loads(line) for line in (run / "events.jsonl").read_text().splitlines()]
        self.assertEqual(events[-1]["event"], "run.finished")
        self.assertFalse(events[-1]["complete"])
        self.assertTrue(latest["timing_complete"], "report corruption must not erase actual execution timings")
        timings = [json.loads(line) for line in
                   (ROOT / latest["computations"]["record_file"]).read_text().splitlines()]
        self.assertIn(removed_id, {entry["id"] for entry in timings},
                      "completed statement timing was reconstructed from the damaged report")
        self.assertTrue(all(entry["complete"] for entry in timings))

        errors = [row for row in current
                  if row["file"] == "tests/acceptance/ellipses.cas"
                  and row["kind"] == "internal" and row["fails"]]
        self.assertTrue(
            any(removed_id in row["detail"] and "incomplete" in row["detail"] for row in errors),
            f"the current failure must identify the omitted assertion {removed_id}: {errors}",
        )
        self.assertNotIn(removed_id, {row["id"] for row in current},
                         "an earlier complete result supplied the missing current assertion")
        self.assertLessEqual(
            {row["file"] for row in current},
            {"tests/acceptance/ellipses.cas", "tests/acceptance/numbers.cas"},
            "the selected report merged historical results from unselected inputs",
        )


if __name__ == "__main__":
    unittest.main()
