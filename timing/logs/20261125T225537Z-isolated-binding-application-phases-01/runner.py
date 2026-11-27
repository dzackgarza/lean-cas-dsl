from pathlib import Path
import datetime, hashlib, json, os, subprocess, sys, time, traceback

stage = Path(__file__).resolve().parent
repo = stage.parents[1]

def stamp():
    return datetime.datetime.now(datetime.timezone.utc).isoformat()

def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()

def save(name, value):
    path = stage / name
    pending = path.with_name(path.name + ".pending")
    pending.write_text(json.dumps(value, indent=2) + "\n")
    pending.replace(path)

def changed(root, entries):
    return [name for name, digest in entries.items()
            if not (root / name).is_file() or sha(root / name) != digest]

state = {"started_utc": stamp(), "runner_pid": os.getpid(), "modules": [], "status": "running"}
save("status.json", state)
manifest = None
try:
    manifest = json.loads((stage / "snapshot.json").read_text())
    assert manifest["overlay_ready"], "the released artifact overlay is not finalized"
    for key, root in [("staged_sources", stage), ("runner_inputs", stage),
                      ("overlay_artifacts", stage), ("source_inputs", repo),
                      ("unchanged_namespace_artifacts", repo)]:
        differences = changed(root, manifest[key])
        assert not differences, f"snapshot inputs changed: {key}: {differences}"
    env = os.environ.copy()
    live = (repo / ".lake/build/lib/lean").resolve()
    inherited = []
    for entry in env.get("LEAN_PATH", "").split(os.pathsep):
        if entry and Path(entry if os.path.isabs(entry) else repo / entry).resolve() != live:
            inherited.append(entry)
    env["LEAN_PATH"] = os.pathsep.join([str(stage / "artifacts")] + inherited)
    env["CAS_APPLICATION_LOG_DIR"] = str(stage / "application")
    env["CAS_FEEDBACK_RUN"] = "isolated-binding-application-phases-20261125-01"
    env["CAS_FEEDBACK_CONTEXT"] = str(stage / "snapshot.json")
    state["lake_environment"] = {key: env.get(key) for key in
        ["LEAN_PATH", "LEAN_SRC_PATH", "LEAN_SYSROOT", "PATH",
         "CAS_APPLICATION_LOG_DIR", "CAS_FEEDBACK_RUN", "CAS_FEEDBACK_CONTEXT"]}
    for module in manifest["module_order"]:
        source = (stage / "src" / Path(*module.split("."))).with_suffix(".lean")
        target = stage / "artifacts" / Path(*module.split("."))
        command = ["lean", "--root=" + str(stage / "src"), str(source),
                   "-o", str(target) + ".olean", "-i", str(target) + ".ilean",
                   "-c", str(target) + ".c"]
        module_log = stage / "logs" / (module + ".log")
        item = {"module": module, "command": command, "started_utc": stamp(),
                "log": str(module_log.relative_to(stage))}
        state["modules"].append(item)
        with module_log.open("wb") as output:
            process = subprocess.Popen(command, cwd=repo, env=env, stdin=subprocess.DEVNULL,
                                       stdout=output, stderr=subprocess.STDOUT)
            item["pid"] = process.pid
            save("status.json", state)
            print(json.dumps({"module": module, "pid": process.pid, "log": str(module_log)}), flush=True)
            started = time.monotonic()
            item["exit_code"] = process.wait()
            item["seconds"] = round(time.monotonic() - started, 3)
        item["finished_utc"] = stamp()
        item["produced_artifacts"] = {
            str(path.relative_to(stage)): sha(path)
            for path in sorted(target.parent.glob(target.name + ".*")) if path.is_file()}
        save("status.json", state)
        print(json.dumps(item), flush=True)
        if item["exit_code"] != 0:
            state["status"] = "failed"
            break
    else:
        state["status"] = "passed"
except BaseException as error:
    state["status"] = "error"
    state["exception"] = repr(error)
    traceback.print_exc()
finally:
    if manifest is not None:
        for key, root in [("source_inputs", repo), ("unchanged_namespace_artifacts", repo),
                          ("staged_sources", stage), ("overlay_artifacts", stage)]:
            differences = changed(root, manifest[key])
            state[key + "_changes"] = differences
            if differences:
                state["status"] = "failed"
                state["isolation_error"] = "captured input bytes changed during isolated validation"
    state["finished_utc"] = stamp()
    save("status.json", state)
    save("result.json", state)
print(json.dumps({"status": state["status"], "result": str(stage / "result.json")}), flush=True)
sys.exit(0 if state["status"] == "passed" else 1)
