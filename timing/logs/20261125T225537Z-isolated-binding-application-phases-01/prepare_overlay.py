from pathlib import Path
import datetime, hashlib, json, shutil, traceback

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

state = {"started_utc": stamp(), "status": "preparing", "ordinary_artifact_writes": 0}
save("preparation.json", state)
try:
    manifest = json.loads((stage / "source-snapshot.json").read_text())
    for root, key in [(repo, "source_inputs"), (stage, "staged_sources")]:
        for name, digest in manifest[key].items():
            assert sha(root / name) == digest, f"source changed before overlay: {name}"
    assert sha(stage / "candidate.patch") == manifest["patch"]["sha256"]
    artifacts = stage / "artifacts"
    assert not artifacts.exists(), "preserve existing artifacts; replay in a fresh copied stage"
    artifacts.mkdir()
    for name in ["application", "logs", "evidence", "base"]:
        (stage / name).mkdir(exist_ok=True)
    manifest["base_sources"] = {}
    for name, digest in manifest["source_inputs"].items():
        destination = stage / "base" / name
        destination.parent.mkdir(parents=True, exist_ok=True)
        shutil.copy2(repo / name, destination)
        assert sha(destination) == digest
        manifest["base_sources"][str(destination.relative_to(stage))] = digest
    evidence = manifest["frozen13_stream"]
    destination = stage / "evidence" / "frozen13-original.jsonl"
    shutil.copy2(repo / evidence["path"], destination)
    assert sha(destination) == evidence["sha256"]
    evidence["retained_path"] = str(destination.relative_to(stage))
    build = repo / ".lake/build/lib/lean"
    assert build.is_dir()
    replaced = {Path(*module.split(".")) for module in manifest["module_order"]}
    manifest["unchanged_namespace_artifacts"] = {}
    manifest["overlay_artifacts"] = {}
    manifest["excluded_regenerated_artifacts"] = {}
    for source in sorted(build.rglob("*")):
        if not source.is_file():
            continue
        relative = source.relative_to(build)
        digest = sha(source)
        manifest["unchanged_namespace_artifacts"][str(source.relative_to(repo))] = digest
        module = relative.parent / relative.name.split(".", 1)[0]
        if module in replaced:
            manifest["excluded_regenerated_artifacts"][str(relative)] = digest
            continue
        destination = artifacts / relative
        destination.parent.mkdir(parents=True, exist_ok=True)
        shutil.copy2(source, destination)
        assert sha(destination) == digest, f"artifact changed during copy: {relative}"
        manifest["overlay_artifacts"][str(destination.relative_to(stage))] = digest
    for name, digest in manifest["unchanged_namespace_artifacts"].items():
        assert sha(repo / name) == digest, f"ordinary artifact changed during snapshot: {name}"
    for module in manifest["module_order"]:
        target = artifacts / Path(*module.split("."))
        target.parent.mkdir(parents=True, exist_ok=True)
        assert not list(target.parent.glob(target.name + ".*")), f"old artifact escaped exclusion: {module}"
    manifest["runner_inputs"] = {name: sha(stage / name) for name in
                                ["runner.py", "prepare_overlay.py", "launch.sh",
                                 "source-snapshot.json", "candidate.patch"]}
    manifest["overlay_ready"] = True
    manifest["overlay_prepared_utc"] = stamp()
    manifest["ordinary_build_directory_removed_from_lean_path"] = True
    manifest["normal_heartbeat_options"] = "unchanged; no budget overrides or resets added"
    manifest["live_lake_build_invocations"] = 0
    save("snapshot.json", manifest)
    state.update({"status": "prepared", "snapshot_sha256": sha(stage / "snapshot.json"),
                  "ordinary_artifacts": len(manifest["unchanged_namespace_artifacts"]),
                  "copied_artifacts": len(manifest["overlay_artifacts"]),
                  "excluded_artifacts": len(manifest["excluded_regenerated_artifacts"])})
except BaseException as error:
    state["status"] = "failed"
    state["exception"] = repr(error)
    traceback.print_exc()
    raise
finally:
    state["finished_utc"] = stamp()
    save("preparation.json", state)
    print(json.dumps(state), flush=True)
