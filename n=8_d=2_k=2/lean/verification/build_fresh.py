#!/usr/bin/env python3
"""Compile project sources into an initially empty project artifact directory.

Invoke inside a fresh source snapshot, with LEAN_PATH listing its empty artifact
directory and the pinned Lean and external dependency libraries. This program
does not prepare those libraries or run any verification program.
"""

import concurrent.futures
import hashlib
import json
import os
from pathlib import Path
import re
import shutil
import subprocess
import sys
import time


def main():
    project = Path.cwd().resolve()
    output = project / ".lake/build/lib/lean"
    logs = project / "fresh-build-logs"
    if output.exists() and any(output.rglob("*")):
        raise RuntimeError("Project artifact directory must initially be empty")
    if any(project.rglob("*.olean")):
        raise RuntimeError("Source snapshot contains an existing compiled Lean object")
    if any(project.rglob("*.olean.*")):
        raise RuntimeError("Source snapshot contains an existing Lean object sidecar")
    expected = str(output)
    entries = os.environ.get("LEAN_PATH", "").split(":")
    if not entries or entries[0] != expected:
        raise RuntimeError("First LEAN_PATH entry must be this empty project output")
    sysroot = Path(os.environ["LEAN_SYSROOT"]).resolve()
    for entry in entries[1:] + [str(sysroot / "lib/lean")]:
        if (Path(entry) / "PBCounterexample").exists() or any(
                Path(entry).glob("PBCounterexample.olean*")):
            raise RuntimeError(f"Old project artifacts are visible in LEAN_PATH: {entry}")
    output.mkdir(parents=True, exist_ok=True)
    logs.mkdir()
    sources = sorted(project.glob("PBCounterexample/**/*.lean"))
    sources.append(project / "PBCounterexample.lean")
    modules = {".".join(p.relative_to(project).with_suffix("").parts): p for p in sources}
    source_hashes = {name: hashlib.sha256(path.read_bytes()).hexdigest()
                     for name, path in modules.items()}
    executable = Path(shutil.which("lean")).resolve()
    if executable != (sysroot / "bin/lean").resolve():
        raise RuntimeError("Lean executable does not belong to LEAN_SYSROOT")
    compiler = {"executable": str(executable),
                "executable_sha256": hashlib.sha256(executable.read_bytes()).hexdigest(),
                "version": subprocess.check_output([str(executable), "--version"], text=True),
                "lean_toolchain": (project / "lean-toolchain").read_text(),
                "sysroot": str(sysroot)}
    shared_kernel = sysroot / "lib/lean/libleanshared.so"
    if not shared_kernel.is_file():
        raise RuntimeError("Expected pinned Linux Lean shared library is missing")
    compiler["shared_library_sha256"] = hashlib.sha256(shared_kernel.read_bytes()).hexdigest()
    dependencies = {}
    for name, path in modules.items():
        deps = set(re.findall(r"^import\s+(PBCounterexample(?:\.\w+)*)\s*$",
                              path.read_text(), re.MULTILINE))
        if not deps <= modules.keys():
            raise RuntimeError(f"Unknown project imports for {name}: {deps - modules.keys()}")
        dependencies[name] = deps
    evidence = {"lean_path": entries, "project": str(project), "compiler": compiler,
                "initial_source_sha256": source_hashes, "modules": {}}
    (logs / "build.json").write_text(json.dumps(evidence, indent=2) + "\n")
    done = set()
    pending = set(modules)
    active = {}

    def compile_module(name):
        source = modules[name]
        target = output.joinpath(*name.split(".")).with_suffix(".olean")
        target.parent.mkdir(parents=True, exist_ok=True)
        if hashlib.sha256(source.read_bytes()).hexdigest() != source_hashes[name]:
            raise RuntimeError(f"Source changed before compilation: {name}")
        command = [str(executable), "--trust=0", "--root=.", "-o", str(target),
                   str(source.relative_to(project))]
        start = time.monotonic()
        with (logs / f"{name}.log").open("w") as log:
            rc = subprocess.run(command, stdout=log, stderr=subprocess.STDOUT).returncode
        if hashlib.sha256(source.read_bytes()).hexdigest() != source_hashes[name]:
            raise RuntimeError(f"Source changed during compilation: {name}")
        if rc == 0 and (not target.is_file() or target.stat().st_size == 0):
            raise RuntimeError(f"Lean reported success without its expected object: {name}")
        return {"command": command, "exit_code": rc,
                "seconds": time.monotonic() - start,
                "source_sha256": source_hashes[name],
                "artifact_sha256": {str(p.relative_to(output)):
                    hashlib.sha256(p.read_bytes()).hexdigest()
                    for p in sorted(target.parent.glob(target.stem + ".*")) if p.is_file()}}

    with concurrent.futures.ThreadPoolExecutor(max_workers=4) as pool:
        while pending or active:
            for name in sorted(pending):
                if len(active) == 4:
                    break
                if dependencies[name] <= done:
                    print(f"BUILD_START {name}", flush=True)
                    active[pool.submit(compile_module, name)] = name
                    pending.remove(name)
            if not active:
                raise RuntimeError(f"Import cycle or failed prerequisite: {sorted(pending)}")
            completed, _ = concurrent.futures.wait(active,
                return_when=concurrent.futures.FIRST_COMPLETED)
            for future in completed:
                name = active.pop(future)
                result = future.result()
                evidence["modules"][name] = result
                (logs / "build.json").write_text(json.dumps(evidence, indent=2) + "\n")
                print(f"BUILD_END {name} EXIT={result['exit_code']}", flush=True)
                if result["exit_code"]:
                    print((logs / f"{name}.log").read_text(), flush=True)
                    raise RuntimeError(f"Compilation failed: {name}")
                done.add(name)
    current_sources = sorted(project.glob("PBCounterexample/**/*.lean"))
    current_sources.append(project / "PBCounterexample.lean")
    current_hashes = {".".join(p.relative_to(project).with_suffix("").parts):
                      hashlib.sha256(p.read_bytes()).hexdigest() for p in current_sources}
    if current_hashes != source_hashes:
        raise RuntimeError("Project source inventory or contents changed during the build")
    evidence["all_project_artifact_sha256"] = {
        str(p.relative_to(output)): hashlib.sha256(p.read_bytes()).hexdigest()
        for p in sorted(output.rglob("*")) if p.is_file()}
    for name, result in evidence["modules"].items():
        for artifact, digest in result["artifact_sha256"].items():
            if evidence["all_project_artifact_sha256"].get(artifact) != digest:
                raise RuntimeError(f"Compiled artifact changed after its module finished: {name} {artifact}")
    evidence["final_source_sha256"] = current_hashes
    evidence["success"] = True
    (logs / "build.json").write_text(json.dumps(evidence, indent=2) + "\n")
    print(f"FRESH_PROJECT_SOURCE_BUILD_OK modules={len(done)}", flush=True)


if __name__ == "__main__":
    try:
        main()
    except Exception as exc:
        print(f"FRESH_PROJECT_SOURCE_BUILD_FAILED: {exc}", file=sys.stderr, flush=True)
        sys.exit(1)
