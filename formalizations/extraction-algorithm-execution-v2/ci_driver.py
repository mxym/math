#!/usr/bin/env python3
"""Actual v2 producer; invokes the original immutable mathematical recipe."""
from pathlib import Path
import argparse, os, shutil, subprocess, sys
import execution as e
from audit_runtime import configure, hosted_context, check_ci_binaries

a = e.a


def github_identity():
    required = ["GITHUB_SHA", "GITHUB_RUN_ID", "GITHUB_RUN_ATTEMPT", "GITHUB_REPOSITORY", "GITHUB_WORKFLOW_REF", "GITHUB_WORKFLOW_SHA"]
    values = {name: os.environ[name] for name in required}
    if values["GITHUB_REPOSITORY"] != "mxym/math":
        raise RuntimeError("Unexpected repository identity")
    if values["GITHUB_WORKFLOW_SHA"] != values["GITHUB_SHA"]:
        raise RuntimeError("Actual workflow revision differs from checked event revision")
    if not values["GITHUB_WORKFLOW_REF"].startswith("mxym/math/" + e.WORKFLOW + "@refs/"):
        raise RuntimeError("Actual workflow reference is not v2")
    return dict(source_commit=values["GITHUB_SHA"], run_id=values["GITHUB_RUN_ID"], run_attempt=values["GITHUB_RUN_ATTEMPT"], repository=values["GITHUB_REPOSITORY"], workflow_ref=values["GITHUB_WORKFLOW_REF"], workflow_commit=values["GITHUB_WORKFLOW_SHA"])


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("command", choices=["environment", "bootstrap", "run"])
    args = parser.parse_args()
    runtime = configure(True)  # Original explicit hosted-only guard, forbidden in local WSL.
    env, output = runtime["env"], runtime["output"]
    e.check()
    identity = github_identity()
    e.check_commit(identity["source_commit"])
    output.mkdir(exist_ok=True)
    if args.command == "environment":
        with open(os.environ["GITHUB_ENV"], "a") as handle:
            for key in ["TMPDIR", "MATHLIB_CACHE_DIR", "XDG_CACHE_HOME", "ELAN_HOME"]:
                if "\n" in env[key]:
                    raise RuntimeError("Invalid exclusive runtime path")
                handle.write(key + "=" + env[key] + "\n")
            handle.write("EXTRACTION_ALGORITHM_V2_EVIDENCE=" + str(output) + "\n")
        print("EXCLUSIVE_V2_GITHUB_RUNTIME_CONFIGURED " + str(output))
        return
    policy = a.readj(e.BASE / "CI_EXECUTION_POLICY.json")
    if args.command == "bootstrap":
        installer = hosted_context() / "elan-init.sh"
        subprocess.run(["curl", "--fail", "--location", "--retry", "3", "--connect-timeout", "15", "--max-time", "90", policy["elan_init_url"], "--output", str(installer)], env=env, check=True)
        a.dump(output / "BOOTSTRAP.json", dict(installer_url=policy["elan_init_url"], installer_sha256=a.sha(installer), execution=e.execution_binding(), github=identity))
        subprocess.run(["sh", str(installer), "-y", "--no-modify-path", "--default-toolchain", "none"], env=env, cwd=e.BASE, check=True)
        subprocess.run([env["ELAN_HOME"] + "/bin/elan", "toolchain", "install", policy["lean_toolchain"]], env=env, cwd=e.BASE, check=True)
        a.dump(output / "BOOTSTRAP_BINARIES.json", check_ci_binaries())
        subprocess.run(["lake", "exe", "cache", "get"], env=env, cwd=e.BASE, check=True)
        e.check()
        a.check_pins()
        print("V2_PINNED_CI_BOOTSTRAP_PASS")
        return
    before = e.snapshot(check_ci_binaries())
    a.dump(output / "PRE_AUDIT.json", before)
    command = [sys.executable, "reproduce.py", "--github-actions", "--fresh"]
    with (output / "driver.log").open("w") as log:
        process = subprocess.Popen(command, cwd=e.BASE, env=env, stdout=subprocess.PIPE, stderr=subprocess.STDOUT, text=True)
        for line in process.stdout:
            log.write(line)
            log.flush()
            print(line, end="", flush=True)
        code = process.wait()
    if code:
        raise RuntimeError("Original full mathematical audit failed with exit " + str(code))
    after = e.snapshot(check_ci_binaries())
    if before != after:
        raise RuntimeError("Source/execution/workflow/tool drift across full CI audit")
    a.dump(output / "POST_AUDIT.json", after)
    context = dict(identity, actual_workflow=e.workflow_binding(), execution=e.execution_binding(), status="GITHUB_CI_AUDIT_COMPLETED_PENDING_ARTIFACT_DOWNLOAD_CHECK", source_manifest_sha256=e.MATH_MANIFEST_SHA256, latest=a.readj(output / "LATEST.json"), actual_mathematical_command=command[1:], actual_mathematical_cwd=e.BASE.relative_to(e.REPO).as_posix(), original_v1_workflow_role="Provenance only; not executed by this v2 producer")
    a.dump(output / "CI_CONTEXT.json", context)
    for name in e.ORIGINAL_EXPORTS:
        shutil.copy2(e.BASE / name, output / name)
    e.copy_execution_evidence(output)
    hashes = {path.relative_to(output).as_posix(): a.sha(path) for path in sorted(output.rglob("*")) if path.is_file() and path != output / "ARTIFACT_HASHES.json"}
    a.dump(output / "ARTIFACT_HASHES.json", hashes)
    print("V2_FULL_CI_EVIDENCE_SEALED_PENDING_DOWNLOAD_CHECK " + str(output))


if __name__ == "__main__":
    main()
