#!/usr/bin/env python3
"""Separate immutable execution revision for the unchanged algorithm math scope."""
from pathlib import Path
import argparse, hashlib, json, re, subprocess, sys

ROOT = Path(__file__).resolve().parent
BASE = ROOT.parent / "extraction-algorithm-audit"
REPO = ROOT.parent.parent
sys.path.insert(1, str(BASE))
import reproduce as a

REVISION = "extraction-algorithm-execution-v2"
MATH_HEAD = "6a8e2d3637152983cda6d4723e23474098f4ecfb"
MATH_MANIFEST_SHA256 = "8b99b7d144b8c27a4092028f557a47bf01fb38d0ded6eef543a4abd612e51386"
BINDING_COMMIT = "694037a7e0a0791d91e6d909e2e342236ad92df7"
WORKFLOW = ".github/workflows/extraction-algorithm-v2.yml"
TEMPLATE = "extraction-algorithm-v2.workflow.yml"
MANIFEST = ROOT / "EXECUTION_HASHES.json"
EXPECTED_SCOPE = dict(endpoint_theorems=459, model_definitions=276, same_type_controls=65)
ORIGINAL_EXPORTS = ["SOURCE_HASHES.json", "FROZEN_OLD_INPUTS.json", "SCOPE.json", "ROOTS.txt", "DEFINITIONS.txt", "CONTROLS.txt", "CI_EXECUTION_POLICY.json"]


def own_inputs():
    result = {}
    for path in sorted(ROOT.rglob("*")):
        relative = path.relative_to(ROOT)
        if any(part in {"verification", "__pycache__"} for part in relative.parts):
            continue
        if relative.as_posix() == "EXECUTION_HASHES.json":
            continue
        if path.is_symlink():
            raise RuntimeError("Symlinked execution input " + str(relative))
        if path.is_file():
            result[path.relative_to(REPO).as_posix()] = a.sha(path)
    return result


def source_precheck():
    if a.sha(BASE / "SOURCE_HASHES.json") != MATH_MANIFEST_SHA256:
        raise RuntimeError("Original mathematical manifest changed")
    manifest = a.readj(BASE / "SOURCE_HASHES.json")
    if len(manifest) != 340 or a.inventory() != manifest:
        raise RuntimeError("Original 340 bound inputs changed")
    if a.old_inventory() != a.readj(BASE / "FROZEN_OLD_INPUTS.json"):
        raise RuntimeError("Protected prior evidence/source changed")
    scope, roots, definitions, controls = a.scope_lists()
    if scope["source_head"] != MATH_HEAD or scope["state"] != "READY" or scope["pending_required"]:
        raise RuntimeError("Wrong original READY mathematical source")
    actual = dict(endpoint_theorems=len(roots), model_definitions=len(definitions), same_type_controls=len(controls))
    if actual != EXPECTED_SCOPE or a.readj(BASE / "CI_EXECUTION_POLICY.json")["expected_scope"] != actual:
        raise RuntimeError("Original fixed scope changed")
    a.validate_source_head(scope, manifest)
    return manifest


def proposed_manifest():
    original = a.readj(BASE / "SOURCE_HASHES.json")
    prefix = BASE.relative_to(REPO).as_posix() + "/"
    return dict(
        schema=1, execution_revision=REVISION, mathematical_source_head=MATH_HEAD,
        original_binding_commit=BINDING_COMMIT,
        original_source_manifest_sha256=MATH_MANIFEST_SHA256,
        original_bound_input_count=340, expected_scope=EXPECTED_SCOPE,
        original_frozen_recipe_inputs={name: value for name, value in original.items() if name.startswith(prefix)},
        execution_inputs=own_inputs(),
        actual_workflow=dict(path=WORKFLOW, template=(ROOT / TEMPLATE).relative_to(REPO).as_posix(), template_sha256=a.sha(ROOT / TEMPLATE)),
        original_workflow_role="Frozen v1 recipe provenance only; not the actual v2 workflow",
    )


def workflow_binding():
    path = REPO / WORKFLOW
    if path.is_symlink() or not path.is_file():
        raise RuntimeError("Actual v2 workflow is not installed as a regular file")
    digest = a.sha(path)
    if digest != a.sha(ROOT / TEMPLATE):
        raise RuntimeError("Actual v2 workflow bytes differ from the execution-bound template")
    return dict(path=WORKFLOW, sha256=digest, bound_template_sha256=a.sha(ROOT / TEMPLATE))


def check(require_workflow=True):
    source_precheck()
    manifest = a.readj(MANIFEST)
    if manifest != proposed_manifest():
        raise RuntimeError("Execution-v2 inputs/recipe binding changed")
    if require_workflow:
        workflow_binding()
    return manifest


def check_commit(commit):
    if not re.fullmatch(r"[a-f0-9]{40}", commit) or a.run("git", "rev-parse", "HEAD") != commit:
        raise RuntimeError("Execution checkout differs from the immutable event commit")
    manifest = check()
    paths = [MANIFEST, REPO / WORKFLOW] + [REPO / relative for relative in manifest["execution_inputs"]]
    for path in paths:
        relative = path.relative_to(REPO).as_posix()
        committed = subprocess.check_output(["git", "show", commit + ":" + relative], cwd=REPO)
        if path.read_bytes() != committed:
            raise RuntimeError("Execution input differs from event Git blob " + relative)


def execution_binding():
    manifest = check()
    return dict(execution_revision=REVISION,
                execution_manifest_sha256=a.sha(MANIFEST),
                execution_inputs=manifest["execution_inputs"],
                original_frozen_recipe_inputs=manifest["original_frozen_recipe_inputs"],
                actual_workflow=workflow_binding())


def snapshot(binaries):
    binding = execution_binding()
    return dict(source_manifest_sha256=MATH_MANIFEST_SHA256,
                source_inputs=a.inventory(),
                protected_inputs_manifest_sha256=a.sha(BASE / "FROZEN_OLD_INPUTS.json"),
                execution=binding, binaries=binaries)


def axiom_set(path):
    # ReplaySupport writes exactly a single LF for the empty sorted list.
    raw = Path(path).read_bytes()
    if raw == b"\n":
        return set()
    try:
        text = raw.decode("utf-8")
    except UnicodeDecodeError as error:
        raise RuntimeError("Invalid axiom-list UTF-8") from error
    lines = text.splitlines()
    if "\r" in text or not text.endswith("\n") or not lines or len(lines) != len(set(lines)) or any(not name or name.strip() != name for name in lines):
        raise RuntimeError("Noncanonical axiom-list encoding")
    if any("\r" in name or any(char.isspace() for char in name) for name in lines):
        raise RuntimeError("Noncanonical axiom name")
    return set(lines)


def copy_execution_evidence(output):
    import shutil
    destination = Path(output) / "execution-v2"
    destination.mkdir(exist_ok=False)
    shutil.copy2(MANIFEST, destination / "EXECUTION_HASHES.json")
    for relative in a.readj(MANIFEST)["execution_inputs"]:
        source = REPO / relative
        target = destination / source.relative_to(ROOT)
        target.parent.mkdir(parents=True, exist_ok=True)
        shutil.copy2(source, target)


def verify_execution_evidence(base, context, pre, post):
    expected = execution_binding()
    if context.get("execution") != expected or pre.get("execution") != expected or post.get("execution") != expected:
        raise RuntimeError("Artifact execution-v2/workflow binding mismatch")
    if context.get("actual_workflow") != expected["actual_workflow"]:
        raise RuntimeError("Artifact actual workflow is not the executed v2 workflow")
    exported = Path(base) / "execution-v2"
    if (exported / "EXECUTION_HASHES.json").read_bytes() != MANIFEST.read_bytes():
        raise RuntimeError("Downloaded execution manifest differs from exact checkout")
    inputs = expected["execution_inputs"]
    for relative, digest in inputs.items():
        target = exported / (REPO / relative).relative_to(ROOT)
        if a.sha(target) != digest:
            raise RuntimeError("Downloaded execution input differs " + relative)
    expected_files = {"EXECUTION_HASHES.json"} | {(REPO / relative).relative_to(ROOT).as_posix() for relative in inputs}
    actual_files = {path.relative_to(exported).as_posix() for path in exported.rglob("*") if path.is_file()}
    if actual_files != expected_files:
        raise RuntimeError("Execution evidence has missing/extra inputs")
    if pre != post or pre["source_inputs"] != a.readj(BASE / "SOURCE_HASHES.json") or pre["source_manifest_sha256"] != MATH_MANIFEST_SHA256:
        raise RuntimeError("Source/execution/tool pre-post drift")
    if pre["protected_inputs_manifest_sha256"] != a.sha(BASE / "FROZEN_OLD_INPUTS.json"):
        raise RuntimeError("Protected input binding drift")
    return expected


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("command", choices=["freeze", "check"])
    parser.add_argument("--without-installed-workflow", action="store_true", help="Metadata preflight only; production CI/reader always require the installed workflow")
    args = parser.parse_args()
    if args.command == "freeze":
        if args.without_installed_workflow:
            parser.error("freeze does not use this preflight option")
        source_precheck()
        target = MANIFEST
        if target.exists():
            raise RuntimeError("Execution manifest already frozen; use a separate revision")
        a.dump(target, proposed_manifest())
        print("EXECUTION_V2_METADATA_FROZEN " + a.sha(target))
    else:
        check(require_workflow=not args.without_installed_workflow)
        print("EXECUTION_V2_METADATA_PREFLIGHT_PASS" if args.without_installed_workflow else "EXECUTION_V2_INSTALLED_WORKFLOW_BINDING_PASS")


if __name__ == "__main__":
    main()
