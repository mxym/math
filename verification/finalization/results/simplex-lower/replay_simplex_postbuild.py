#!/usr/bin/env python3
"""Complete frozen kernel audits of a current sealed-verifier fresh build.

Historical closure sizes are fingerprints, not mathematical hypotheses.
This continuation checks the actual complete graph against the frozen roots,
source pins, ownership/types/axioms and unchanged empty-kernel audit code.
It does not rebuild or reseal the historical release, or load archived owned
proof objects. Run the sealed fresh builder first, then pass its BUILD.json
directory. A numeric historical-count mismatch is retained in the report.
"""
import argparse
import datetime
import gzip
import hashlib
import importlib.util
import json
import os
from pathlib import Path
import re
import shutil
import subprocess
import sys

sys.dont_write_bytecode = True
REPO = Path(__file__).resolve().parents[2]
ALLOWED = {"propext", "Classical.choice", "Quot.sound"}
SUITES = {
    "upper": ("sharp-simplex-upper-bound", 123, 848, 1833, 55067, 54277),
    "lower": ("simplex-truncation-sharpness", 125, 850, 1849, 55163, None),
}


def need(condition, message):
    if not condition:
        raise RuntimeError(message)


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def read(path):
    return json.loads(gzip.decompress(path.read_bytes()) if path.suffix == ".gz" else path.read_bytes())


def write(path, data):
    path.write_text(json.dumps(data, indent=2, ensure_ascii=False) + "\n")


# Insert a graph export into a copy of the frozen audit, immediately before
# its unchanged empty-kernel replay. This adds no mathematical declaration.
GRAPH_EXPORT = r'''
  let mut graphRows : Array Json := #[]
  for (n, ci) in cs.toList do
    let moduleName := match env.getModuleIdxFor? n with
      | some idx => env.header.moduleNames[idx.toNat]!.toString
      | none => "(kernel)"
    let extra := match ci with
      | .inductInfo v => v.all ++ v.ctors
      | .ctorInfo v => [v.induct]
      | .recInfo v => v.all
      | _ => []
    graphRows := graphRows.push <| Json.mkObj [
      ("name", toJson n.toString), ("module", toJson moduleName),
      ("all_direct", toJson ((extra ++ ci.getUsedConstantsAsSet.toList).map Name.toString)),
      ("axiom", toJson ci.isAxiom), ("unsafe", toJson ci.isUnsafe),
      ("partial", toJson ci.isPartial)]
  let some graphPath ← IO.getEnv "FINALIZATION_GRAPH_PATH" |
    throwError "Missing graph output path"
  liftIO <| IO.FS.writeFile graphPath (Json.compress (toJson graphRows))
'''


def main():
    script_digest = sha(Path(__file__))
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--kind", choices=SUITES, required=True)
    parser.add_argument("--fresh-build", type=Path, required=True)
    parser.add_argument("--dependency-project", type=Path, required=True)
    parser.add_argument("--lean-bin", type=Path, required=True)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    package, modules, public_count, owned_count, historical_all, historical_main = SUITES[args.kind]
    root = REPO / "formalizations" / package
    formal = root / "project/formal"
    build = args.fresh_build.resolve()
    out = args.output.resolve()
    need(not out.exists() and not out.is_relative_to(root), "Choose a fresh output outside the release")
    spec = importlib.util.spec_from_file_location("sealed_integrity_" + args.kind, root / "scripts/release_integrity.py")
    need(spec is not None and spec.loader is not None, "Missing sealed integrity verifier")
    integrity = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(integrity)
    snapshot = integrity.validated_snapshot(root)
    metadata = read(build / "BUILD.json")
    need(metadata["status"] == "PASS" and metadata["owned_modules"] == modules
         and metadata["owned_cache_fallbacks"] is False, "Incomplete fresh-build receipt")
    lean = (args.lean_bin / "lean").resolve()
    tool = lean.parent.parent
    for name, digest in read(root / "provenance/TOOLCHAIN_FILES_SHA256.json")["files"].items():
        need(sha(tool / name) == digest, "Pinned toolchain changed: " + name)
    sources = read(root / "audit/independent/import-closure.json.gz")
    pk = args.dependency_project.resolve() / ".lake/packages"
    pins = {p["name"]: p["rev"] for p in read(formal / "lake-manifest.json")["packages"]}
    need(metadata["pins"] == pins, "Build/dependency pin mismatch")
    for name, revision in pins.items():
        head = subprocess.check_output(["git", "rev-parse", "HEAD"], cwd=pk / name, text=True).strip()
        need(head == revision, "Dependency revision changed: " + name)
        subprocess.run(["git", "diff", "--quiet", "HEAD", "--"], cwd=pk / name, check=True)
    for name, row in sources.items():
        base = formal if row["package"] == "owned" else tool / "src/lean" if row["package"] == "lean" else pk / row["package"]
        need(sha(base / row["relative_source"]) == row["sha256"], "Source closure changed: " + name)
    records = {r["module"]: r for r in metadata["results"]}
    own_sources = {n: r for n, r in sources.items() if r["package"] == "owned"}
    need(set(records) == set(own_sources) and len(records) == modules, "Owned build coverage differs")
    for name, row in records.items():
        artifact = build / "owned" / Path(name.replace(".", "/")).with_suffix(".olean")
        need(not artifact.is_symlink() and sha(artifact) == row["olean_sha256"], "Fresh object changed: " + name)
        need(row["source_sha256"] == own_sources[name]["sha256"], "Fresh object source differs: " + name)
    reference_artifacts = read(root / "provenance/EXTERNAL_ARTIFACTS_REFERENCE.json.gz")["modules"]
    external = {n: r for n, r in sources.items() if r["package"] != "owned"}
    fresh_external = set(metadata["new_external_modules"])
    need(set(reference_artifacts) == set(external) and fresh_external <= set(external), "External provenance coverage differs")
    suffixes = [".olean", ".olean.private", ".olean.server", ".ilean", ".ir", ".ir.sig"]
    for name, row in external.items():
        rel = Path(name.replace(".", "/"))
        artifact = build / "external-overlay" / rel.with_suffix(".olean")
        need(artifact.is_file(), "Missing external object: " + name)
        reference = reference_artifacts[name]
        need(reference["source_sha256"] == row["sha256"] and reference["package"] == row["package"], "External object/source pin differs")
        if name in fresh_external:
            need(not artifact.is_symlink(), "Fresh external object replaced with a cache")
        else:
            hashes = {suffix: sha(build / "external-overlay" / rel.with_suffix(suffix))
                      for suffix in suffixes if (build / "external-overlay" / rel.with_suffix(suffix)).is_file()}
            need(hashes == reference["artifacts"], "Reused external artifact differs from reference: " + name)
    # Keep every artifact used by the continuation stable across its checks.
    artifact_hashes = {}
    for directory in [build / "owned", build / "external-overlay"]:
        for artifact in directory.rglob("*"):
            if artifact.is_file():
                artifact_hashes[str(artifact)] = sha(artifact)
    out.mkdir(parents=True)
    (out / "logs").mkdir()
    env = os.environ.copy()
    env["PATH"] = str(lean.parent) + os.pathsep + env.get("PATH", "")
    env["LEAN_PATH"] = os.pathsep.join(map(str, [build / "owned", tool / "lib/lean", build / "external-overlay"]))
    flags = ["-DautoImplicit=false", "-DmaxSynthPendingDepth=3", "-DwarningAsError=true"]
    controls = []

    def run(argv, key, negative=False):
        result = subprocess.run(list(map(str, argv)), cwd=formal, env=env, text=True, capture_output=True)
        text = result.stdout + result.stderr
        for path, label in [(root, "${RELEASE}"), (build, "${FRESH_BUILD}"), (out, "${OUTPUT}"), (pk.parent.parent, "${DEPENDENCIES}"), (tool, "${TOOLCHAIN}")]:
            text = text.replace(str(path), label)
        (out / "logs" / (key + ".log")).write_text(text)
        if negative:
            need(result.returncode != 0 and "type mismatch" in text.lower(), "Negative goal not rejected: " + key)
            need(not any(s in text.lower() for s in ["unknown module", "unknown identifier", "unexpected token", "unknown constant", "failed to synthesize"]), "Broken negative fixture: " + key)
        else:
            need(result.returncode == 0 and not re.search(r"\b(?:warning|error)\s*:", text), "Audit failed: " + key + "\n" + text)
        controls.append({"check": key, "exit_code": result.returncode, "expected_rejection": negative})
        return text

    checks = root / "audit/checks"
    axiom_text = run([lean, *flags, checks / "IndependentPublicAudit.lean"], "IndependentPublicAudit")
    rows = re.findall(r"'([^']+)' depends on axioms: \[([^\]]*)\]", axiom_text, re.S)
    rows += [(n, "") for n in re.findall(r"'([^']+)' does not depend on any axioms", axiom_text)]
    axioms = {n: sorted({re.sub(r"\.\{[^}]+\}$", "", x.strip()) for x in a.split(",") if x.strip()}) for n, a in rows}
    reference_axioms = read(root / ("audit/independent/public-axioms.json.gz" if args.kind == "upper" else "audit/independent/public850-axioms.json.gz"))
    need(len(rows) == public_count and axioms == reference_axioms, "Public proof/axiom inventory differs")
    text = run([lean, *flags, checks / "OwnedInventory.lean"], "OwnedInventory")
    inventory = json.loads(text.split("OWNED_INVENTORY_JSON=", 1)[1].strip())
    expected_inventory = read(root / "audit/independent/owned-declarations.json.gz")
    byname = {r["name"]: r for r in inventory}
    need(len(inventory) == owned_count and byname == {r["name"]: r for r in expected_inventory}, "Owned names/types/owners/kinds/axioms differ")
    need(all(not r["unsafe"] and not r["partial"] and r["kind"] not in {"axiom", "opaque"} and set(r["axioms"]) <= ALLOWED for r in inventory), "Forbidden owned declaration")
    need(all(byname[n]["kind"] == "theorem" for n in axioms), "Public name is not a theorem")
    names = ["LiteralPositiveControls", "NegativeAbbreviationAsProof", "NegativeConstantOmission", "NegativeWrongQuantifier", "KernelNegativeControl"] if args.kind == "upper" else ["LiteralPositiveControls", "NegativeMainSubstitution", "NegativeFormulaOmission", "KernelNegativeControl"]
    for name in names:
        text = run([lean, *flags, checks / (name + ".lean")], name, name.startswith("Negative"))
        if name == "KernelNegativeControl":
            need("EXPECTED_KERNEL_REJECTION:" in text and "KERNEL_NEGATIVE_CONTROL_PASS" in text, "Kernel negative control missing")
    outcomes = {}
    for name, roots, marker in [("ReplayAllSafeOwned", owned_count, "ALL_SAFE_OWNED_EMPTY_KERNEL_REPLAY_PASS")] + ([("ReplayLiteralMain", 1, "MAIN_EMPTY_KERNEL_REPLAY_PASS")] if args.kind == "upper" else []):
        source = (checks / (name + ".lean")).read_text()
        anchor = '  logInfo m!"REPLAY_BEGIN'
        need(source.count(anchor) == 1, "Frozen replay instrumentation point changed")
        instrumented = source.replace(anchor, GRAPH_EXPORT + anchor)
        audit = out / (name + ".lean")
        audit.write_text(instrumented)
        graph_file = out / (name + ".graph.json")
        env["FINALIZATION_GRAPH_PATH"] = str(graph_file)
        print("Replaying " + name, flush=True)
        text = run([lean, *flags, audit], name)
        found = re.search(r"REPLAY_BEGIN roots=(\d+) closure=(\d+) skipped=\[\] trust=0 empty=true", text)
        need(found is not None and int(found[1]) == roots, "Incomplete/unsafe replay roots")
        count = int(found[2])
        need(f"{marker} roots={roots} closure={count}" in text, "Empty-kernel replay did not complete")
        graph_rows = read(graph_file)
        graph = {r["name"]: r for r in graph_rows}
        need(len(graph_rows) == len(graph) == count, "Kernel/graph count mismatch")
        root_names = set(byname) if name == "ReplayAllSafeOwned" else {"Entry005.sharpMain"}
        seen, pending = set(), list(root_names)
        while pending:
            node = pending.pop()
            if node in seen:
                continue
            need(node in graph, "Missing referenced graph declaration: " + node)
            seen.add(node)
            pending.extend(graph[node]["all_direct"])
        need(seen == set(graph), "Collected graph is not exactly the full root closure")
        need(all(not r["unsafe"] and not r["partial"] and (not r["axiom"] or n in ALLOWED) for n, r in graph.items()), "Forbidden graph declaration")
        owned_nodes = {n for n, r in graph.items() if r["module"] in own_sources}
        if name == "ReplayAllSafeOwned":
            need(owned_nodes == set(byname), "Replayed owned coverage differs")
        else:
            old_owned = set(read(root / "audit/independent/main-owned-dependency-closure.json"))
            need(owned_nodes == old_owned, "Literal Main owned dependency set differs")
        for n, row in graph.items():
            need(row["module"] in sources or row["module"] == "(kernel)", "Unknown defining module: " + row["module"])
        (out / (name + ".graph.json.gz")).write_bytes(gzip.compress(graph_file.read_bytes(), mtime=0))
        graph_file.unlink()
        outcomes[name] = {"roots": roots, "closure": count, "complete_graph": True, "empty_environment": True, "trust_level": 0, "skipped": []}
    rational = out / "rational"
    rational.mkdir()
    if args.kind == "upper":
        target = rational / "exact_controls.py"
        shutil.copyfile(root / "audit/mathematical/exact_controls.py", target)
        commands = [[sys.executable, "-B", target], [sys.executable, "-O", "-B", target]]
    else:
        target = root / "scripts/exact_rational_controls.py"
        commands = [[sys.executable, "-B", target, "--output", rational / "normal.json"], [sys.executable, "-O", "-B", target, "--output", rational / "optimized.json"]]
    normal = run(commands[0], "rational-normal")
    optimized = run(commands[1], "rational-optimized")
    need(normal == optimized, "Exact rational normal/optimized output differs")
    need(integrity.validated_snapshot(root) == snapshot, "Frozen release changed during replay")
    need(all(sha(Path(p)) == digest for p, digest in artifact_hashes.items()), "Build artifact changed during replay")
    need(sha(Path(__file__)) == script_digest, "Continuation script changed during replay")
    write(out / "CONTROLS.json", controls)
    write(out / "PUBLIC_AXIOMS.json", axioms)
    write(out / "OWNED_INVENTORY.json", inventory)
    actual_all = outcomes["ReplayAllSafeOwned"]["closure"]
    report = {"status": "PASS", "timestamp_utc": datetime.datetime.now(datetime.timezone.utc).isoformat(), "kind": args.kind,
              "continuation_script_sha256": script_digest,
              "fresh_build_receipt_sha256": sha(build / "BUILD.json"), "fresh_owned_modules": modules, "public_proofs": public_count,
              "owned_declarations": owned_count, "replays": outcomes, "sources_unchanged": True, "allowed_axioms": sorted(ALLOWED),
              "external_reference_artifact_guard": True, "fresh_external_modules": len(fresh_external),
              "historical_fingerprint": {"all_owned": historical_all, "literal_main": historical_main},
              "current_fingerprint": {"all_owned": actual_all, "literal_main": outcomes.get("ReplayLiteralMain", {}).get("closure")},
              "historical_full_external_graph_available": False,
              "historical_owned_names_types_owners_kinds_axioms_identical": True,
              "literal_main_owned_dependency_set_identical": args.kind == "upper",
              "numeric_history_is_retained_not_resealed": True,
              "limits": ["Pinned Lean compiler/kernel/runtime/machine and standard axioms remain trusted.", "The upper theorem uses the earlier gSharp coefficient; the quadratic refinement is a written proof.", "A closure-size drift is not a claim to identify the unavailable historical external node-by-node graph."]}
    write(out / "VERIFICATION.json", report)
    print(json.dumps(report, indent=2), flush=True)


if __name__ == "__main__":
    main()
