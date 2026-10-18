#!/usr/bin/env python3
"""D-only reader tests. Synthetic CI-shaped fixtures are NOT hosted CI evidence."""
from pathlib import Path
from unittest.mock import patch
import copy, hashlib, json, os, shutil, subprocess, sys, tarfile, tempfile
import execution as e
import verify_artifact as reader

a = e.a
ARCHIVE_SHA256 = "017452204e7a55a76d20a8f0c2d4d16eec0415a937a679562af447d308f2ac6f"
EVIDENCE_MANIFEST_SHA256 = "b65c69f2c31500efe2136152d54dd9a806bc769263983bcd4f000a43b75642fd"


def main():
    sys.path.insert(0, "/mnt/d/math/tmp/extraction-full-lean-20261016")
    from ensure_d_storage import configure_env
    configure_env(dict(os.environ))
    e.source_precheck()
    if Path(reader.__file__).resolve()!=e.ROOT/"verify_artifact.py" or a.ROOT!=e.BASE:raise RuntimeError("Test imported a different execution reader or math driver")
    temporary_parent = Path("/mnt/d/math/tmp/extraction-resume-20261018/algorithm-execution-v2-tests")
    temporary_parent.mkdir(exist_ok=True)
    results = []
    with tempfile.TemporaryDirectory(prefix="reader-", dir=temporary_parent) as temporary:
        root = Path(temporary)
        candidate = root / "EXECUTION_CANDIDATE.json"
        a.dump(candidate, e.proposed_manifest())
        case = root / "axioms.txt"
        for raw, expected in [(b"\n", set()), (b"propext\n", {"propext"}), (b"Classical.choice\nQuot.sound\npropext\n", a.ALLOW)]:
            case.write_bytes(raw)
            if e.axiom_set(case) != expected:
                raise RuntimeError("Valid canonical axiom-list rejected")
        malformed = [b"", b"\n\n", b"propext", b"propext\n\n", b"propext\npropext\n", b" propext\n", b"propext \n", b"\r\n", b"propext\r\n", b"propext\rQuot.sound\n", b"Classical. choice\n", b"\xff\n"]
        for raw in malformed:
            case.write_bytes(raw)
            try:
                e.axiom_set(case)
            except RuntimeError:
                continue
            raise RuntimeError("Malformed axiom-list accepted " + repr(raw))
        results.append(dict(test="canonical_axiom_encoding", valid=3, malformed_rejected=len(malformed), status="PASS"))

        # No production bypass flag exists. Only this internal unit test supplies
        # a workflow binding, because the parent has not installed the new file.
        binding = dict(path=e.WORKFLOW, sha256=a.sha(e.ROOT / e.TEMPLATE), bound_template_sha256=a.sha(e.ROOT / e.TEMPLATE))
        with patch.object(e, "MANIFEST", candidate), patch.object(e, "workflow_binding", return_value=binding), patch.object(e, "check_commit"):
            # Only uncommitted fixture execution metadata is mocked; production
            # entry points always require exact event Git blobs and actual file.
            e.check()
            fixture = root / "SYNTHETIC_NOT_HOSTED_CI"
            fixture.mkdir()
            output_name = "algorithm-SYNTHETIC-READER-TEST"
            output = fixture / output_name
            output.mkdir()
            archive = e.BASE / "verification/algorithm-20261018T192021588552Z-full-evidence.tar.gz"
            if a.sha(archive) != ARCHIVE_SHA256:
                raise RuntimeError("Sealed local replay archive changed")
            with tarfile.open(archive) as handle:
                members = handle.getmembers()
                if len({member.name for member in members}) != len(members):
                    raise RuntimeError("Duplicate sealed archive entry")
                raw_manifest = handle.extractfile("EVIDENCE_HASHES.json").read()
                if hashlib.sha256(raw_manifest).hexdigest() != EVIDENCE_MANIFEST_SHA256:
                    raise RuntimeError("Sealed local evidence manifest changed")
                hashes = json.loads(raw_manifest)
                if {member.name for member in members} != set(hashes) | {"EVIDENCE_HASHES.json"}:
                    raise RuntimeError("Sealed archive inventory changed")
                for member in members:
                    if not member.isfile() or Path(member.name).is_absolute() or ".." in Path(member.name).parts:
                        raise RuntimeError("Unsafe sealed archive member")
                    data = handle.extractfile(member).read()
                    if member.name != "EVIDENCE_HASHES.json" and hashlib.sha256(data).hexdigest() != hashes[member.name]:
                        raise RuntimeError("Sealed archive entry changed")
                    target = output / member.name
                    target.parent.mkdir(parents=True, exist_ok=True)
                    target.write_bytes(data)
            commit = a.run("git", "rev-parse", "HEAD")
            identity = dict(source_commit=commit, run_id="0", run_attempt="1", repository="mxym/math", workflow_ref="mxym/math/" + e.WORKFLOW + "@refs/heads/SYNTHETIC", workflow_commit=commit)
            hosted_output = Path("/home/runner/work/_temp/extraction-algorithm-0-1/evidence") / output_name
            stages = a.readj(output / "STAGES.json")
            stages[-1]["command"][-1] = str(hosted_output / "AuditInvocation.lean")
            invocation = (e.BASE / "Audit.lean").read_text().replace('"verification/algorithm-', json.dumps(str(hosted_output / "algorithm-"))[:-1])
            (output / "AuditInvocation.lean").write_text(invocation)
            a.dump(output / "STAGES.json", stages)
            summary = a.readj(output / "SUMMARY.json")
            summary["runtime_guard"] = "GITHUB_HOSTED_LINUX_RUNNER_VERIFIED"
            summary["stages"] = stages
            summary["audit_invocation_sha256"] = a.sha(output / "AuditInvocation.lean")
            a.dump(output / "SUMMARY.json", summary)
            latest = dict(directory=output_name, summary_sha256=a.sha(output / "SUMMARY.json"))
            a.dump(fixture / "LATEST.json", latest)
            binary_hashes = a.readj(e.BASE / "CI_EXECUTION_POLICY.json")["binary_sha256"]
            binaries = {name: dict(path="SYNTHETIC_NOT_EXECUTED/" + name, sha256=digest) for name, digest in binary_hashes.items()}
            before = e.snapshot(binaries)
            for name in ["PRE_AUDIT.json", "POST_AUDIT.json"]:
                a.dump(fixture / name, before)
            context = dict(identity, actual_workflow=binding, execution=e.execution_binding(), status="GITHUB_CI_AUDIT_COMPLETED_PENDING_ARTIFACT_DOWNLOAD_CHECK", source_manifest_sha256=e.MATH_MANIFEST_SHA256, latest=latest, actual_mathematical_command=["reproduce.py", "--github-actions", "--fresh"], actual_mathematical_cwd=e.BASE.relative_to(e.REPO).as_posix())
            a.dump(fixture / "CI_CONTEXT.json", context)
            a.dump(fixture / "BOOTSTRAP_BINARIES.json", binaries)
            a.dump(fixture / "BOOTSTRAP.json", dict(installer_url=a.readj(e.BASE / "CI_EXECUTION_POLICY.json")["elan_init_url"], installer_sha256="SYNTHETIC_NOT_DOWNLOADED", execution=e.execution_binding(), github=identity))
            a.dump(fixture / "TEST_FIXTURE.json", dict(status="SYNTHETIC_READER_FIXTURE_NOT_HOSTED_CI", actual_kernel_replay_rerun=False, source="Sealed genuine local full replay; hosted context/path fields adapted ONLY to exercise the portable reader. This fixture is deleted after the tests."))
            for name in e.ORIGINAL_EXPORTS:
                shutil.copy2(e.BASE / name, fixture / name)
            e.copy_execution_evidence(fixture)

            def seal():
                a.dump(fixture / "ARTIFACT_HASHES.json", {path.relative_to(fixture).as_posix(): a.sha(path) for path in sorted(fixture.rglob("*")) if path.is_file() and path != fixture / "ARTIFACT_HASHES.json"})

            def verify():
                return reader.verify(fixture, commit, "0", "1")

            seal()
            verified = verify()
            if (verified["roots"], verified["definitions"], verified["controls"], verified["kernel_declarations"]) != (459, 276, 65, 56276):
                raise RuntimeError("Full synthetic fixture scope mismatch")
            results.append(dict(test="full_reader_on_explicit_synthetic_fixture", status="PASS", genuine_local_closure=56276, controls=65, hosted_ci_claim=False))

            def reject(name, changes, reseal=True):
                originals = {path: path.read_bytes() for path in changes}
                try:
                    for path, value in changes.items():
                        path.write_bytes(value)
                    if reseal:
                        seal()
                    try:
                        verify()
                    except (RuntimeError, ValueError, KeyError) as error:
                        results.append(dict(test=name, status="REJECTED_AS_REQUIRED", reason=str(error)))
                    else:
                        raise RuntimeError("Altered fixture accepted " + name)
                finally:
                    for path, value in originals.items():
                        path.write_bytes(value)
                    seal()

            def encoded(value):
                return (json.dumps(value, indent=2, ensure_ascii=False) + "\n").encode()

            empty = output / "algorithm-control-52-axioms.txt"
            if empty.read_bytes() != b"\n":
                raise RuntimeError("Expected genuine empty-axiom control changed")
            reject("byte_tamper_without_resealing", {empty: b"propext\n"}, False)
            reject("empty_bytes_axiom_list", {empty: b""})
            reject("unexpected_control_axiom", {empty: b"TrustMe\n"})
            target = output / "algorithm-control-52-type-dependencies.txt"
            names = target.read_text().splitlines()
            names[names.index("True.intro")] = "EffectiveEncoding.compileLabelWord_length"
            reject("forged_type_prerequisites", {target: ("\n".join(names) + "\n").encode()})
            changed = copy.deepcopy(context)
            changed["actual_workflow"]["path"] = ".github/workflows/extraction-algorithm.yml"
            reject("old_workflow_misreported_as_actual", {fixture / "CI_CONTEXT.json": encoded(changed)})
            changed = copy.deepcopy(context)
            changed["execution"]["execution_revision"] = "v1"
            reject("execution_revision_mismatch", {fixture / "CI_CONTEXT.json": encoded(changed)})
            changed_stages = copy.deepcopy(stages)
            changed_stages[-1]["command"][3] = "-j2"
            changed_summary = copy.deepcopy(summary)
            changed_summary["stages"] = changed_stages
            raw_summary = encoded(changed_summary)
            changed_latest = dict(latest, summary_sha256=hashlib.sha256(raw_summary).hexdigest())
            changed_context = dict(context, latest=changed_latest)
            reject("weakened_replay_command", {output / "STAGES.json": encoded(changed_stages), output / "SUMMARY.json": raw_summary, fixture / "LATEST.json": encoded(changed_latest), fixture / "CI_CONTEXT.json": encoded(changed_context)})
            exported_reader = fixture / "execution-v2/verify_artifact.py"
            reject("changed_exported_reader", {exported_reader: exported_reader.read_bytes() + b"# altered\n"})
            changed = copy.deepcopy(before)
            changed["execution"]["execution_manifest_sha256"] = "0" * 64
            reject("execution_prepost_mismatch", {fixture / "POST_AUDIT.json": encoded(changed)})
            changed = a.readj(fixture / "SOURCE_HASHES.json")
            changed.pop(next(iter(changed)))
            reject("missing_original_bound_input", {fixture / "SOURCE_HASHES.json": encoded(changed)})
            verify()

    # Plain/spoofed GitHub flags cannot bypass the unchanged WSL guard.
    process = subprocess.run([sys.executable, str(e.ROOT / "ci_driver.py"), "environment"], capture_output=True, text=True)
    if process.returncode == 0:
        raise RuntimeError("Local CI-mode bypass unexpectedly accepted")
    results.append(dict(test="local_hosted_mode_forbidden", status="REJECTED_AS_REQUIRED", exit_code=process.returncode))
    protected = e.source_precheck()
    report = dict(status="EXECUTION_V2_INTERNAL_READER_TESTS_PASS_NOT_HOSTED_CI", original_inputs=len(protected), source_manifest_sha256=e.MATH_MANIFEST_SHA256, candidate_execution_manifest=e.proposed_manifest(), tests=results, kernel_rerun=False, fixtures_deleted=True)
    destination = e.ROOT / "verification"
    destination.mkdir(exist_ok=True)
    a.dump(destination / "SELFTEST.json", report)
    print(json.dumps({key:value for key,value in report.items() if key!="candidate_execution_manifest"}, indent=2))


if __name__ == "__main__":
    main()
