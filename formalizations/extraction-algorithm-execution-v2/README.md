# Algorithm audit execution revision v2

This is a separate execution scope for the existing frozen mathematical scope. It does not replace or edit any of its 340 inputs, 459 theorem roots, 276 model roots, or 65 strict controls. The mathematical/manuscript source remains `6a8e2d3637152983cda6d4723e23474098f4ecfb`; the original source-manifest SHA256 is `8b99b7d144b8c27a4092028f557a47bf01fb38d0ded6eef543a4abd612e51386`.

The completed local original runner positively replayed 56276 declarations at kernel trust zero and rejected all 65 exact same-type corruptions. Its frozen v1 post-run reader then rejected control 52's actual empty axiom list, written by the helper as one LF byte. The separately bound local reader-v2 accepted that canonical encoding and reverified the complete original evidence. Commit `13fecc54661d56e57647a27fce5f30d0f43fa57a` preserves the failure, revised reader provenance, logs and complete evidence archive. This format correction requires no local kernel replay. This new prefix does not claim that its own hosted CI has run.

`EXECUTION_HASHES.json` independently binds this prefix's driver, reader, shared execution checks, tests, workflow template and provenance. It also records all 31 original audit recipe input hashes from the unchanged original mathematical manifest. The manifest is intentionally separate from the original 340-input binding. New execution files are not represented as existing in the older mathematical source commit.

The parent installs `extraction-algorithm-v2.workflow.yml` byte-for-byte as `.github/workflows/extraction-algorithm-v2.yml`. Every production entry point checks that actual path against the independently frozen template, and checks every execution input, the manifest and actual workflow against the immutable event commit's Git blobs. The old `.github/workflows/extraction-algorithm.yml` can be retired in an explicit later Git commit; its original template and reader remain preserved in the original mathematical scope. A v2 artifact records only the v2 workflow as `CI_CONTEXT.actual_workflow`. The original v1 workflow is recipe provenance, not an execution claim.

The new producer uses the original hosted-only storage guard and exact pinned toolchain/cache policy, then invokes the unchanged `reproduce.py --github-actions --fresh` from `extraction-algorithm-audit`. It verifies the 340 source inputs, all protected earlier scopes, new execution inputs, installed workflow and actual binary hashes before and after the run. All temporary/cache/evidence output stays in the exclusive hosted-runner directory. The hosted mode remains forbidden on local Windows/WSL, and no local D-storage bypass is introduced.

The downloadable artifact includes the original scope exports, new execution manifest and every new execution input. The independent download job checks all file hashes, actual event/workflow/run identity, unchanged source/recipe/execution bindings, freshness, every kind/type/axiom report, whole trust-zero dependency closure, every positive control type closure and every exact same-type kernel rejection. Canonical LF-only empty axiom lists decode as empty; empty bytes, duplicate names, blank lines, whitespace, CRLF and unexpected axioms are rejected. Existing substantive checks are retained and explicit original stage commands and exclusive hosted replay-output locations are additionally checked.

Preparation and metadata checks (read-only; no builds):

```sh
python3 selftest.py
python3 execution.py freeze
python3 execution.py check --without-installed-workflow
```

The `--without-installed-workflow` option is only a metadata preflight before the parent copies the template. It is never used by the producer or artifact reader. After installation, use `python3 execution.py check`. The actual workflow has two jobs: fresh producer and downloaded-artifact verification. Its artifact upload includes the bound `.gitignore` metadata file, under the exclusive evidence directory only.

Downloaded verification at the exact run checkout:

```sh
python3 verify_artifact.py /path/to/download --expected-commit EVENT_SHA --run-id RUN_ID --run-attempt ATTEMPT
```

`selftest.py` exercises the reader on a deliberately labelled local fixture derived from real full replay evidence; it does not run Lean or claim a hosted CI result. The pre-install fixture alone mocks workflow installation and event-Git-blob checks; all production entry points require them. It rejects malformed axiom encodings and independent alterations to execution binding, exact stage command, control prerequisite, actual workflow, and evidence bytes. All fixtures stay in D-backed temporary storage. The local completed evidence remains sealed and unchanged.

The independently read mathematics still excludes whole-program Turing time, a uniform efficient offline-net finder, unassumed provider/primitive costs, and later unbound author modules. Reviews and tests in this prefix are internal AI checks, not a claim of external human certification.
