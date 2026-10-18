# Separate hosted CI plan and local storage boundary

The new template is exclusively for the completion scope. It leaves the old
`extraction-connections.yml` unchanged. Current state is implementation/preflight,
not a hosted CI PASS. The parent installs the exact bound template at the new
workflow path and dispatches after the bound source and audit metadata are pushed.

Default local execution still imports the exact D guard, validates its hash,
verifies the mounted loop backing image and uses the shared D lock/cache. CI
requires explicit `--github-actions`, hosted Linux/X64 environment variables,
actual event checkout SHA, `/home/runner/work` workspace and the standard
`/home/runner/work/_temp` root. It explicitly rejects Windows and WSL. The CI
branch cannot be selected by a local default invocation. Its runner environment
is an operational check, not a cryptographic runner attestation.

Every CI-created temporary/cache/toolchain/evidence path is beneath the run-id
and attempt-specific runner temporary directory. Build outputs use only the
runner's own checkout. The one Mathlib source/cache is resolved by the exact
Lake manifest; no author build or local D cache is mounted into GitHub. Full
Git history is fetched so the aa1 historical blob safeguard remains effective.

The workflow pins checkout/upload/download actions by resolved commit and
checks out the exact event SHA with credentials not persisted. The elan
installer URL names an exact Git commit. Its download hash is recorded and the
installed official Linux x86-64 Lean/Lake binaries must match the fixed local
release hashes before and after the mathematical audit. Mathematical source,
all local configs/imports, audit programs and manuscript/provenance inputs are
bound separately. The installed workflow must equal its bound template.

Fresh checking covers 518 theorem roots,175 model definitions,84 strict
same-type controls and their full dependency closure. No optional subset mode
is used by CI. Each control has positive type-closure replay and exact-root
kernel type-mismatch rejection. Pre/post source and tool hashes must agree;
all logs and summaries have SHA-256 bindings. Upload occurs even on failure;
an incomplete artifact cannot pass the separate download verifier. The verifier
compares its downloaded manifest against the exact checkout and independently
checks all stage hashes, scope counts, selected axiom reports, whole positive
replay, all controls and run identity. It is separate transport/evidence
verification, not a second full kernel replay.

Standard runner memory varies with repository visibility. The runtime records
actual available memory, leaves 1GiB headroom and caps Lean at 11GB; it fails if
less than 5GB is available to Lean or less than 3GiB disk remains after cache
bootstrap. A resource failure is not mathematical PASS. Workflow timeout is
120 minutes; the full replay stage permits 120 minutes, bounded additionally
by the workflow budget. Initial resource/time estimates are from local limited
replay and must be replaced by measured full local and hosted results.

Primary operational references checked during preparation:
- https://docs.github.com/en/actions/reference/runners/github-hosted-runners
- https://docs.github.com/en/actions/tutorials/store-and-share-data
- https://github.com/actions/upload-artifact
- https://github.com/actions/download-artifact
