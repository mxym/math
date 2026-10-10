# Literal verification evidence

`kernel-r2` is a completed fresh Lake build, separate 26-module source build,
206-root audit, 53,415-declaration empty-kernel trust-zero replay, and three
rejected source mutations. Only propext, Classical.choice and Quot.sound occur.
The precise toolchain binary hash, dependency source checks and all source and
object hashes are in verification.json. The compressed closure list expands
to the literal replay output; SHA256SUMS binds the retained evidence files.

SOURCE_BLOBS.used.json preserves that run's exact manifest. The subsequent
addition of fetch_cache.sh to the manifest does not change any Lean source,
verifier, audit root, toolchain or dependency. A second clean run is being
recorded separately; no old development log is presented as that run.

The Windows/WSL run is a source-isolated kernel check on the authorized device,
not an independent human review. The GitHub Actions workflow is configured for
an independent hosted runner; no successful hosted run is claimed here until
its actual result has been retrieved and recorded.


## Current core extension: core-r1

This is a new run completed on 2026-10-10, not a reuse of the older boundary
profile receipt. See `core-r1/verification.json` and `core-r1/PROVENANCE.json`.
It freshly builds all 31 modules, replays 57,811 declarations from an empty
trust-zero kernel for 222 roots, and rejects six source mutations. The exact
axioms are Classical.choice, Quot.sound, and propext. All source hashes stayed
unchanged. Full logs, closure names, and mutated sources are retained in
`core-r1/complete-logs.tar.gz`; `core-r1/SHA256SUMS` binds the original log files.

This run used an authorized WSL Ubuntu-22.04 host and previously cached but
source-pinned external dependencies. Fresh owned-source directories and the
empty-kernel replay are both explicit in the report. GitHub Actions is a
separate clean-runner check, not the same run under another label.

## Independent GitHub-hosted core verification: core-ci

The clean Ubuntu 24.04 GitHub-hosted run
https://github.com/mxym/math/actions/runs/38044016825 succeeded on proof commit
50b22571a8132cdc3582f0efa8e329c5fe88aeb8. Its original 44-file artifact is retained
byte-for-byte as `core-ci/original-actions-artifact.zip`; its SHA-256 is
`cc25c294504edf35e7d348313c9a32988d01a1b07f808d15ba0e82e43640022c`.

`core-ci/verification.json` is extracted from that original artifact, not
reconstructed from a local report. `core-ci/COMPARISON.json` records a direct
comparison: all source hashes, all 31 compiled-object hashes, the entire replay
summary, and all six negative-control results equal the local core-r1 run.
The current proof/configuration bytes also match those recorded source hashes.
This verifies the stated partial closure only, not the absent sharp theorem.
