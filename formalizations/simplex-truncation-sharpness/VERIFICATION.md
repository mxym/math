# Reproduce and verify

**This package proves the literal `Entry005.truncationSharpnessGoal`. It does not prove the prescribed upper bound `Entry005.sharpMainGoal`.** The mathematical source is frozen independently of the public packaging tools.

## 1. Authenticate and inspect the source archive

Compare the archive SHA-256 against a trusted external release record or repository commit before executing its scripts. Internal hashes are not signatures. Extract into a new directory. All archive members are regular files under `formalizations/simplex-truncation-sharpness/`; paths, member bytes, normalized metadata, and deterministic gzip/tar output are checked by the packaging controls.

From that package directory, run:

```sh
python3 -B scripts/verify_integrity.py
python3 -O -B scripts/verify_integrity.py
```

This checks an immutable expected inventory, an independently bound required-payload hash inventory, every current manifest/checksum record, original-input identity, the exact two redacted input derivatives, all 125 mathematical source identities, audit inputs, scripts, documentation, and retained license records. It rejects omitted or extra files, duplicate JSON keys, unsafe paths, symlinks, non-regular members, and coordinated changes to source/provenance followed by outer resealing. Only a real `.git/` directory is excluded; builds, logs, cache and bytecode directories belong outside the package.

`SOURCE_MANIFEST.json` and `SHA256SUMS` seal the current public payload. `project/BUNDLE_MANIFEST.json` describes the original 290-file input before the declared metadata redactions. `project/SOURCE_FILES_SHA256.json` is an older 215-record checkpoint. Neither historical manifest is the public current-payload verifier. Do not regenerate them.

## 2. Provision exact official dependencies

The supported reference platform is Linux x86-64, Python 3.11+, curl, git, tar with zstd, and ripgrep. Lean is 4.34.1, commit `5045d0056413266e57c625dcd7c365b10e377c52`; mathlib is `d13f23b723b8a846827a245b89c10fc7d3f11612`. All nine package pins are in `project/formal/lake-manifest.json`. No `lake update` is used.

For a complete network-backed bootstrap into a fresh external work directory:

```sh
python3 -B scripts/bootstrap.py --work /absolute/new-sharpness-work
```

With the exact official toolchain already available:

```sh
python3 -B scripts/bootstrap.py \
  --work /absolute/new-sharpness-work \
  --lean-bin /absolute/lean-4.34.1-linux/bin
```

The outer bootstrap validates the sealed package, copies the input project to that fresh work directory, then runs its preserved official bootstrap using Bash. The original bootstrap downloads the official compiler release (archive SHA-256 `47bf4bbd78f70c2e9670598ab7124d92b6efb7330ff33e5fbb4030f6fd72e4e4`), provisions locked dependencies and official mathlib cache, and runs its source verifier. The public wrapper then performs the independent fresh replay described below. Existing proxy/TLS settings are retained. Nothing is installed globally and no cache or log is written into the sealed package.

The original audit reused already verified official dependencies and did not repeat the network download/bootstrap transaction. The public final-copy check likewise uses the offline/cache route below. The network-backed wrapper is provided for reproduction; a package-integrity pass alone does not claim that its downloads were executed in this release preparation.

## 3. Fresh independent verification with existing dependencies

A dependency project must contain `.lake/packages/` with all nine exact Git revisions and clean tracked sources. Supply a fresh output directory outside the release:

```sh
python3 -B scripts/verify.py \
  --lean-bin /absolute/lean-4.34.1-linux/bin \
  --dependency-project /absolute/pinned-dependency-project \
  --output /absolute/new-sharpness-replay
```

Optional `--extra-cache /absolute/pinned-external-lib-lean` may be repeated for additional independently verified external artifacts. It is not a cache of owned proofs: the runner selects only non-owned module artifacts, checks their exact recorded hashes, and never places an old owned namespace on its Lean search path. Existing dependency caches are read-only. Sparse symlink leaves and any missing external source builds go into the new output directory; no multi-gigabyte dependency copy is made.

Before creating build output or loading the non-TCB source-inventory helper, the runner verifies package integrity. It then checks every official toolchain-file hash, all nine dependency pins and tracked cleanliness, all 4,745 source-import closure records, and the exact source-derived 850 public names. The 4,620 external artifact families are matched against the retained independent-audit reference; absent or mismatched non-toolchain families are rebuilt from pinned sources.

It rebuilds all 125 owned mathematical modules from source, with `autoImplicit=false`, into an initially empty owned-output directory. Every owned dependency must already be a freshly built regular file before a dependent owned module compiles. There is no resume, skip-build, stale-owned fallback, or success based only on an existing log.

The independent Lean checks then verify:

1. All 850 public declarations and their printed recursive axiom sets, with exact declaring-module/theorem ownership.
2. The entire 1,849-declaration module-owned inventory, including private/generated declarations, literal printed types, kinds, owners, safety flags and axiom sets. All are safe and nonpartial; no custom axiom or opaque owned constant is accepted.
3. The exact expanded literal target and an arbitrary inscribed competitor's volume comparison.
4. Intended type-mismatch rejection of upper-Main substitution and omission of the actual-defect formula premise.
5. Rejection of a deliberately malformed proof term by the same trust-zero kernel replay API.
6. Actual replay of all 1,849 roots and their 55,163-declaration recursive closure into `mkEmptyEnvironment 0`, with no skipped root and unchanged root types/universe parameters.
7. Fifteen independent exact-rational geometry/determinant/defect/centroid corroborations, including wrong-sign and wrong-factor controls, in both normal and optimized Python. These finite tests do not replace the arbitrary-dimensional Lean theorem.

Successful completion prints `SHARPNESS_PUBLIC_REPLAY_PASS` and writes `FINAL_VERIFICATION.json` outside the package. Full fresh compiler/check logs remain there; compact inventories are gzip-compressed. No package-supplied `.olean` is distributed or accepted as an owned proof substitute.

## 4. Packaging controls and deterministic archive

Run the hostile production-entry regressions without Lean or network access:

```sh
python3 -B scripts/test_release_integrity.py --output /absolute/guard-results.json
```

The suite itself executes the integrity, archive, fresh-build and bootstrap entry points under normal Python and `-O`. Tampered inputs must be rejected before archive/build output is created or unvalidated helpers can execute. It also checks one-time explicit seal initialization, refusal to reseal an existing package, repeated-byte archive determinism, fresh extraction, unsafe output rejection, and preservation of preexisting outputs on validation failure.

To make an archive of this already sealed source:

```sh
python3 -B scripts/make_archive.py --output /absolute/simplex-truncation-sharpness.tar.gz
```

The packager only verifies; it never creates, updates, repairs, or silently re-signs manifests. `seal_release.py --initialize` is an explicit maintainer-only initialization operation. It requires both seals absent and the fixed required inventory already bound; ordinary users should not run it. A new payload needs separately reviewed versioned metadata and a new external digest.

## Evidence and trust boundaries

[The retained independent technical report](audit/independent/TECHNICAL_REPORT.md), [semantic review](audit/independent/SEMANTIC_REVIEW.md), and [audit layout guide](audit/README.md) describe the original mathematical audit. Its compact evidence includes `FINAL_PASS.json`, `independent-verification.json`, `empty-kernel-replay.json`, `ownership-summary.json`, per-module build/resolution records, exact-source fetch records, and the direct replay/negative-control logs. The newly derived public tooling is verified separately; those original reports are not silently treated as an audit of packaging changes.

The logical axioms are only `propext`, `Classical.choice`, and `Quot.sound`, or subsets. Trust remains in the pinned Lean kernel implementation/runtime and in the mathematical interpretation of literal definitions, which is separately reviewed. This is not a fresh rebuild of all mathlib or all OpenAI/math, a proof of compiler correctness, an external human referee report, or a novelty certificate.

Internal integrity records cannot authenticate a coordinated replacement of the validator and every record. Use a trusted external archive digest or repository commit. The tooling assumes a quiescent local filesystem and trusted Python/system executables; it is not a sandbox against concurrent hostile filesystem mutation. Dependency artifacts are pinned to the recorded official/cache provenance or freshly rebuilt from pinned sources; actual empty-kernel replay then rechecks the selected logical closure.

The full prescribed stability upper Main, all-maxima classifications, arbitrary-parameter centroid identities, best-maximum excess, optimal upper constants, Banach–Mazur estimates and Rogers–Shephard claims remain outside this sharpness checkpoint.
