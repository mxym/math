# Verification and trust boundaries

## Prerequisites

Provision the official Linux x86-64 Lean 4.34.1 distribution (compiler commit `5045d0056413266e57c625dcd7c365b10e377c52`) and the nine clean pinned Git checkouts listed by `project/lean/lake-manifest.json`. A dependency project must expose them under `.lake/packages/`. The source package contains the 995 nonofficial class-field source modules and all owned sources, but no compiled objects or large dependency cache.

The public entry point is Python 3.12+ and does not download dependencies or mutate them. Strict compiler/runtime hash checks are platform-specific; other platforms require a separately validated configuration. Source mathematical claims are not platform-specific binary-hash claims.

    python3 -B scripts/verify_integrity.py
    python3 -B scripts/test_release_integrity.py --output /outside/package-controls.json
    python3 -B scripts/test_source_completeness.py --output /outside/source-controls.json
    python3 -B scripts/verify.py --lean-bin /path/to/lean/bin --dependency-project /path/to/dependency-project --preflight-only --output /path/to/new-preflight
    python3 -B scripts/verify.py --lean-bin /path/to/lean/bin --dependency-project /path/to/dependency-project --extra-cache /optional/read-only/official/lib/lean --output /path/to/new-full-run

Choose a nonexistent output directory outside the sealed release. The default resource guards stop if this run allocates more than 1.5 GiB or the filesystem has less than 750 MiB free; `--max-new-bytes` and `--minimum-free-bytes` explicitly configure these limits. These are observed stop conditions checked before/after commands and at ten-second waits, not an operating-system quota preventing every instantaneous overshoot. They are checked again after the output manifest is written and before the final PASS marker. Official-cache symlinks do not copy the cache. This version has no resume shortcut: recovering observation of a still-running process is different from restarting against old outputs. A new resume implementation would require its own review and an explicit same-run ledger boundary. `--extra-cache` may be repeated, but is considered only for exact-reference official artifacts; no owned or CFT cache object is accepted. `--preflight-only` verifies source/pin/artifact planning and explicitly does not prove Main. It emits a preflight marker, never the full verification marker.

## Full run

1. Fail closed on missing, changed, unlisted or nonregular package files, symlinks, malformed metadata, altered required payload, bad source identities and incomplete checksums. Validation never repairs or reseals a package.
2. Verify the official toolchain distribution, every pinned dependency revision/origin and clean tracked source state. Resolve all 8,129 modules in the complete recursive import source closure, including implicit Init and Lean/Lake audit-runtime sources, to exactly one provider. The completed combined audit resolves these same modules plus the three newly built audit helpers. Missing nonofficial source cannot be hidden by an `.olean`.
3. Build an isolated overlay from SHA-bound official artifacts and their sidecars. Freshly compile official modules that lack a matching recorded artifact; toolchain artifact mismatch is fatal. All external cache paths remain read-only and are excluded from the owned/CFT search boundary.
4. Freshly compile every one of the 129 main modules, five bridges and 995 CFT source modules into the new output tree in dependency order. No resume shortcut or pre-existing owned/CFT object is accepted. The complete source set, commands, exit codes, logs and output digests are recorded.
5. Recreate the three standard axiom declarations from stock Lean; compare actual imported types/universe parameters. Check the combined owned inventory, explicit compiler-generated exclusions, safe-root dependency closure, and literal no-premise Main type against the completed independent certificate.
6. Run positive endpoint checks and intended type-mismatch negative controls. Run a small successful empty-kernel replay and a stored-proof-corruption rejection control.
7. Saturate the literal Main stored type/body/family dependencies and replay all 125,368 selected constants with official `Kernel.Environment.replay` into `mkEmptyEnvironment 0`, seeded with no imported constants. Check the exact root, type, permitted axioms and declared closure; reject partial, unsafe or missing proof dependencies.
8. Revalidate the entire source closure and toolchain snapshot, all fresh main/sidecar artifacts, all three helper sources and artifacts, selected official cache links, every recorded run-log hash, and stock/literal/combined/Main result and closure hashes. Require the resolved module set to equal the source graph plus exactly three audit helpers. Seal all run records and files in `OUTPUT_MANIFEST.json`, bound to this exact release identity. Only then emit `QUADRATIC_ORDERS_MAIN_PUBLIC_REPLAY_PASS` and `FINAL_VERIFICATION.json`.

The original completed Main replay took about 16 minutes for its kernel stage alone. The total full-source build can take substantially longer. This can be a long, memory-intensive build, especially class-field and empty-kernel stages. Keep sufficient disk/memory available. Source compilation alone, stock imports alone, cached `#print axioms` alone or a historical author log is not this replay.

## Validate completed run artifacts

After the full run prints its `OUTPUT_MANIFEST_SHA256`, retain that digest separately. Run the read-only production checker:

    python3 -B scripts/verify_output.py --output /path/to/full-run --expect-manifest-sha256 THE_RECORDED_DIGEST
    python3 -B scripts/test_output_integrity.py --output /outside/output-controls.json

`verify_output.py` checks recorded-run artifact integrity and internal bindings. It does not rerun the compiler or kernel, prove that an arbitrary historical execution really happened, or authenticate a manifest without an independently trusted digest. Its success marker is `RUN_OUTPUT_INTEGRITY_PASS`, never a new theorem-replay PASS. Normal official-cache symlinks are permitted only as recorded file-level bindings. The test uses explicitly synthetic artifact fixtures and calls the exact production checker in normal and optimized Python; a positive synthetic fixture is not a Lean proof claim.

## Completed audit versus new wrapper

The mathematical independent audit already executed its fresh builds and empty-kernel Main replay. Its CFT build was independently completed once and then authenticated for the round-five audit; the same 995-module build is not gratuitously repeated during packaging. The new public wrapper defaults to a fresh CFT rebuild for an external reproducer. The release preparation report must state separately which wrapper checks were actually executed on the final extracted copy. Do not infer a new end-to-end wrapper run from the older mathematical certificate or from packaging tests.

The old offline-v3 helper is only a verifier of the author's original cache-bound evidence. Independent fresh object bytes can differ, so it is not used to certify this package's fresh build. No cross-environment equality to author `.olean` bytes is claimed.

## Integrity limits and release operations

Hash manifests detect partial/accidental tampering and coordinated ordinary metadata changes through an immutable payload anchor. They are not signatures: authenticate the final archive SHA256 or exact repository commit through an independent trusted channel. Validation assumes a quiescent filesystem, not a malicious concurrent filesystem adversary. Lean kernel/runtime correctness and the standard axioms are explicit trust assumptions.

`seal_release.py --initialize` is a one-time maintainer action only when both seal files are absent and all frozen required payloads match. It refuses resealing. `make_archive.py` archives a validated byte snapshot with deterministic metadata and refuses output inside the package. Neither command publishes anything. The final independent release-copy review is a separate required gate.
