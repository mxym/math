# Verification and trust boundaries

## Recommended complete offline run

Use Python 3.12+, the official Linux x86-64 Lean 4.34.1 distribution (commit `5045d0056413266e57c625dcd7c365b10e377c52`) and the nine dependency checkouts pinned by `project/formal/lake-manifest.json`. All dependency tracked sources must be clean. The compiler distribution's recorded files, every recursive import source and reused external artifact are SHA256 checked. The same source set can be checked on other platforms with appropriately independently audited tooling, but this release's strict binary reference check is deliberately platform-specific.

    python3 -B scripts/verify_integrity.py
    python3 -B scripts/test_release_integrity.py --output /outside/package-controls.json
    python3 -B scripts/test_source_completeness.py --output /outside/source-controls.json
    python3 -B scripts/verify.py --lean-bin /path/to/lean/bin       --dependency-project /path/to/project-with-lake-packages       --extra-cache /optional/path/to/external/lib/lean       --output /path/to/new-run

The dependency project contains `.lake/packages/{mathlib,batteries,aesop,Qq,Cli,LeanSearchClient,importGraph,plausible,proofwidgets}`. Extra caches are optional read-only search roots. An output directory must be new and outside the sealed release. No network provisioning has been executed or claimed for this release. Provision the official pinned toolchain and dependency sources separately. `scripts/bootstrap.py` is a convenience alias for the same complete verifier with already provisioned dependencies, not a downloader.

## What production verification does

1. Fail closed on missing/changed/unlisted files, bad metadata or checksums, symlinks and nonregular members, or a rewritten required inventory. It does not repair or reseal anything. It imports package helpers only after this check.
2. Validate actual toolchain file hashes, compiler revision, nine Git revisions and tracked-clean dependency status.
3. Enumerate exact 123 owned modules and 848 public proof names; recursively resolve all 4,743 imports to unique pinned source providers. **A cached `.olean` never substitutes for a missing nonofficial source.** The full source closure must match the independent source hashes before cache reuse.
4. Select only exact-reference external objects, rehashing all relevant sidecars. Missing/mismatched non-toolchain external objects are freshly built from validated pinned sources; official toolchain mismatches are rejected. All supplied caches remain read-only. An isolated sparse overlay contains only external namespaces, never old Entry005/Mxym/OAI objects.
5. Freshly compile all 123 owned modules with `autoImplicit=false`, `maxSynthPendingDepth=3`, `warningAsError=true`; require every owned dependency and output to be a fresh regular file. No incremental-20 mode, resume shortcut or source-less module fallback is accepted.
6. Check actual public declarations and all 1,833 module-owned declarations against independent type/owner/kind/axiom inventories, rejecting unsafe/partial/opaque/custom-axiom nodes.
7. Execute nine literal positive checks, three intended type-mismatch negatives and the forged-kernel-proof rejection control.
8. Run immutable independent Lean programs that collect actual recursive declarations and replay them into `mkEmptyEnvironment 0`. Expected counts: Main 1 root/54,277 declarations; all-owned 1,833 roots/55,067 declarations; `skipped=[]`, `trust=0`, `empty=true`. Imports alone are not accepted as replay.
9. Run the exact rational corroboration in normal and optimized Python, in the external output directory, and recheck every sealed release byte.

Expected final marker: `SHARP_UPPER_MAIN_PUBLIC_REPLAY_PASS`. Inspect `FINAL_VERIFICATION.json`, `BUILD.json`, `EXTERNAL_ARTIFACTS.json`, the public/owned inventories and full local logs. The unchanged legacy ZonotopeVolume may emit an informational `Try this: [apply] abel_nf`; this is not a warning and is not hidden.

## Recorded evidence versus public reproduction

`audit/independent/` is a public derivative of the completed independent composite-source audit. Its historical paths and private delivery IDs have been redacted only in nonmathematical copies. Some large JSON/log files are compressed. `audit/mathematical/` is a separately scoped traditional argument/source-semantic review, not itself a kernel certificate. `project/evidence/`, `project/reviews/` and the original README are historical author-side checkpoints. They do not certify this package's current inventory.

The production wrapper, packaging guards and documentation are derived release tools; a fresh run from the final extracted archive is required before a parent release gate. The preparation report outside the archive records that result without modifying an already sealed archive. No source-only archive is proof of its own publication.

## Integrity and trust limits

The immutable required-payload identity, source identity ledger, current manifest and checksums protect against accidental or partial mutation and coordinated ordinary metadata edits. They are not signatures: someone able to rewrite the validator and every internal record together can create a different self-consistent package. Authenticate the final archive SHA256 or exact repository commit through an independent trusted channel. Validation assumes a quiescent filesystem; it is not a sandbox against adversarial concurrent filesystem replacement.

Proof checking relies on the recorded Lean kernel/runtime and standard logical axioms `propext`, `Classical.choice`, `Quot.sound`. External object hashes bind the audited runtime artifacts; they do not claim a fresh rebuild of every dependency. Recursive proof declarations are actually rechecked at trust zero. Source semantic review, kernel acceptance, toolchain provenance, package integrity, rights and publication status are separate claims.

`seal_release.py --initialize` is an explicit one-time maintainer operation only when both seal files are absent and every frozen required payload already matches. It refuses to reseal. `make_archive.py` only archives an already valid snapshot, uses deterministic metadata and refuses outputs inside the sealed tree. All hostile entry-point controls run with normal Python and `-O`; they use exceptions, not removable assertions.
