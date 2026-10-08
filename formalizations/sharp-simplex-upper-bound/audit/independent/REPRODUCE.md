# Reproduce the independent sharp Main audit

## Inputs and prerequisites

Use this directory's `received/` inputs and `composed-source/`. The certified composition is the original 203-file readable patch plus the exact one-file supplement. Original sources remain separately in `entry005-sharp-upper-main-20261007/`.

Provide pinned Lean 4.34.1 and the nine clean dependency checkouts specified by `composed-source/scripts/pins.json`. Dependency cache paths are read-only sources for sparse symlink overlays; no owned Entry005/Mxym/OAI output from an earlier audit is imported as an owned fallback. The independently verified 714 source tree is also needed for the byte-for-byte baseline comparison.

Environment overrides:

- `ENTRY005_PACKAGES_DIR`: directory containing the nine pinned dependency repositories
- `ENTRY005_LEAN_ROOT`: Lean 4.34.1 toolchain root, containing bin/lean and src/lean
- `ENTRY005_714_FORMAL`: the independently audited 714 delivery's formal source directory
- `ENTRY005_714_CACHE`: the previously verified official-dependency cache, lib/lean directory
- `ENTRY005_533_CACHE`: optional secondary official-dependency cache; set to a nonexistent empty location when the first cache is complete

The scripts default to the verified neighboring audit layout used in the recorded run. The source-inventory helper and Lean check templates are included locally. No network download is performed. Source providers are unique, hashed, and pinned. Missing official objects are freshly compiled from their pinned sources.

## Run in a fresh extracted directory

The reproduction bundle omits `rebuild/`, so a fresh extraction cannot reuse this audit's owned outputs. Existing result files are harmless: resumption requires an actual regular output with the recorded matching source and object hashes; otherwise the source is recompiled.

Run:

    python3 independent_build.py
    python3 prepare_checks.py
    python3 independent_checks.py

Expect `ALL_123_OWNED_REBUILT_PASS`, then `INDEPENDENT_FULL_SHARP_MAIN_AUDIT_PASS`.

For an inventory-only preflight, use `python3 independent_build.py --prepare-only`. This does not constitute proof certification.

Inspect:

- `checks/FINAL_PASS.json`
- `checks/owned-source-set.json`
- `checks/import-closure.json`
- `checks/unresolved-source-closure.json`
- `checks/ownership-summary.json`
- `checks/owned-declarations.json`
- `logs/ReplayLiteralMain.log`
- `logs/ReplayAllSafeOwned.log`
- four negative-control logs and nine positive literal checks

Expected final mathematical counts: 123 modules, 848 public proofs, 1,833 owned declarations, Main replay closure 54,277, all-owned replay closure 55,067. Both replays use a genuinely empty kernel environment at trust level zero and exclude all nonstandard axioms.

No `.olean`, `.ilean`, or official dependency tree is included in the evidence archive.
