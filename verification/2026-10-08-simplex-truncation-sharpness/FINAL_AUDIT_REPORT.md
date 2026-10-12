# Independent final-copy audit: simplex truncation sharpness v2

**Result: PASS. No blocking finding.** The authenticated v2 public archive was inspected, safely extracted into a new directory, and the extracted public `scripts/verify.py` was run once end to end. All checks completed successfully with process exit code 0. This review did not edit the submitted source, regenerate its seals, publish to GitHub, or repeat the underlying mathematical research.

## Exact identity

- Public archive: `simplex-truncation-sharpness-source-20261007-v2.tar.gz`
- Archive SHA-256: `add152175863fb929ecf58510bb48ff9fc8be7e234fe45d72953e56333355b2c`
- Archive length: **3,510,798 bytes**
- Payload: **365 unique regular files**, all under `formalizations/simplex-truncation-sharpness/`
- All effective member paths, member bytes, normalized metadata, gzip CRC, and equality to the complete `stage-v2` payload passed independent inspection. Canonical path-only PAX headers represent long filenames.
- The archive bytes were manually materialized as exclusive regular-file writes under this audit's previously nonexistent `fresh/` directory. No package code was executed before external digest and member validation.
- Original input ZIP: `entry005-actual-truncation-sharpness-20261007.zip`, **835,939 bytes**, **290 regular files**
- Original input SHA-256: `85f444c30899ea9a5b76b7cb912ca10165f5c2302714d5ee199e033a69fd8074`
- Original ZIP CRC and every original-file hash were independently checked. Exactly **288 input members are byte-identical**. Only `project/sources/delivery-lineage.json` and `project/sources/pyramid-provenance.json` differ; their JSON structures and all nonstring values are preserved, with four private-delivery strings replaced by explanatory placeholders.
- All **125 mathematical modules** are byte-identical to the original input. `Targets.lean` SHA-256 is `8bc873bff65384b67b05d3d4fd405bdf9c728e0befb0e6ac355373fa3ded7c94`.

The superseded v1 SHA-256 was `4a27cf57bf01f2c1076d6e492548e08ca910c74b3ede6b13ea901a1f0cfdfe43`. Independent v1→v2 comparison found only the corrected `INPUT_ARCHIVE.json` public-mapping sentence and its required validator/hash/seal bindings changed. The proof files and verification runner are unchanged. The complete replay result in this report applies to v2.

## Actual verification results

1. The fresh extracted package passed `verify_integrity.py` under both ordinary Python and Python `-O`: **365 frozen files**.
2. The full public verification runner checked the pinned Lean **4.34.1**, commit `5045d0056413266e57c625dcd7c365b10e377c52`, distribution file hashes; all **nine** exact dependency revisions and clean tracked sources; and the complete **4,745-module** source/import closure.
3. Independently of the runner, this audit recomputed all **4,620 external artifact families**, comprising **27,651 artifact files** and **3,820,053,063 bytes read**, from the original independent audit's actual file resolution. Every family, package identity, and source hash matched the sealed reference. These were hash reads, not a multi-gigabyte cache copy.
4. The public runner accepted exactly those **4,620** external reference families. **Zero external modules required rebuilding.** It rebuilt all **125 owned modules** from the fresh extracted sources into a new output directory, in approximately **366.06 seconds** of summed compile time. There were **zero warnings or errors**, and no owned-cache fallback.
5. This audit separately enumerated and rehashed all **125 actual fresh owned `.olean` files** against the runner's build receipts and source hashes. All owned outputs are regular files, with no symlinks anywhere in the owned tree. Neither the external overlay nor the actual toolchain library contains an Entry005/Mxym/OAI owned namespace.
6. All **850 public proof declarations** passed source-name, actual theorem ownership, and recursive-axiom comparison. All **1,849 module-owned declarations**, including private/generated ones, passed type, kind, module, axiom, safety, and nonpartial checks. Only subsets of `propext`, `Classical.choice`, and `Quot.sound` were accepted.
7. Literal-target and arbitrary-inscribed-competitor positive checks passed. Upper-Main substitution and omitted-defect-formula negative fixtures failed for their intended type mismatches. The malformed-proof kernel negative control was actually rejected by the pinned replay API.
8. **All 1,849 owned roots and their 55,163-declaration recursive closure were replayed into `mkEmptyEnvironment 0`, trust level 0, with no skipped roots and unchanged root types/universe parameters.** Both exact replay markers appear in the new run's log.
9. The **15 exact-rational corroborations** passed under both normal and optimized Python, including wrong-sign and wrong-factor controls. Their two JSON outputs are identical.
10. The seven public independent Lean checking programs are byte-identical to the prior independent audit's checking programs. The final source snapshot and archive SHA were independently rechecked after the run and remain unchanged.

The completed runner printed:

`SHARPNESS_PUBLIC_REPLAY_PASS 125 fresh modules; 850 public; 1849 owned; 55163 empty-kernel declarations`

## Independent hostile checks and runner review

Two independently implemented tamper cases, each executed in normal and optimized Python, passed:

- Inject executable top-level code into `source_inventory.py`, recompute ordinary outer seals, and invoke the production verification runner. The fixed required payload binding rejects it before helper execution or build-output creation; the sentinel remains absent.
- Change a proof-source file and its ordinary original-source provenance record, then recompute ordinary outer seals. The distinct required payload binding still rejects it before output creation.

The detailed boundary review is in `RUNNER_TRUST_REVIEW.md`. No blocking issue was found. Its important limits remain: externally authenticate the complete archive; trust the pinned kernel/runtime and local Python/system environment; assume a quiescent filesystem; do not interpret internal hashes as signatures or this procedure as a malicious-filesystem sandbox. The optional network bootstrap was reviewed but not executed. Reusing hash-matched external artifacts is not a fresh rebuild of all dependencies.

Separately, the parent release-preparation task reported and supplied a passing `PACKAGING_GUARD_CONTROLS-v2.json`: **83 cases / 666 production invocation records**, normal and `-O`, including archive determinism and fresh extraction. Its scope is packaging/entry-point integrity only. This final-copy audit inspected that result but did not rerun that entire suite; the independent attacks and full fresh kernel run above are this audit's own results.

## Scope of the mathematical claim

The package proves the literal `Entry005.truncationSharpnessGoal`. The prescribed upper `Entry005.sharpMainGoal` remains open **in this checkpoint**. This release does not contain or certify a later Main candidate, the full paper, all maximizing-simplex classifications, arbitrary-parameter centroid identities, best-maximum upper estimates, or other unproved extensions. It is not a human-referee endorsement or novelty certificate.

## Evidence

- `ARCHIVE_AND_INPUT_IDENTITY.json`: all-member archive/source identities and safe fresh extraction
- `V1_TO_V2_REVIEW.json`: exact revision boundary
- `METADATA_REDACTION_REVIEW.json`: the two metadata-only input derivatives
- `INDEPENDENT_CHECKS_IDENTITY.json`: seven retained Lean checks
- `EXTERNAL_REFERENCE_RECOMPUTED.json.gz`: independent external-family hash receipts
- `INDEPENDENT_NEGATIVE_CONTROLS.json`: four independent production-runner attack invocations
- `integrity-normal.log`, `integrity-optimized.log`: fresh package guard results
- `full-verify.log`, `full-verify.exitcode`: the complete run's entry-point result
- `replay/BUILD.json`, `replay/EXTERNAL_ARTIFACTS.json`: fresh compilation and selected external-artifact receipts
- `replay/PUBLIC_AXIOMS.json.gz`, `replay/OWNED_INVENTORY.json.gz`: newly collected declaration evidence
- `replay/logs/`: fresh compiler, ownership, semantic, negative-control, and empty-kernel replay logs
- `replay/FINAL_VERIFICATION.json`: complete public runner result
- `FINAL_OUTPUT_CROSSCHECK.json`: independent final artifact/source/closure cross-check
- `RUNNER_TRUST_REVIEW.md`: reviewed trust boundary and explicit limitations
- `AUDIT_EVIDENCE_SHA256.json`: hashes of the compact audit evidence and reports
