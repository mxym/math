# Source, audit, and public-copy provenance

The package separates three layers: the received submission, the independent verification of that submission, and the public-copy packaging. The public copy corrects an evidence description and makes verification portable. It does not alter the submitted mathematical Lean proof or create a new license.

## 1. The received source

The independent audit received `prescribed-family-continuum-remainder-lean.zip`, exactly **1,875,200 bytes**, with SHA-256:

`b8fb480b8888321b864cf3c58a81cad3dfc223cc837071b940be58a93cca0e51`

Its original source-freeze record has SHA-256:

`48841d7974245af1cf7de677580ecec934ed6310bbbb21f2456cbe6b77081e71`

Its original manifest has SHA-256:

`521428348fb113864c6af3d010156ca18f91d97bdc9fac4bdadaf6da2af01fa4`

The independent extraction checked all 228 original manifest entries and the exact 229-file extracted inventory, rejecting unsafe archive entries. It checked all 18 newly frozen remainder sources and established that the 45 inherited geometric modules matched the earlier audited version-3 source archive. The earlier archive digest is:

`747386b02dbd12ae6f7b763d79fdb1e9bd70ca1e195e1b84d943cb0bcff82cb5`

These are hashes of historical inputs, not hashes of the newly packaged public archive. The received ZIP itself is not required to be present in this source package. [INPUT_ARCHIVE.json](provenance/INPUT_ARCHIVE.json) retains its identity by filename, size, and digest; the original [MANIFEST.json](submitted-evidence/MANIFEST.json), [source-freeze.json](submitted-evidence/source-freeze.json), and [base-source-comparison.json](submitted-evidence/base-source-comparison.json) retain their original internal path conventions.

## 2. The mathematical sources remain unchanged

All **110 submitted project `.lean` files**, including proof modules and project-local probes, are copied byte-for-byte. The 65 owned modules rebuilt by the audit consist of 45 geometric modules, 18 remainder modules, and 2 aggregate imports. Those counts describe different inventories and should not be conflated.

The submitted `lean-toolchain`, `lakefile.toml`, `lake-manifest.json`, and `PublicTheorems.json` are also preserved. In particular, the old default Lake target is retained; see [VERIFICATION.md](VERIFICATION.md) for the correct full-suite command.

Two useful direct source anchors are:

- [FinalProof.lean](project/ContinuumRemainder/FinalProof.lean): `f54bc7886852aaf0a36a537556bbe92d193eb49944863f36f87bcd05c122f912`
- [Specification.lean](project/ContinuumRemainder/Specification.lean): `0a98b8858428b1cd7c34263358c67a769121d049ae964008bd91abcd1382102e`

The complete public-path identity map is [ORIGINAL_SOURCE_SHA256.json](provenance/ORIGINAL_SOURCE_SHA256.json). The public integrity checker validates these source anchors as well as the package seal. A new package archive hash is expected because layout, documentation, and included audit artifacts differ from the original submission.

## 3. The replay attribution correction

The submitted [KernelReplay.lean](submitted-evidence/KernelReplay.lean) contains only:

```lean
import ContinuumRemainder.FinalProof
```

Its successful import with `--trust=0` is an import check. The file does not create an empty environment, collect a closure, or explicitly replay stored declarations into a new kernel environment. The submitted README's stronger description of that check is therefore not supported by the file or its empty success log.

The submitted file is preserved unchanged. The [historical README](submitted-evidence/README.original.txt), [replay record](submitted-evidence/kernel-replay-record.json), and [import logs](submitted-evidence/kernel-trust-zero-fresh.log) remain separately identified as submitted evidence. Some public prose/log copies have nonmathematical path redactions, as recorded in the derivative ledger. Keeping historical evidence does not endorse its erroneous replay description.

The independent audit supplied the actual programs [ReplayClosure.lean](audit/checks/ReplayClosure.lean) and [ReplayAllSafeOwned.lean](audit/checks/ReplayAllSafeOwned.lean). They construct `mkEmptyEnvironment 0` and invoke kernel replay over the stored dependency closure. The endpoint-union replay checked 34,923 declarations; the all-safe-owned replay checked 35,620 declarations from all 1,445 safe owned roots. Their [endpoint log](audit/independent/logs/ReplayClosure.log) and [all-safe log](audit/independent/logs/ReplayAllSafeOwned.log) document the results.

These are independently implemented verification results. They do not retroactively turn the submitted import-only program into a different program. No mathematical source correction was needed to obtain them.

## 4. What changed in the public copy

[PUBLIC_DERIVATIVE_LEDGER.json](provenance/PUBLIC_DERIVATIVE_LEDGER.json) records source origins, original and public hashes, destination paths, and adaptation descriptions. The main packaging changes are:

- New root documentation states the exact theorem, reading route, verification boundary, provenance, and licensing status.
- Submitted evidence is grouped under `submitted-evidence/`. Obsolete checkpoint prose is kept under [historical/](submitted-evidence/historical/), including `DEPENDENCIES.md` and `CONTINUATION_CONTRACT.md`.
- Selected historical prose and logs omit private transport identifiers or replace machine-specific paths. These public derivatives must not be represented as byte-identical copies when the ledger says otherwise.
- Independent audit and boundary-test programs are grouped under `audit/checks/` and `audit/controls/`. The public closure collector accepts an output location rather than writing to the original audit machine's path.
- Large independent JSON inventories are compressed reproducibly; their decompressed bytes are unchanged.
- Public report derivatives explain that the replay-attribution correction is now implemented while preserving the historical mathematical verdict and counts.
- Public scripts check the seal, run the verification suite with explicit local dependencies and a new output directory, and create a local archive. They neither fetch dependencies implicitly nor publish the result.

The public package deliberately does not bundle previous build directories, shared dependency caches, all original transient logs, or private delivery metadata. The selected evidence remains linked to its original hashes. This is an inspectable derivative source package, not a claim that the full original audit workspace has been reproduced byte-for-byte.

## 5. Audit provenance and independence

The original independent audit report's SHA-256 is:

`6dbf9d37febf998651796c70ee479e214202ccaf2b8f197b5614789b0d990adb`

The bundled [AUDIT_REPORT.md](audit/independent/AUDIT_REPORT.md) is its explicitly identified public derivative, so its hash differs. The [FINAL_AUDIT.json](audit/independent/FINAL_AUDIT.json) retains the historical verdict and adds the public-copy correction status; references to original report hashes identify the original record, not the derivative's current bytes.

The independent audit rebuilt the owned source, examined the exact statement and construction, checked declaration ownership and axiom closure, ran genuine empty-kernel replay, and constructed independent semantic and hostile controls. It was independent AI/model review and Lean verification. It is not external human peer review, authorship adjudication, or certification of novelty or priority.

The [semantic review](audit/independent/SEMANTIC_REVIEW.md) and [boundary report](audit/independent/BOUNDARY_AUDIT_REPORT.txt) retain the division between semantic inspection and executable evidence. The former's conditional wording describes that review's role before the separate compiler/replay layer was completed; the final audit records the combined result.

## 6. Dependency and licensing provenance

[DEPENDENCY_PROVENANCE.json](provenance/DEPENDENCY_PROVENANCE.json) records the pinned Lean distribution and all nine package revisions. [TOOLCHAIN_FILES_SHA256.json](provenance/TOOLCHAIN_FILES_SHA256.json) records the checked distribution files. The existing notices under [third_party_licenses/](third_party_licenses/) come from the earlier checked base release and are retained unchanged.

The collection notice preserves attribution to inherited OpenAI/math material and its existing license; dependency notices apply to their respective components. No new personal author credit or blanket proof-package license is inferred from those notices. [LICENSE_NOTICE.md](LICENSE_NOTICE.md) explains this boundary. Verification of a mathematical claim is not a grant of rights to all material in the package.

## 7. Release and publication are separate

Preparing or archiving this package is a local operation. It is not evidence that a repository was pushed, a release was published, an external reviewer endorsed it, or a rights holder approved new license metadata. Any future distributor should preserve the original-source anchors, the submitted-versus-independent evidence distinction, the derivative ledger, and the applicable existing notices.
