# Verification and trust boundary

This package contains preserved proof sources, historical submitted evidence, independent audit programs and selected audit results, and public reproduction scripts. Historical results are not new results from your computer. A successful integrity check is not a Lean proof check; a successful import is not an explicit empty-kernel replay.

## 1. Check the sealed package

From the extracted package root, run:

```sh
python3 scripts/verify_integrity.py
```

The verifier checks the existing `SOURCE_MANIFEST.json` and `SHA256SUMS`, the exact declared payload inventory, byte-identity anchors for original sources, the public derivative ledger, provenance records, and retained license notices. It rejects missing or unlisted payload files, payload symlinks, and nonregular payload entries. It does not repair or replace a manifest when files differ.

The runtime directories `.git/`, `project/.lake/`, `vendor/`, and `replay-evidence/` are excluded from the sealed payload and archives; their contents are not verified by the package seal. Exclusions apply only to real directories, not symlinks at those roots. Keep local dependency caches and generated verification outputs outside the payload. The mathematical verifier separately checks the dependencies it actually uses.

SHA-256 records establish consistency with the recorded bytes. They are not digital signatures or independent evidence of the package publisher's identity. Retain an independently obtained archive digest if authenticity matters.

## 2. Prepare the pinned environment

The recorded audit used the official Linux x86_64 Lean 4.34.1 release, commit `5045d0056413266e57c625dcd7c365b10e377c52`. The recorded `lean` executable SHA-256 is `e8baaa71855a616dc351028f3ad2200051b0671f423a1696a100e809302d5550`. Toolchain file hashes and upstream source/release details are in [TOOLCHAIN_FILES_SHA256.json](provenance/TOOLCHAIN_FILES_SHA256.json) and [DEPENDENCY_PROVENANCE.json](provenance/DEPENDENCY_PROVENANCE.json).

Provide Python 3, that pinned Lean toolchain, and a dependency project containing usable compiled artifacts and tracked source checkouts for every package pinned by [lake-manifest.json](project/lake-manifest.json):

| Package | Revision |
| --- | --- |
| mathlib | `d13f23b723b8a846827a245b89c10fc7d3f11612` |
| plausible | `118aa17ee84656b8bd727fef7c458ee8c833385c` |
| LeanSearchClient | `ddf04cf3949fa556442341e87d47f9f6e6074707` |
| importGraph | `e928b72544873815af278d38681b31c0293588e3` |
| proofwidgets | `106ff4fafc74ef4ac99d81dbf3ab399118f497a5` |
| aesop | `355695d523e41d0554926416cba2a2b3544fbbc9` |
| Qq | `6a489d9af5d0c47e5b259e2e8bcdfc1811b5a259` |
| batteries | `f2effa3d803fda822b1f97b806c47cf2adfbcbc2` |
| Cli | `e92c9f15fdfacc8536f31cfb3b7ad26c3c8cd204` |

The dependency-project argument refers to a Lake project with these packages under `.lake/packages/`. Matching version labels alone are insufficient; exact revisions, source state, toolchain, and usable compiled artifacts matter. The public source package does not bundle all dependency source trees, the Lean distribution, or their full caches. The wrapper has no fetch/bootstrap mode; it requires prepared local dependencies.

The supplied wrapper reuses dependency caches read-only and writes owned outputs into a new directory. If the official pinned Floor module is absent from the caches, it builds that source in its own overlay. It does not edit the dependency checkout or shared cache to fill the gap. This is not a source rebuild of all mathlib.

## 3. Run the public mathematical verifier

```sh
python3 scripts/verify.py --lean-bin PATH --dependency-project PATH --output NEWDIR
```

- `--lean-bin PATH`: the pinned distribution's executable directory, containing `lean`.
- `--dependency-project PATH`: the prepared Lake dependency project described above.
- `--output NEWDIR`: a new output directory, separate from the sealed payload and dependency caches.
- Optional `--extra-mathlib PATH`: an additional cache for the exact same pinned mathlib revision when the primary cache is incomplete.

The wrapper checks integrity and dependency provenance, freshly compiles all **65 owned modules**, runs the supplied and independent positive/negative controls, checks the exact target, ownership/closure and axiom inventories, and runs both explicit replay programs. It uses no previously compiled owned Lean objects. Fresh owned-object hashes are recorded and compared to the independent audit. Sources and loaded artifacts from all 1,322 actual defining modules are also hashed and compared. Exact source hashes and reused dependency-artifact hashes must match; newly rebuilt owned objects and missing official overlays may differ because compiled objects can contain build-path metadata. Such differences are recorded rather than accepted as evidence of a changed theorem. Source identity, declaration/graph/axiom checks, and fresh empty-kernel replay provide the mathematical checks. The exact arithmetic regressions run under both Python modes; a single invocation performs one owned-module rebuild, not two. Packaging guard controls are included as well. The 65 modules comprise 45 inherited geometric modules, 18 remainder modules, and the two aggregate imports.

The preserved [lakefile.toml](project/lakefile.toml) still names `ContinuumGeometric` as its default target. A bare `lake build` therefore does not reproduce this stronger theorem's complete verification. Use the public wrapper for the stated suite.

The final success record is `NEWDIR/VERIFICATION.json`; intermediate evidence includes `BUILD.json`, `OWNED_OBJECT_SHA256.json`, `OWNED_OBJECT_COMPARISON.json`, `DEPENDENCY_SYMLINKS.json`, `ACTUAL_MODULE_SOURCE_ARTIFACT_HASHES.json`, `ACTUAL_MODULE_COMPARISON.json`, `PUBLIC_ROOT_SUMMARIES.json`, `CONTROLS.json`, `PACKAGING_GUARD_CONTROLS.json`, compressed `FAST_*` JSON inventories, and `logs/`. Read the generated report and logs before reporting a pass. A failed or interrupted run establishes only the stages recorded as completed. Missing dependencies, unknown imports, parser errors, and unknown identifiers are infrastructure failures, not successful mathematical rejection of a negative control. The full suite includes substantial compilation and two complete kernel replays; no fixed wall-clock or memory guarantee is made.

The historical audit independently ran fresh normal-Python and Python `-O` rebuilds and compared all 65 objects and compiler logs. To exercise the wrapper itself under both Python modes, use distinct new output directories:

```sh
python3 scripts/verify.py --lean-bin PATH --dependency-project PATH --output NEWDIR_NORMAL
python3 -O scripts/verify.py --lean-bin PATH --dependency-project PATH --output NEWDIR_OPTIMIZED
```

These commands do not by themselves assert byte identity between the two new runs; their corresponding output records must be compared. Different output paths can themselves change compiled-object bytes, so record those differences and use the source, declaration, axiom, and replay checks rather than equating object-byte differences with proof failure. Historical mode-identity results are separately preserved below.

## 4. What the recorded independent audit established

The [audit report](audit/independent/AUDIT_REPORT.md) and [machine-readable verdict](audit/independent/FINAL_AUDIT.json) record:

- **65 fresh owned-module rebuilds**, with byte-identical objects and compiler logs in normal Python and Python `-O`.
- **1,454 owned declarations**, selected by actual defining module: 1,114 theorem/helper declarations, 320 definitions, 6 inductives, 8 constructors, and 6 recursors.
- **568 public source theorems** whose printed axiom sets agree with independently collected/raw closure information, including five with no axioms.
- **1,445 safe owned declarations** and a full safe-owned closure of **35,620 declarations from 1,322 defining modules**.
- **34,919 declarations** in the main theorem's closure; **34,923** in the endpoint-union replay.
- **28 submitted positive probes** compiling and **28 deliberately false submitted controls** rejected for their intended mathematical diagnostics. These include 21/22 inherited base probes/controls and 7/6 new probes/controls.
- **33 additional independent theorems in 4 positive modules**, **6 independent false fixtures**, and **15 exact rational arithmetic regressions**, with matching reports and logs across Python modes.
- An independent total/partial-domain semantic probe and a concrete nonempty dyadic configuration.

The [rebuild/control record](audit/independent/REBUILD_AND_CONTROL_VERIFICATION.json), [owned module list](audit/independent/OWNED_MODULES.json), [public theorem inventory](audit/independent/INDEPENDENT_PUBLIC_NAMES.json), and [source inspection](audit/independent/SOURCE_INSPECTION.json) provide details. Compressed inventories and graph data are [FAST_OWNED_INVENTORY.json.gz](audit/independent/FAST_OWNED_INVENTORY.json.gz), [FAST_PROOF_GRAPH.json.gz](audit/independent/FAST_PROOF_GRAPH.json.gz), and [FAST_CLOSURE_SUMMARY.json.gz](audit/independent/FAST_CLOSURE_SUMMARY.json.gz). Their decompressed bytes match the independent audit's original JSON, as recorded in the derivative ledger.

The recorded audit checked 43,783 dependency symlink targets and recorded source plus loaded-object/private/server artifact hashes for each actual defining module. That historical count describes its environment; a new cache layout need not have the same number of links. See [ACTUAL_MODULE_SOURCE_ARTIFACT_HASHES.json](audit/independent/ACTUAL_MODULE_SOURCE_ARTIFACT_HASHES.json).

## 5. The actual empty-kernel replay

The submitted [KernelReplay.lean](submitted-evidence/KernelReplay.lean) is an **import-only test**. It does not create an empty environment or replay declarations. Its preserved successful import logs cannot establish either of the following independent replay results.

1. [ReplayClosure.lean](audit/checks/ReplayClosure.lean) gathers the main theorem, compact corollary, and proved blocker roots, their stored dependencies, and required inductive companions. It rejects unexpected axioms and unsafe/partial nodes, creates `mkEmptyEnvironment 0`, and calls the official kernel replay operation. It checks that endpoint types and universe parameters are unchanged. The recorded result is `EMPTY_KERNEL_REPLAY_PASS 34923 declarations` in [ReplayClosure.log](audit/independent/logs/ReplayClosure.log).
2. [ReplayAllSafeOwned.lean](audit/checks/ReplayAllSafeOwned.lean) selects every safe root by its actual defining module, including private/generated names outside the visible namespace prefixes, and performs the same fresh replay. The recorded result is `ALL_SAFE_OWNED_EMPTY_KERNEL_REPLAY_PASS 35620 declarations` in [ReplayAllSafeOwned.log](audit/independent/logs/ReplayAllSafeOwned.log).

The only permitted axiom dependencies are `propext`, `Classical.choice`, and `Quot.sound`. Nine inherited compiler-generated partial `*_unsafe_rec` helpers are explicitly inventoried; none appears in the stored type/value closure of any safe owned declaration. This is not a claim that every compiler-generated declaration in the environment is safe.

The audit also tested its actual production ownership guard with a deliberately injected global axiom outside the project namespace. The guard rejected it; the adversary never entered the proof build. The historical result is recorded in [PRODUCTION_GUARD_CONTROL.json](audit/independent/PRODUCTION_GUARD_CONTROL.json). The public wrapper reruns this isolated self-test using the same production closure collector with only the injected import and owned-module entry added. The genuine proof build and replay remain separate from the adversarial fixture.

## 6. Semantic and boundary checks

[ExactMain.lean](audit/checks/ExactMain.lean) expands the target predicates in an empty context. [SemanticProbe.lean](audit/checks/SemanticProbe.lean) checks ordinary interval volume, concrete nonvacuity, and genuinely partial functions whose remainder bound holds only eventually. [SEMANTIC_REVIEW.md](audit/independent/SEMANTIC_REVIEW.md) explains the proof-to-statement correspondence; it is a source review, not an extra kernel theorem about the English text.

The [independent controls](audit/controls/independent/) test signed fractional powers with a nonzero remainder, strict activation/buffer endpoints, and actual counterexamples to dropping selected hypotheses. [UniversalFamilyControl.lean](audit/controls/independent/UniversalFamilyControl.lean) proves that every positive-measure candidate set has an adaptive logarithmically syndetic configuration defeating it. Thus the family-before-set quantifier order is essential. The [boundary audit](audit/independent/BOUNDARY_AUDIT_REPORT.txt) records the control suite; [semantic_exact_checks.py](scripts/semantic_exact_checks.py) retains its 15 exact arithmetic regressions.

These controls detect specific erroneous variants. The universal statement rests on the closed theorem and its proof, not on testing finitely many numerical cases.

## 7. Remaining trust and limits

The verification depends on the official Lean implementation, the correctness of its kernel/replay machinery, the supplied toolchain, and ordinary mathlib definitions representing the intended real, topological, and measure-theoretic objects. Replaying stored dependency terms checks their kernel validity; it does not independently re-elaborate every dependency source file or audit the compiler implementation.

The independent review was AI/model-based. No external human referee, novelty or priority certification, new license, practical construction algorithm, or theorem beyond [THEOREM.md](THEOREM.md) is claimed.

## 8. Create a local archive without resealing

```sh
python3 scripts/make_archive.py --output FILE
```

Choose an output outside the source tree. The script validates the existing seal and produces a deterministic `.tar.gz` rooted at `formalizations/continuum-remainder-avoidance/`, reporting its SHA-256. Reproducibility is for the same payload and Python/zlib implementation. Excluded runtime directories are not included. This command does not regenerate a seal to hide changed files and does not publish, upload, or push anything.

The separate `scripts/seal_release.py --initialize` is for maintainers creating an initial seal and refuses an existing seal. It is not a remedy for a recipient's failed integrity check. Investigate a mismatch against the received package and its recorded provenance instead.
