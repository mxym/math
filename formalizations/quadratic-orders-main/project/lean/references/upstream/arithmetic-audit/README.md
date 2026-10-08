# Isolated arithmetic foundation audit

This project keeps external foundations separate from the main entry002 proof library. It uses Lean 4.34.1 and exactly the main project's mathlib revision. It proves conditional implications to `PrincipalSplitPrimeSupplyTarget` and `MainTarget` from the displayed genuine number-field prime-ideal counting asymptotic. Both unconditional targets remain open.

The source layout is portable:

```text
upstream/
  arithmetic-provenance.json
  arithmetic-recursive-source-audit.json
  classfield-mathlib-imports.txt
  pnt-mathlib-imports.txt
  patches/
  ClassFieldTheory/Lean4/...
  PrimeNumberTheoremAnd/PrimeNumberTheoremAnd/...
  arithmetic-audit/
    lakefile.lean
    lake-manifest.json
    lean-toolchain
    ArithmeticSupplyRayBridge.lean
    ArithmeticSupplyPNT.lean
    ArithmeticSupplyDensityConversions.lean
    ArithmeticSupplyRayConductor.lean
    ArithmeticSupplyFromPrimeIdealPNT.lean
    ArithmeticSupplyMainFromPrimeIdealPNT.lean
    ConductorAudit.lean
    ConductorCompilerAudit.lean
    PrimeIdealAudit.lean
    PrimeIdealCompilerAudit.lean
    ArithmeticAudit.lean
    PntAudit.lean
    DensityAudit.lean
    RayCompilerAudit.lean
    PntCompilerAudit.lean
    DensityCompilerAudit.lean
    verify.py
    source_scan.py
```

All source-directory paths in `lakefile.lean` are relative. The delivered project requires no workspace-specific paths or symlinks. Its `.lake` directory is build state and should be excluded from the deliverable.

## Provenance

OpenAI/math is fixed at `adc7f1241b42e322a6451854ab7e4b4c146bf78a`. Its manifest pins ClassFieldTheory at `2eb22d6485af45f29c5219de6c49f196a61c4f49` and PrimeNumberTheoremAnd at `c39a751132c88b6e8080b74c74023fd95b3d8be0`. The exact compatibility patches from that same OpenAI/math commit were applied verbatim. Their SHA-256 hashes and every imported post-patch source hash are recorded in the adjacent provenance and source-audit JSON files. License snapshots accompany both source packages.

The class-field bridge imports 995 internal external-package modules and 381 direct Mathlib modules. The PNT bridge imports four internal external-package modules and 16 direct Mathlib modules. The delivered sources may contain exactly these closures instead of the larger upstream packages; the configured libraries build the required endpoints without the unused package-wide targets.

## Bootstrap and verify

Install the official Lean toolchain named by `lean-toolchain`, with `lake` available on `PATH`. From this directory run:

```sh
python3 verify.py --bootstrap
```

The script checks exact patch and imported-source hashes, fetches the pinned official mathlib dependency graph, gets its official cache, and compiles the selected endpoints. It then runs the endpoint axiom checks and recursively traverses every referenced declaration's stored type and body, including private declarations. The strict source scanner rejects disabled kernel checking and other proof escapes. Seven ordinary opaque values with real bodies are explicitly reviewed in `arithmetic-opaque-source-review.json` and also audited as separate roots; their stored bodies are traversed. It compares that traversal with Lean's `collectAxioms`, and rejects any extra axiom, unsafe dependency, partial dependency, or missing declaration. The expected logical axioms are only `propext`, `Classical.choice`, and `Quot.sound`.

Once dependencies have been bootstrapped, rerun without downloads:

```sh
python3 verify.py
```

Fresh logs and structured recursive-audit summaries are written into this project's `logs/` directory. The separate class-field compilation involves 995 source modules and can take substantial time.

## What the endpoints establish

`ArithmeticSupplyRayBridge` uses an actual finite abelian intermediate-field extension and actual arithmetic Frobenius. For every actual ray modulus it produces a ray class field, with complete splitting equivalent to existence of a nonzero field generator satisfying the modulus's actual local congruences and principal-ideal equality. A separate elementary bridge proves that this generator has an actual ring-of-integers representative whose principal ideal is exactly the original integral prime ideal. It does not assume such a field as input to prove its existence.

`ArithmeticSupplyPNT` proves the actual rational-prime counting ratio tends to one. Its Wiener–Ikehara and WeakPNT foundations are proved in the exact patched PNT package.

`ArithmeticSupplyDensityConversions` proves two analytic conversion steps for an explicitly supplied cumulative counting function: relative natural density with respect to the rational prime count gives the `x/log x` normalization, and this normalization gives the corresponding dyadic difference limit. It does not supply a splitting-prime density or identify the inclusive endpoint count in the entry002 target.

Round3 proves the actual conductor local-to-global congruence, actual conjugate ideal transport and distinctness, and signed residue assembly. The actual number-field prime-ideal asymptotic remains open. Two new conditional endpoints derive the unchanged universal supply and all-orders main target from exactly that displayed counting asymptotic, with no separate splitting-density or generator premise. The separate main project now supplies the actual inclusive dyadic endpoint conversion in GenericCumulativeDyadicDensity; it composes with these analytic lemmas.

The prior round2 portable verifier passed in its development workspace. Its retained logs under `logs/` contain all 25 foundation recursive roots, with exact body-traversal/`collectAxioms` agreement, only the standard three axioms, and zero unsafe, partial, or missing dependencies. No second kernel or full Mathlib source rebuild is claimed; pinned official Mathlib cache artifacts are trusted, while all selected external sources were compiled.

## Round3 conductor and conditional endpoints

`ArithmeticSupplyRayConductor` constructs the genuine principal ideal modulus `(f)`, derives `f ∣ a−1` from actual local ray congruences, and obtains actual conductor-order prime generators and conjugate residue pairs. Its supporting main modules are resolved through the relative `srcDir := "../../.."`; the delivered main `Entry002/` source tree must remain in that relative location.

`ArithmeticSupplyFromPrimeIdealPNT` derives the exact universal principal-supply target from the actual asymptotic for genuine nonzero prime ideals in every number field. It constructs the actual ray extension and its actual finite Galois normal closure, derives true splitting descent, excludes conductor primes using exact eventual dyadic equality, and assembles genuine conductor kernels. `ArithmeticSupplyMainFromPrimeIdealPNT` composes this result with the closed finite-sieve engine to derive the unchanged all-orders `MainTarget`. Both implications have the same sole analytic theorem parameter; the number-field prime-ideal asymptotic is not proved or installed as an axiom. Unconditional target flags remain false.

The expanded verifier checks the exact owned supporting source/import ledger in `conductor-owned-source-audit.json`, in addition to the unchanged 999 external sources and exact patches/pins. `ConductorCompilerAudit` records all 246 stored declarations of the elementary conductor supporting closure. `PrimeIdealCompilerAudit` audits every stored declaration in the new conditional modules and cutoff module, traversing their complete actual main/external dependencies. All imported main roots are also independently audited by the main project. The prior 25 foundation roots remain a separately counted inventory; new root counts are recorded separately in the fresh summaries and final portable log.

## Source authentication and negative controls

The top-level `../arithmetic-original-git-provenance.json` is a compact Git content proof: 136 exact commit/tree objects, 126,034 bytes. The verifier authenticates their actual Git object bytes against the three exact pinned commit IDs. It authenticates the original OpenAI/math manifest and the compatibility patch blobs through that commit's tree. Every one of the 999 selected external Lean files is then checked against its original package commit. For the 76 selected patched files, it reconstructs the original bytes by reversing the exact compatibility diff in a temporary directory, checks the original Git blob ID (or authenticated original absence for 48 new files), reapplies the exact diff, and compares resulting bytes with the delivered source. This establishes commit-to-exact-patch-to-delivered-byte correspondence, without storing another pristine source tree. It authenticates content at a pinned commit; it does not claim to verify an author's identity or cryptographic signature. The final archive SHA-256 additionally anchors the delivered evidence and verifier bytes.

The exact 16/6/3 baseline root names, all 88 expected owned source module names, and all 21 expected control/config/evidence paths are hard-coded in `verify.py`. Physical module-to-source paths are checked too. Exact conductor, conditional and analytic root/inventory sets, including every generated helper, are fixed in `audit-root-sets.json` under a hard-coded SHA-256 anchor. The verifier rejects missing or substituted roots even at an unchanged count, and requires every new owned stored declaration to be a root. The analytic roots are exactly its full owned inventory plus the explicit external `WienerIkeharaTheorem'` root; that external theorem is not part of the owned inventory. Old PNT/conversion supporting helper inventories are also pinned; their original baseline roots retain the prior full transitive traversal policy.

The owned source ledger also pins the verifier, source scanner, Git verifier, negative-control script, every endpoint and compiler-audit control, exact root ledger, configs and provenance evidence. The original 15 negative controls reject removed/substituted roots in all five workloads, omitted owned source or control ledger rows, a missing source, a modified patch, and a patch that disagrees with the authenticated original Git blob. Those controls did not cover external source-manifest duplicates or omissions; the round4 repair below adds that coverage. Controls use copied row arguments and isolated temporary files. They never modify stable main sources or delivered patches. `python3 verify.py` runs these checks and the fresh complete audits sequentially. The baseline 25, conductor 246 and conditional 7 root counts are separate workloads with possible overlap, not a count of independent mathematical results.

## Round4 external source-set repair

Review found a real third-round validator gap: removing the Wiener row, duplicating another PNT row to retain 999 rows, and modifying the omitted Wiener source could pass the old production source checks. The old Git verifier authenticated only the manifest-listed files and checked a final row count. Its 15 negative controls did not test that attack. This finding concerns validator coverage; the original delivered 999 distinct external sources still passed their original Git-content authentication. The frozen third-round archive is unchanged.

Round4 derives the expected external physical-path set without reading `arithmetic-recursive-source-audit.json`. `git_provenance.authenticate_external_closure` starts from the three fixed ray-class endpoints and `PrimeNumberTheoremAnd.Wiener`, follows their actual external imports, and authenticates each source before using its import graph. Original paths/blob IDs come from the exact pinned package commit trees; the compatibility patch blobs come from the exact pinned OpenAI/math commit tree. Patched sources must reverse to the authenticated original bytes or authenticated original absence and replay to exactly the delivered bytes. This independently derives 995 class-field dependency paths and four PNT paths. Their sorted canonical physical paths, each followed by a newline, have SHA-256 `d16aafaa6a3eeeaad6e0fc7370ff9860d86b685d40aaae5bcef9e0a70a5d385c`.

`validate_external_manifest` requires the exact package/endpoint scopes, unique canonical physical source paths, and equality with that independently authenticated set. It also compares manifest byte hashes and imports with the authenticated sources. `verify.verify_sources` calls this production Git/set validator before any manifest-selected checks. Duplicate, missing, extra, or substituted rows cannot redefine the expected closure; an altered omitted endpoint is still authenticated and rejected. The manifest is checked evidence rather than the source of the expected membership. The validator code and fixed endpoint/commit constants remain part of the trusted delivered verifier, anchored with the source/evidence archive hash; this is Git content authentication rather than signature verification.

The expanded suite has 31 negative controls: the historical 15, 11 external-set controls, and five analytic workload controls. Separate duplicate, missing, and extra cases run both the membership validator and the production source validator. A 999-row deletion/duplicate case is also rejected. The exact omitted/duplicated/modified Wiener attack is rejected by both `verify_sources` and `verify_git_provenance`; a forged Wiener byte hash/import list cannot redefine the authenticated traversal. Analytic controls reject a removed root, a substituted root at unchanged count, omission of the explicit Wiener root, omission of an owned inventory declaration, and substitution of the external Wiener theorem into the owned inventory. Positive membership validation also accepts reordered package/file rows. Fixtures copy only the mutable manifest and Wiener file and read the remaining delivered sources through temporary links, avoiding large source/cache copies.

To run all production source, patch, pin, Git, owned-ledger and source-scan checks without invoking Lean or cache tools, use `python3 -B verify.py --sources-only`. Run `python3 -B negative_controls.py` separately for the negative suite. `python3 -B verify.py --stored-audits-only` additionally validates all six stored compiler logs and reruns the negative suite, without invoking Lean. A default `python3 -B verify.py` builds the required bridge/endpoint targets and freshly runs all six endpoint and recursive compiler probes; `--bootstrap` first obtains the exact pinned dependencies/cache. Python-only postprocessing does not claim a new Lean compilation or a new recursive declaration traversal. The historical third-round compiler evidence below remains explicitly historical.

## Round4 prime-ideal Wiener workload

`ArithmeticSupplyPrimeIdealWiener` applies the exact patched `WienerIkeharaTheorem'` to the genuine number-field von Mangoldt coefficients. Its six proved statements close the elementary Chebyshev and summability inputs, identify the natural cumulative sum and endpoint term, show that endpoint term vanishes after normalization, and derive the actual weighted and literal natural prime-ideal counting conclusions from the displayed analytic boundary premises. Those premises are a function `G : ℂ → ℂ` continuous on `1 ≤ re(s)` and equality with the true coefficient L-series minus `1 / (s - 1)` on `1 < re(s)`. Construction of that boundary function remains open. The original universal prime-ideal PNT premise, original conditional supply/MainTarget assembly, and unconditional target flags retain their original statements and open status.

The new analytic workload audits every owned stored declaration in that module and the five main modules `Entry002.PrimeIdealAnalyticDefs`, `Entry002.PrimeIdealPowerSummation`, `Entry002.PrimeIdealVonMangoldtBound`, `Entry002.PrimeIdealChebyshev`, and `Entry002.PrimeIdealNaturalPNTBridge`, including private/generated helpers. The actual compiler inventory contains 112 safe owned declarations, so the exact workload has 113 roots after adding `WienerIkeharaTheorem'`. Exact names come from that actual compiler inventory and are fixed in the hard-pinned root ledger. Every owned inventory name must appear as a root, and the only additional root is `WienerIkeharaTheorem'`. Stored-type/body traversal must agree exactly with `collectAxioms`, admit only `propext`, `Classical.choice`, and `Quot.sound`, and report no unsafe, partial, or missing dependencies. `PrimeIdealWienerAudit.lean` records the endpoint types and axioms; `PrimeIdealWienerCompilerAudit.lean` produces `logs/analytic-recursive-audit.log` and its validated structured summary. The six workloads are counted separately and may overlap.

The initial traversal log `logs/analytic-initial-recursive-audit.log` establishes the exact compiler-name inventory; `logs/round4-analytic-root-freeze.json` records that freeze and source/control hashes. Final traversal evidence uses the distinct canonical `logs/analytic-recursive-audit.log` produced after fresh compilation. Python integration checks are retained as `logs/round4-analytic-integrated-sources-only.log` and `logs/round4-analytic-integrated-stored-audits.log`; the latter explicitly postprocesses all six stored workloads. Earlier external-repair-only logs with 26 controls remain historical; the integrated suite now runs 31. Bootstrap also obtains the pinned official cache for direct Mathlib imports of all 88 authenticated owned sources.


## Final round3 verification evidence

The final portable verification completed with exit 0 on 2026-10-07 at 18:20:40 UTC. Its master log is `../../../logs/arithmetic-upstream-round3-portable-verification-final.log`; the exact structured results are in this project's `logs/{ray,pnt,density,conductor,primeideal}-recursive-audit-summary.json`. All baseline 25, conductor 246 and conditional 7 roots passed stored-type/body traversal with exact `collectAxioms` agreement, only the standard three axioms, and zero unsafe, partial or missing dependencies. The original 15-control result is retained in the round4 workspace as `logs/round3-negative-controls-historical.log`; reproduction writes the current suite to `logs/negative-controls.log`. A prior interrupted development run is retained under its distinct historical log name and is not the final verification result.

A separate clean build removed only the six owned isolated modules' output artifacts and freshly compiled all six from the authenticated frozen sources. It completed with exit 0 at 18:22:15 UTC; see `../../../logs/arithmetic-isolated-owned-clean-build.log`. `logs/owned-clean-build-olean-comparison.json` records each before/after `.olean` SHA-256. Five objects are byte-identical; ArithmeticSupplyRayBridge's object changed despite unchanged source. The affected recursive workloads were therefore rerun against the fresh objects with separate `*-postfresh-recursive-audit` logs: exact conditional 7, ray 16 and conductor 246 root sets all passed. `../../../logs/arithmetic-isolated-postfresh-verification.log` ends at 18:35:18 UTC with exit 0, including repeated source, patch, pin and original Git-content checks. `logs/postfresh-object-binding.json` confirms that all six object hashes still match the clean build’s recorded after-hashes. PNT and conversion objects were byte-identical, so their final portable 6/3-root audits still bind those objects.

These runs trust the pinned official mathlib cache and reuse the previously compiled, recursively audited 995-module class-field foundation, whose sources and exact compatibility patches are authenticated again. They do not claim a fresh full mathlib or 995-module class-field rebuild in round3, or a second kernel. The main project independently freshly built and audited every main owned declaration.
