# Entry005: independent full sharp Main audit

Date: 2026-10-07 UTC. Final verdict: **PASS for the exact composed source identified below.**

## What was proved

`Entry005.sharpMain` is an actual theorem inhabiting the unchanged `Entry005.sharpMainGoal` and `Entry005.MainTarget`. It holds for every dimension `d ≥ 3`, every qualifying actual compact convex body, and **every prescribed maximum-volume inscribed simplex S**, with that S's original centroid, the original `gSharp d`, actual `entryDefect`, and exponent `1/(d−1)`. It has no added cone-law, polar-geometry, Minkowski, first-variation, cap, retention, or local-estimate premise.

This certificate concerns the sharp **upper** Main. The separately audited truncation-sharpness theorem is not recompiled in this audit and is not counted among its 848 proofs.

## Exact certified input and repaired delivery gap

The original Library item `[private delivery identifier removed]`, version 0, was genuinely a `text/plain` Git patch, not a ZIP:

- 1,422,231 bytes; 203 indexed files
- SHA256 `9a0a33f57cc6a3f9f373040ae11fd98ade985bbd5712f31fca3b82f702b7a932`
- Index `[private delivery identifier removed]`, version 0; SHA256 `dade68daabe6fec12878b8a360002501b7294e1800a50a0f764059b66887bfef`

Every reconstructed file matched its indexed exact length and SHA256. However, two delivered modules imported `Entry005.SelectedAnchorHullRoundness`, absent from the original 122-module inventory. A complete source-provider scan detected that gap before proof compilation. Eight supplied modules, including Main, were blocked. The original 203-file delivery therefore remains **incomplete as delivered**; its author-side/cache-based checks were not treated as an independent full-source certificate.

The authoritative exact-source supplement is Library `[private delivery identifier removed]`, version 0:

- 5,664-byte text patch, SHA256 `01dab955ed966f094eedb30de00a392af6615f8960114a8099187f7061a7a71e`
- `formal/Entry005/SelectedAnchorHullRoundness.lean`, 105 lines, 5,338 bytes
- Source SHA256 `edfca1a3ae33a55278773cc6c7784acbb355570b3072afe9a70c158b95813fd4`
- Three actual additional theorems, not an axiom or assumed bridge

The certificate binds **the original 203 exact files plus this one exact source**, retained separately as `composed-source/`, with 204 files, 123 owned modules, and 848 public proofs. Original input bytes were not edited. The old bundled 122/845 accounting is superseded by the independent derived inventory; no future repackaging is implicitly certified.

The complete mathematical source-set identity is SHA256
`36f41bf0bc292a93c5e45ce71b8483be82661f0e67f8326650850b3b1906497a`.
It hashes compact JSON mapping lexicographically sorted module names to their exact source SHA256; `checks/owned-source-set.json` gives both scheme and mapping.

## Independent machine checks

- Compiler: pinned Lean 4.34.1, commit `5045d0056413266e57c625dcd7c365b10e377c52`.
- All nine dependency repositories matched their pinned revisions and were tracked-clean before and after the audit. No dependency source was edited or downloaded.
- The entire recursive import closure contains **4,743 source modules**, each resolved to exactly one source provider. No missing nonofficial source remains.
- **123/123 owned modules** were independently freshly compiled to regular, owned outputs using `autoImplicit=false`, `maxSynthPendingDepth=3`, `warningAsError=true`. No old-owned namespace fallback was on `LEAN_PATH`.
- All **848 public proofs** were independently enumerated from source and checked against actual compiled declaration kind and owner module, not an author-supplied abbreviated count.
- Module ownership enumerated **1,833 declarations**, including private/generated declarations. None is unsafe, partial, a custom axiom, or an opaque declaration. Every recursive axiom set is contained in `{propext, Classical.choice, Quot.sound}`.
- **Nine literal positive controls** passed: Main, original alias, local theorem, fully quantified Main, expanded prescribed-simplex maximality/centroid infimum, actual pyramid/projection-ratio defect, and original gSharp/Q/J definitions.
- **Four negative controls** passed: a Prop alias supplied as a proof, omission of the original constant, existential-simplex quantifiers substituted for every prescribed simplex, and a forged kernel proof of True with value Nat.zero. The first three failed specifically with type mismatches; the replay mechanism rejected the forged declaration.
- All compilation warnings: **zero**. The unchanged legacy `ZonotopeVolume` emitted one informational `Try this: [apply] abel_nf` suggestion; this is recorded rather than falsely claiming every foundational log was empty.

### Actual empty-environment kernel replay

This was not an import-only test. Each replay recursively collected the declarations actually used by the roots, rejected unsafe/partial nodes and unexpected axioms, created `mkEmptyEnvironment 0`, invoked kernel replay, and verified every root's exact type and universe parameters in the resulting kernel environment.

1. Literal `Entry005.sharpMain`: **1 root, 54,277 declarations**, `trust=0`, `empty=true`, `skipped=[]`, PASS.
2. Every safe declaration owned by all 123 source modules: **1,833 roots, 55,067 declarations**, `trust=0`, `empty=true`, `skipped=[]`, PASS.

The Main closure contains 1,197 owned declarations. It does not contain `FiniteSupportMinkowskiObligation`, the old conditional finite-enclosing cap theorem, or `sharpMain_of_local_and_actual_coarse`. The actual unconditional scalar gluing theorem is used with its local and coarse hypotheses discharged by proofs.

## Semantic review of the proof chain

### Same witness and genuine polar geometry

`normalized_sharp_upper_local` obtains one actual joint compact-limit probability law μ, one strictly increasing subsequence φ, one anchor tuple w, and one measurable assignment r. It does not identify independently chosen witnesses. Actual normalized directional moments, the unchanged threshold, and the strong cost give a real b-ball inside the convex hull of those same anchors.

The supplemented hull theorem was read independently: separation by a closest point gives a direction whose hull support is less than b. Applying the directional negative-part bound to the opposite direction gives positive-part expectation at least 2b. The pointwise assignment estimate and cost at most b give a strict upper bound below 2b, a contradiction. The unit-ball variant establishes coordinate and assignment-error integrability, rather than assuming them silently.

`PolarSimplexConstruction` constructs actual affine-basis coordinates, positive origin weights, dual gradients, and polar vertices. It proves affine independence, exact equality of the simplex carrier and its supporting halfspaces, containment of K and the unit ball, radius M, distinct normalized facet normals, positive heights, exact atom equality n_i/h_i=w_i, and support equalities σ_P(w_i)=1. These are discharged constructions, not leftover Main hypotheses.

### Radial scale, preserved constants

Actual radial facet cones of each supporting approximant cover P after individual dilations with ratios `1 ≤ s_i ≤ M`. The proof does not require the approximant to lie inside P. Cone volumes and `s^d ≤ 1+d M^(d−1)(s−1)` yield

`V(P)/V(K) ≤ 1 + d M^(d−1)(I−1) ≤ 1 + d M^d ε`.

The limit is taken along the same φ and μ as the assignment. It retains the strong bound `ε ≤ (d+1)(d+2)t/(1+t)`, with `t=(d+1)e`, and proves that the original Q absorbs `M^(d−1)(d+1)(d+2)`. This gives the original scale `(1+M Q t)^d`; replacing the strong cost too early by a coarse Q budget would not justify that constant.

Actual facet centering/correction gives brightness control and the half-unit ceiling. The unchanged scale/cap algebra therefore retains the original J and L. The threshold yields `dρ ≤ 1/8`. Existing maximum-simplex/Hausdorff retention is then applied to the *supplied S* and its centroid, not to a newly selected maximum. Affine normalization and the actual invariance theorems restore that same S. Actual defect nonnegativity, the original local theorem, and the original coarse bound close both global threshold branches, including zero defect.

The separately completed mathematical review `sharp_main_bridge_mathematical_review_20261007/REVIEW.md`, SHA256 `ccbcefa73a4a0351169854b66a58ceb8fdfc3ef900a9e624ca5bfeb2c9738f34`, complements this kernel audit. Its mathematical PASS was not used as a substitute for any compilation or replay.

## Unchanged original definitions

All 102 verified-714 foundational source modules are byte-identical to the earlier independently audited delivery. Specific original definition identities:

- Constants: `b3cdc026d3b5be2f495e8613bd98f36408b6ece56811adc1b562994fc447425e`
- Targets: `8bc873bff65384b67b05d3d4fd405bdf9c728e0befb0e6ac355373fa3ded7c94`
- MainTarget: `bd1b99380fd495acae3387fec8d2a99131cdb1f30aea97fa2bbaf65c7ee1d8ac`
- Final SharpUpperMain: `03d5ac8ccde7b92d7f5084a50e9aa841ad539684a8582a98d0546431c170a2aa`

## Evidence and reproducibility

`checks/FINAL_PASS.json` is the compact result. Input/source inventories, dependency pins, import-provider closure, fresh output hashes, actual owner/type/axiom records, literal controls, negative controls, and both kernel replay logs are retained. `AUDIT_EVIDENCE_SHA256.json` binds the evidence and scripts. `REPRODUCE.md` describes independent reproduction using the pinned official source/toolchain and read-only dependency cache. The audit did not copy the multi-gigabyte dependency cache; its local working footprint remained under 60 MiB before packaging.

No source repair beyond accepting the exact missing source was invented, no author object substituted for a fresh owned output, and no publication or external sharing action was taken.
