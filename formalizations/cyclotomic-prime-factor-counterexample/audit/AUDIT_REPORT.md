# CGF Conjecture 48: static semantic and evidence audit

Date: 2026-10-08 UTC. Verdict: **PASS for semantic correspondence and evidence consistency.** No mathematical or proof-coverage gap was found. A publication-metadata cleanup is required before distributing a public copy of the raw verification archive.

## Attribution and scope

The reviewed archive is `cgf_conjecture48_independent_lean_evidence_616877a1_20261008.tar.gz`, 18,311,823 bytes, SHA-256 `c2bcb597d513f9929eadd8bc749737a966ef9f919ee8040781609e02dac878d9`.

The designated verification operator performed the recorded fresh Lean compilation, all-owned audit, empty-kernel replay, and negative control on 2026-10-08, 10:53:35–10:56:55 UTC. **This reviewer did not install or run Lean, execute the verifier, or repeat that machine run.** This review read the proof and checker sources, inspected retained output, independently recomputed file/graph/arithmetic checks with a separate Python script, and checked exact public-source identities. It is an additional evidence and semantic review, not another independent machine reproduction or external human peer review.

Public checkpoint: [commit 616877a1](https://github.com/mxym/math/tree/616877a1f3ac57ddc23737901581e666b0aabdd1/notes/cyclotomic-prime-factor-counterexample/lean-source-checkpoint). The frozen mathematical certificate is at [commit 0b9aa237](https://github.com/mxym/math/blob/0b9aa237472dfc7cfc252d8708aadd3fd5e897df/notes/cyclotomic-prime-factor-counterexample/cyclotomic_prime_factor_20261008/certificate.json).

## 1. Provenance and integrity

- Recomputed all 111 entries of `PACKAGE_SHA256.json`; its scope exactly matches every other file in the archive.
- Recomputed all 19 entries of the checkpoint `PACKAGE_MANIFEST.json` and all 73 entries of the fresh run's `SHA256SUMS`, with no missing or unlisted files in either scope.
- Queried the public checkpoint directory at the exact commit through the GitHub connector. All 20 current Git blob identities and sizes agree with the archived directory record and the independently recomputed Git blob hashes of the packaged files.
- All 20 packaged checkpoint files match the retained publication snapshot. All 11 author Lean files match the recovered author files, the public snapshot, and the fresh-run source snapshots byte for byte; every SHA-256 agrees with both pre-reset and recovered hashes.
- The verifier source and template hashes match the run's control-source manifest. Substituting the declared module and root lists into the template exactly reproduces `OwnedAudit.lean`; the negative-control source is also identical.
- The separately retrieved frozen certificate has SHA-256 `64b10e5427ecaaaf9076e5d8b592831393db9fcb2b412c5894fd928d5fd4dfad`. All 217 coefficients and 109 centered weights match it. A new exact-integer convolution of the four displayed cyclotomic formulas to the sixth power independently reproduces every coefficient. This arithmetic cross-check supplements rather than replaces the Lean identities.

## 2. Mathematical meaning

The relevant paper defines the basic class without a scalar or monomial factor and the unimodal submonoid inside that class. Conjecture 48 asks whether every member other than 1 has a prime-index cyclotomic factor. Its scope does not impose irreducibility, squarefreeness, or exclusion of proper powers. The Lean definitions and witness meet this published scope. Source: [Billey–Swanson, Definitions 1, 3, 45 and Conjecture 48](https://arxiv.org/html/2305.07620v3).

The formal witness is literally `F = (Polynomial.cyclotomic 4 ℤ * cyclotomic 9 ℤ * cyclotomic 25 ℤ * cyclotomic 30 ℤ)^6` (`BasicProperties.lean:18–20`). It uses the imported Mathlib cyclotomic definition, not a separately defined lookalike. Its closure records assign the cyclotomic definition and integer-map theorem to `Mathlib.RingTheory.Polynomial.Cyclotomic.Basic`, and the rational irreducibility/coprimality theorems to `.Roots`; the recorded imported-interface print agrees.

`IsBasicCGF` requires coefficientwise nonnegativity for every natural index and a finite product of genuine cyclotomics of indices at least 2, with natural multiplicities and no added scalar or monomial (`BasicProperties.lean:22–39`). Monicity, constant coefficient 1, degree/natDegree 216, and `F ≠ 1` are proved separately.

The finite list is not assumed to be the coefficient sequence: `product_eq_coefficient_polynomial` proves an actual polynomial equality using four proved cyclotomic formulas and ordinary ring normalization (`Expansion.lean:42–48`). `F_coeff` connects that identity to every natural index; the tail is proved zero. Positivity on 0–216 and global nonnegativity follow.

`UnimodalCoeffs` quantifies over all natural pairs of indices. `F_unimodal` handles the decreasing side through degree 216 and the zero tail (`Counterexample.lean:65–81`). Stronger statements give strict increase to index 108, strict decrease to index 216, and a unique maximum among all natural indices. The peak is 11,434,392 and the minimum first-half adjacent difference is 5. The 109 centered weights begin with 1, so their minimum and the minimum of the 108 adjacent differences must not be conflated.

Prime exclusion is universal, not a bounded search. `cyclotomic_not_dvd_product_pow_rat` uses rational coprimality of distinct cyclotomics and irreducibility for a positive index; the integer statement maps any purported divisibility to the rational polynomial ring (`PrimeExclusion.lean:17–44`). It applies to every `p` satisfying `Nat.Prime p`.

`F_centered_certificate` proves the full centered polynomial identity plus all weight-positivity statements. `qInteger` is the geometric sum of powers of X. The quotient certificate proves `N^6 = F * D^6` and `D^6 ≠ 0`, with numerator indices 4, 9, 25, 30 and denominator indices 1, 6, 10, 15. The nonzero proof uses `D(1) = 900` (`CenteredCertificate.lean:110–147`). This is a sufficient denominator-cleared bridge to the paper's quotient presentation; it does not claim a separately formalized rational-function division theorem.

Finally, `conjecture48_false` derives the negation of the full quantified `Conjecture48` directly from this witness (`Counterexample.lean:89–111`). **The result refutes the entire original Conjecture 48 within its stated basic/unimodal domain, rather than merely certifying finite data.** It establishes no claim about other CGF conjectures, minimum degree, or worldwide priority.

## 3. Declaration coverage and closure

The source module list and audited module list are identical: eight mathematical modules plus three author print-audit modules. No module is excluded. The latter three introduce no mathematical constants.

The inventory contains 112 owned declarations: all 73 explicitly named declarations plus 39 generated/private declarations. The author audit reports all 73 exactly once. Every exported inventory node equals its matching graph node. The complete closure reachable from the 112 owned declarations equals the entire exported graph of 29,737 nodes.

Independently checked edge counts: 304,413 type-reference edges, 513,368 value-reference edges, and 30,502 structural-reference edges. Every target exists. Reachability was independently recalculated for each requested root:

- `explicit_counterexample`: 29,681
- `conjecture48_false`: 29,661
- `F_centered_certificate`: 29,581
- `F_qInteger_quotient_certificate`: 29,553

Their union is exactly 29,717 nodes. The larger 29,737-node all-owned closure, including unused owned helpers, is the recorded replay target.

There are no owned axioms and no unsafe or partial declarations anywhere in the mathematical closure. The only closure axioms are `propext`, `Classical.choice`, and `Quot.sound`. For all 112 owned declarations, a separate graph traversal reproduces the recorded axiom set exactly. No `sorryAx` or native-decision axiom appears.

## 4. Empty-kernel semantics and execution record

Pins are Lean 4.34.1 / commit `5045d0056413266e57c625dcd7c365b10e377c52` and Mathlib `d13f23b723b8a846827a245b89c10fc7d3f11612`. All nine package revisions agree between environment configuration and run manifest; executable/runtime hashes are recorded.

The runner creates a unique new directory with `exist_ok=False`, snapshots the hash-checked source bytes, clears inherited Lean search-path variables, places the new build directory first, and invokes Lean directly. The 24 retained commands consist of 11 compilations, 11 dependency listings, the all-owned replay, and the negative control; all recorded exit codes are zero and timestamps are sequential. All owned dependencies listed by `--deps` resolve inside that same fresh build. No prior owned `.olean` is copied into it. Source snapshots and compiler output files are covered by the manifests.

The checker calls `mkEmptyEnvironment 0`, then verifies that the initial constant map has zero entries. At the pinned upstream `Environment.lean:1530–1543`, that argument populates `header.trustLevel`, with an empty constant map. The retrieved upstream file matches SHA-256 `ee364e4788ce0560c87f621eeb3c4c3dfec62e8db4e15e099fd80e6adc533b86` and its official Git blob hash. By contrast, the two zeros in `addDeclCore 0 0` are heartbeat and recursion limits (`Environment.lean:297–298`), not the trust setting.

The pinned `FoldConsts.lean:67–74` traverses type and value, including opaque values. The custom gatherer additionally includes mutual groups, constructors, parent inductives, recursor groups and the quotient dependency on Eq. `Lean.Replay` checks definitions, theorem values, opaque declarations and inductive blocks; it compares reconstructed constructors and recursors. Replay itself permits axioms and skips unsafe/partial constants, so the checker's prior whitelist and unsafe/partial rejection are material safeguards. Both are present. After replay, every original closure name must exist with the same type and universe parameters.

The retained log reports the 29,737-node empty-kernel replay PASS. The negative control supplies a theorem of False with the proof `True.intro`; the recorded error is the intended declaration type mismatch. Merely observing some exception would not suffice, and the control specifically checks the mismatch text.

The shared-cache comparison covers path, size and mtime metadata. It establishes unchanged recorded metadata, not independent authentication of every cached dependency byte. As usual, the execution claim retains the pinned Lean kernel/runtime and verification machinery as its trusted implementation base. This static reviewer did not independently authenticate the binary provenance or execute the archived `.olean` files.

## 5. Publication and interpretation notes

The raw package has two non-mathematical execution-routing fields, `owner_thread` and `parent_thread`, in both environment-config copies. Remove those fields only in a clearly identified public projection, preserve the original evidence privately, and provide a new complete public manifest. Check that all other configuration parameters and the author source/compiler-log bytes are unchanged. This is a publication hygiene issue, not a mathematical failure. No embedded Library identifier or Library recovery instructions were found in the packaged reference materials.

The old source checkpoint's `pending` text is historical and intentionally unchanged. The runner's `author_claim_verified=false` / `semantic_review=REQUIRED_SEPARATELY` also belongs to the mechanical record; the companion semantic review supplies the separate assessment. Neither should be silently relabeled as if it were the original run's semantic result.

The author `verify.sh` script was not exercised end to end by the designated run. The independent runner compiled all 11 exact author Lean files instead. Public wording should retain that distinction and should attribute the machine execution to the designated verifier, while describing this report as a static semantic/evidence audit.

Recomputed audit results are in `static-audit-result.json`; the independent checking script is `audit_record.py`. Neither executed Lean. There were no Git writes or Release operations in this review.
