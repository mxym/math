# Mutual-information continuity counterexample: classical Lean formalization v2

This package formalizes the counterexample from the [unchanged written-proof v1](https://github.com/mxym/math/releases/tag/mutual-information-continuity-counterexample-v1). It starts with actual `Fin 3 → Fin 3 → ℝ` joint probability tables and proves a strict violation at every `0 < epsilon <= 1/16`, as well as a counterexample in every positive-distance neighborhood.

The target is the general different-marginals mutual-information proposal in [arXiv:2408.15226v2, Eq. (106)](https://arxiv.org/html/2408.15226v2#S4), also [v1, Eq. (54)](https://arxiv.org/html/2408.15226v1#S3.SS3). Local dimensions three and three give the proposed term `epsilon * log 8`. The proof changes both marginals. It does not resolve the fixed-one-marginal version.

## Formalized statements

All names below are in namespace `MutualInformationCounterexample`.

- `P_probability` and `Q_probability`: every entry is nonnegative and the actual joint table sums to one.
- `P_marginalA`, `P_marginalB`, `Q_marginalA`, `Q_marginalB`: the actual row and column sums give the written marginals.
- `mutualInformation_P` and `mutualInformation_Q`: Shannon entropies computed from those tables give `I(P) = h(e) + (1-e) log 2` and `I(Q) = log 2 - h(e)`.
- `totalVariation_P_Q`: the half-L1 distance of the actual tables is exactly `e`.
- `counterexample_family`: valid probability tables with `h(e) + e log 8 < |I(P)-I(Q)|` for every `0 < e <= 1/16`.
- `proposed_classical_bound_false`: the corresponding universal classical claim is false.
- `counterexamples_arbitrarily_close`: every `r > 0` contains valid witnesses with `0 < e < r` and the same strict violation.

The definitions use finite sums of `-x * Real.log x`, with zero contributions at zero probability. Mutual information is the sum of the two marginal entropies minus the joint entropy. The model is not an assumed entropy identity or an abstract inequality supplied as a hypothesis.

## Independent verification

The exact proof source SHA-256 is `1726a70d840a8af78ccde0fb0801273a5e9acc424b258684fce21c07d6c9419d`. The proof source was not edited during verification.

The source module was freshly compiled with the pinned official Lean 4.34.1 and nine pinned dependencies. All **38 owned declarations**, including generated declarations, and their **16,161-declaration closure** passed replay in an initially empty kernel at **trust level 0**. The family theorem closure has 16,144 declarations; the universal-negation and arbitrarily-close theorem closures each have 16,151. No owned module was excluded.

The only axioms are the three pinned standard axioms `propext`, `Classical.choice` and `Quot.sound`, whose actual signatures were checked. No owned axiom, unsafe or partial declaration, `sorry`, `admit`, or `native_decide` was accepted. An intentionally invalid proof of `False` was rejected by the empty trust-zero kernel. Dependency-cache fingerprints were unchanged during the run.

`verification/LiteralSemantics.lean` was separately compiled against the freshly built source module. It independently writes the probability tables, nonnegativity/normalization, Shannon entropy, row/column sums, mutual information and half-L1 distance, and checks the family and every-positive-neighborhood statements by unfolding the actual definitions. It also checks that both marginals differ for positive `e`.

## Reproduce

With an already installed matching toolchain and all nine repositories at the revisions in `lake-manifest.json`, run from this directory:

```sh
python3 reproduce.py \
  --output /absolute/path/to/a/new-verifier-directory \
  --toolchain /absolute/path/to/the/lean-4.34.1-toolchain \
  --packages-root /absolute/path/to/the/pinned-package-directories \
  --cache-root /absolute/path/to/the/existing-mathlib-download-cache
```

The output directory must be new. The driver checks actual compiler/runtime hashes and package revisions, creates a new owned build directory, compiles the exact hashed source, audits every owned declaration and dependency, replays the closure at trust zero and runs the negative kernel control. It does not install, download, rebuild dependencies or reuse the archived owned build output. Existing package build caches must be available; this source imports the full pinned `Mathlib` module. The recorded configuration uses one thread and a 12,288 MiB Lean memory threshold.

For ordinary library builds, the included `lean-toolchain`, `lakefile.lean` and pinned `lake-manifest.json` also describe the package. The independent certificate comes from the explicit fresh verification driver, not a claimed GitHub Actions result.

## Records and compressed dependency graph

`verification/complete-replay.tar.gz` contains the complete recorded fresh run, including source snapshot, freshly generated owned build output, all command logs, declaration inventory, dependency closure, exact standard-axiom records, negative control and original run checksums. It also includes the literal semantic check and unified review. Each archive entry is additionally bound by an archive-level checksum inventory.

`verification/all-owned-closure.json.gz` is a standalone lossless compression of the same complete 16,161-declaration dependency graph. `verification/replay-summary.json`, `verification/UNIFIED_REVIEW.json` and `MANIFEST_V2.json` give machine-readable bindings and scope. The package-level `SHA256SUMS` binds every file other than itself.

The verifier is adapted from the published standard-axiom/empty-kernel harness in `mxym/math` at commit `4d2eefd40ee930216ccd8fc0f51e4bf694251967`, `formalizations/laplacian-chollet-all-graphs-progress/verifier/`. Only task configuration and the reproduction ownership label were adapted; the theorem source and kernel-audit implementation were not changed.

## Scope of this version

This is the complete formalization of the **classical probability-table counterexample**, including arbitrarily small distance. The written diagonal quantum embedding is not formalized here, and no general quantum spectral-function library is supplied. The necessary-leading-coefficient discussion in written-paper Section 5 remains a written argument; this package does not claim that every additional conclusion in the paper has a Lean theorem.

Novelty and priority are unconfirmed. No external human peer-review certificate is claimed. Written-proof v1, its publication time and all its assets remain unchanged.
