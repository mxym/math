# Actual finite spectral protocols

This is a new audit scope for the entanglement-extraction manuscript. It imports the unchanged finite extraction core and local cap packages, the independently developed symmetric-support package, and the finite information-spectrum matrix lemmas. Lean is fixed at **4.34.1**, with Mathlib **d13f23b723b8a846827a245b89c10fc7d3f11612**.

## Mathematical endpoints

- `oneShotSpectralEnvelope_actual_lower` constructs an original-input unitary and two complete local finite Kraus families attaining **T_K / 4**. The top spectral prefix, its actual Hermitian idempotent, rank, positive selection and remainder, maximizing prefix, and every integer-floor loss are constructed or proved internally. The definition uses Mathlib's actual decreasing Hermitian eigenvalues. `prefixWidth_div_target` identifies its weight with exactly the three-cap `v_r` in the manuscript.
- `oneShotSpectralEnvelope_actual_upper` gives **H_N T_K** for every original-input unitary and every trace-preserving finite Kraus channel with positive partial-transpose conjugate. It derives the actual eigenbasis effect diagonal, both scalar caps and its full Hilbert--Schmidt budget, then proves the finite rearrangement and harmonic comparison. No spectral trace inequality is supplied as a premise. Together these endpoints close the two-sided finite spectral comparison of Theorem 2.4; its additional real-order Holder/Renyi estimate is a separate remaining statement.
- `finite_projection_mass_lower` constructs one complete local protocol with fidelity at least `Tr(P X).re` for **every actual PSD X**. It neither assumes that X commutes with P nor assumes that X minus its compression is positive. The proof derives domination of P by the preprocessed fidelity effect.
- `pure_iid_integerBell_actual_extractor` and `pure_iid_integerBell_optimal` prove the mathematical integer Bell-pair optimum on **actual normalized pure iid two-qubit inputs**, with rank `choose(k+3,3)`, all-unitary preprocessing and physical finite PPT Kraus converses. Pure iid inputs are proved to span their common support in the dependency; support equivalence is not assumed. `pure_iid_integerBell_eq_paper_floor` proves the exact real-logarithm floor formula, including integer boundary cases.
- `purePower_fidelity_guarantee_upper` and `purePower_fidelity_feasible_lower` work for arbitrary positive local dimensions m,n, every finite k, and all integer targets K. A worst-input guarantee over all actual normalized pure iid inputs is bounded by `min(1, m^k/K, sqrt((mn)^k/(K^2 r)))`; every feasible integer Bell rank d is attained on that entire promise class by one fixed actual local protocol. Here r is the proved actual symmetric-support rank `choose(k+mn-1,mn-1)`. The adversarial average reduction is proved by positive radial integration and finite phases, not supplied as an ensemble or Haar hypothesis.
- `product_kraus_partialTranspose`, `productKraus_PTConjugatePositive`, and `conjugateMatrix_complete` give the actual product-channel transpose-conjugate Kraus representation and completeness. `PTConjugatePositive_iff_second` proves that the existing first-factor convention and the manuscript's second-factor convention impose equivalent positivity conditions, using actual ordinary matrix transpose on input and output.
- `sectorKraus_complete` and `sectorKraus_encoded` prove complete local sector-controlled Kraus semantics and exact removal of off-sector coherences. They are reusable construction lemmas, not a completed all-state multiscale protocol theorem.

The lower constructions quantify one original-space U and complete local channels before every input in their stated promise class. They add no supplied input system, postselection, or normalization of a successful branch. Their finite Kraus maps are completely positive by the original core's arbitrary finite amplification theorem. Conversely, upper bounds need only the stated necessary positivity of the transpose conjugate. This package does **not** formalize the equivalence between abstract complete positivity and existence of a finite Kraus representation.

## Reproduction and audit scope

Run in this directory:

```sh
lake exe cache get
python3 reproduce.py --check-only
python3 reproduce.py --fresh
```

The script checks the toolchain and actual pinned Git dependencies, binds every owned mathematical module and its recursively imported repository source files, rebuilds this package's own outputs, prints selected theorem types and axioms, replays all **85 explicitly listed roots** and their dependencies in a fresh trust-zero kernel, and requires **13 same-type forged proofs** to be rejected. The audit helper is separate from mathematical modules. Only `propext`, `Classical.choice` and `Quot.sound` are permitted in the mathematical dependency closure. It writes immutable timestamped logs and a source-manifest-bound summary. A cached dependency build is distinguished from an empty-kernel proof replay; no claim is made that Mathlib was rebuilt from scratch.

The older 39/91/235/444 scopes and the separate 83-root core and 11-root local-cap scopes are unchanged. Importing their source as dependencies of this new audit does not expand those historical audits.

## Remaining scope

This package does not certify the full manuscript. In particular, it does not yet prove the mixed-state common Schur protocol, the entire real-order Holder estimate, all rate/reliability/Renyi variational and limiting statements, the general rank-s Schur/Haar two-moment law, or a gate syntax, denotation, synthesis algorithm and asymptotic gate-count bound for the pure circuit. The finite symmetric-input optimum is not a proof of the circuit complexity claim. The pure average reduction above does not stand for the general rank-s Haar formula. Further formalizations should be separate reviewed successors with explicit source bindings.