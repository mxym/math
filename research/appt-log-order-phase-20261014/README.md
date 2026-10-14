# Finite APPT entropy above order one and the sharp pole phase

**Yongxian Zhang (张永贤)** · School of Computer Science and Engineering,
South China University of Technology · mxymmxym1@gmail.com ·
ORCID 0009-0000-3864-3536. No external funding. OpenAI AI assistants assisted.
Copyright 2026 Yongxian Zhang; all rights reserved for original material.

[Real-order power envelope](LOG_POWER_ENVELOPE.md) ·
[Exact pole phase and sharp cutoff](SHARP_POLE_PHASE.md) ·
[Prepared proof obligations](THEOREM_MAP.md) · [Literature scope](LITERATURE.md) ·
[Complete independent internal read](MANUSCRIPT_REVIEW.json).

For every integer D≥15 and every real α>1, the necessary outer spectral
polytope has the exact maximum

    max Σλ_i^α=max_(1≤j≤D−3) (j3^α+D−j)/(D+2j)^α.

Its only equality spectra are the maximizing two-level plateaus. On actual
C²⊗C^n, n≥8, this gives the exact APPT and absolutely separable Rényi minimum
and every equality state, at every α>1. Only the clipped floor and ceiling
of D(3^α−1−2α)/[2(α−1)(3^α−1)] need comparison. The proof uses a complete
logarithmic size-biased convex comparison, including every tail vertex and
the D=15/16/17 boundary cases. It closes the 1<α<2 interval in this domain.
The small-qubit intermediate-order cases remain outside this theorem.

Independently, for every D≥8 there is a unique τ_D>2 satisfying

    [(2·3^τ_D+D−2)/(3^τ_D+D−1)]·[(D+2)/(D+4)]^τ_D=1.

For actual qubit–qudit n≥4, the pole (I+2vv*)/(D+2) minimizes Rényi entropy
**exactly when α≥τ_D**, on the entire positive real-order axis, including
the separately proved order-one comparison. At τ_D all equality states
have projection rank one or two; above it only rank one remains. Every
dimension pair with D≥8 has the same pole value for α≥τ_D, and m≥3 has
only pole equality even at the critical order. A rational actual PPT
negative control excludes the outer rank-two plateau in these dimensions.

The sharp worst-partition cutoff has the expansion

    τ_D=(log2)(D+3)/2−(log2)/[6(D+3)]+O(D^−3).

Its leading constant log2/2 is sharp along even dimensions, by actual
qubit competitors. The correction to log2/log[(D+4)/(D+2)] is negative and
exponentially small. No exact subcritical minimum or partition-specific
necessary cutoff for m≥3 is inferred from the pole criterion.

These are complete ordinary proofs in the displayed domains, not complete
Lean. Prior vertices, purity, von Neumann entropy and the ASEP white-noise
endpoint remain credited; the prior qubit APPT=ASEP theorem is a disclosed
input. This is another strengthening of the same APPT direction, with no
additional major-conjecture count, historical-first certification or
external human peer-review status.

## Supporting verification

The checker verifies eight exact integer entropy certificates, two polynomial
coefficient identities, 1,232 finite rational stop-loss formulas and four
actual higher-local-dimensional negative PPT controls. Separately it evaluates
272 real-order vertex cases and eleven crossing equations numerically at
90 decimal digits. The all-order optimizations and unique-root theorem are
the written proofs, not extrapolations from these checks.

```bash
python3 check_log_phase.py --out DIAGNOSTICS_LOCAL.json
python3 check_sources.py
```

Windows ordinary/optimized and WSL runs passed with one shared implementation.
[Run comparison](DIAGNOSTIC_COMPARISON.json) preserves their scope. The
independent assistant read the full 471-line initial manuscripts/map and
the final two-line D=17 clarification, verifying exact byte correspondence.
Its actual inherited-input read ranges and separate symbolic checks are
recorded. This is internal assistant review, not external human peer review.
[Source bindings](SOURCE_HASHES.json) bind the final bytes. No prior Lean
source, audit root, build or claimed kernel coverage is extended. No new
Release, DOI, submission or external message is introduced by this packet.
