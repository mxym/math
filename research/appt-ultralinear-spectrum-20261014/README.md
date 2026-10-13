# APPT fast-order phase law and spectra

**Yongxian Zhang (张永贤)** · School of Computer Science and Engineering,
South China University of Technology · mxymmxym1@gmail.com ·
ORCID 0009-0000-3864-3536. No external funding. OpenAI AI assistants assisted.
Copyright 2026 Yongxian Zhang; all rights reserved for original material.

[Complete value proof](FAST_ORDER_VALUE.md) ·
[Complete spectral criteria](FAST_ORDER_SPECTRA.md) ·
[Proof obligations](THEOREM_MAP.md) ·
[Independent internal full read](MANUSCRIPT_REVIEW.json).

For actual all-global-unitary APPT densities, let D=mn,
E_α=log D−min S_α and u_D=3D/(D+2). As m→∞ and α/m→∞,

    E_α ~ max{2/m, log u_D−log D/α},

uniformly over every n≥m, with no upper bound on α or n. This is a relative
equivalent for the first nonzero deficit, including the bulk floor 2/m when
the peak expression alone vanishes. The stronger logarithmic moment formula
retains both exact finite bases:

    log M*_α
      =max{α log u_D−log D,
            α log[(m+1)/(m−1)]−log[eα*2/(m−1)]}+o(1).

At comparable peak and bulk moment scales, their maximum is sharp. Their
sum would overstate the leading moment. The necessary physical peak/width
coupling suppresses one contribution when the other is sharp.

The spectrum proof gives a necessary and sufficient sharp-moment criterion
on every aspect ratio, including oscillating transitions and α≫D. Its two
branches are the exact peak-resolution condition and a full-width rare
upper-level condition with size-biased concentration in an o(1/α) edge
layer. At the critical ratio, branches may alternate. A separate complete
leading entropy criterion retains only the actual peak and middle Laplace
contributions. An actual APPT projection sequence is entropy near-optimal
while its normalized moment ratio tends to zero.

These are **complete ordinary mathematical proofs, not complete Lean**.
The earlier [all-positive-order value theorem](../appt-growing-renyi/ALL_ORDER_VARIATIONAL.md)
and its physical finite constructions are explicitly inherited inputs.
The closed projection maximum was already present in the fixed-local
calculation of [ENTROPY_ASYMPTOTIC.md](../appt-multilevel-counterexample/ENTROPY_ASYMPTOTIC.md),
E32/Section 12.3. The new work is the uniform fast-order competition and
all-aspect spectral analysis. This strengthens the same APPT direction;
it is not separately counted as solving another major conjecture.

The independent assistant read all 482 lines of the two proof manuscripts
and prerequisite map and found no unresolved mathematical changes. Its
literal source hashes, inherited-read boundary and review-time exclusion
are in the record. This is internal assistant review, not external human
peer review or verified historical priority. Old Lean packages retain their
original objectives and roots; no Lean execution or audit expansion occurred.

## Finite diagnostics and source correspondence

The new standard-library checker specifies actual finite density families
by rational strength/protection, integer rank and rational trace. It evaluates
their spectral moments numerically at high precision. Forty-two cases cover
peak/bulk competition, the entropy/moment separation, and the wrong
uncalibrated top base when α≫D. They are diagnostic evaluations, not universal
optimization proofs or sampled-unitary certificates. A scalar grid records
only its evaluated competitor, not a certificate of the continuous maximum.

Ordinary and `-O` Windows runs and a WSL run passed. The latter shares the
same implementation; one floating field differs by about 2.62×10^-33, within
the recorded tolerance. They are not three independent implementations.
[Comparison record](DIAGNOSTIC_COMPARISON.json) and
[source bindings](SOURCE_HASHES.json) preserve this scope.

```bash
python3 check_physical_windows.py --out DIAGNOSTICS_LOCAL.json
python3 check_sources.py
```

The source check binds manuscripts, the full-read record, explicit inherited
inputs, diagnostic records and local links. It does not machine-prove the
mathematics. Fixed-m moving-order optimization, exact finite extrema,
absolute separability and complete formalization remain outside this packet.
No new Release, DOI, aiXiv submission or external peer-review status is claimed.
