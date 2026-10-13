# Exact finite APPT Rényi extrema at high order

**Yongxian Zhang (张永贤)** · School of Computer Science and Engineering,
South China University of Technology · mxymmxym1@gmail.com ·
ORCID 0009-0000-3864-3536. No external funding. OpenAI AI assistants assisted.
Copyright 2026 Yongxian Zhang; all rights reserved for original material.

[Finite power envelope and qubit–qudit proof](POWER_ENVELOPE.md) ·
[All-dimension high-order proof](FINITE_SPIKE_PHASE.md) ·
[Credited pole separability construction](POLE_SEPARABILITY.md) ·
[Prepared proof obligations](THEOREM_MAP.md) · [Literature boundary](LITERATURE.md) ·
[Independent complete internal read](MANUSCRIPT_REVIEW.json).

For actual APPT and absolutely separable densities on C²⊗C^n, every n≥4
and every real α≥2 have the exact finite power maximum

    max Tr(ρ^α)=max_(1≤j≤2n−3) (j3^α+2n−j)/(2n+2j)^α.

Taking log and dividing by 1−α gives the exact Rényi entropy minimum.
All equality states are (I+2P)/(2n+2j) for arbitrary orthogonal projections
P of a maximizing rank j. Only the clipped floor and ceiling of

    j_*=2n(3^α−1−2α)/[2(α−1)(3^α−1)]

need be compared. All ties are retained. The proof first solves the necessary
outer spectral polytope for every integer D≥8 and real α≥2, then proves
actual qubit–qudit attainment. A nonphysical outer exception at D=8, α=2
is explicitly excluded rather than promoted to a density optimizer.

For every pair 2≤m≤n, D=mn, a finite sufficient high-order band has the
unique pole spectrum (3,1,...,1)/(D+2):

    α≥D/2+1 for D≥6;   α≥24 for D=4.

In either actual physical set,

    min S_α=[α log(D+2)−log(3^α+D−1)]/(α−1).

Every pole (I+2vv*)/(D+2) is absolutely separable by the credited known
white-noise endpoint, with a finite product decomposition supplied here.
The D=6 comparison is separate; the D=4 proof uses the physical determinant
condition and controls all states approaching the eigenvalue cap. An actual
qubit rank-two projection beats the pole at α=cD whenever
0<c<log(2)/2 and D is large, proving a dimension-only eventual cutoff has
order Θ(D). The sufficient constants and transition coefficient are not
asserted sharp.

These are complete ordinary proofs in the displayed domains, not complete
Lean. The existing vertices and α=2 purity are Tran's results; the qubit
APPT=ASEP theorem is Johnston's; the separability endpoint is prior
Vidal–Tarrach mathematics. They are explicitly credited. This strengthens
the same APPT entropy direction and is not another counted major conjecture.
No verified historical-first assertion or external human peer review is
claimed. General finite minima below the stated bands and complete
formalization remain open within this work.

## Supporting diagnostics

The standard-library checker verifies the needed polynomial coefficients,
12,393 finite rational endpoint comparisons, the D=8 outer purity tie,
the D=6 and D=4 rational certificates, 354 exact finite cubic-phase matrix
entries and three rational Schmidt normalization examples. An actual two-qubit
density passes the linear relaxation while its partial transpose has exact
expectation −1/10. This protects the physical necessity of the determinant
condition. Separately, 370 evaluated real-power cases check the displayed
formulas and integer-rank calculation numerically at 80 decimal digits.

These are supporting exact checks and finite numerical diagnostics. The
continuous-order optimization, arbitrary-dimensional phase identity and
equality proofs are the manuscripts, not extrapolations from those runs.
No unitary sampling, additional formalization or expanded Lean audit is used.

```bash
python3 check_finite_extrema.py --out DIAGNOSTICS_LOCAL.json
python3 check_sources.py
```

The independent assistant read all 558 lines of the three proof manuscripts
and prepared map, with no mathematical changes requested. The record binds
their literal bytes and the reviewer's actual primary-source read scopes.
This is internal assistant review, not external human peer review.
[Run comparison](DIAGNOSTIC_COMPARISON.json) and
[literal source bindings](SOURCE_HASHES.json) preserve the finite checks.
The Windows normal, Windows optimized and WSL runs share one implementation,
so they do not constitute three independent mathematical proofs. No new
Release, DOI, aiXiv submission or external message is part of this packet.
