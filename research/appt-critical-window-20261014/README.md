# APPT critical window and the sharp pole cutoff through constant order

**Yongxian Zhang (张永贤)** · School of Computer Science and Engineering,
South China University of Technology · mxymmxym1@gmail.com ·
ORCID0009-0000-3864-3536. No external funding. OpenAI AI assistants assisted.
Copyright2026 Yongxian Zhang; all rights reserved for original material.

[Complete ordinary proof](PAPER.md) · [Prepared obligations](THEOREM_MAP.md) ·
[Literature scope](LITERATURE.md) · [Independent internal read](MANUSCRIPT_REVIEW.json).

For every fixed ℓ≥3, put q=(ℓ+1)/(ℓ−1), t=q−1 and κ=1/log(3/q).
The sharp dimension-only eventual APPT pole cutoff for the class m≥ℓ,
through its constant term, is

    X_ℓ(D)=κ[logD−loglogD−log(etκ)].

For **every fixed ε>0**, all sufficiently large D=mn, all ℓ≤m≤n,
and **every real α≥X_ℓ(D)+ε**, the APPT and absolutely separable (ASEP)
Rényi minima are exactly the pole value

    [α log(D+2)−log(3^α+D−1)]/(α−1),

with precisely the equality states (I+2vv*)/(D+2). The dimension threshold
depends only on ℓ,ε. At X_ℓ(D)−ε an actual ℓ⊗n APPT projection family
beats the pole for every large n. The lower family is not asserted ASEP;
necessity is along D=ℓn, rather than on every separate admissible D.
For every fixed m≥3, the eventual APPT uniqueness cutoff, defined as the
infimum of all thresholds above which every order has only the pole
spectrum, equals X_m(mn)+o(1). This definition assumes no finite-order
monotonicity of pole optimality. No ASEP cutoff lower bound is inferred.

There is also a complete **bounded-offset critical envelope**. Fix m≥3
and set ℓ=m, α=κ(logD−loglogD)+s, with s in any fixed compact interval.
Then the actual APPT normalized moment maximum satisfies, uniformly in s,

    max D^(α−1)Trρ^α
      ~ [D^(κlogq)/(logD)^(κlog3)] max{3^s,q^s/(etκ)}.

For E=logD−min S_α this is equivalent to

    (α−1)(E−logq)+loglogD
      →logq+max{s/κ,−log(etκ)}.

The branch meeting point is s*=−κlog(etκ). The formula includes it,
without a finite optimizer classification within the o(1) transition
window or a subcritical ASEP envelope. Joint growing-ℓ uniformity is
not asserted. The [previous sharp-leading theorem and fixed-local phase](../appt-sharp-log-cutoff-20261014/README.md)
and [explicit finite32logD+1 band](../appt-nonqubit-log-band-20261014/README.md)
retain their original proofs and read records.

The proof uses a common tail pivot, genuine partial-transpose spectral
arrangements and an optimized actual three-Schmidt test. These forbid
coexistence of a near-maximal relative peak and a high bulk. A strict
Taylor estimate controls all distances to the physical pole. Elsewhere,
the exact continuous scalar chord optimum contributes the1/α factor
that produces the negative loglogD correction and constant shift.

## Supporting verification

The standard-library checker verifies25 exact integer-order scalar
formulas,150 finite rational comparisons and three actual PPT negative
controls. Each negative control passes the old rank-two/second cap,
averaged two-head circle and top-three/bottom-six bound, while violating
the common-pivot circle. Separately,100 finite critical-window cases are
evaluated at150 decimal digits. Finite examples do not prove the full
continuous-order, asymptotic or all-APPT assertions.

```bash
python3 check_critical.py --out DIAGNOSTICS_LOCAL.json
python3 check_sources.py
```

Windows ordinary/optimized and WSL runs passed using one shared
implementation; [the comparison](DIAGNOSTIC_COMPARISON.json) binds their
scope. The [independent internal review](MANUSCRIPT_REVIEW.json) records
the complete300-line manuscript/map read and exact source bytes. No old
240/249/471/558-line reading is enlarged. This continues the same APPT
direction, without a new major-conjecture count, complete Lean, expanded
kernel audit, external human peer review or historical-first certification.
[Source bindings](SOURCE_HASHES.json) record the packet; no new Release,
DOI, submission or external message is included.
