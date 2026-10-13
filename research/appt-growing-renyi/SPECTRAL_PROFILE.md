# Which actual spectra minimize entropy along every Rényi-order regime?

Yongxian Zhang (张永贤), School of Computer Science and Engineering,
South China University of Technology; mxymmxym1@gmail.com;
ORCID 0009-0000-3864-3536. Research proof, 14 October 2026.
No external funding; OpenAI AI assistants assisted. All rights reserved for
original material. This is ordinary mathematics, not a new Lean audit,
external human peer review or historical-first certificate.

## 1. One classification covering every limiting order

Take actual APPT densities ρ_j on C^(m_j)⊗C^(n_j), m_j→∞ and n_j/m_j→γ<∞.
Let D_j=m_jn_j, α_j>0 and y_(j,i)=D_jλ_(j,i) in decreasing order. Put

    B=max{4,γ},    K=4+B,
    ℓ_j=y_(j,D_j),
    Q_j=Σ_i(y_(j,i)−1)²,
    δ_j=max_(i<D_j)|y_(j,i)−1|,
    Δ_j=max_i|y_(j,i)−1|.

Here the index omitted from δ_j is the least eigenvalue, while the high-order
criterion below omits the *largest*. Say the sequence is near-optimal if

    [log D_j−S_(α_j)(ρ_j)]/E_(α_j)(m_j,n_j)→1.             (S0)

This is relative optimality at the first nonzero entropy-deficit scale,
not merely S_(α_j)/log D_j→1, which would be too weak.

**Theorem S1.** If α_j→α_0 in the extended interval [0,∞], condition S0 is
equivalent to the row below.

| Limiting order | Necessary and sufficient actual spectral condition |
| --- | --- |
| α_0=0 | `ℓ_j^(α_j)→0` |
| 0<α_0<1/2 | `ℓ_j→0`, `δ_j→0`, `Q_j→1+B` |
| α_0=1/2 | `δ_j→0`, `dist(ℓ_j,{0,1})→0`, `Q_j−(1+B+3ℓ_j)→0` |
| 1/2<α_0<2 | `Δ_j→0` and `Q_j→K` |
| α_0=2 | `Q_j→K` |
| 2<α_0<∞ | `y_(j,1)→3`, `max_(i≥2)|y_(j,i)−1|→0`, `Q_j→K` |
| α_0=∞ | with `χ_j=α_j log[3D_j/(D_j+2)]−log D_j`, `h_j=α_j log{[3D_j/(D_j+2)]/y_(j,1)}`, require `h_j/(1+max{χ_j,0})→0` |

At either finite transition, α_j may approach from either side or alternate.
The criterion is the transition row, not the stronger criterion for a fixed
order strictly on one side. At α_0=∞ the moment-excess criterion instead
requires h_j→0; entropy and moment optimality are explicitly distinguished.
At α_0=0 actual singular states are permitted. At every other row, the
corresponding physical arguments exclude infinitely many singular terms.

For orders or bounded aspect ratios that oscillate without a limit, the same
classification applies on every subsequence with convergent extended order
and finite aspect. Optimality of the whole sequence is equivalent to optimality
on each such convergent subsequence. This is the standard subsequence criterion,
not an additional assumption that all sequences converge.

## 2. Compact-order changes do not alter the leading criterion

For α>0 define the continuous normalized kernel f_α on x≥−1. At α=1 it is
`(1+x)log(1+x)−x`; otherwise it is

    f_α(x)=[(1+x)^α−1−αx]/[α(α−1)].

Its common integral representation is

    f_α(x)=x² ∫_0^1(1−s)(1+sx)^(α−2) ds.                (S1)

It remains valid at x=−1 for every α>0 because the resulting endpoint
integrand behaves as `(1−s)^(α−1)`. On a compact I=[a,b]⊂(0,∞), differentiating
the integrand in α is dominated by an integrable bound independent of x∈[−1,2].
For negative x it is bounded by a constant times
`(1−s)^(min{a,2}−1)|log(1−s)|`; for positive x it is bounded using
`1≤1+sx≤3`. This proves

    |f_α(x)−f_β(x)|≤C_I|α−β|x²                          (S2)

for α,β∈I and x∈[−1,2]. No nonzero least-eigenvalue premise is needed.

The actual eigenvalues satisfy 0≤y_i≤3 and Q=O_γ(1). The exact moment/log
identity and its continuous α=1 value therefore give, uniformly α∈I,

    D[log D−S_α(ρ)]=αΣ_i f_α(y_i−1)+O_(I,γ)(1/D).        (S3)

Even near α=1 its logarithm remainder is uniform: after division by α−1
it is O[α²|α−1|(Σf_α)²/D], rather than an artificial pole. At α=1 the
leading equality is exact. Equations S2–S3 show that replacing α_j→α_0>0
by the fixed α_0 changes every actual-state scaled deficit by o(1), uniformly
over the whole physical state set.

The sharp coefficient Φ_α(γ) is continuous at every finite positive α.
Thus S0 for α_j→α_0∈(0,∞) is equivalent to fixed-α_0 leading optimality.
This supplies the finite transition rows directly and justifies why one cannot
apply a fixed-side rigidity estimate with a vanishing coercivity coefficient.

## 3. The finite positive-order rows

For 0<α_0≤1/2 the complete fixed-order physical classifications are in
`SUBUNIT_RIGIDITY.md`. They give precisely the two stated low-order rows,
including the alternating two-branch criterion at α_0=1/2.

For 1≤α_0<2 the companion entropy theorem gives full relative spectral
flatness and sharp Q=K. At α_0=2 the objective is an exact logarithm of purity,
so Q→K alone is necessary and sufficient. For α_0>2 the complete fixed-order
criterion is the positive-spike/flat-rest/sharp-Q row of
`ENTROPY_ASYMPTOTIC.md` Section 12.2.

For completeness the remaining interval 1/2<α_0<1 follows from the same
physical bounds, without assuming an unproved subunit rigidity theorem.
Put θ=2(1−α_0)∈(0,1). Weighted arithmetic-geometric comparison gives

    (1+x)^(α_0−2)
      ≤θ(1+x)^(−3/2)+(1−θ)(1+x)^(−1).

Integrate twice using S1, including x=−1 by continuity. This gives

    f_(α_0)(x)≤θ f_(1/2)(x)+(1−θ)f_1(x).                 (S4)

Both actual-state endpoint sums are at most K/2+o(1): these are the sharp
half-order and von Neumann upper theorems. Subunit optimality in this interval
is exactly saturation of its kernel sum at K/2. Since both weights in S4 are
strictly positive, saturation forces the von Neumann kernel sum to approach
K/2. The known von Neumann criterion gives Δ→0 and Q→K. Conversely these
conditions make the entire spectrum Taylor-flat and S3 gives the optimal
scaled deficit. This proves the interval row and completes every finite
positive-order case.

The singular spectrum is uniform of rank D−1, by the actual rank-two test.
Its deficit has scaled value D log[D/(D−1)]→1 at every positive order.
All finite-positive limiting optimum coefficients in these rows exceed one,
so infinitely many singular terms would prevent optimality. In the infinity
row G3 forces y_1→3, which also forces the least normalized eigenvalue to one
and eventual full rank. This explains the rank boundary claimed after S0.

## 4. The two moving endpoints

At α_j→0, the bounded-aspect state identity in `SMALL_ORDER_BOUNDARY.md` is

    D[log D−S_α(ρ)]=1−ℓ^α+(α/2)Q+o(1).

Since Q is bounded, the second term vanishes. The optimal scaled deficit tends
to one, uniformly, regardless of α log m. Hence relative optimality is exactly
ℓ^α→0. This condition cannot be replaced by ℓ→0: a polynomially small
least eigenvalue may still have ℓ^α→1 when α log m→0.
The singular spectrum realizes it. The complete finite (α log m,α n/m) window
for unbounded aspect, including its two critical branches, is proved separately
in the zero-order note and is not hidden in this bounded-aspect row.

At α_j→∞ the exact necessary-and-sufficient entropy criterion is G6 in
`PAPER.md`; all its uniform actual-state moment reduction and scalar log
arguments were proved there. This gives the final row, including arbitrary
growth relative to m and D. A smaller positive-spike strength can satisfy
relative entropy optimality while its moment-excess ratio tends to zero in
the supercritical regime, so the two criteria are not conflated.

This completes S1. All rows are on the actual ordered eigenvalues and the
specified objective scale. No eigenbasis rigidity, exact finite optimizer,
absolute separability or new Lean coverage is inferred. The entries from older
papers are credited as such; their collection here is a proof-range synthesis,
not separate new major-problem counts.
