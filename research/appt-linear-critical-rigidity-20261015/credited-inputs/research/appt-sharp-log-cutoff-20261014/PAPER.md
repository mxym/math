# Sharp logarithmic APPT cutoff hierarchy and the fixed-local growing-order phase

Yongxian Zhang (张永贤), School of Computer Science and Engineering,
South China University of Technology; mxymmxym1@gmail.com;
ORCID0009-0000-3864-3536.14 October2026. No external funding.
OpenAI AI assistants assisted. All rights reserved for original material.
Ordinary research proof, not complete Lean or external human peer review.

## 1. Statements and exact scopes

Fix an integer ℓ≥3 and set

    r=ℓ(ℓ−1)/2, q=(ℓ+1)/(ℓ−1), t=q−1=2/(ℓ−1),
    κ_ℓ=1/log(3/q).

**Theorem S.** For each real c>κ_ℓ there is D0(ℓ,c) such that every
actual bipartite pair ℓ≤m≤n, D=mn≥D0, and every real α≥c logD+1
has the same APPT and absolutely separable (ASEP) minimum Rényi entropy

    [α log(D+2)−log(3^α+D−1)]/(α−1).                    (S1)

Its equality states are exactly (I+2vv*)/(D+2), for arbitrary unit v.
The threshold D0 is uniform over m,n,α once ℓ,c are fixed. Conversely,
for every0<c<κ_ℓ, the pole fails on actual ℓ⊗n APPT states at α=c logD
for all sufficiently large n. No ASEP membership of those competitors
is asserted. Thus κ_ℓ is the sharp leading coefficient of the eventual
dimension-only APPT guarantee for the class m≥ℓ, with necessity along
D=ℓn. No lower cutoff for every individual admissible D is inferred.

In particular the full nonqubit class has sharp coefficient

    κ_3=1/log(3/2),

improving the explicit sufficient32logD+1 band asymptotically. The
coefficient decreases to1/log3 as fixed ℓ grows; no joint growing-ℓ
uniformity of D0 is claimed. The separate qubit scale remains linear.

**Theorem P.** Fix m≥3 and let n→∞, α→∞, with α/logD→c in [0,∞].
For E=logD−min_(actual APPT) S_α and q_m=(m+1)/(m−1),

    E→max{logq_m, log3−1/c}.                            (S2)

At c=0 the second term is interpreted as−∞; at c=∞ it is log3.
This covers every such sequence, including the critical c=κ_m.
It is an APPT phase theorem; the competing bulk family is not claimed
ASEP and no subcritical ASEP phase or optimizer classification is inferred.

## 2. A finite-head bound from an actual ℓ-Schmidt test

For a sorted actual APPT spectrum λ, the APPT set is convex and invariant
under global unitaries. Average all permutations among the first r
eigenvectors and among the remaining D−r. This genuine APPT density has
spectrum (a[r],b[D−r]), where a≥λ_r≥b and ra+(D−r)b=1.

Let v=ℓ^(-1/2)Σ_(j=1)^ℓ|jj>. Its partial transpose has eigenvalues
−1/ℓ on the antisymmetric rank-r subspace and +1/ℓ on the symmetric
subspace. Let Q project onto the negative subspace. Place the r large
eigenvectors of the averaged density on Q by a global unitary. Testing
the density bI+(a−b)Q against vv* after partial transpose gives

    b−[(ℓ−1)/2](a−b)≥0,   a≤qb.

Normalization therefore implies

    λ_r≤a≤q/[D+(q−1)r]=q/(D+ℓ).                       (S3)

Every construction/test here is on an actual ℓ⊗ℓ subspace of the given
pair. It is a necessary APPT bound, not a sufficient classification.
For y_i=Dλ_i, at most r−1 entries can exceed q. This applies uniformly
to every actual m≥ℓ. Taking ℓ=3 bounds every y_i, i≥3, by2D/(D+3)<2.

We also use disclosed physical inputs from the preceding
[finite logarithmic-band proof](../appt-nonqubit-log-band-20261014/PAPER.md):

    p=y_1≤u=3D/(D+2),  y_i<5/2 for i≥2;
    δ=u−p≥0, μ=(D−p)/(D−1), b0=D/(D+2);
    y_i≥μ−2δ for i≥2,
    Σ_(i≥2)(y_i−μ)²≤5(D−1)δ.                           (S4)

The last two statements are its complete bottom-three trace argument and
variance estimate, valid at every δ≥0 and D≥9. At δ=0 they already
force exactly the pole spectrum. The maximum eigenvalue and rank-two
outer condition are credited prior results; S4 is not a new kernel audit.

## 3. An actual two-head witness controls every exceptional variance

Put s=y_2. Average only eigenvectors3,...,D, giving actual APPT scaled
spectrum (p,s,β[D−2]), with β=(D−p−s)/(D−2)≤s. On an embedded3⊗3
subspace place the p and s eigenvectors on the antisymmetric pairs12
and13. For a real Schmidt vector x_1|11>+x_2|22>+x_3|33>, the scaled
partial-transpose expectation is

    β−(p−β)x_1x_2−(s−β)x_1x_3.

If R=sqrt((p−β)²+(s−β)²)>0 choose
x_1=1/√2, (x_2,x_3)=(p−β,s−β)/(√2R). It is a unit actual test.
If R=0 the following bound holds trivially. APPT hence gives

    (p−β)²+(s−β)²≤4β²,
    (s−β)²≤(3β−p)(β+p).                               (S5)

Set z=s−b0. Since s≥μ=b0+δ/(D−1), z≥0. Exact trace algebra gives

    3β−p=[(D+1)δ−3z]/(D−2)≤(10/7)δ,
    β+p≤μ+p≤9/8+3=33/8,
    s−μ=[(D−2)/(D−1)](s−β).

Consequently, for D≥9,

    (s−μ)²≤(165/28)δ<6δ       when δ>0.                (S6)

For0≤δ≤ε<1 every positive tail deviation is at most s−μ, whereas
S4 bounds negative deviations by2δ. Thus every tail has squared
deviation at most6δ. In particular the r−2 exceptional tails
y_2,...,y_(r−1) have total squared deviation at most6(r−2)δ.
This bound has no D factor, which is essential for the sharp coefficient.

## 4. Proof of the complete eventual order band

Fix c>κ_ℓ. Choose ε in (0,1) so small that

    L=3−2ε>max{5/2,q exp(1/c)}.

For all sufficiently large D, u≥3−ε. Also μ≤D/(D−1)≤q, since
D≥m²≥ℓ². Increase D0 so that α≥c logD+1 always implies α>2.
Write T=α−1≥c logD. All constants in this section depend only on ℓ,c.

First let0<δ≤ε, so p≥L. Apply Taylor's theorem for x^α at μ to
every tail. Their linear deviations cancel exactly. The r−2 exceptional
tails and μ are in [0,5/2]; all other tails and μ are in [0,q]. S4/S6 give

    Σ_(i≥2)y_i^α≤(D−1)μ^α
      +(αTδ/2)[5(D−1)q^(T−1)+6(r−2)(5/2)^(T−1)].       (S7)

Here the bulk squared-deviation sum was bounded by the full S4 sum;
no positivity of individual deviations is assumed. Integration gives

    (D−1)(μ^α−b0^α)≤αδq^T,
    u^α−p^α≥αδL^T.

The total power is strictly below u^α+(D−1)b0^α as soon as

    [1+5T(D−1)/(2q)](q/L)^T
       +[6T(r−2)/5]((5/2)/L)^T<1.                     (S8)

This holds for **every** T≥c logD once D is sufficiently large. For
any0<a<1, Ta^T and (1+AT)a^T decrease when T>1/log(1/a), for every
A≥0, as seen by differentiation. Thus each S8 term is bounded by its
value at T=c logD for large D. The first is
O((logD)D^(1−c log(L/q)))→0 and the second is
O((logD)D^(−c log(L/(5/2))))→0. Both exponents have the required
strict sign by the choice of L. This proves the whole real-order band,
including arbitrarily small positive δ, rather than only fixed-order sequences.

For δ≥ε, use S3 for all indices≥r and ordering for the first r−1:

    Σ_i y_i^α≤(r−1)(u−ε)^α+Dq^α,
    Σ_i y_i^α/u^α≤(r−1)(1−ε/3)^α+[D(q/(3−ε))^α].       (S9)

Both terms decrease with α and tend to zero at α=c logD+1, because
c log((3−ε)/q)>1. For large D they sum to less than1. At δ=0, S4
already gives the unique pole spectrum. The known ASEP white-noise pole
attains the strict APPT upper bound on both physical sets. This proves
S1 and every equality state, uniformly over all m≥ℓ,n,α in the band.

## 5. Actual lower competitors and sharpness

On actual ℓ⊗n let α=c logD,0<c<κ_ℓ, k=floor(D/(tα)), and take
any rank-k orthogonal projection P. For any unit Schmidt vector w of rank
at most ℓ, the total negative trace of (ww*)^Γ is

    Σ_(i<j)s_i s_j≤(ℓ−1)/2=1/t.

Since0≤P≤I, Tr[P(ww*)^Γ]≥−1/t; hence I+tP^Γ≥0. Every global
unitary replaces P by another projection. Thus σ=(I+tP)/(D+tk) is
actual all-unitary APPT, with no inferred ASEP status.

For θ=k/D its normalized moment is exactly

    M(σ)=D^(α−1)Trσ^α=(1−θ+θq^α)/(1+tθ)^α
                              ~q^α/(etα).              (S10)

Indeed αtθ→1, θq^α→∞ and integer rounding contributes at most1/D.
For the pole, M(pole)~1+3^α/D. If c log3≤1, this is bounded while
S10 diverges. Otherwise their ratio is asymptotic to

    D^(1−c log(3/q))/(et c logD)→∞.

Therefore the pole has strictly larger Rényi entropy at these orders.
This proves APPT necessity along D=ℓn and the sharp worst-case coefficient
κ_ℓ. It does not prove any competing ASEP lower bound, an exact finite
transition, or a necessary threshold on every separate dimension partition.

## 6. The complete fixed-local growing-order phase

Fix m≥3, set ℓ=m, and keep r,q,t fixed. S3 and the peak cap imply

    M(ρ)≤[(r−1)/D]u^α
           +[(D−r+1)/D][qD/(D+m)]^α                    (S11)

for every actual APPT state. The entropy deficit is logM/(α−1).
Taking logarithms, the sum of two positive terms differs from the larger
logarithm by at most log2. Therefore for α→∞, α/logD→c, S11 gives
the upper limit max{logq,log3−1/c}; at c=0 the head term is negligible,
and at c=∞ the upper limit is log3.

If c<∞, then α=o(D). The same actual projection family with
k=floor(D/(tα)) satisfies S10 along the entire sequence, because α→∞,
αtθ→1 and q^α/α→∞. Its entropy deficit tends to logq. The exact
pole moment gives limit max{0,log3−1/c}. Taking the larger of these
two physical lower bounds matches S11. For c=∞ the pole alone gives
log3 and matches the upper bound. This proves S2 for all stated sequences,
including both endpoint regimes and the critical value.

## 7. Scope and inputs

The local witness arguments are rederived on actual states. Prior
rank-two/cap inputs and the pole ASEP endpoint remain credited through
the preceding finite-band packet and its sources. That earlier249-line
internal review does not review this new manuscript. Finite diagnostics
can check the identities; full ranges and asymptotic uniformity are proved
above. This is the same APPT direction, not a newly counted major conjecture.
No complete Lean, new audit root, external human peer review, verified
historical priority, new Release, DOI or submission is asserted here.
