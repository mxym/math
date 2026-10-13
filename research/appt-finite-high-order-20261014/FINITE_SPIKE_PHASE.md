# Exact finite high-order Rényi minimum in every bipartite dimension

Yongxian Zhang (张永贤), School of Computer Science and Engineering,
South China University of Technology; mxymmxym1@gmail.com;
ORCID 0009-0000-3864-3536. Research proof, 14 October 2026.
No external funding; OpenAI AI assistants assisted. Original material all
rights reserved. Complete ordinary proof of the stated bands; no complete
Lean formalization, external human peer review, or historical priority claim.

## 1. The finite theorem

Let 2≤m≤n, D=mn, and use natural-log Rényi entropy
S_α(ρ)=log Tr(ρ^α)/(1−α). Define the sufficient order cutoff

    A_D=D/2+1  for D≥6,
        24     for D=4.                                 (H1)

**Theorem H.** For every actual bipartite APPT density and every real α≥A_D,

    min_APPT S_α=min_ASEP S_α
      =[α log(D+2)−log(3^α+D−1)]/(α−1).                 (H2)

All equality states in either set, and only those states, have the form

    ρ_v=(I+2vv*)/(D+2),  v any unit vector.              (H3)

Both order ranges are finite sufficient bands. Their constants are not
asserted optimal, and the theorem does not determine the finite minimum
below A_D. It covers fixed small dimensions as well as growing ones.
The pole's absolute separability is a known white-noise endpoint, proved
explicitly with attribution in [POLE_SEPARABILITY.md](POLE_SEPARABILITY.md).
This is an optimality theorem in a stated band, not a solution of the general
APPT=ASEP problem.

**Theorem N (scale of a dimension-only eventual cutoff).** Along qubit–qudit
dimensions D=2n→∞, for every fixed 0<c<log(2)/2, the pole H3 is not a power
maximizer at α=cD once D is sufficiently large. Thus a dimension-only order
bound guaranteeing pole optimality for every larger order cannot be o(D),
or have limiting coefficient strictly below log(2)/2. Together with H1 this
proves the sufficient cutoff has the correct order Θ(D), not the sharp
coefficient or the exact transition order in every dimension pair.

## 2. Necessary physical inequalities

For every actual ordered APPT spectrum λ, a variable rank-two Schmidt test
gives, as rederived in [POWER_ENVELOPE.md](POWER_ENVELOPE.md),

    (λ_1−λ_(D−1))²≤4λ_D λ_(D−2),
    λ_1≤λ_(D−2)+λ_(D−1)+λ_D≤3(1−λ_1)/(D−1),
    λ_1≤3/(D+2).                                        (H4)

The average of the three smallest tail entries is at most the mean of the
whole tail. These necessary conditions come from the actual unitary orbit;
the linear inequality alone is not a substitute for APPT.

When λ_1=3/(D+2), equality throughout the two linear bounds forces all
D−1 tail entries to equal 1/(D+2). Thus equality at the top cap has exactly
the pole spectrum. The harder point is strict finite-power optimality when
the top eigenvalue is below its cap.

## 3. D≥8

Theorem P of POWER_ENVELOPE gives the full outer maximum for every α≥2.
Its only possible physical equality spectra are π_j. By equation P17,
α≥D/2+1 makes its real maximizing rank x_*<1. Therefore π_1 is the unique
outer maximizer. Here α≥5, so the D=8, α=2 exception never enters.
Every actual APPT power sum is bounded by

    Tr(ρ^α)≤(3^α+D−1)/(D+2)^α,                          (H5)

with equality only at the pole spectrum. H3 is ASEP in every pair (m,n),
so H5 is attained on both physical sets. Taking log and dividing by 1−α<0
proves H2 and H3 in these dimensions.

## 4. The remaining D=6 case

D=6 can only be 2⊗3. The same known outer vertex list P7 applies, but its
α=2 purity comparison used earlier does not hold at this dimension, so a
separate comparison is necessary. For α≥4, P17 gives x_*<1; hence π_1
strictly dominates π_2 and π_3. Uniform vertices have power sums at most
4^(1−α), and

    4^(1−α)/F_(6,α)(1)≤4(2/3)^α≤64/81<1.              (H6)

The remaining outer vertices have sums

    G_i(α)=(i2^α+5−i)/(5+i)^α,  i=1,2,3.

At α=4 the exact values are

    F_(6,4)(1)=43/2048,
    G_1(4)=5/324,  G_2(4)=35/2401,  G_3(4)=25/2048,

all strictly smaller. For α≥4,

    d/dα log[F_(6,α)(1)/G_i(α)]
      =log[(5+i)/8]+[3^α/(3^α+5)] log 3
                        −[i2^α/(i2^α+5−i)] log 2
      ≥log[(5+i)/16]+(81/86)log 3>0.                    (H7)

To verify the strict final sign without a decimal estimate, the largest
log[16/(5+i)] is log(8/3)<1, since e>1+1+1/2+1/6=8/3.
The first two positive terms of the expansion of 2atanh(1/2) give
log 3>1+1/12=13/12; consequently (81/86)log 3>1053/1032>1.
Each ratio is therefore increasing, and its value at four exceeds one.
Strict convexity excludes all nonvertex equality spectra. H5 and the
physical attainment prove H2–H3 for D=6 and every α≥4.

## 5. D=4: physical stability near the maximum eigenvalue

For two qubits put y_i=4λ_i and, in decreasing order, write

    p=y_1,  w=y_2,  v=y_3,  u=y_4,
    δ=2−p≥0,  S=u+v+w=4−p=2+δ,
    μ=S/3=2/3+δ/3,  t=2/3.

The rank-two determinant condition in H4 is (p−v)²≤4uw. Therefore

    (w−u)²=(S−v)²−4uw
       ≤(S−v)²−(p−v)²=2δ(4−2v)≤8δ.                   (H8)

When δ=0 this forces u=v=w=2/3, the pole spectrum. Suppose first that
0<δ<1/16. The three tail values have mean μ and range at most √(8δ).
It follows that

    μ≤11/16,
    w≤μ+√(8δ)<11/16+1/√2<7/5=:V,
    p>31/16>19/10=:L.                                  (H9)

The penultimate comparison follows by squaring 1/√2<57/80. For any values
in [u,w], their variance is at most (w−u)²/4; average
(w−x)(x−u)≥0 to see this. Thus the total squared tail deviations are ≤6δ.
Taylor's theorem for x^α on [0,V], α≥2, and cancellation of the linear
deviations yield

    u^α+v^α+w^α≤3μ^α+3α(α−1)δV^(α−2).

Integrating the derivative from t to μ, and from p to two, respectively,

    3μ^α−3t^α≤αδV^(α−1),
    2^α−p^α≥αδL^(α−1).                                 (H10)

For T=α−1≥15 the elementary strict inequality

    (19/14)^T>1+(15/7)T                                 (H11)

holds. Indeed (19/14)^5>4, so its value at T=15 exceeds 64>232/7.
Also log(19/14)>5/19, so the derivative of the difference in H11 is
positive for every T≥15: it is at least 64(5/19)−15/7>0.
Combining H10 with H11 proves, for every α≥16 and 0<δ<1/16,

    p^α+u^α+v^α+w^α<2^α+3(2/3)^α.                     (H12)

This is a quantitative strict estimate all the way to δ=0. Mere compactness
or a fixed gap below the top cap would not cover that region.

## 6. D=4: the region away from the cap

If δ≥1/16, then p≤31/16. Since every y_i≤p and Σ_i y_i=4,

    Σ_i y_i^α≤4p^(α−1),
    4p^(α−1)/2^α≤2(31/32)^(α−1).

For α≥24 the last expression is at most 2exp(−23/32)<1. For an exact check
of this final comparison, the first four terms of exp(23/32) are

    1+23/32+(23/32)²/2+(23/32)³/6=400871/196608>2.

Hence H12 holds strictly throughout the far region as well. Together with
Section 5, equality is possible only when δ=0, which H8 identifies with the
pole spectrum. Divide H12 by 4^α; its right side is exactly the pole's
(3^α+3)/6^α. The known actual ASEP pole gives H2–H3 for all α≥24.

The need for H8 is real: the ordered spectrum (1/2,1/2,0,0) belongs to the
linear outer polytope and beats the pole at many powers, but it is not APPT.
An explicit state with that spectrum is
(|Ψ^−><Ψ^−|+|11><11|)/2. Its partial transpose has expectation −1/10 on
(2|00>+|11>)/√5. This is an actual negative control; relaxing away the
determinant constraint would give a false finite theorem.

## 7. The high-order scale cannot be sublinear in D

On C²⊗C^n, D=2n, let Q be any rank-two orthogonal projection and set
σ_2=(I+2Q)/(D+4). Section 5 of POWER_ENVELOPE proves actual all-unitary
APPT, and Johnston's disclosed theorem gives ASEP. Comparing it to H3,

    Tr(σ_2^α)/Tr(ρ_v^α)
      =[(2·3^α+D−2)/(3^α+D−1)]·[(D+2)/(D+4)]^α.        (H13)

For α=cD with fixed c>0, the first factor tends to two because 3^(cD)/D
diverges. The logarithm of the second factor is
cD log[1−2/(D+4)]→−2c. Thus the ratio tends to 2exp(−2c)>1 whenever
c<log(2)/2. These are actual finite physical competitors for all large
even D, so the pole fails to optimize there.

If an eventual guarantee had a dimension cutoff a(D)=o(D), it would imply
pole optimality at α=cD for any fixed such c once cD≥a(D), contradicting
H13. The same argument excludes a limiting coefficient below log(2)/2.
The upper guarantee D/2+1 in H1 has linear scale, establishing the claimed
Θ(D) order. No sharp coefficient is inferred from this lower competitor.

## 8. Scope of proof and verification

This proof treats every real order in the displayed finite bands and all
actual m⊗n pairs. The outer polytope and the purity case are prior results;
the real-power envelope, physical equality classification and finite-band
extension are explained in their dependency map. The ASEP pole is credited
prior mathematics, with an explicit finite decomposition. General equality
of APPT and ASEP is neither required nor asserted.

The constants 24 and 1/2 in the sufficient cutoff can be improved only by
further analysis; this manuscript does not assert their optimality. There
is no complete Lean proof of the new finite power argument. Old APPT and
finite-tree audits keep their previous roots and input bytes. Finite formula
checks, normal/optimized Python runs and the physical negative control are
supporting diagnostics, not a proof by sampling.
