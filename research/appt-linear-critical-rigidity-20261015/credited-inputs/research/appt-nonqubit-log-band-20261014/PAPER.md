# Exact finite APPT pole optimization at logarithmic order when m≥3

Yongxian Zhang (张永贤), School of Computer Science and Engineering,
South China University of Technology; mxymmxym1@gmail.com;
ORCID 0009-0000-3864-3536. Research proof, 14 October 2026.
No external funding. OpenAI AI assistants assisted. Original material all
rights reserved. Ordinary proof of the displayed finite band, not complete
Lean, external human peer review or verified historical priority.

## 1. Finite theorem and the two local-dimension scales

**Theorem N.** Let 3≤m≤n, D=mn≥9. For every real order

    α≥32log D+1,

the actual all-global-unitary APPT and absolutely separable (ASEP) entropy
minima are both

    [α log(D+2)−log(3^α+D−1)]/(α−1).                    (N1)

All equality states, and only those states, are (I+2vv*)/(D+2), for arbitrary
unit v. Natural logarithms are used. The constant32 is sufficient, not
asserted optimal. The theorem is finite, including every m≥3 dimension
pair and every real order in its band.

A dimension-only eventual pole cutoff for the **APPT** set, uniformly among
these nonqubit pairs, must have order at least log D. Specifically, on actual
3⊗n states, the pole fails at α=c log D for every fixed
0<c<1/log(3/2) and all sufficiently large n. Together with N1 this gives
the correct cutoff order Θ(log D). This lower bound does not assert that
the competing projection-only states are ASEP.

The preceding [qubit pole theorem](../appt-log-order-phase-20261014/SHARP_POLE_PHASE.md)
has exact transition τ_D~(log2)D/2. Thus the actual APPT eventual cutoff has
different dimension scales for m=2 and m≥3. The earlier universal linear
bound can still be used where stronger at small D; the logarithmic band
improves its scale for the nonqubit class. No partition-specific sharp
logarithmic coefficient or all subcritical minimum is determined here.

## 2. A necessary second-eigenvalue bound on actual states

The APPT density set is convex and invariant under global unitaries. Indeed
for each U, partial-transpose positivity of UρU* is a convex constraint.
For a sorted actual spectrum λ, average the unitary swap of its first two
eigenvectors, then average all permutations of the remaining eigenvectors.
The resulting genuine APPT density has spectrum

    (a,a,b,...,b),   a=(λ_1+λ_2)/2≥λ_2,
    b=(1−2a)/(D−2),  2a+(D−2)b=1.                     (N2)

This is a finite convex combination of actual orbit points, not a presumed
sufficient condition on an eigenvalue relaxation.

Embed a3⊗3 basis. Let Q project onto the antisymmetric pairs(1,2) and(1,3),
and w=(2|11>+2|22>+|33>)/3. Then w is unit and
Tr[Q(ww*)^Γ]=−4/9−2/9=−2/3. The averaged density is globally unitarily
equivalent to bI+(a−b)Q. Its PPT test therefore gives

    b−(2/3)(a−b)≥0,  a≤(5/2)b,
    λ_2≤a≤5/[2(D+3)].                                  (N3)

This also rules out b=0. The rational physical test was explicit in the
preceding pole packet; no general APPT=ASEP equivalence is used. A sharper
second-eigenvalue bound is unnecessary for this proof.

Set y_i=Dλ_i and define

    u=3D/(D+2),  V=(5/6)u.

The known physical rank-two witness gives
y_1≤y_(D−2)+y_(D−1)+y_D and y_1≤u. N3 gives

    y_i≤y_2≤5D/[2(D+3)]<V,   i≥2.                     (N4)

The global tail gap N4 is precisely where m≥3 matters.

## 3. The trace constraint controls every tail value near the cap

Put p=y_1, δ=u−p≥0, and let μ=(D−p)/(D−1) be the mean of the D−1 tail
values. Their deviations sum to zero. Write the three smallest deviations
a≤b≤c. The physical outer inequality yields

    a+b+c≥−Kδ,  K=(D+2)/(D−1).

All other D−4 deviations are at least c. Consequently

    0≥a+b+c+(D−4)c≥−Kδ+(D−4)c,
    c≤Kδ/(D−4),
    a≥−Kδ−2c≥−Cδ,
    C=K(D−2)/(D−4)≤77/40<2.                            (N5)

Both factors in C decrease with D≥9. Thus **every** tail eigenvalue is
at least μ−2δ. This conclusion holds arbitrarily near the cap; it is not
a fixed gap or compactness estimate. When δ=0 it forces all tail deviations
nonnegative, and their zero sum makes every tail value equal
u/3=D/(D+2), the pole spectrum.

Since all tail values lie in [μ−2δ,V] with mean μ, their total squared
deviations are bounded by

    Σ_(i≥2)(y_i−μ)²≤2(D−1)Vδ.                          (N6)

To see the variance estimate, average (V−x)(x−a_min)≥0, subtract μ² and
use variance≤(V−μ)(μ−a_min)≤V·2δ. Actual tail nonnegativity remains valid
even if the displayed lower bound is negative.

## 4. A scalar inequality for the continuous order band

For every real D≥9 and T≥32log D,

    (11/10)^T>1+T(D−1).                                (N7)

Here is a proof on the full continuous ranges. Put k=32/11. Since
log(11/10)>1/11, at T_0=32log D the left side exceeds D^k.
The function f(D)=D^k−1−32(D−1)log D is positive at nine:
log9<9/4 and the exact integer comparison9^32>577^11 imply f(9)>0.
For log9<9/4 one can use log3<11/10<9/8 from the first two terms of
2atanh(1/2) and its geometric remainder.

Also log D<√D for D≥9: √D−log D is increasing there and is positive at
nine using log3<4/3. Therefore

    f'(D)=kD^(k−1)−32log D−32(D−1)/D>0.

For an explicit comparison, divide by √D. The first term is
kD^(31/22)>kD^(4/3)≥k·9^(4/3)>576/11, whereas the magnitude of the
remaining terms is less than32(1+1/√D)≤128/3<576/11.
Thus f(D)>0 for all D≥9. Finally the derivative with respect to T of
(11/10)^T−1−T(D−1) is positive for T≥T_0, because

    (11/10)^Tlog(11/10)>D^k/11>D^(5/2)/11>D−1.

The last step uses D^(3/2)≥27>11. This proves N7 without a grid extrapolation.

## 5. Strict real-power optimum in both cap regions

Let α≥32log D+1 and T=α−1. First take0<δ≤u/12. Then

    p≥L=(11/12)u,  L/V=11/10.

Since α>2, Taylor's theorem for x^α on [0,V], N6 and cancellation of the
linear tail deviations give

    Σ_(i≥2)y_i^α≤(D−1)μ^α+α(α−1)(D−1)V^(α−1)δ.

Put b_0=D/(D+2). Since μ=b_0+δ/(D−1), integration of the power derivative
and μ≤V yields

    (D−1)(μ^α−b_0^α)≤αδV^(α−1),
    u^α−p^α≥αδL^(α−1).

Consequently

    Σ_i y_i^α−[u^α+(D−1)b_0^α]
      ≤αδV^(α−1)[1+T(D−1)−(11/10)^T]<0               (N8)

by N7. This strict estimate covers all positive distances to the cap.

If δ≥u/12, every y_i≤p≤(11/12)u and Σ_i y_i=D. Hence

    Σ_i y_i^α≤Dp^(α−1),
    Dp^T/u^α≤(D/u)(11/12)^T
              ≤(D/u)exp(−T/12)≤(D/u)D^(−8/3)<1.       (N9)

Here u>1 and D≥9. Thus the objective is strictly below the pole value in
this region as well. At δ=0, N5 already identified precisely the pole
spectrum. Dividing by D^α proves its exact power maximum and all equality
spectra. The pole is ASEP in every pair by the credited known white-noise
endpoint, explicitly proved in the earlier
[finite product decomposition](../appt-finite-high-order-20261014/POLE_SEPARABILITY.md).
It attains the APPT bound on both physical sets. The spectral theorem gives
all equality states (I+2vv*)/(D+2), proving N1 and uniqueness.

## 6. Actual APPT competitors force the logarithmic lower scale

Fix m=3, D=3n→∞ and α=c log D with fixed c>0. Choose a genuine orthogonal
projection P of rank r=floor(D/α) and put

    σ_D=(I+P)/(D+r),  θ=r/D.

It is actual all-unitary APPT. For any unit test w with at most three
Schmidt coefficients, the negative trace of (ww*)^Γ is
Σ_(i<j)s_i s_j≤[(Σ_i s_i)²−1]/2≤1. Since0≤P≤I,
Tr[P(ww*)^Γ]≥−1; thus I+P^Γ≥0. A global unitary replaces P by another
projection. No ASEP membership is inferred for this competing family.

Its normalized α-moment, M=D^(α−1)Tr(σ_D^α), is exactly

    M(σ_D)=[1−θ+θ2^α]/(1+θ)^α
                    ~2^α/(eα),                         (N10)

because αθ→1, θ2^α→∞ and integer rounding changes θ by at most1/D.
For the pole,

    M(ρ_v)=[(3^α+D−1)/D]·[D/(D+2)]^α~1+3^α/D.

If c log3≤1 the latter is bounded while N10 diverges. Otherwise their
ratio is asymptotic to

    D^(1−c log(3/2))/(ec log D).

For every0<c<1/log(3/2) this tends to infinity in either case. Therefore
the actual projection competitor has strictly lower Rényi entropy for all
large D, and the pole fails at these logarithmic orders. An eventual
dimension-only APPT guarantee cannot be o(log D); together with N1 its
correct order is Θ(log D). The coefficient32 is not asserted sharp, and
this lower proof does not establish an ASEP cutoff lower bound.

## 7. A physical countercontrol for the missing qubit restriction

The logarithmic guarantee cannot be extended to m=2. Take actual
2⊗2048, D=4096, α=300 and any rank-two projection Q. The density
(I+2Q)/(D+4) is all-unitary APPT by the qubit projection proof, yet its
moment ratio to the pole is greater than105/82>1:

    (2·3^300+D−2)/(3^300+D−1)>3/2,
    [(D+2)/(D+4)]^300=(1−1/2050)^300≥35/41.

The first inequality follows from3^300≥3^8>4097 and the second from
Bernoulli's inequality. Also32log4096+1<32·12·(7/10)+1<300.
This is an actual finite APPT competitor above the false unrestricted
logarithmic band, with an exact rational lower certificate. It protects
the m≥3 physical hypothesis and agrees with the separate linear qubit scale.

## 8. Scope

All finite orders and dimensions in N1 are covered by the ordinary proof;
the Θ(log D) lower scale refers to APPT only. The existing pole endpoint,
rank-two witness and projection constructions remain credited inputs.
No general APPT=ASEP theorem, exact subcritical minima, optimal logarithmic
coefficient, new major-conjecture count, complete Lean or enlarged audit
coverage is claimed. This is a further result in the same APPT programme.
