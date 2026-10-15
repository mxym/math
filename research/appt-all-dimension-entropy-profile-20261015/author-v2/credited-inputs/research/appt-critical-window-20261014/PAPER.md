# Sharp APPT pole cutoff through constant order and the full critical envelope

Yongxian Zhang (张永贤), School of Computer Science and Engineering,
South China University of Technology; mxymmxym1@gmail.com;
ORCID0009-0000-3864-3536.14 October2026. No external funding.
OpenAI AI assistants assisted. All rights reserved for original material.
Ordinary proof, not complete Lean or external human peer review.

## 1. Statements

Fix an integer ℓ≥3. Throughout, natural logarithms are used. Set

    R=ℓ(ℓ−1)/2, K=ℓ(ℓ+1)/2, H=R−1,
    q=K/R=(ℓ+1)/(ℓ−1), t=q−1,
    κ=1/log(3/q),
    X_ℓ(D)=κ[logD−loglogD−log(etκ)].                    (W1)

**Theorem W.** For every ε>0 there is D0(ℓ,ε) such that every actual
ℓ≤m≤n, D=mn≥D0, and every real α≥X_ℓ(D)+ε has exactly the pole
APPT and absolutely separable (ASEP) minimum Rényi entropy

    [α log(D+2)−log(3^α+D−1)]/(α−1),                   (W2)

with equality precisely at (I+2vv*)/(D+2), for arbitrary unit v.
The dimension threshold is uniform over m,n,α once ℓ,ε are fixed.
On actual ℓ⊗n, at α=X_ℓ(D)−ε an actual APPT projection state beats
the pole for all sufficiently large n. Its ASEP status is not asserted.

For fixed m≥3 define the APPT eventual uniqueness cutoff by

    A_(m,n)=inf{a>1: the pole is the unique spectral optimum
                         at every real order α>a}.

This set is nonempty by the earlier high-order pole theorem. The two
bounds prove A_(m,n)=X_m(mn)+o(1). This definition assumes no monotonicity
of the pole's optimality at earlier orders. No matching ASEP lower cutoff,
necessity on every separate admissible D, or optimizer classification
inside an o(1) transition window is inferred.

**Theorem C.** Fix m≥3, set ℓ=m, let D=mn→∞ and

    α=κ(logD−loglogD)+s,
    B_D=D^(κlogq)/(logD)^(κlog3).

Uniformly for s in every fixed compact real interval, the actual APPT
normalized moment maximum M*=max D^(α−1)Trρ^α satisfies

    M*/B_D→max{3^s,q^s/(etκ)}.                        (W3)

For E=logD−min_(actual APPT)S_α, equivalently,

    (α−1)(E−logq)+loglogD
              →logq+max{s/κ,−log(etκ)}.              (W4)

The critical offset is s*=−κlog(etκ). Both branches are included at s*.
This is an APPT envelope; no subcritical ASEP envelope is claimed.

## 2. A common tail pivot from actual spectral arrangements

Let λ be an actual sorted APPT spectrum. A maximally entangled ℓ-Schmidt
pure vector has partial-transpose eigenvalues −1/ℓ on R antisymmetric
directions, +1/ℓ on K symmetric directions, and zero elsewhere.
By a global unitary place λ_1,...,λ_R on the negative sector and the
K smallest eigenvalues on the positive sector. These are disjoint because
D≥m²≥ℓ²=R+K. The actual PPT test implies

    Σ_(i=1)^R λ_i≤Σ_(i=D−K+1)^D λ_i.

Put b=λ_(D−K+1). The physical rank-two outer condition gives
λ_1≤λ_(D−2)+λ_(D−1)+λ_D≤3b. Consequently b>0 and

    λ_R≤qb,   λ_1≤3b,
    z_i=λ_i/b∈[1,q] for R≤i≤D−K,
    z_i∈[1,3] for i≤H,  z_i∈[0,1] for i>D−K,
    Db≤D/(D−K+1)=1+O_ℓ(1/D).                         (W5)

The last bound follows by summing the D−K+1 eigenvalues at least b.
These are necessary inequalities on actual states, not an APPT equivalence
for a presumed scalar relaxation. All constants depend only on fixed ℓ.

There is also a stronger two-head test relative to this same b. For an
arbitrary real nonnegative unit Schmidt triple x_1,x_2,x_3, place λ_1
and λ_2 on the antisymmetric pairs12 and13 of its partial transpose.
Place λ_(D−K) on the third negative pair23, and the six smallest
eigenvalues on its six positive directions. The chosen indices are
distinct: D−K≥R≥3, K≥6, and the positive indices lie in the bottom K.
The third negative eigenvalue is at least b, and all positive ones are
at most b. The expectation of this actual orbit point is therefore at most

    b−(λ_1−b)x_1x_2−(λ_2−b)x_1x_3.

APPT makes that upper bound nonnegative for every triple. Optimizing with
x_1=1/√2 and (x_2,x_3) proportional to (λ_1−b,λ_2−b), or using the
trivial case when both differences vanish, proves

    (z_1−1)²+(z_2−1)²≤4.                             (W6)

In particular, if z_1≥3−η with0<η<1 then every tail ratio is at most
q_η=1+sqrt(4η−η²). Choose η small enough that q_η<q. This controls
the coexistence of a large relative peak and a high bulk on actual states.

## 3. The exact scalar chord maximum

For fixed q>1 and α>1 define

    F_q(α)=max_(0≤θ≤1) [1+θ(q^α−1)]/[1+(q−1)θ]^α.

For x∈[1,q], convexity gives x^α≤1+(x−1)(q^α−1)/(q−1).
Thus a group of L ratios in [1,q] with mean1+tθ has power sum at most
L[1+θ(q^α−1)]. Writing Q=q^α, differentiation gives the unique maximum

    θ*=(Q−1−αt)/[t(α−1)(Q−1)],
    F_q(α)=(α−1)^(α−1)(Q−1)^α
                    /[tα^α(Q−q)^(α−1)].              (W7)

The derivative has the sign of Q−1−αt−t(α−1)(Q−1)θ and hence only
one zero. Both endpoint values equal1, and strict Jensen makes every
interior two-point value greater than1; therefore that zero lies in(0,1)
and is the unique maximum for every real α>1. This proves the exact scalar
statement without discrete sampling. The exact ratio to Q/(etα) is

    e(1−1/α)^(α−1)(1−1/Q)^α/(1−q/Q)^(α−1)→1.

Consequently

    F_q(α)~q^α/(etα),                                 (W8)

uniformly over every range whose minimum α tends to∞. The latter follows
from the ordinary limit: beyond any fixed sufficiently large lower α,
the relative error is uniformly small. This includes the continuous
critical-to-linear-logarithmic intervals used below.

## 4. A strict physical neighborhood of the pole

Use the previously proved actual cap and bottom-three trace stability:

    y_i=Dλ_i, u=3D/(D+2), δ=u−y_1≥0,
    μ=(D−y_1)/(D−1), b0=D/(D+2),
    y_i≥μ−2δ for i≥2.                                 (W9)

These hold at all D≥9, and δ=0 forces precisely the pole spectrum.
They are disclosed ordinary inputs from the earlier finite-band proof.
Choose a small fixed h∈(0,1/3) such that

    W=1+4sqrt(h)<q, L=3−2h, L/W>3/q.

This is possible because L/W→3 and q>1 as h→0. When0≤δ≤h and D
is sufficiently large, W5 and y_1≥u−h imply z_1≥3−3h. W6 therefore
gives every tail y_i≤(Db)[1+sqrt(12h−9h²)]≤W. The last inequality
holds eventually since Db≤1+O_ℓ(1/D) and sqrt12<4. Also y_1≥L.

By the elementary variance bound for numbers in [a_min,W] with mean μ,

    Σ_(i≥2)(y_i−μ)²≤(D−1)(W−μ)(μ−a_min)
                                 ≤2(D−1)Wδ.

Taylor's theorem for x^α, cancellation of all linear tail deviations,
and integration of the mean shift μ=b0+δ/(D−1) and peak loss give

    Σ_i y_i^α−[u^α+(D−1)b0^α]
        ≤αδW^(α−1)[1+(α−1)(D−1)−(L/W)^(α−1)].        (W10)

For every fixed S, the bracket is negative at every real
α≥κ(logD−loglogD)−S once D is sufficiently large. Indeed T=α−1 at
the smallest allowed order gives

    (L/W)^T/[1+T(D−1)]
      ≍D^(κlog(L/W)−1)/(logD)^(κlog(L/W)+1)→∞.

The exponent is strictly positive. This ratio increases for all larger
T once T>1/log(L/W), by differentiating its logarithm. This is a complete
continuous-order estimate, including arbitrarily small δ>0. Every state
in this physical neighborhood, except δ=0 itself, is strictly below the
pole moment at all those orders.

## 5. Complete bounds outside that neighborhood

Fix any C>κ and a fixed S. Uniformly for

    κ(logD−loglogD)−S≤α≤C logD+1,

we have α→∞ and α=O(logD). Finite counts depending only on ℓ change
normalization by (D/[D−O_ℓ(1)])^α=1+o(1), uniformly over this interval.
Write P_D(α)=D^(α−1)Tr(pole^α); throughout the interval

    P_D(α)~3^α/D,

uniformly, since κlog3>1 and α/D→0.

First suppose z_1≤3−η. W5 gives H exceptional ratios at most3−η,
L0=D−H−K middle ratios in[1,q], and K bottom ratios at most1.
Let their middle mean be1+tθ. The total ratio sum Z=Σz_i is at least
L0(1+tθ). Apply the chord bound and the exact normalized-moment identity
M=D^(α−1)Σz_i^α/Z^α to get

    M≤(D/L0)^(α−1)F_q(α)
                 +(D/L0)^α[H(3−η)^α+K]/D.

The second term is o(P_D) uniformly on the interval. Hence

    M≤(1+o(1))F_q(α)+o(P_D(α)).                        (W11)

Next suppose z_1≥3−η but δ≥h. All tails are at most q_η relative to b.
The L1=D−K−1 nonbottom tails have ratios in[1,q_η], so the same chord
argument, retaining the peak contribution exactly, gives

    M≤y_1^α/D+(D/L1)^(α−1)F_(q_η)(α)+(D/L1)^αK/D.

The first term divided by P_D is at most(1−h/3)^α. The second divided
by P_D tends to zero uniformly, because q_η<q and

    D(q_η/3)^α/α
       =O(D^(1−κlog(3/q_η))(logD)^(κlog(3/q_η)−1))→0.

The bottom term is negligible as well. Thus M=o(P_D) in this region.
Together with W10/W11, these bounds exhaust every actual APPT spectrum.
No scalar relaxation is treated as a sufficient APPT characterization.

## 6. The constant-order cutoff and all higher orders

At α=X_ℓ(D)+ε, W8 and the pole moment give

    F_q(α)/P_D(α)→exp(−ε/κ)<1.                        (W12)

For larger α in the interval of Section5, this ratio is bounded by
(1+o(1))D(q/3)^α/(etα). The latter is strictly decreasing with α.
Therefore W11 is strictly below P_D uniformly at every
X_ℓ(D)+ε≤α≤C logD+1. The other two physical regions are already
strictly below P_D, except for the pole itself. At every higher α use the
previous sharp-leading theorem with any fixed C>κ: it proves exactly the
same unique pole value for all α≥C logD+1 and all sufficiently large D,
uniformly in m≥ℓ,n. The ASEP pole attains the APPT bound on both sets.
This proves the entire upper assertion of Theorem W.

For the lower assertion on actual ℓ⊗n take k=floor(D/(tα)) and
σ=(I+tQ)/(D+tk), Q an arbitrary rank-k projection. The complete Schmidt
negative-trace bound is at most(ℓ−1)/2=1/t; hence I+tQ is all-unitary
PPT for every projection, as already proved in the previous packet.
Its exact normalized moment is

    M(σ)=[1−θ+θq^α]/(1+tθ)^α, θ=k/D,
                               ~q^α/(etα).

At α=X_ℓ(D)−ε, integer rounding has αtθ→1, θq^α→∞, and the moment
ratio to the pole tends to exp(ε/κ)>1. The genuine APPT competitor
therefore has strictly lower Rényi entropy. It is not asserted ASEP.
The definition of A_(m,n) gives X_m−ε≤A_(m,n)≤X_m+ε for all large n,
proving A_(m,n)=X_m+o(1) without an assumed all-order monotonicity bridge.

## 7. Full bounded-offset moment and entropy envelope

Set ℓ=m and α=κ(logD−loglogD)+s, for s in a fixed compact interval.
In the near-cap region W10 bounds every actual state by the exact pole.
The remaining regions give W11 or o(P_D), uniformly in s. Thus

    M*≤(1+o(1))max{P_D(α),F_q(α)}.

Both lower terms are attained to relative1+o(1) by actual APPT states:
the exact pole and the integer-rank projection family of Section6. Hence
this is an asymptotic equality on the full actual set. Since κlog(3/q)=1,

    P_D/B_D→3^s, F_q/B_D→q^s/(etκ),

uniformly in bounded s, proving W3. Taking logarithms is legitimate
uniformly because the two limiting terms are bounded away from zero on
every compact interval. Subtract (α−1)logq and use the same identity:

    logM*−(α−1)logq+loglogD
       →logq+max{slog(3/q),−log(etκ)}.

This is W4, including the branch meeting point s*=−κlog(etκ).

## 8. Attribution and verification boundary

Prior physical rank-two/cap bounds, the full bottom-three trace stability,
the actual projection criterion, sharp-leading all-order pole theorem and
ASEP pole endpoint are disclosed inputs from the two preceding packets.
Common-pivot arrangements, chord optimization, physical neighborhood and
critical comparisons have been proved above. No prior240/249/471-line read
covers this manuscript. Finite diagnostics are supporting checks rather
than proofs of continuous orders, asymptotic uniformity or full APPT scope.
The result continues the same APPT programme; no independent major count,
complete Lean, extended audit, external human peer review, exhaustive
historical priority, new Release, DOI or submission is asserted.
