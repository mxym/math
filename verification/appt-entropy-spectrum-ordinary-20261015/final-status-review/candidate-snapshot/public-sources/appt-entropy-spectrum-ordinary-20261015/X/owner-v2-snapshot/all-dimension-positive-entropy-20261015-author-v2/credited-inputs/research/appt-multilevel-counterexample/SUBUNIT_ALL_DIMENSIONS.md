# Subunit APPT entropy in every total-dimension growth regime

Research proof, 13 October 2026. Yongxian Zhang (张永贤), School of Computer
Science and Engineering, South China University of Technology.
ORCID 0009-0000-3864-3536; mxymmxym1@gmail.com.
No external funding. OpenAI AI assistants assisted the work.
Copyright 2026 Yongxian Zhang; all rights reserved for original material.

This completes the ordinary mathematical first nonzero entropy-deficit
equivalent for every fixed 0<α<1 as total dimension tends to infinity,
including fixed, growing and oscillating smaller local dimensions. The
fixed-local secant optimization is a classical scalar argument, not claimed
as a newly invented method. The sharp joint-growth input is the separately
proved [SUBUNIT_RENYI.md](SUBUNIT_RENYI.md). This continuation is a written
proof, not a Lean theorem, external peer review or priority certification.

## 1. The exact quantities and results

On C^m⊗C^n, 2≤m≤n, put D=mn and

    E_α(m,n)=log D−min_(ρ density, all-unitary APPT) S_α(ρ),
    r_m=(m+1)/(m−1),
    c_(m,α)=(r_m^α−1)/(r_m−1),
    z_(m,α)=(1−α)c_(m,α)/[α(1−c_(m,α))],
    h_(m,α)=log z_(m,α)+log(c_(m,α)/α)/(α−1).

The order α is fixed in (0,1). Then 0<c_(m,α)<α<1,
1/r_m<z_(m,α)<1, and h_(m,α)>0.

**Fixed-local theorem.** For every fixed integer m≥2,

    E_α(m,n) → h_(m,α)                     as n→∞.          (A1)

As m→∞ with α fixed,

    h_(m,α) ~ α/(2m²).                                    (A2)

Set a_α=max{2α,1} and define

    B_α(m,n)=max{(a_α+2α)/(mn), a_α/(mn)+h_(m,α)}.

**Uniform all-dimension theorem.**

    lim_(N→∞) sup_(2≤m≤n, mn≥N)
             |E_α(m,n)/B_α(m,n)−1| = 0.                    (A3)

Thus one total-dimension threshold works for every pair of local dimensions.
This is an asymptotic equivalent, not an exact finite-dimensional minimum or
an assumed interpolation formula. It remains a statement for each fixed α;
no uniformity as α approaches zero with dimension is asserted.

## 2. A genuine physical spectral interval

Fix m and let R=m(m−1)/2, S=m(m+1)/2. For an actual APPT density write its
ordered eigenvalues λ_1≥...≥λ_D. Take a unit pure Schmidt witness with all m
Schmidt coefficients 1/√m. Its partial transpose has R negative eigenvalues
−1/m and S positive eigenvalues 1/m, with all other eigenvalues zero.
These follow directly from the diagonal, symmetric and antisymmetric
Schmidt basis vectors.

All-unitary APPT allows a global eigenbasis placing the R largest state
eigenvalues in the negative slots and the S least in the positive slots;
the slots are disjoint because D≥m²=R+S. Positivity of its expectation gives

    Σ_(i=1)^R λ_i ≤ Σ_(i=D−S+1)^D λ_i.

With b=λ_(D−S+1), ordering yields

    R λ_R ≤ S b,       λ_R ≤ r_m b.                         (A4)

The pivot b is positive: otherwise the positive-slot sum is zero, so every
top eigenvalue is zero and trace one is impossible. Every eigenvalue in

    R≤i≤D−S+1

therefore lies in [b,r_m b]. Exactly L=R+S−2=m²−2 slots are omitted.
This interval is a necessary consequence of the original all-global-unitary
APPT condition, not a spectral-ansatz premise.

The ordinary rank-two physical test also gives λ_1≤3/(D+2). For completeness,
place λ_1 in the negative pair slot, two of the three least eigenvalues on
its two diagonal slots, and the third in its positive pair slot; the equal
two-component Schmidt test gives λ_1 no larger than their sum. Ordering
then bounds this least-three sum by 3(1−λ_1)/(D−1), yielding the displayed
bound. Hence all normalized eigenvalues y_i=Dλ_i lie in [0,3].

Let z=Db and θ_D=(D−L)/D. The mean of all y_i is one, and the omitted
contribution is at most 3L/D. Thus

    1−3L/D ≤ (1/D)Σ_bulk y_i ≤1.

Since the bulk lies in [z,r_m z], for all sufficiently large D,

    (1−3L/D)/(r_m θ_D) ≤ z ≤ 1/θ_D.                        (A5)

For fixed m this places z in a compact positive interval and at distance
O_m(1/D) from [1/r_m,1]. It justifies uniform secant errors despite the
possibly zero exceptional eigenvalues.

## 3. The unrestricted upper half and scalar optimum

Concavity of x^α gives on [z,r_m z]

    y^α ≥ z^(α−1)[c_(m,α) y+(1−c_(m,α))z].

Sum over the actual bulk; omitted power terms are nonnegative. Equations
(A5) and the bulk-mean bound give

    M_α(ρ):=(1/D)Σ_i y_i^α
      ≥ F_(m,α)(z)−O_(m,α)(1/D),
    F_(m,α)(z)=z^(α−1)[c_(m,α)+(1−c_(m,α))z].             (A6)

The error is uniform over every actual APPT state. Clipping z to [1/r_m,1]
changes F by O_(m,α)(1/D), since its derivative is bounded on the compact
positive neighborhood in (A5).

F equals one at both endpoints. For every interior z, take the two values
z and r_m z with upper weight (1−z)/[(r_m−1)z]; their mean is one, and
strict concavity gives F(z)<1. The derivative is

    F'(z)=z^(α−2)[(α−1)c_(m,α)+α(1−c_(m,α))z].

Its bracket is strictly increasing. Consequently its unique zero is the
interior minimum z_(m,α), where

    F_min=(c_(m,α)/α) z_(m,α)^(α−1) ∈(0,1).

The exact entropy identity is

    log D−S_α(ρ)=log M_α(ρ)/(α−1).

Since α−1<0, (A6) bounds the deficit above by h_(m,α)+O_(m,α)(1/D).
This proves the upper half of (A1) without assuming a number of spectral levels.

## 4. Actual all-unitary lower states

For every coordinate projection P of rank k, the matrix

    B=I+[2/(m−1)]P

is APPT in the original physical sense. Given any unit Schmidt vector s,
let W be its partial-transposed pure projector. The expectation Tr(PW)
is at least −N, where N=Σ_(i<j)s_i s_j. Cauchy and Σ s_i²=1 give
2N=(Σ s_i)²−1≤m−1. Therefore Tr(BW)≥1−2N/(m−1)≥0, for every
unitary conjugate of P and every unit complex test vector. Positivity and
trace normalization produce a genuine density/APPT state. The same finite
contraction sufficiency also has the established physical Lean endpoint
`APPTReview.absolutelyPPT_dimension_contraction`; it is not an unproved input.

Its eigenvalues have ratio r_m, with k upper entries. Choose integers k_D
with k_D/D approaching

    q_*=(1−z_(m,α))/[(r_m−1)z_(m,α)] ∈(0,1).

The normalized lower eigenvalue tends to z_(m,α), and the power mean tends
to F_min. Thus these actual states attain the limiting entropy deficit
h_(m,α). Integer rank rounding is legitimate for every D=mn and has error
at most 1/D. This proves the lower half and hence (A1).

## 5. Large-local expansion

Write ε=r_m−1=2/(m−1). Taylor expansion at ε=0 gives

    c_(m,α)=α+α(α−1)ε/2+O_α(ε²),
    z_(m,α)=1−ε/2+O_α(ε²),
    q_*=1/2+O_α(ε).

Both normalized endpoint deviations are O_α(ε), their mean is zero and their
variance is ε²/4+O_α(ε³). The local power expansion therefore gives

    F_min=1+α(α−1)ε²/8+O_α(ε³),
    h_(m,α)=α ε²/8+O_α(ε³)=α/(2m²)[1+O_α(1/m)].

The denominators of z_(m,α) tend to α(1−α)>0, so these expansions are valid
for every fixed α in the stated interval. This proves (A2).

## 6. Every dimensional growth path

The previously proved uniform joint-growth law is

    E_α(m,n) ~ [a_α+(α/2)max{4,n/m}]/D

as m→∞, uniformly n≥m. From (A2), uniformly in that same range,

    D B_α(m,n)
      =max{a_α+2α,a_α+D h_(m,α)}
      ~ a_α+(α/2)max{4,n/m}.

Indeed D h_(m,α)=(α/2)(n/m)[1+O_α(1/m)], and dividing its error by
a_α+(α/2)max{4,n/m} makes it O_α(1/m), independently of n/m.

To prove the total-dimension uniformity, suppose (A3) fails and take offending
pairs D_j→∞ with a fixed relative-error lower bound. If their m_j have a
bounded subsequence, a further subsequence has one fixed integer m; then
n_j→∞, (A1) gives E_α→h_(m,α)>0 and B_α→h_(m,α), contradiction. If no
bounded subsequence exists, m_j→∞ and the joint-growth comparison just given
is again a contradiction. This covers oscillating smaller dimensions as well
as fixed and growing ones and proves (A3).

## 7. Boundaries and attribution

The interval secant method and finite ratio-projection construction are
classical ingredients. The arbitrary-order fixed-m expression extends the
companion formula (E32) by the same secant argument with concavity rather than
convexity; it is credited as such. The order-dependent negative-hole branch
and sharp subunit joint-growth law are proved in the separately linked note.
No unproved APPT=absolute-separability equality or finite spectral-optimizer
conjecture is assumed. The input is actual all-unitary APPT throughout.

The proof determines leading asymptotic entropy minima, not exact finite
minima, higher-order coefficients, efficient thresholds, varying-order limits
or all exact finite fixed-m maximizing spectra. The all-dimension theorem and its real-power
analysis are not covered by the earlier 39-root half-order Lean audit.


## 8. Complete fixed-local leading spectral classification

For fixed m≥2 and α∈(0,1), let n→∞ along any sequence of actual APPT density
matrices, and define the actual empirical normalized spectral measure

    μ_D=(1/D)Σ_i δ_(Dλ_i).

Let z_*=z_(m,α), q_*=(1−z_*)/[(r_m−1)z_*], and

    μ_*=(1−q_*)δ_(z_*)+q_*δ_(r_m z_*).

Then the following are equivalent:

    log D−S_α(ρ_D) → h_(m,α);                             (A7)

    μ_D converges weakly to μ_*.                            (A8)

Furthermore either condition forces the actual extreme eigenvalues to satisfy

    Dλ_1→r_m z_*,       Dλ_D→z_*>0.                       (A9)

In particular all eigenvalues eventually stay uniformly in any fixed small
enlargement of [z_*,r_m z_*], and the states are eventually full rank. This
does not require every eigenvalue to approach one of the endpoints: a vanishing
fraction of interior eigenvalues is allowed. It does not classify eigenvectors
or exact finite-dimensional minimizers.

**Proof.** At fixed m the exceptional count L=m²−2 is constant, and y_i=Dλ_i
are all in [0,3]. If (A7) holds then their power mean tends to F_min.
The unrestricted secant lower bound (A6), the compact positive range (A5)
and the unique minimum of F force the actual pivot z=Db to tend to z_*.
Moreover the mean secant gap on the bulk tends to zero. For any fixed positive
distance from both endpoints, strict concavity makes that gap uniformly
positive once z is close to z_*. Therefore the empirical mass in the interior
away from the endpoints tends to zero. All subsequential weak limits are
supported on {z_*,r_m z_*}; they have mean one because [0,3] is compact and
the actual mean is exactly one. That fixes the upper weight to q_* and proves
(A8). Conversely weak convergence on this compact interval preserves the
continuous power function y^α, including at zero; its mean tends to F_min,
which gives (A7) by the exact entropy identity.

To prove (A9), q_*>0 means a positive fraction of eigenvalues approach the
upper endpoint. Since R is fixed, ordering gives liminf Dλ_R≥r_m z_*.
Inequality (A4) and z→z_* give Dλ_R→r_m z_*. The same true uniform-Schmidt
test now yields

    0≤Σ_(i≤R)(Dλ_i−Dλ_R)
       ≤S z−R Dλ_R → S z_*−R r_m z_* =0.

Thus Dλ_1−Dλ_R→0 and Dλ_1→r_m z_*.
Similarly,

    0≤Σ_(i≥D−S+1)(z−Dλ_i)
       ≤S z−R Dλ_R →0,

so z−Dλ_D→0 and Dλ_D→z_*. Both endpoints are positive, proving eventual
full rank. Every conclusion uses the actual spectral inequality from all-unitary
APPT; an arbitrary interval-valued substitute spectrum would not alone imply
the extreme-eigenvalue part. This completes the fixed-local classification.

The statements (A7)–(A9) are additional written conclusions, not part of the
earlier half-order Lean audit. They hold for fixed m and α; the finite-aspect
classification with m→∞ is separately given in SUBUNIT_RIGIDITY.md.
