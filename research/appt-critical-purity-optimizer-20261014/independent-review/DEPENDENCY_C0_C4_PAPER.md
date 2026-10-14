# The complete cubic-scale correction to APPT entropy

Ordinary written proof, 14 October 2026. Independently reviewed. All orders are fixed
before the dimension limit. No Lean or kernel verification is asserted.

## 1. Physical object and the whole target

Let E_alpha(m,n)=log D-min S_alpha(rho), D=mn, where rho ranges over actual
complex density matrices that are PPT after every global unitary. Natural
logarithms are used; S_1 is von Neumann entropy. Let t=2/(m-1), q=1+t, and
let G_alpha(m,D) be the maximum deficit among all normalized spectra with k
copies of q and D-k copies of 1, for integer 0<=k<=D. Every such spectrum
is actual APPT. We consider all m<=n with m tending to infinity and
delta_m=D/m^3 tending to a fixed delta>0.

For alpha>0 put

    psi_alpha(y)=[y^alpha-1-alpha(y-1)]/(alpha-1), alpha!=1;
    psi_1(y)=y log y-y+1, with psi_1(0)=1.

Thus psi_alpha(0)=1 and psi_alpha''(y)=alpha y^(alpha-2), y>0.
Positive and negative anomalies have gains psi_alpha(1+p) and
psi_alpha(1-beta). The complete correction will optimize BOTH lists, with
no prior restriction on their lengths.

## 2. An explicit graph cost

For finite lists 0<=p_i<2 and 0<=beta_j<1, a pattern assigns
each positive p_i to a distinct unordered edge, and each beta_j either to
a diagonal vertex or to a distinct positive edge slot. A positive edge
slot may coincide with a p edge, since they are different witness slots.
The symmetric nonnegative matrix P has off-diagonal entry equal to the
sum of the p and beta assigned there, and diagonal entry 2 beta if a beta
is assigned to that vertex. No slot is used twice within the same list.
Zero list entries can be discarded. All assignments and all coincidences
are included. Up to relabeling, at most 2 len(p)+2 len(beta) vertices are
needed; isolated vertices do not affect the cost.

If the largest eigenvalue of P is less than 2, define

    C(P)=4[1^T(2I-P)^(-1)1-h/2],                         (1)

where h is its number of vertices. Otherwise C(P)=infinity. Define
C(p,beta) as the maximum over ALL these finitely many patterns. For
infinite decreasing nonnegative lists, define C as the supremum of the
finite-prefix costs. In particular the empty cost is zero. These are
explicit finite graph assignments and matrix inverses, with no quantum
optimization hidden in their definition.

The walk expansion is

    C(P)=4 sum_(k>=1) 2^(-k-1) 1^T P^k 1.               (2)

Every term is nonnegative. Consequently costs increase when entries are
added. Disjoint patterns have additive cost. In particular

    C(p,beta)>=sum_i 4p_i/(2-p_i)
                         +sum_j 2beta_j/(1-beta_j),     (3)

whenever the right side is finite, and C>=2(sum p+sum beta).
The two single-anomaly costs in (3) come from an isolated edge and an
isolated diagonal, respectively.

More generally, retain any finite prefix and put all other anomalies in
unused slots. Formula (2), retaining all prefix walks and only the first
walk term of the rest, proves

    C(full)>=C(prefix)+2(sum of omitted anomalies).     (4)

For an infinite list this follows by taking longer finite prefixes. The
prefix pattern can be chosen to maximize its cost before filling the
other slots. Infinite costs cause no difficulty in (3)-(4).

## 3. Main statements

Define

    F_alpha(delta)=sup_(finite p,beta)
       [sum_i psi_alpha(1+p_i)+sum_j psi_alpha(1-beta_j)
                                     -alpha delta C(p,beta)/2],  (5)

with the empty value zero and infinite-cost values excluded. The same
value is an attained maximum over infinite decreasing summable lists.

**C0.** On the ENTIRE physical all-unitary APPT set,

    D[E_alpha(m,n)-G_alpha(m,D)] -> F_alpha(delta).       (6)

**C1.** Restricting both lists to at most L entries gives an attained
finite-dimensional maximum F_alpha,L. It increases to F_alpha, and
0<=F_alpha-F_alpha,L<=A/L on compact positive alpha and delta sets, with
A depending on those compact sets. Thus (5) is a complete explicit
dimension-free variational formula, including orders below two.

**C2.** Define

    delta_crit(alpha)=max{
       max_(0<p<2) (2-p)psi_alpha(1+p)/(2 alpha p),
       max_(0<beta<1) (1-beta)psi_alpha(1-beta)/(alpha beta)}.      (7)

Both maxima are attained in the interiors. Then F=0 exactly when
delta>=delta_crit. Above the threshold its unique maximizing anomaly
profile is empty. At the threshold all profiles are empty or exactly
one anomaly attaining its corresponding ratio in (7). Ties between
different positive, negative, and empty profiles are all retained.
This is a limiting bulk onset, not an exact finite-dimensional equality.

**C3.** For every fixed alpha>=2 and every delta>0, the FULL value is

    F_alpha(delta)=max_(0<=p<2)
           [psi_alpha(1+p)-2 alpha delta p/(2-p)].        (8)

All its nonempty maximizing profiles have exactly one positive anomaly
and no negative anomaly. At alpha=2, delta_crit=1/4. Below that threshold
the unique maximizing p is in (1,2) and solves

    delta=p(2-p)^2/4; F_2(delta)=p^2(p-1).                (9)

At delta=1/4 both p=0 and p=1 maximize; above it only p=0 does.

**C4.** Section 9 gives necessary and sufficient spectral conditions for
near maximizers at the ADDITIVE scale in (6), including arbitrary
alternation among critical profiles. Empirical convergence alone is
insufficient.

## 4. Exact physical reduction and a uniform anomaly bound

Let lambda be any actual APPT spectrum in decreasing order. Set
R=m(m-1)/2, K=m(m+1)/2, b=lambda_(D-K+1)>0,

    x_i=lambda_i/b, kappa=x_R-1,
    p_i=x_i-1-kappa (i<=R), beta_j=1-x_(D+1-j) (j<=K),
    c_m=m^2(t-kappa), T_m=sum p_i+sum beta_j.             (10)

The maximally entangled Schmidt witness, assigning the top R values to
the negative directions and the bottom K to the positive directions,
gives

    0<=kappa<=t, T_m<=R(t-kappa)<=c_m/2, T_m<=m.          (11)

All slots are distinct because m^2<=D. The positivity of b follows from
the single-edge witness lambda_1-lambda_D<=2b and trace one.

We use the already established ordinary paired-gap graph and row
inequalities from SHARP_ASYMPTOTIC.md Sections 2-4, without widening any
Lean audit. In units of b, g_i=x_i-x_(D+1-i), w=g_R, eta_i=g_i-w.
Their exact finite bound is sum eta_i^2<=8. Since
eta_i=p_i+beta_i-beta_R>=p_i, sum p_i^2<=8. Also beta_R<=m/R=t,
beta_i<=eta_i+beta_R for i<=R, and beta_j<=beta_R for R<j<=K. Therefore,
for all m>=3,

    sum p_i^2+sum beta_j^2<=34.                          (12)

For example the three separate bounds are 8, 16+4m/(m-1)<=22, and
4m/(m-1)^2<=3. This bound holds before assuming c_m is bounded.
The earlier exact normalization bound is s=D^(-1)sum x_i=1+O(1/m),
uniformly over all actual spectra; x_i<=3.

Clip every x_i into [1,1+kappa], obtaining y_i, and let
s_0=D^(-1)sum y_i. The difference consists exactly of the lists p and
-beta in (10). Its absolute sum is T_m. For fixed alpha>0, both kernels
psi_alpha(z) and their continuous limits at z=0 are bounded on [0,4].
For base values near one, their Taylor residual divided by the squared
increment is uniformly bounded, including an increment ending at zero.
Their derivative at such a base is O(1/m). Equations (11)-(12) thus give

    sum psi_alpha(x_i/s)<=sum psi_alpha(y_i/s_0)+A_alpha. (13)

This includes the change of mean: |s-s_0|<=T_m/D, the derivative on all
clipped normalized values is O(1/m), and hence its total cost is
O(T_m/m)=O(1). The quadratic residuals cost O(sum p^2+sum beta^2).
The constants can be chosen on compact positive alpha sets.

For ANY normalized values z_i of mean one, with A=sum psi_alpha(z_i),

    D e_alpha= D log[1+(alpha-1)A/D]/(alpha-1),           (14)

and at alpha=1 the value is exactly A. Here A=O(D/m^2+1)=O(m), so
D e_alpha=A+o(1), uniformly in this physical cubic regime. Equation (13)
therefore bounds the deficit of any actual state by the clipped deficit
plus O(1/D), with the exact trace normalization retained.

## 5. Coercivity and the additive kernel identity

Let B_alpha(kappa) be the real-rank interval maximum

    max_(0<=theta<=1)
    {log[1+theta((1+kappa)^alpha-1)]
                                  -alpha log(1+kappa theta)}/(alpha-1),

with its continuous value at alpha=1. For 0<kappa small the maximizing
theta is unique. At alpha!=1 it is

    theta=[(1+kappa)^alpha-1-alpha kappa]
           /[(alpha-1)kappa((1+kappa)^alpha-1)],

and at alpha=1 it is [ (1+kappa)log(1+kappa)/kappa-1 ]/kappa.
Endpoint convexity (concavity followed by the negative divisor for
alpha<1) bounds the deficit of every clipped spectrum by B_alpha.
The displayed formulas and Taylor expansion give

    theta=1/2+O(kappa), B_alpha'(kappa)=alpha kappa/4+O(kappa^2).

Integer rounding at kappa=t costs at most O_alpha(t^2/D^2); hence
D[B_alpha(t)-G_alpha]=o(1). In particular, for some a_alpha,delta>0 and
all sufficiently large m, equations (13)-(14) give

    D[e_alpha(rho)-G_alpha]<=A_alpha-a_alpha,delta c_m.   (15)

Indeed B'(u)>=alpha u/8 near zero, and
D(t^2-kappa^2)>=D t(t-kappa) is a positive constant times delta_m c_m.
Pure bulk gives correction zero. Consequently every sequence with
correction bounded below, and in particular all near maximizers, has
c_m bounded. This is a conclusion, not a finite-anomaly assumption.

Once c_m is bounded, T_m is bounded. The single-diagonal instance of
Section 6, which uses only this boundedness and not (17), keeps beta_1
a fixed distance below one. All kernel derivatives needed in the
following comparison therefore stay bounded, also for alpha<1.
Repeating the mean comparison in
(13) now gives an additive o(1), and the Taylor residual at a base near
one converges to psi_alpha(1+p) or psi_alpha(1-beta). The sum of errors
is O(T_m/m)=o(1). Define the nonnegative EXACT clipped loss

    J_m=D[B_alpha(kappa)-e_alpha(y/(D s_0))].             (16)

The differentiation of B and integer rounding then give

    D[e_alpha(rho)-G_alpha]
      =sum psi_alpha(1+p_i)+sum psi_alpha(1-beta_j)
                              -alpha delta_m c_m/2-J_m+o(1).     (17)

The lower-bound construction below achieves J_m=o(1). No unnormalized
second moment or uncentered power sum has replaced actual entropy.

## 6. Every graph pattern is a necessary physical protection cost

For an arbitrary Schmidt vector with nonnegative coordinates, each p_i
may be assigned to a distinct negative edge of its partial-transpose
witness, and each beta_j to a positive diagonal or edge slot. Every
such eigenbasis assignment is realized by a global unitary. The exact
witness matrix, in units of b and with twice the quadratic form, is

    M_m=(2+kappa)I-kappa 11^T-P_m.                      (18)

Off-diagonal entries are nonpositive. A negative Rayleigh value, if any,
has a nonnegative witness after taking absolute values. Thus the actual
copositive condition is equivalent to M_m being positive semidefinite.
This implication does not assume a replacement definition of APPT.

For c_m bounded, kappa>0 eventually. The matrix
A_m=(2+kappa)I-P_m is positive definite: a null vector at its smallest
eigenvalue can be taken nonnegative, and would make (18) negative since
its overlap with 1 is positive. The rank-one criterion therefore gives

    kappa 1^T A_m^(-1)1<=1.

Let a=2+kappa and K_a(P)=1^T(aI-P)^(-1)1-m/a. Rearrangement yields the
EXACT finite constraint

    c_m>= [kappa m^2 a/(m-1)] K_a(P_m).                 (19)

The prefactor tends to 4. The nonnegative walk expansion of K_a shows
that for every fixed finite-prefix pattern P_0, filled with all other
anomalies in unused slots,

    K_a(P_m)>=K_a(P_0)+2(T_m-T_prefix)/a^2.             (20)

This accounts for ALL omitted mass, even mass spread over a growing
number of tiny anomalies. For a convergent fixed prefix, (19)-(20)
imply

    c>=C(prefix)+2 liminf(T_m-T_prefix).                (21)

Patterns at eigenvalue two have infinite limiting cost. For clarity,
the resolvent gap is uniformly protected at bounded cost: if v>=0 is
a normalized Perron vector, v_i<=1, so 1^T P^k 1>=v^T P^k v=rho(P)^k.
The walk series then bounds K_a below by rho/[a(a-rho)]. Thus a bounded
c in (19) keeps every rho(P_m) a fixed distance below two. This also
justifies the finite-prefix inverse limits used in (21).

## 7. Actual lower attainability and complete compactness

Fix finite lists with C(p,beta)<infinity and choose c>C(p,beta). Put
kappa=t-c/m^2. Use raw eigenvalues 1+kappa+p_i for the finitely many
positive heads, 1-beta_j for the negative heads, and otherwise endpoint
values 1 or 1+kappa. Choose their total upper rank nearest the interval
optimum D theta_alpha(kappa); normalize by their ACTUAL trace.
For large m both endpoint ranks exceed R and K, respectively.

For any physical witness the adverse assignment uses the top R and
bottom K values; all other assignments have greater trace pairing by
the elementary rearrangement inequality. Each such assignment in the
constructed spectrum has the exact form (18) with a finite pattern
embedded in m vertices. Conversely all these patterns were included.
For each pattern, the exact rank-one criterion is (19). Its right side
tends to C(P), and there are only finitely many patterns up to relabeling.
The strict choice c>C therefore makes EVERY matrix (18) positive
semidefinite at sufficiently large m. This proves actual all-unitary
APPT, rather than feasibility only for a necessary relaxation.

Clipping this state leaves endpoint values; its fraction differs from
theta_alpha(kappa) by O(1/D). Its J_m tends to zero. Equation (17) gives
the finite-profile value with penalty alpha delta c/2. Let c decrease
to C AFTER taking the dimension limit. The empty profile is the
already physical q bulk. This proves the lower bound F in (6).

Here are the upper and compactness details. From (12), the head gain of
actual spectra is bounded by a constant on compact alpha sets. For a
finite-cost graph profile, a star holding all its positives gives
sum p_i^2<4; a star holding all negative edges with the largest negative
on its center gives sum beta_j^2<=4. Thus graph-profile gain is also
bounded by a constant A independent of list length. Only costs
c<=2A/(alpha delta)+1 are needed for maximization. Equation (11), or
the cost bound C>=2T, then bounds total list mass by a constant T_0.
For decreasing lists of that mass, the sum of squared entries after
rank L is at most T_0^2/(L+1). Kernel gains are bounded by a constant
times squared entries, including negative entries ending at zero.
Thus their omitted gain is at most A_0/(L+1).

Equations (17) and (21), using a prefix cost-maximizing pattern, imply
for every fixed L

    limsup D[e_alpha(rho)-G_alpha]<=F_alpha,L+A_0/(L+1). (22)

The same tail estimate and monotone prefix costs give
F_alpha,L<=F_alpha<=F_alpha,L+A_0/(L+1). Finite costs are maxima of
finitely many continuous inverse formulas; bounded-cost sets stay
away from their inverse singularities and are closed and bounded.
Thus each finite maximum is attained. Together with the physical lower
bound, (22) proves (6), without restricting the original spectra.

The stronger inequality (4) gives for any finite profile of value V

    V<=F_alpha+A_0/(L+1)-alpha delta T_tail.             (23)

Near maximizing profiles therefore have uniformly vanishing tail mass
as L grows. Diagonal subsequences converge in l1, their head gains
converge, costs are lower semicontinuous, and their limiting costs do
not exceed the limiting bounded budgets. Dropping any excess budget
only increases the value. The definition of F by finite prefixes and
their truncation bounds excludes a value greater than F. This proves
attainment over infinite summable lists, and compactness of the full
maximizing set, with its cost coordinate. It also proves C1, with
constants uniform on compact positive alpha/delta sets.

## 8. Exact bulk onset and the all-profile reduction for alpha>=2

By (3), every gain/cost ratio is at most the largest single-anomaly
ratio in (7). The ratios tend to zero at BOTH ends of their intervals
and are positive in between. Single-anomaly physical constructions
from Section 7 attain every strict-cost limiting value. These facts
prove exactly F=0 iff delta>=delta_crit and emptiness above threshold.

There is strict cost interaction whenever two nonzero anomalies occur.
Two positive edges can meet at a vertex: a positive walk of length two
then contributes more than their disjoint sum. A positive edge and a
negative diagonal can meet at its endpoint, with the same strict walk
increase. For two negatives y>=z>0, put y on a diagonal and z on an
incident positive edge. If its largest eigenvalue is below two, its
cost is

    4[z^2+2z+2y]/[4-4y-z^2].

It exceeds 2y/(1-y)+2z/(1-z). After subtracting the first term, the
remaining comparison has positive numerator proportional to
4(1-y)(y-z)+z(2-y-z)>0. Otherwise its cost is infinite. All remaining
anomalies can stay disjoint. For infinite lists take finite prefixes.
At the critical ratio, any two nonzero entries therefore give strictly
negative value. This proves all equality profiles in C2.

For C3, arrange the decreasing positive p_i and the negative beta_(i+1)
on the same star edges, and beta_1=b on its central diagonal. Pad the
lists by zeros. Put u_i=p_i+beta_(i+1), U=sum u_i, S=sum u_i^2.
The star pattern requires S<4(1-b) for finite cost, and direct inversion
gives

    C_star=2[U^2+4U+S+4b]/[4(1-b)-S].                  (24)

Since U>=sqrt(S)=s, this is at least
4[s^2+2s+2b]/[4-4b-s^2]. Put r=sqrt(s^2+b^2)<2. It is at least
4r/(2-r). Indeed this last comparison is equivalent to
s^2+2s+2b>=r(s+2-b), whose squared difference is

    b[2s(s+2)(s+2-b)+b^2(2s+4-b)]>=0.                 (25)

Both sides being compared are nonnegative. The comparison is strict
if b>0. Also sum p_i^2+sum beta_j^2<=S+b^2=r^2.
For alpha>=2, Taylor's integral formula shows psi_alpha(1+p)/p^2
is increasing and at least alpha/2, whereas
psi_alpha(1-beta)<=alpha beta^2/2. Consequently

    sum gains<=psi_alpha(1+r), C>=4r/(2-r).             (26)

The objective is bounded by the one-variable expression in (8), and
the single positive construction matches it. Equality at a nonempty
maximizer forces b=0, hence all negatives vanish, and U=s, hence at
most one positive is nonzero. This argument also works at alpha=2
because the STRICT cost comparisons supply the equality information.
At alpha=2, differentiating p^2-4 delta p/(2-p) proves (9): its positive
maximum occurs at the unique stationary point in (1,2) for delta<1/4.
The ratio in (7) is maximized at p=1 with value 1/4; the negative ratio
has maximum 1/8 at beta=1/2. All critical and empty ties follow.

No single-anomaly reduction is asserted for orders below two. Formula
(5), its finite approximation, and the bulk onset still cover them.

## 9. Necessary and sufficient near-maximizer criteria

Let K_alpha,delta be the COMPACT set of all decreasing summable lists
(p,beta) and real budgets c satisfying C(p,beta)<=c and

    sum gains-alpha delta c/2=F_alpha(delta).           (27)

In fact every such c equals C(p,beta), since delta>0. Use the l1 metric
on the two lists plus the ordinary metric on c. Extend each actual
finite list in (10) by zeros. An actual APPT sequence is near maximizing
at the additive cubic scale, meaning

    D[e_alpha(rho_m)-G_alpha(m,D)] -> F_alpha(delta),

IF AND ONLY IF both

    J_m->0,
    distance((p^(m),beta^(m),c_m),K_alpha,delta)->0.      (28)

To prove necessity, (15) bounds c_m. For each fixed prefix, (20)-(21)
and the tail gain estimate strengthen (22) by the losses
alpha delta T_tail and J_m. Near maximality therefore forces
limsup T_tail<=A_0/[alpha delta(L+1)] and J_m->0. Every subsequence has
an l1-convergent subsubsequence. Equation (21) ensures its limit is
feasible; (17) and continuity of its gains make it satisfy (27).
Compactness proves the distance condition for the whole sequence.
Conversely (28) bounds c_m, makes its gains and penalty approach the
maximal value, and (17) proves near maximality. There is no requirement
to converge to a single branch of K; alternating critical families are
included.

The loss J_m explicitly tests the clipped BODY, rather than only an
empirical distribution. It can alternatively be resolved into two
nonnegative losses: the interval endpoint-chord loss at its actual
mean, and the loss of that mean from the interval's optimum. Thus it
detects endpoint saturation and optimal rank fraction at the required
additive precision. Finite integer rounding costs o(1) here. Equation
(28) also excludes mass disappearing into infinitely many tiny heads.
For alpha>=2, K is exactly the scalar maximizer set in (8) with its
single-positive cost, plus any empty maximizer. For arbitrary alpha it
is the maximizing compact set of the explicit full graph formula.

## 10. Provenance and scope

The first nonzero entropy law in all growth regimes, and the growing-
order leading variational law, were already proved in the inherited
ordinary packets. They are inputs and are not rebranded as this result.
The new target is the additive D^-1 correction on the cubic scale,
including the actual all-unitary upper, all-profile graph cost, exact
limiting bulk onset, and additive spectral near-maximizer criteria.
This draft changes no original quantum definition and does not assert
an exact finite-dimensional optimizer, an effective dimension threshold,
absolute separability, a varying-order uniform theorem, or a Lean audit.
Publication and repository promotion require separate complete review.
