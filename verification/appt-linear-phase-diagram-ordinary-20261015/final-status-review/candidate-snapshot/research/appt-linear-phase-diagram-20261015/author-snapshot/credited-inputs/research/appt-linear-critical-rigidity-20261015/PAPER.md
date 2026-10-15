# Actual APPT spectra in the linear-order peak--bulk window

Yongxian Zhang (张永贤), South China University of Technology.
15 October 2026, Asia/Shanghai. Complete ordinary proof independently read
in full by an internal AI agent; REVIEW.md and FINAL_STATUS_BINDING.json
bind the source and status edits. Same APPT direction; no new major count.

## 1. Original quantum objects and the previously unclassified window

Consider actual complex PSD trace-one all-global-unitary APPT densities
rho_m on C^m tensor C^n, with integers m<=n, m->infinity, D=mn. Sort their
eigenvalues and put y_i=D lambda_i. Let the positive real orders satisfy

    alpha/m -> c in (0,infinity), 3^alpha/D -> r in [0,infinity).   (S1)

No aspect restriction is imposed: in this window D is exponentially large
in m. Write M(rho)=D^-1 sum y_i^alpha and E_alpha=max_APPT(log D-S_alpha).
Near-optimality means the actual FIRST-NONZERO-scale condition

    (log D-S_alpha(rho_m))/E_alpha ->1.                 (S2)

The existing linear-order and calibrated all-order theorems already prove
the optimized entropy VALUE, including all aspect ratios. They explicitly
do not classify all-aspect optimizing spectra. The bounded-aspect spectral
classification applies to a different dimension range. This paper derives
necessary and sufficient actual spectral criteria in S1; no new claim to
the already completed all-order value theorem is made.

## 2. Explicit parameters and the complete criterion

Let R=m(m-1)/2, K=m(m+1)/2, j=D-K+1. The actual middle indices are

    Bset={R,...,j}, N=D-m^2+2.

For all sufficiently large m, N>0. Define A=y_j>0, B=y_R, the actual
middle mean mu=N^-1 sum_(Bset)y_i, kappa=B/A-1 and

    theta=(mu/A-1)/kappa if kappa>0, theta=0 if kappa=0,
    L=(m-1)kappa in [0,2],
    z_i=(m-1)(y_i/A-1) in [0,L], i in Bset,
    J=N^-1 sum_(Bset) z_i(L-z_i).                       (S3)

Here A=mu/(1+kappa theta), theta in [0,1] and the mean of z_i is L theta.
The finite protection function is the credited actual-witness quantity

    eta_m(kappa)=2(m-2)kappa^2/[2-(m-3)kappa].

The denominator is strictly positive on the full permitted interval.
Define the nonnegative ACTUAL peak slack

    P=[A^alpha(3-eta_m(kappa))^alpha-y_1^alpha]/D >=0.    (S4)

For c>0,r>=0 retain the existing scalar objective

    g_c(l)=2cl^2/[3(2-l)] (0<=l<2), exp[-g_c(2)]=0,
    F(c,r;l,h)=exp(-clh)[1+h(exp(cl)-1)+r exp(-g_c(l))],
    F_*(c,r)=max_(l,h in [0,2]x[0,1]) F(c,r;l,h),
    M(c,r)={(l,h):F(c,r;l,h)=F_*(c,r)}.                 (S5)

This compact maximizing SET retains every scalar tie. It is an explicit
one-dimensional maximization after the existing exact h-optimization
formula L20. No unproved uniqueness is assumed.

**Theorem S (all actual near-optimizers in S1).** Condition S2 is equivalent
to the following three simultaneous spectral conditions:

    dist((L,theta),M(c,r))->0, J->0, P->0.              (S6)

The distance is ordinary Euclidean distance to the FULL compact set.
The criterion quantifies over the original APPT matrices, not only the
three-level construction used to attain the lower bound.

On any subsequence with (L,theta)->(l,h), S6 implies that the empirical
measure of the scaled ACTUAL eigenvalues converges in the 1-Wasserstein
metric to

    D^-1 sum_i delta_(m(y_i-1))
       -> (1-h)delta_(-lh)+h delta_(l(1-h)).            (S7)

If l=0 this is delta_0 and theta need not have a unique limit.
Every member of M(c,r) is realized by a sequence of actual APPT densities
meeting S2. Alternation among maximizing parameters remains allowed.

**Corollary B (pure bulk, r=0).** Put

    h_c=1/(2c)-1/(exp(2c)-1) in (0,1).

Then M(c,0)={(2,h_c)}. Near-optimality S2 is equivalent simply to weak
convergence of the empirical measure in S7 to

    (1-h_c)delta_(-2h_c)+h_c delta_(2(1-h_c)).           (S8)

In this window physical bounds control all exceptional moments separately;
weak convergence is not being used alone to control arbitrary unbounded
exponential moments.

**Corollary P (a surviving peak).** On any S6 subsequence with r>0 and
(L,theta)->(l,h), l<2, the actual largest eigenvalue satisfies

    m(3-y_1) -> 3lh+2l^2/(2-l).                        (S9)

Also max_(i>=2)|y_i-1|->0. If l=2 instead, the actual largest moment
y_1^alpha/D tends to zero; S9 is not asserted at that endpoint.

## 3. Credited physical bounds with original quantifiers

The existing actual-witness proof gives the following necessary bounds
for every APPT density, not a sufficient replacement definition:

    0<=kappa<=2/(m-1), y_1<=A(3-eta_m(kappa)),
    0<=y_i<=3, y_1<=3D/(D+2), y_2<5/2.                 (S10)

The first line is the peak/middle coupling L6-L7 of
LINEAR_ORDER_VARIATIONAL.md. The uniform second-eigenvalue bound is the
actual convex-orbit averaging and three-Schmidt test N2-N4 in
appt-nonqubit-log-band-20261014/PAPER.md; m>=3 is essential there.
The positive pivot and trace-one normalization retain their prior physical
proofs. All are ordinary credited inputs; no old Lean roots are rerun.

Since alpha/m stays in a fixed positive compact interval and 3^alpha/D
is bounded, every fixed polynomial in m divided by D tends to zero. The
trace identity and the m^2-2 exceptional slots give

    |mu-1|<=2(m^2-2)/N, alpha log mu->0.                (S11)

Every exceptional eigenvalue other than y_1 contributes in total at most

    m^2(5/2)^alpha/D
       <=(3^alpha/D)m^2(5/6)^alpha ->0.                (S12)

Both bounds hold uniformly over actual states in this parameter window.

## 4. An exact nonnegative-loss decomposition

For each middle index set u_i=z_i/L when L>0; if L=0 set u_i=0. Its
mean is theta when L>0. The convex chord loss is

    C=D^-1 sum_(Bset) A^alpha
          [1+u_i((1+kappa)^alpha-1)-(1+kappa*u_i)^alpha] >=0.

At kappa=0 the loss is zero. Using the EXACT middle mean cancels the
linear chord terms. Separating y_1 from the other exceptional slots gives
the exact identity

    M(rho)= (N/D)A^alpha[1+theta((1+kappa)^alpha-1)]
            +A^alpha(3-eta_m(kappa))^alpha/D-C-P+T_exc, (S13)

where T_exc is the nonnegative actual moment on exceptional indices other
than 1 and tends to zero by S12. No trace term or replaced baseline slot
is dropped before estimating this equality.

Write c_m=alpha/m and r_m=3^alpha/D. Uniformly over the permitted actual
parameters, the first two terms in S13 equal

    F(c_m,r_m;L,theta)+o(1).                            (S14)

Here is the endpoint check, rather than an assumption of a uniform Taylor
expansion at l=2. Along any convergent subsequence L->l,theta->h,
S11 gives A^alpha->exp(-clh), and (1+kappa)^alpha->exp(cl). If l<2,

    alpha*eta_m(kappa)->2cl^2/(2-l),
    alpha log(1-eta_m(kappa)/3)->-g_c(l).

If l=2, m*eta_m(kappa)->infinity and hence the peak term is at most
r_m*A^alpha exp(-alpha*eta_m(kappa)/3)->0. These are precisely the
continuous conventions in S5. Compactness of L,theta and of c_m,r_m
proves uniform o(1) by contradiction. Thus

    M(rho)=F(c_m,r_m;L,theta)-C-P+o(1).                (S15)

The actual optimum converges to F_*(c,r)>1 by the existing linear-order
theorem. Its gap from M(rho) is the sum of the nonnegative scalar gap,
C and P, up to o(1). Therefore it vanishes if and only if all three
nonnegative losses vanish. Because both optimal logarithms stay bounded
above and bounded away from zero, this is also equivalent to S2.
Continuity and compactness identify vanishing scalar gap with the first
condition of S6, including every tie.

## 5. Replacing the chord loss by explicit spectral spread

The second derivative in u of (1+kappa*u)^alpha is

    alpha(alpha-1)kappa^2(1+kappa*u)^(alpha-2).

For the present compact positive c-range and every u in [0,1], it lies
between constant positive multiples of L^2, uniformly for large m. Also
A^alpha is bounded above and bounded away from zero by S11. The elementary
second-derivative chord comparison therefore bounds C between constant
positive multiples of

    (N/D) N^-1 sum_i L^2*u_i(1-u_i)=(N/D)J.

This proves C->0 iff J->0, including L->0, and completes S6.
If L->l>0, J->0 puts all middle empirical mass at the two endpoints;
the exact mean fixes their weights at 1-h,h. If l=0, all scaled middle
entries already collapse to zero. S11 and A=mu/(1+kappa theta) give

    m(A-1)->-lh, m A kappa->l.

The m^2-2 exceptional atoms have total first-moment contribution at most
2m(m^2-2)/D->0 by y_i in [0,3]. These facts prove S7 in 1-Wasserstein.

## 6. Pure-bulk converse, peak height, and genuine attainment

For r=0, at every interior h the bulk objective strictly increases with
the width l>0. This follows by differentiating in K=cl: the derivative is
h(1-h)exp(-Kh)(exp(K)-1)>0. The endpoints h=0,1 give value 1, smaller
than F_*(c,0). Thus l=2 is forced, and the existing exact h formula gives
the unique h_c above. Also 0<=P<=r_m*A^alpha->0.

This proves necessity of S8. Conversely, all actual middle values
m(y_i-1) lie in one fixed compact interval by S3/S11. Weak empirical
convergence to S8 consequently determines the middle exponential moment
at order alpha/m->c, by a bounded continuous extension from that interval.
Indeed (1+z/m)^alpha->exp(cz) uniformly for bounded z in this range.
The head contribution is at most r_m->0 and all other exceptional moments
vanish by S12. The limiting moment is exactly F_*(c,0), proving S2.
This justifies the pure empirical converse without an unbounded-test error.

For r>0,l<2, the target peak term in S14 has a strictly positive limit.
Thus P->0 is equivalent to alpha log[A(3-eta_m(kappa))/y_1]->0. Expand
only in this interior-width case, using S11, to obtain S9. In particular
y_1->3. The credited physical tail inequalities in the sharp cutoff proof
give, with u=3D/(D+2),delta=u-y_1 and tail mean mu_tail,

    y_i>=mu_tail-2delta (i>=2), (y_2-mu_tail)^2<=6delta.

Since delta->0 and mu_tail->1, all remaining y_i tend uniformly to one.
At l=2 the upper peak target vanishes, proving only the stated moment
conclusion, not the invalid interior expansion.

Every maximizing (l,h) is genuinely attained: use the previously proved
integer-rank projection/spike construction with kappa=l/(m-1) for l>0,
and kappa=1/m^2 for l=0. Choose the integer rank nearest hD, clipped to
[m^3,D-m^3]; this interval exists eventually because D is exponential.
Then both bulk levels occur within the actual middle set, and the ACTUAL
parameters converge to (l,h), including h=0 or 1. At l=2 the spike
coefficient is zero. At l=0 the vanishing positive width realizes every
redundant limiting h, whereas the exact pole itself has the theta=0
convention. Their exact normalization and all-global-unitary APPT
sufficiency were proved by the existing Schmidt SOS. Their moment limits
are F(c,r;l,h). This proves the attainability claim and allows sequences
alternating among tied maximizers.

## 7. Why a bulk empirical law does not imply a unique outlier pattern

Take alpha/m->c and D growing so that 3^alpha/D->0. The projection-only
endpoint with upper fraction h_c is near-optimal and has y_1->1. But take
instead L=2-m^(-1/2), kappa=L/(m-1), and the same rank fraction in the
actual protected-spike family. Then eta_m(kappa)->0, its bulk law is still
S8, and y_1->3. It is also near-optimal by the proved criterion.

Thus the bulk empirical conclusion is compatible with very different
extreme eigenvalues in this window. General operator flatness, a single
finite exact optimizer, or an eigenbasis cannot be inferred from S8.
The surviving-peak statement S9 has the explicit additional r>0,l<2
hypotheses. This is one sharp-window spectral classification, not a claim
that every-aspect rigidity at all orders is now complete.

All existing value theorems and physical witnesses remain credited.
The separate complete independent ordinary read has passed. No new Lean, enlarged old audit,
external human peer review, priority certificate, absolute separability
of the projection competitors, submission, email, Release or DOI. No
external funding; OpenAI AI assistants assisted. Original rights reserved;
third-party notices and the original author/question attributions remain.
