# Rectangular APPT bulk rigidity and the optimal fourth-root stability law

Author: Yongxian Zhang (张永贤), South China University of Technology.
ORCID 0009-0000-3864-3536; mxymmxym1@gmail.com. 15 October 2026.
Author ordinary manuscript, pending a distinct independent ordinary review.
No external funding. OpenAI AI assistants assisted research and writing.
Copyright 2026 Yongxian Zhang; original material all rights reserved,
third-party attribution retained. No new Lean scope, historical-first claim,
submission, release or completed major-problem count is asserted.

## 1. The original state set and the new joint range

Fix ANY finite A>0. Let m->infinity, integers n>=m, gamma=n/m, D=mn,
and allow arbitrary real orders satisfying

    0<alpha<=A,                 alpha gamma->infinity.          (1.1)

All oscillations in alpha and n are permitted. In particular gamma->infinity;
alpha may stay in any positive compact interval, cross 1/2, 1 or 2, or tend
to zero with alpha gamma->infinity. There is no assumption on alpha log m.

The state rho is EVERY original complex PSD trace-one density on
C^m tensor C^n which remains PPT after EVERY global unitary conjugation.
Write its decreasing actual eigenvalues lambda_i and y_i=D lambda_i. Put

    Q=sum_i(y_i-1)^2, q=Q/gamma,
    nu=D^-1 sum_i delta_(m(y_i-1)),
    beta=(delta_-1+delta_1)/2,
    e_alpha(rho)=log D-S_alpha(rho),
    E_alpha=max_actual_APPT e_alpha,
    d_alpha(rho)=1-e_alpha(rho)/E_alpha>=0,
    epsilon=1/m+1/(alpha gamma).                              (1.2)

S_1 is the continuous von Neumann entropy. All powers at a zero eigenvalue
have their ordinary positive-order values. The compact actual APPT state set
and continuity give the maximum. E_alpha>0, for instance by the actual
nonuniform two-level states constructed below. W_2 is the quadratic
Wasserstein metric on probability measures on the real line; its second
moment is retained, not inferred from bare weak convergence.

The established U/Z and fixed-order entropy theorems already determine the
leading VALUE in this regime. Their bounded-aspect spectral classifications
do not give the statement below, and Z2 explicitly treats finite alpha gamma
and finite alpha log m. The leading value is credited, not claimed as a
separate new problem resolution. A quantitative value comparison is proved
here because it is required to bind the sharp stability error at joint scales.
Pending S5/S6 and the phase-4 scalar geometry are not dependencies.

## 2. Uniform actual-state profile and complete spectral criterion

**Theorem A (uniform physical-state profile).** There are constants depending
only on A such that, once m is sufficiently large and epsilon sufficiently
small, for EVERY allowed n, alpha and actual APPT density,

    | e_alpha(rho)/[alpha/(2m^2)]-q | <=C_A epsilon,
    | E_alpha/[alpha/(2m^2)]-1 | <=C_A epsilon,
    | e_alpha(rho)/E_alpha-q | <=C_A epsilon.                  (2.1)

The constants and common thresholds are independent of the state, n and
alpha in (1.1). Thus for every sequence in that domain the following are
equivalent:

    e_alpha(rho)/E_alpha->1;
    Q/gamma->1;
    W_2(nu,beta)->0.                                         (2.2)

The actual physical body-width/mean/spread criterion in Section 5 is also
equivalent. In the positive compact-order subcase this criterion is the same
across both order transitions 1/2 and 2, and at the von Neumann point. Indeed
for every fixed 0<a<=A, uniformly over ALL actual states,

    sup_(alpha in [a,A])|e_alpha/E_alpha-Q/gamma|->0
       as m->infinity, gamma->infinity.                      (2.3)

Consequently nearoptimality at any one sequence of orders in [a,A] implies
simultaneous nearoptimality at EVERY order in that whole interval.

**Theorem B (quantitative fourth-root stability).** With the same uniform
quantifiers after adjusting constants and thresholds,

    W_2(nu,beta)<=C_A [d_alpha(rho)+epsilon]^(1/4).           (2.4)

The exponent 1/4 is optimal: for every fixed nonempty positive compact
interval I=[a,A], there is an explicitly defined sequence of ACTUAL APPT
two-level densities with actual integer projection ranks such that, uniformly
over alpha in I,

    d_alpha=(4+o(1))/l^2,
    W_2(nu,beta)^2=(4+o(1))/l,
    epsilon=O_I(l^-4).                                     (2.5)

Thus no bound of the same form with exponent p>1/4 and a constant uniform
in the state/dimensions can hold, even at any single fixed positive order.
This is an actual quantum-state sharpness example, not an unattained
two-atom relaxation.

Every relatively entropy-optimal sequence in (1.1) is eventually full rank.
It need not have uniform flatness max_i|y_i-1|->0: a physical peak tending
to three is compatible with (2.2). The whole actual rescaled empirical law
is the relevant quantity here; exceptional heights have negligible quadratic
mass when gamma diverges. This conclusion is not an extension of a
fixed-finite-aspect outlier classification without its aspect hypotheses.

## 3. Credited physical spectrum and power kernels down to alpha=0

Use the exact physical notation of G7-G15 in the captured complete
research/appt-growing-renyi/PAPER.md. For m>=3 set

    R=m(m-1)/2, K=m(m+1)/2, j=D-K+1,
    B={R,...,j}, N=|B|=D-m^2+2, E={1,...,D}\B,
    b=lambda_j>0, t=1/(Db).

The actual all-unitary witnesses, trace and rearrangement proofs give

    |t-1|<=nu_m=1/m+2/(m-1),
    0<=y_i<=3,
    |y_i-1|<=delta_m=O(1/m) for i in B,
    Q_E=sum_(i in E)(y_i-1)^2<=C_m=O(1),
    Q<=zeta_m(gamma+8), zeta_m=1+O(1/m),
    y_R/y_j-1<=2/(m-1).                                   (3.1)

All implicit constants here are universal, after one common m threshold,
independent of n and the state. The exact formulas for delta_m, C_m and
zeta_m are retained in G11-G14. In particular |E|=m^2-2 does not replace
the much stronger bounded exceptional square sum Q_E. These are necessary
physical consequences for every actual state, not a proposed sufficient
description of the APPT feasible set.

For alpha>0 define on -1<=x<=2

    f_alpha(x)=[(1+x)^alpha-1-alpha x]/[alpha(alpha-1)]
       if alpha!=1,
    f_1(x)=(1+x)log(1+x)-x.

The continuous value at x=-1 is retained. Its exact integral form is

    f_alpha(x)=x^2 integral_0^1(1-s)(1+sx)^(alpha-2) ds.      (3.2)

At x=-1 the integrand behaves as (1-s)^(alpha-1), which is integrable
for EVERY positive alpha, and f_alpha(-1)=1/alpha. This endpoint cannot
be bounded by a constant independent of alpha when alpha->0.

For 0<alpha<=A, (3.2) implies uniformly

    0<=f_alpha(x)<=K_A x^2/alpha,     -1<=x<=2.             (3.3)

For -1<=x<=0 and alpha<=2 use 1+sx>=1-s, giving integral at most 1/alpha;
for alpha>=2 the integral is at most 1/2. For 0<=x<=2 it is at most
3^max(A-2,0)/2. Since alpha<=A these establish (3.3), with no lower
bound on alpha. On |x|<=delta_m<1/2, bases stay away from zero and
alpha-2 lies in the bounded interval [-2,A-2], so

    f_alpha(x)=x^2/2+O_A(delta_m x^2)                       (3.4)

uniformly even through alpha=1 and as alpha->0. A direct mean-value bound
on (1+sx)^(alpha-2) gives this estimate.

Put F_alpha=sum_i f_alpha(y_i-1). From (3.3)-(3.4), (3.1) and Q_B=Q-Q_E,

    F_alpha=Q/2+O_A(Q_B/m+Q_E/alpha),
    2F_alpha/gamma=q+O_A(1/m+1/(alpha gamma)).               (3.5)

In the second line one may absorb 1/gamma into A/(alpha gamma), because
alpha<=A. The estimates use gamma>=1 and Q<=zeta_m(gamma+8). They show
precisely why the condition alpha gamma->infinity is needed when orders
approach zero; without it a bounded exceptional square mass is not negligible.

## 4. Exact trace normalization, the entropy profile and actual attainment

Let M_alpha=D^-1 sum_i y_i^alpha. For alpha!=1 trace one gives the exact
identity

    M_alpha=1+alpha(alpha-1)F_alpha/D,
    e_alpha=(alpha-1)^-1 log M_alpha.                        (4.1)

There is no logarithm of a truncated or unnormalized spectrum. By (3.3),
(3.4) and the physical bounds,

    |alpha(alpha-1)F_alpha/D|<=K_A( alpha gamma+1)/D
                                 <=K'_A/m^2.               (4.2)

Thus log(1+z)=z[1+O(|z|)] yields

    e_alpha=alpha F_alpha/D [1+O_A(m^-2)]                   (4.3)

uniformly for alpha!=1. No pole at alpha=1 is introduced: the factor
alpha-1 cancels before estimating the remainder, and at alpha=1
D e_1=F_1 exactly. Formula (4.3) also applies when F_alpha=0, with both
sides zero. Combining it with (3.5) and gamma/D=1/m^2 proves the first
line of (2.1). The terms arising from the relative error in (4.3) are
absorbed into O_A(epsilon) when epsilon is small.

For completeness construct an actual lower family, with the finite integer
rank retained. Put c=2/(m-1), k=floor(D/2), theta=k/D, and let P be any
rank-k complex orthogonal projection. Define

    rho_P=(I+cP)/(D+ck).                                   (4.4)

This is PSD, full rank and trace one. To prove APPT under EVERY global U,
test against any pure partially transposed Schmidt witness W. If its unit
Schmidt coefficients are s_1,...,s_m>=0, its negative eigenvalues are
-s_i s_j. Since 0<=UPU*<=I,

    Tr[(UPU*)W]>=-sum_(i<j)s_i s_j>=-(m-1)/2.

The last bound follows from (sum_i s_i)^2<=m and sum_i s_i^2=1.
As Tr W=1, Tr[(I+cUPU*)W]>=1-c(m-1)/2=0. This proves actual all-unitary
APPT, not merely a positive eigenvalue list or sampled-unitary test.

Its actual normalized eigenvalues are (1+c)/(1+c theta), k times, and
1/(1+c theta), D-k times. Exact normalization gives

    Q/gamma=m^2 c^2 theta(1-theta)/(1+c theta)^2
            =1+O(1/m),                                    (4.5)

uniformly n>=m; theta=1/2+O(1/D) and D>=m^2. Applying the first profile
bound to this actual state yields E_alpha/[alpha/(2m^2)]>=1-O_A(epsilon).
The physical upper Q/gamma<=1+O(1/m+1/gamma) and that same profile yield
the reverse bound. In fact the lower family is Taylor-flat, so its lower
error is O_A(1/m), though the stated epsilon estimate suffices.

This proves the second line of (2.1). Its denominator stays bounded away
from zero once epsilon is small, and the first two lines prove the third.
The established leading value is not counted as new; the explicit error
rate here is needed for (2.4)-(2.5). Equivalence of the first two conditions
in (2.2) and the uniform positive-compact assertion (2.3) follow immediately.

## 5. Actual body parameters and quadratic transport

Define from the ACTUAL middle spectrum

    A_0=y_j=1/t>0, kappa=y_R/A_0-1 in [0,2/(m-1)],
    L=(m-1)kappa in [0,2],
    mu=N^-1 sum_(i in B)y_i,
    theta=(mu/A_0-1)/kappa if kappa>0, else theta=0,
    z_i=(m-1)(y_i/A_0-1) in [0,L],
    J=N^-1 sum_(i in B)z_i(L-z_i)>=0.                      (5.1)

When kappa=0 all z_i are zero and J=0. Exact trace centering and Cauchy give

    N(mu-1)=-sum_(i in E)(y_i-1),
    m|mu-1|<=m sqrt{|E|Q_E}/N=O(1/gamma),                  (5.2)

in the eventual gamma->infinity range. In particular a mean error has not
been dropped merely because the unscaled mu tends to one.

The exact middle second moment decomposition is

    Q_B/gamma=(N/D)(m/(m-1))^2 A_0^2
                   [L^2 theta(1-theta)-J]
               +(m^2 N/D)(mu-1)^2.                       (5.3)

Indeed the exact z variance is L^2 theta(1-theta)-J; trace-centering at 1
adds the displayed nonnegative mean term. Put

    v=L^2 theta(1-theta)-J in [0,1], delta=1-v>=0.

From (5.2), A_0=1+O(1/m), N/D=1+O(1/gamma) and Q_E=O(1), one obtains

    |q-v|<=K(1/m+1/gamma),
    delta<=d_alpha+K_A epsilon.                            (5.4)

The second bound uses (2.1) and 1/gamma<=A/(alpha gamma).
All constants are uniform over the original state set. Since

    delta=1-L^2/4+L^2(theta-1/2)^2+J,                      (5.5)

q->1 is equivalent to L->2, theta->1/2 and J->0. Thus width and mean
without the actual spread J do not suffice. This algebraic body observation
is supplied self-contained here; no pending S5 theorem is assumed.

To prove quadratic transport, set w=m A_0/(m-1)=1+O(1/m) and
xi=m(mu-1)=O(1/gamma). The ACTUAL middle rescaled point equals

    X_i=m(y_i-1)=xi+w(z_i-L theta).                         (5.6)

For L>0 round z in [0,L] to Z=L with probability z/L and to zero
otherwise. This has endpoint weights theta,1-theta and exact conditional
quadratic cost

    E[(z-Z)^2|z]=z(L-z).

Hence the squared W_2 cost to the middle endpoint law, after (5.6), is at
most w^2 J. If delta<=1/4, (5.5) gives L>=1,
2-L<=2delta, |theta-1/2|<=sqrt(delta), and J<=delta. The two transformed
endpoint locations differ from -1 and +1 by at most
K[sqrt(delta)+1/m+1/gamma]. Moving their weights to exactly one half has
quadratic cost 4|theta-1/2|. The W_2 triangle inequality therefore gives

    W_2(nu_B,beta)^2<=K[sqrt(delta)+(1/m+1/gamma)^2],       (5.7)

where nu_B is the normalized actual middle law. If delta>1/4, its second
moment is uniformly bounded by (5.2)-(5.3), so increasing K makes the
same bound valid as well; no division by a collapsing L is needed there.

Finally the exceptional part has mass |E|/D=O(1/gamma) AND quadratic
mass in the actual X scale

    D^-1 sum_(i in E)m^2(y_i-1)^2=Q_E/gamma=O(1/gamma).

Replace that part by an equal mass of beta, coupling it with squared cost
at most 2Q_E/gamma+2|E|/D. Mixing the middle coupling with this replacement
and using the triangle inequality gives

    W_2(nu,beta)^2<=K[sqrt(delta)+1/m+1/gamma].             (5.8)

Squaring (5.8), applying (5.4), and absorbing 1/gamma into A/(alpha gamma)
prove (2.4). In particular q->1 implies W_2(nu,beta)->0. Conversely for
any coupling, the L^2 triangle inequality gives

    |sqrt(integral X^2 dnu)-sqrt(integral X^2 dbeta)|<=W_2(nu,beta).

But integral X^2 dnu=Q/gamma and integral X^2 dbeta=1. Therefore W_2->0
implies q->1, completing all equivalences in (2.2). This proof accounts for
exceptional second moments explicitly instead of upgrading weak convergence.

## 6. Sharpness with exact ranks and actual APPT sufficiency

Let l run through even integers tending to infinity, l>=4, and choose

    m=l^4, n=m^2, gamma=m, D=m^3=l^12,
    theta=1/2+1/l, k=D/2+D/l,
    c=2/(m-1), rho_l=(I+cP_k)/(D+ck).                       (6.1)

k is an INTEGER strictly between zero and D; P_k is an actual rank-k
orthogonal projection. The all-global-unitary Schmidt proof of Section 4
applies unchanged for every such rank, proving actual APPT. Define

    s=m c/(1+c theta)=2m/(m+2/l).

The ACTUAL full empirical law is exactly

    nu=(1-theta)delta_(-s theta)+theta delta_(s(1-theta)),
    q=s^2 theta(1-theta)
      =(1-4/l^2)(1+2/(lm))^-2
      =1-4/l^2+O(l^-5).                                   (6.2)

For theta>=1/2 the monotone optimal coupling to beta sends the entire
lower mass 1-theta to -1, mass theta-1/2 from the upper atom to -1, and
the remaining one half to +1. Its exact quadratic cost is

    W_2(nu,beta)^2
     =(1-theta)(1-s theta)^2
       +(theta-1/2)[1+s(1-theta)]^2
       +(1/2)[s(1-theta)-1]^2
     =1+q-2s(1-theta)
     =4/l-4/l^2+O(l^-5).                                  (6.3)

The coupling is optimal by the one-dimensional increasing-quantile rule;
alternatively exchanging a crossing pair lowers squared cost, so the
displayed unique ordered allocation minimizes cost. This does not depend
on any assumption about an arbitrary spectral relaxation being physically
attainable: the actual density and integer ranks have already been supplied.

For each fixed I=[a,A] with a>0, epsilon=O_I(l^-4). By the UNIFORM actual
state and maximum estimates (2.1), (6.2) gives, uniformly alpha in I,

    d_alpha=1-q+O_I(l^-4)=4/l^2+O_I(l^-4).                 (6.4)

Thus the finite-value joint-scale error is strictly smaller than the
stability gap; an unquantified value equivalent would not justify (6.4).
Equations (6.3)-(6.4) prove (2.5) and

    W_2(nu,beta)/[d_alpha+epsilon]^p
          =(2/4^p+o(1))l^(2p-1/2)->infinity

for every p>1/4. They establish the claimed optimal stability exponent
within the actual original APPT domain, including the finite normalization.

## 7. Rank, outliers and scope limits

For an actual singular APPT state in m>=3 the least eigenvalue is zero.
The credited shifted star G8 then forces a_1=0 and beta_2=0 in its pivot
notation: its right side is 4(1-beta_1)=0. Hence lambda_1=lambda_(D-1)=b,
and sorting makes every first D-1 eigenvalue b=1/(D-1). Thus the only
singular APPT spectrum is uniform of rank D-1, as already established in
the endpoint papers. Its deficit at EVERY positive order is log[D/(D-1)].
Relative to alpha/(2m^2) it is O(1/(alpha gamma))->0 in (1.1). Therefore
nearoptimality cannot have infinitely many singular terms. This proves
the eventual full-rank assertion without replacing a tiny positive least
eigenvalue by an exact zero.

The condition alpha gamma->infinity cannot simply be omitted while keeping
the bulk profile. For example take m=k,n=k^2,alpha=k^-2 and the actual APPT
state (I-vv*)/(D-1). It has q=m^2/(D-1)~1/k, whereas
e_alpha=log[D/(D-1)]>=1/D and therefore
e_alpha/[alpha/(2m^2)]>=2k->infinity. Its every-unitary APPT property follows
from the fact that a partially transposed pure projector has largest
eigenvalue at most one. This is a physical outside-domain counterexample,
not a proposed extension of (2.1) into the finite zero-order window.

The credited actual protected projection/spike construction G24-G30, with
H->infinity and H/m->0, has y_1->3 and Q/gamma->1 whenever gamma->infinity.
For example choose H=ceil(sqrt(m)) and n=m^2. Its every-unitary SOS proof
and actual integer projection ranks are in G; it is not a new construction
claimed here. Equivalence (2.2) makes it entropy-optimal for every fixed
positive compact order band, although max_i|y_i-1| does not tend to zero.
This rejects copying the fixed-finite-aspect flatness criterion into the
present range. A bounded exceptional physical height need not be excluded;
its rescaled quadratic mass is negligible precisely because gamma grows.

No claim is made for alpha gamma bounded as alpha->0, alpha unbounded,
fixed m, eigenvector rigidity, exact finite extrema, or a complete all-order/
all-aspect synthesis. The existing finite two-parameter zero-order theorem
and the pending higher-order scopes retain their separate hypotheses and
review status. This is one additional ordinary theorem scope in the APPT
research direction, not a separate major-problem count. All source bytes,
actual read coverage, finite controls and failed-tool diagnostics are bound
in the accompanying manifests. No old Lean audit is enlarged or relabeled.
