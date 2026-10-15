# A total-dimension two-scale reduction of actual APPT spectra at diverging order

Yongxian Zhang (张永贤), South China University of Technology.
15 October 2026. No external funding. OpenAI AI assistants assisted.
Original material all rights reserved; third-party notices retained.
Complete author manuscript; independent current-source review
pending. No Lean, external human peer review, priority or new major count.

## 1. Original objects and the two new uniform extensions

For integers 2<=m<=n, D=mn, let rho range over actual complex positive
semidefinite trace-one matrices on C^m tensor C^n that remain PPT after
EVERY global unitary. Write their ordered eigenvalues as lambda_i and
y_i=D lambda_i. For a finite real alpha>=2 put

    M_alpha(rho)=D^-1 sum_i y_i^alpha,
    M*_alpha(m,n)=max_actual_APPT M_alpha,
    e_alpha=log D-S_alpha(rho)=log M_alpha/(alpha-1),
    E_alpha=max_APPT e_alpha=log M*_alpha/(alpha-1).

The objectives are the sharp moment-EXCESS ratio (M-1)/(M*-1) and the
relative first-nonzero entropy deficit e/E=log M/log M*. They cannot be
replaced by a raw moment ratio or entropy divided by log D. All logarithms
are natural. The actual spike state below makes M*>1 at every alpha>1.

The earlier growing-m V theorem already gives the value profile. The
new author S9 manuscript gives a physical peak/body reduction when m
and alpha both tend to infinity. Its exceptional-energy method and
three-log-regime proof are credited, and the full needed argument is
included here. No independent S9 decision is assumed. Here we extend the
physical reduction uniformly to ALL dimension pairs, including fixed D,
and calibrate its sharp moment benchmark at fixed m as well. The final
explicit necessary-and-sufficient tests have one joint total-D/order
threshold and include fixed, growing and alternating smaller dimensions.

## 2. Actual finite body data, with the qubit peak counted once

Set

    R=m(m-1)/2, S=m(m+1)/2, j=D-S+1,
    r0=max{2,R}, B={r0,...,j}, E={1,...,D}\B.

For m>=3, |B|=D-m^2+2>=2. For m=2, |B|=D-3>=1. Thus B is never
empty, and it never contains index 1. Using R=1 without this qubit
adjustment would count the actual peak twice.

The pivot A=y_j is positive. For m>=3 this follows from the mature
maximally entangled witness G9. For m=2, if y_j=0 then all three least
eigenvalues vanish, and the necessary rank-two uniform witness forces
lambda_1<=lambda_D+lambda_(D-1)+lambda_(D-2)=0, a contradiction.

Define, with N=|B|,

    Aplus=y_r0, kappa=Aplus/A-1>=0, mu=N^-1 sum_B y_i,
    theta=(mu/A-1)/kappa when kappa>0, theta=0 otherwise.

If kappa>0, put x_i=(y_i-A)/(A kappa), Z_k=(1+kappa)^alpha-1 and

    h_(alpha,kappa)(x)=[(1+kappa x)^alpha-1]/(x Z_k), x>0,
    h_(alpha,kappa)(0)=alpha kappa/Z_k,
    Lambda=1-sum_B[x_i h_(alpha,kappa)(x_i)]/sum_B x_i.

The actual endpoints are present, so sum_B x_i>0 at positive width.
Convexity gives 0<=h<=1 and 0<=Lambda<=1. At kappa=0 define Lambda=1.
The exact chord identity, already used in FAST and S9, is

    sum_B y_i^alpha
      =N A^alpha[1+theta Z_k(1-Lambda)],
    A=mu/(1+kappa theta).                              (1)

There is no fictitious real rank, endpoint-body premise or discarded
normalization. Lambda is a retained actual spectral functional.

For alpha>=2 define the nonnegative centered kernel

    H_alpha(y)=y^alpha-1-alpha(y-1), y>=0,
    Z(rho)=[H_alpha(y_1)+sum_B H_alpha(y_i)]/D,
    K(rho)=1+Z(rho)>=1.                                (2)

Using (1), this is the following finite expression in the actual peak
and four body quantities mu,kappa,theta,Lambda:

    K=1+D^-1{y_1^alpha-1-alpha(y_1-1)
       +N[(mu/(1+kappa theta))^alpha
             (1+theta Z_k(1-Lambda))-1-alpha(mu-1)]}.   (3)

At zero width the body bracket need not vanish: mu need not be one.
The two centered linear terms remain at arbitrary alpha/D.

## 3. A uniform physical gap for every omitted nonleading coordinate

Put u_D=3D/(D+2). The mature necessary rank-two witness gives

    y_1<=u_D,
    lambda_1<=lambda_D+lambda_(D-1)+lambda_(D-2)
        <=3(1-lambda_1)/(D-1).                         (4)

In particular 0<=y_i<=3, y_1>=1, and u_D>=2 since D>=4.

**Lemma 1.** There exist universal constants Q0<infinity and
15/16<=rho0<1 such that, for EVERY dimension pair and actual APPT state,

    sum_(i in E)(y_i-1)^2<=Q0,
    y_i<=rho0 u_D for every i in E with i!=1.           (5)

No numerical effective value of these constants is claimed here.

**Proof.** For m>=M0, with one fixed sufficiently large M0, mature
G12-G13 give the common bounded exceptional square mass and y_2<=5/2.
Also u_D>=8/3 there. This proves (5) in that range with gap ratio15/16.
These G estimates are uniform in every n>=m, and use actual physical
witnesses, not a surrogate feasible set.

For 3<=m<M0, |E|=m^2-2 and 0<=y_i<=3 give square mass at most4M0^2.
Retain the actual pivot b=lambda_j and the old G7 quantities g_i and
a_i=lambda_i/b-1. The finite star gives g_1^2+g_2^2<=4 and g_1>=g_2,
so a_2<=g_2<=sqrt(2). Furthermore b<=1/j, since the first j eigenvalues
are at least b. Hence

    y_2<= (1+sqrt(2))D/[D-S+1].                         (6)

For all sufficiently large D, simultaneously over this finite m list,
(6) is at most5/2. Taking D also large enough for u_D>=8/3 proves (5)
in these dimension pairs.

Only finitely many m>=3 pairs remain. At each one the original APPT set
is compact: it is a closed subset of the compact finite-dimensional
density set. Ordered eigenvalues are continuous. Its maximum y_2 is
strictly below u_D. Otherwise y_2=u_D would force y_1=u_D. Equality
in the last inequality of (4), since D>=9 and D-1>3, makes all D-1
tail eigenvalues equal to y_1/3. This contradicts y_2=y_1. The maximum
of their finitely many strict ratios is below one.

For m=2, the omitted nonleading indices are exactly D-1,D, irrespective
of how large the second actual eigenvalue is. Their values are at most
D/(D-1), by trace and ordering. The ratio to u_D is at most
(D+2)/[3(D-1)]<=2/3. The three exceptional squared deviations are
bounded by12. Combining these bounds with the finite maximum and15/16
proves (5). In particular no false uniform SECOND-peak gap is assumed
for qubits; that peak is retained in their actual body. QED.

## 4. Universal moment and logarithmic reductions, without a D limit

**Theorem 2.** There are universal constants C, alpha0 such that every
integer 2<=m<=n, every real alpha>=alpha0 and every actual APPT density
satisfy

    0<=(M-K)/(M*-1)<=C alpha^2 rho0^alpha,              (7)
    0<=(log M-log K)/log M*
       <=C[alpha^2 rho0^(alpha/2)+log(1+alpha)/alpha].   (8)

These reductions require only diverging order. Dimensions may remain
fixed; there is no alpha/m, alpha/D or aspect condition.

**Proof.** The exact trace identity is D(M-1)=sum_i H_alpha(y_i).
Since index1 occurs once and is outside B, it gives exactly

    M=K+R_E/D,
    R_E=sum_(i in E,i!=1)H_alpha(y_i)>=0.               (9)

The real-power integral formula, valid including y=0, is

    H_alpha(y)=alpha(alpha-1)(y-1)^2
                integral_0^1(1-s)(1+s(y-1))^(alpha-2)ds.

For 0<=y<=V and V>=1 it implies
H_alpha(y)<=alpha(alpha-1)(y-1)^2 V^(alpha-2)/2.
Lemma1, with rho0 u_D>1, consequently gives

    R_E<=C alpha^2 rho0^alpha u_D^alpha.               (10)

The physical spike (I+2ww*)/(D+2) is APPT after every global unitary,
since every transposed pure projector has least eigenvalue at least-1/2.
Its exact moment and Bernoulli's inequality give

    D(M*-1)>=u_D^alpha-1-2alpha.

As u_D>=2 uniformly, a common alpha threshold makes the right side at
least u_D^alpha/2. With r=u_D^alpha/D, chi=log r this proves

    M*-1>=r/2, log M*>=log(1+r/2).                     (11)

Equations (9)-(11) prove (7), even when M*-1 is arbitrarily tiny.

For logarithms, also use the ACTUAL peak. Set x_1=y_1-1>=0 and
H_1=H_alpha(y_1). The integral shows H_alpha(1+x)/x^2 is nondecreasing
for x>=0 and alpha>=2. If x_1>=1/alpha, every positive omitted
deviation contributes at most alpha^2(y_i-1)^2 H_1. Every negative
one contributes at most alpha(alpha-1)(y_i-1)^2/2. If x_1<1/alpha,
all positive kernel multipliers are at most e, giving the same bound.
The case x_1=0 makes the entire density uniform. Thus

    R_E<=C alpha^2(1+H_1),
    1<=M/K<=1+C alpha^2,                               (12)

because D K>=D+H_1>=1+H_1. The argument is relative to the STATE's
own peak and does not assume nearoptimality.

Let eta=-log rho0>0 and Delta=log M-log K. By (9)-(10) and K>=1,
Delta<=C alpha^2 exp(chi-eta alpha). Also (12) bounds it by
O(log(1+alpha)). If chi<=0, (11) gives log M*>=exp(chi)/3,
which cancels that same small exponential. If 0<chi<=eta alpha/2,
the denominator is at least log(3/2), while the first bound decays.
If chi>eta alpha/2, (11) makes log M*>=eta alpha/4 eventually;
use the polynomial comparison (12) instead. These exhaustive cases
prove (8), with common constants and arbitrary oscillations. QED.

The physical gap extension and the qubit definition are new here. The
centered-kernel and three-chi proof pattern credit the prior S9 author
argument, fully reproduced above rather than assumed independently audited.

## 5. An explicit scalar benchmark at both optimality scales

For m>=3 use the previously calibrated finite V. Put q=(m+1)/(m-1),
t=q-1, R_D=u_D^alpha/D, and

    eta_m(k)=2(m-2)k^2/[2-(m-3)k], 0<=k<=t,
    T_(m,D)(alpha)=max_(0<=k<=t,0<=theta<=1)
       [1+theta((1+k)^alpha-1)
            +R_D((3-eta_m(k))/3)^alpha]/(1+k theta)^alpha. (13)

For m=2,D>=6 define T by the exact compact qubit reduction of the
independently read X manuscript: maximize D^(alpha-1)sum p_i^alpha
over its three explicitly normalized families A(x),B_j(x),C_j(x), with
their stated compact intervals and INTEGER 1<=j<=D-3. This is an
explicit ordinary external Song--Chen extreme-point input, as detailed
in X Section3; it is not an optimization over an unknown APPT feasible
set. The finitely many D=4 cases are outside the following D limit.

**Theorem 3.** Jointly as total dimension D tends to infinity and finite
real order alpha tends to infinity,

    (M*-1)/(T-1)->1, log M*/log T->1,                   (14)

uniformly over ALL integer 2<=m<=n. Equivalently, for each epsilon>0
there exist N,A such that every D>=N,alpha>=A has both relative errors
at most epsilon. Smaller dimensions may be fixed, growing or alternating.

**Proof for growing m.** On alpha/m tending to zero, mature G1 and V18
give M*-1~R_D+alpha(alpha-1)/(2m^2)~T-1. On each alpha>=epsilon m
range, V1 gives M*/T->1; the V17 bulk choice bounds T-1 below by a
fixed positive constant depending on epsilon. Therefore relative raw
moment accuracy also gives relative EXCESS there. A bad sequence has
a further alpha/m subsequence tending to zero or bounded below by a
positive epsilon. These two mature inputs prove the first part of
(14) for growing m without conflating raw moment and tiny excess.
The elementary concavity comparison for log(1+x) then proves the second.

The fixed-m comparison needs a stronger argument than the factor-two
scalar sandwich sufficient for X's relative entropy theorem. It follows
in the next section. Qubits have exact T=M*. Finally any bad joint
D/alpha sequence has a growing-m subsequence or a fixed integer m on
a subsequence. Those cases give the full single joint-tail assertion.

## 6. The fixed-m sharp moment bridge

Fix m>=3 and use F_q(alpha)=max_theta[1+theta(q^alpha-1)]/(1+t theta)^alpha.
Let delta=t/2>0. The normalized two-point moment is nondecreasing in k:
its log derivative is

    alpha theta(1-theta)[(1+k)^(alpha-1)-1]
      /{[1+theta((1+k)^alpha-1)](1+k theta)}>=0.

Both theta endpoints are included. Also eta_m is strictly increasing for
k>0, since its derivative is
2(m-2)k[4-(m-3)k]/[2-(m-3)k]^2>0, and eta_m(t)<2.
For k<=delta, the bulk term of (13) is at most
(1+delta)^alpha, while its peak term is at most R_D. For k>=delta,
the bulk is at most F_q and the peak at most R_D c_m^alpha, where
c_m=(3-eta_m(delta))/3 lies strictly between zero and one. Monotonicity
of eta on its interval follows by direct differentiation. Also choosing
theta=1/alpha gives F_q>=q^alpha/[alpha exp(t)]. Thus

    T/max{F_q,R_D}->1 as alpha->infinity,               (15)

uniformly in D: both possible width regions have at most that maximum
plus an exponentially small multiple of it. The lower bound follows
from k=t and k=0. All actual trace factors and u_D remain in R_D.

The mature fixed-m A theorem gives ONE eventual D0(m) such that at
EVERY order M* is exactly the maximum of

    H=(D/(D-1))^(alpha-1),
    F_int=max_(integer1<=j<=D-1)
           [1+(j/D)(q^alpha-1)]/(1+t j/D)^alpha,
    P=[u_D^alpha+(D-1)(D/(D+2))^alpha]/D.               (16)

This exact theorem is credited, including its single threshold; no
order-dependent thresholds are silently interchanged.

Choose q<u0<3 and a fixed A sufficiently large that
A log(u0/q)>2 and A log3>2. Eventually u_D>=u0.
If alpha>A log D, then F_q/R_D<=D(q/u_D)^alpha<=D^-1.
Since D/(D-1)<=q eventually, the same bound controls H/R_D.
Finally P/R_D=1+(D-1)/3^alpha=1+o(1). Therefore M*/R_D->1 in this
range, and (15) gives M*/T->1.

If alpha<=A log D while alpha tends to infinity, the exact continuous
optimizer satisfies theta*=1/[t(alpha-1)]-alpha/[(alpha-1)(q^alpha-1)]
and hence theta*~1/(t alpha). Its nearest physical rank j/D is interior
eventually. On the joining interval theta>=theta*/2, the log-moment
Hessian has absolute value at most

    1/theta^2+alpha t^2<=C_m alpha^2.

The first derivative vanishes at theta*, so Taylor gives

    0<=log F_q-log F_int<=C_m alpha^2/D^2=o(1),          (17)

uniformly in this logarithmic band. Thus F_int/F_q->1. Meanwhile H->1,
P is between R_D and R_D+1, and F_q tends to infinity. Equations
(16)-(17) give M*/max{F_q,R_D}->1. Together with (15), this is the
fixed-m relative RAW moment comparison uniformly at every diverging
order, not merely a relative entropy statement.

To pass to excess, M* tends to infinity on every fixed-m diverging-order
path uniformly in D. Indeed choose the actual APPT half-rank projection
state (I+tP)/(D+t rank P). Its theta=floor(D/2)/D lies in[1/3,1/2],
and its order-two moment is 1+t^2 theta(1-theta)/(1+t theta)^2>=1+c_m>1.
Scalar log-moment convexity with value zero at order1 implies its
deficit at every alpha>=2 is at least log(1+c_m). Consequently
M*>=exp[(alpha-1)log(1+c_m)] tends to infinity. Raw and excess relative
comparisons therefore agree here. This completes (14).

## 7. Full actual-state tests and a separate infinite-order endpoint

Under joint D->infinity,alpha->infinity, Theorems2-3 give, for EVERY
actual APPT state sequence and arbitrary dimension/order oscillations,

    (M(rho)-1)/(M*-1)->1 iff Z(rho)/(T-1)->1,            (18)
    e_alpha(rho)/E_alpha->1 iff log[1+Z(rho)]/log T->1.   (19)

These are finite-coordinate actual spectral tests. They retain the
body chord loss and actual mean; no presumed endpoint distribution or
instantaneous exact scalar argmax distance replaces them. Approaching
a first-order tie from one side does not force a phase choice when the
value gap vanishes. Geometric classifications in their smaller windows
retain their separate source and review scopes.

At the extended endpoint alpha=infinity, use separately

    e_infinity/E_infinity=log y_1/log u_D,               (20)

exactly, by the actual peak ceiling and attainable spike. No alpha-power
moment or excess is defined by substituting infinity. The entropy test
can include sequences alternating finite diverging orders and the exact
endpoint with this explicit separate definition.

## 8. Attribution and limits

The mature G physical estimates, calibrated growing-m V, fixed-m exact
A theorem, FAST chord identity and explicit external qubit classification
are bound in CREDITED_INPUTS.json. The S9 author's growing-m physical
method is credited and reproduced in Sections3-4; no pending review is
used as a proof premise. The new parts are the uniform all-dimension
omitted-coordinate gap including qubits, the all-dimension two-scale
physical reduction, and the fixed-m sharp-moment/total-D benchmark bridge.

This is an observable reduction, not a complete geometric classification
of all body laws at every order, a general exact finite optimizer formula,
an effective smallest dimension threshold, eigenbasis rigidity or ASEP.
The physical reduction in Theorem2 is uniform even at fixed D; the
explicit benchmark and tests (14),(18),(19) require D and alpha to
diverge. Low and finite positive orders remain separate. No old Lean
root is executed or enlarged. Independent current-source full review and
future public status/index binding remain pending.
