# A uniform full positive-order entropy envelope on actual fixed-local APPT sets

Yongxian Zhang (张永贤), School of Computer Science and Engineering,
South China University of Technology; mxymmxym1@gmail.com;
ORCID0009-0000-3864-3536. No external funding. OpenAI AI assistants assisted.
All rights reserved for original material.14 October2026.
Natural logarithms; ordinary written mathematics.
Same APPT research direction, not a new independent major-conjecture claim.

## 1. Complete statements and known model families

Fix an integer m>=3, let every integer n>=m grow, and put D=mn. Write

    q=(m+1)/(m-1), t=q-1, kappa=1/log(3/q),
    R=m(m-1)/2, K=m(m+1)/2, H=R-1,
    h=t^2/256, eta=t^2/16, W=1+t/4,
    v=1+sqrt(4eta-eta^2)<q, epsilon=1/(2log3),
    chi=(1/2)min{1/2,epsilon log(q/W),
           epsilon log[3/(3-eta)],epsilon log[1/(1-h/3)],
           epsilon log(q/v)}>0.                       (U1)

Let E_(m,n)(alpha)=logD-min_(actual APPT_(m,n))S_alpha, where
S_alpha=log(Tr rho^alpha)/(1-alpha) for alpha>0, alpha!=1,
S_1=-Tr rho logrho, S_0=log rankrho, and S_infinity=-log lambda_max.
The pole (3,1,...,1)/(D+2) is a credited actual ASEP/APPT spectrum.
Let p_D(alpha) be its entropy deficit, with the usual continuous limits:

    p_D(alpha)=log{(D/(D+2))^alpha(3^alpha+D-1)/D}/(alpha-1),
    p_D(0)=0,
    p_D(1)=log(D/(D+2))+(3/(D+2))log3,
    p_D(infinity)=log[3D/(D+2)].                      (U2)

For theta in[0,1], s=1+t theta, define the bulk-family deficit

    g(alpha,theta)={log[1+theta(q^alpha-1)]-alpha logs}/(alpha-1),
    g(1,theta)=theta q logq/s-logs,
    g(0,theta)=0,
    B_m(alpha)=max_(0<=theta<=1)g(alpha,theta) (finite alpha),
    B_m(infinity)=logq.                              (U3)

For every finite alpha>0 the unique maximizing theta is

    theta_alpha=[q^alpha-1-alpha t]/[t(alpha-1)(q^alpha-1)] (alpha!=1),
    theta_1=(q logq-t)/t^2.                          (U4)

At alpha<1 the corresponding moment is minimized; at alpha>1 it is
maximized. U3 is expressed with positive quantities throughout, avoiding
noninteger powers of negative alpha-1. The continuous model at infinity
is a limit, not a claim that a zero-rank finite state has a high eigenvalue.
The projection families and the von Neumann scalar optimization are known
inputs: compare Ahiable–Kothakonda–Winter, Theorem6.10. Our statements below
are error bounds on the complete actual APPT set.

**Theorem U.** There are constants c_m,D0(m) such that, for every actual
n>=m, D>=D0, uniformly over the entire extended axis0<=alpha<=infinity,

    |E_(m,n)(alpha)-max{B_m(alpha),p_D(alpha)}|
                                      <=c_m D^(-chi). (U5)

The single bound covers every order depending on n, including orders
approaching0, approaching or crossing1, diverging at any rate, or equal
to infinity. The rate chi is sufficient, not optimal; no explicit finite
dimension threshold or exact finite transition optimizer is asserted.

**Theorem B.** For each fixed A<infinity there is c_(m,A) such that

    sup_(0<=alpha<=A)|E_(m,n)(alpha)-B_m(alpha)|
                                          <=c_(m,A)/D (U6)

for all sufficiently large n. In particular, with z=q logq/t,

    min_(actual APPT) S_1=logD-[z-1-logz]+O_m(1/D).     (U7)

The scalar constant z-1-logz comes from the credited bulk optimization;
U7 adds a complete physical-set asymptotic error bound.

**Endpoints.** At every actual m>=3,n>=m,

    min S_0=log(D-1), equality iff rho=(I-P)/(D-1), rankP=1,
    min S_infinity=log(D+2)-log3,
                equality iff rho=(I+2P)/(D+2), rankP=1.          (U8)

These known endpoint spectra are included for full domain coverage, not
new independent result credit. The bulk lower attainment is APPT-only;
no ASEP entropy envelope or lower threshold is inferred. We keep m fixed:
no joint growing-m uniformity or full finite-dimensional entropy conjecture
resolution is claimed.

## 2. Actual spectral inputs and a normalization comparison

For every actual sorted APPT spectrum lambda, the previously completely
read ordinary critical-window proof gives the common pivot
b=lambda_(D-K+1)>0. Set z_i=lambda_i/b and s=D^(-1)sum z_i. Then

    z_i in[1,3] for i<=H,
    z_i in[1,q] for R<=i<=D-K,
    z_i in[0,1] for i>D-K,
    D lambda_i=z_i/s.                                (U9)

Its maximal-m-Schmidt negative/positive arrangement and an independent
unit three-Schmidt PPT test also give

    (z_1-1)^2+(z_2-1)^2<=4,
    y_1<=u=3D/(D+2), y_i=D lambda_i,
    delta=u-y_1>=0,
    delta=0 iff lambda is precisely the pole spectrum.          (U10)

These are necessary conditions on actual states, never a sufficient scalar
APPT characterization. At all sufficiently large D, delta<=h implies
every tail y_i<=W; and z_1>=3-eta implies every tail ratio z_i<=v<q.
Those conclusions retain their disclosed physical proofs and read scopes.

Put L0=D-H-K. For large D it is positive. The middle mean is
s0=L0^(-1)sum_(R<=i<=D-K)z_i=1+t theta for some theta in[0,1].
Since all exceptional ratios are bounded and their number is fixed,

    |s-s0|<=c_m/D, s0 in[1,q], s>=L0/D>=3/4,
    |logs-logs0|<=c'_m/D,
    0<=z_i/s<=4, 0<=z_i/s0<=3                        (U11)

at sufficiently large D. This retains all heads and bottom eigenvalues,
including possible zeros, rather than discarding their trace contribution.

## 3. A bounded-order bound uniform through0 and1

For alpha>0 define, with phi_alpha(0)=0,

    phi_alpha(x)=(x^alpha-x)/(alpha-1), alpha!=1,
    phi_1(x)=x logx,
    phi_alpha''(x)=alpha x^(alpha-2)>=0 (x>0).          (U12)

For each fixed A>=2, uniformly over0<alpha<=A and0<=x<=4,
both |phi_alpha(x)| and |x phi_alpha'(x)| are bounded by a constant C_A,
where the latter expression is extended as0 at x=0. To check the endpoint
alpha approaching0, split0<alpha<=1/2: |alpha-1|>=1/2 and x^alpha is
bounded by max(1,4^(1/2)), so the two explicit numerators are bounded.
For1/2<=alpha<=A, use the removable divided-difference identity

    phi_alpha(x)=integral_(0<=r<=1) x^(1+r(alpha-1))logx dr,
    x phi_alpha'(x)=integral x^j(j logx+1) dr,
                       j=1+r(alpha-1)>=1/2.          (U13)

Both integrands are uniformly bounded also as x tends to0, and are valid
at alpha=1. We need no uniform bound on phi_alpha' itself near x=0.

Let T_alpha=D^(-1)sum_i phi_alpha(y_i), y_i=z_i/s. Multiplicative
normalization replacement s->s0 changes each term by at most C_A|logs-logs0|:
its derivative with respect to the logarithmic normalization is
-x phi_alpha'(x). At a zero coordinate both values are exactly0. Finite
exceptional counts and L0/D=1-O_m(1/D), together with U11-U13, imply

    T_alpha=(1/L0)sum_middle phi_alpha(z_i/s0)+O_(m,A)(1/D)
      <=(1-theta)phi_alpha(1/s0)+theta phi_alpha(q/s0)
                                         +O_(m,A)(1/D).       (U14)

The inequality is the convex chord on[1/s0,q/s0], valid on both sides of1.
The first two terms on the right are the bulk family's normalized defect.

Every normalized coordinate list considered here has mean1 and lies in[0,4].
For0<alpha<=1 its moment mean is at least4^(alpha-1)>=1/4; foralpha>=1
it is at least1 by Jensen. Since

    M_alpha=1+(alpha-1)T_alpha,
    E_alpha(rho)=Psi_alpha(T_alpha),
    Psi_alpha(T)=log[1+(alpha-1)T]/(alpha-1), Psi_1(T)=T,
    Psi_alpha'(T)=1/[1+(alpha-1)T]>0,                 (U15)

the map is increasing and has derivative at most4 on the segment joining
the actual and bulk defects: their endpoint moments are at least1/4,
and the moment is affine in T. Thus U14 proves

    E_alpha(rho)<=B_m(alpha)+O_(m,A)(1/D), 0<alpha<=A, (U16)

uniformly over the complete actual state set. No unscaled O(1/D) moment
error has been divided by an arbitrarily small alpha-1.

## 4. Scalar optimization and actual bounded-order attainment

For alpha!=1 the theta derivative of the numerator logarithm in U3 is

    [Q-1-alpha t-t(alpha-1)(Q-1)theta]
        /{[1+(Q-1)theta](1+t theta)}, Q=q^alpha.        (U17)

Strict Jensen gives an interior positive deficit and zero endpoint values.
Foralpha>1 the derivative numerator decreases and for0<alpha<1 it
increases; in each case there is exactly one interior optimum, U4.
Atalpha=1 the derivative of g is
(q logq-t-t^2 theta)/(1+t theta)^2. The inequalities
t/q<logq<t show0<theta_1<1, proving its uniqueness and
B_m(1)=z-1-logz. The family g extends jointly with a bounded theta derivative
on[0,A]x[0,1]: atalpha=1 apply the divided difference of its analytic
numerator, and atalpha=0 the numerator is0 and its denominator is-1.
All logarithm arguments remain strictly positive on this compact set.

For every theta, k=floor(D theta), and any actual rank-k projection P,

    sigma_k=(I+tP)/(D+tk)                              (U18)

is APPT in actual m-by-n. Indeed the total negative trace of every unit
m-Schmidt pure-state partial transpose is at most(m-1)/2=1/t; pairing it
with any projection gives Tr[(I+tP)Gamma]>=1-t/t=0. This is the disclosed
all-unitary projection criterion, independent of rank. Its exact entropy
deficit is g(alpha,k/D). Choosing theta=theta_alpha and using the uniform
theta derivative bound yields

    E_(m,n)(alpha)>=B_m(alpha)-O_(m,A)(1/D), 0<alpha<=A. (U19)

Together with U16 this proves U6 at every positive bounded order, including
orders approaching0 or1 with any rate. Section7 supplies alpha=0 itself.

## 5. Uniform moment envelope from2 to C logD+1

Fix C=kappa+1. Foralpha>1 let

    F_q(alpha)=max_theta [1+theta(q^alpha-1)]/(1+t theta)^alpha,
    P_D(alpha)=(D/(D+2))^alpha(3^alpha+D-1)/D,
    M*=max_(actual APPT) D^(alpha-1)Tr rho^alpha.

We prove uniformly for2<=alpha<=C logD+1 that

    M*/max{F_q(alpha),P_D(alpha)}=1+O_m(D^(-chi)).      (U20)

The actual pole attains P_D. For allalpha>=2, theta_alpha is comparable
to1/alpha with positive constants depending only on m: it is continuous
and positive on finite compact intervals, and alpha theta_alpha->1/t.
Thus for allalpha<=C logD+1 and large D, the rounded theta=k/D is at least
theta_alpha/2 and1<=k<D. The second derivative of
f(theta)=log[1+(q^alpha-1)theta]-alpha log(1+t theta) has absolute value
at most1/theta^2+alpha t^2=O_m(alpha^2) on the rounding segment.
With f'(theta_alpha)=0 this proves the uniform actual lower bound

    M(sigma_k)>=F_q exp[-O_m(alpha^2/D^2)].            (U21)

The coefficient is uniform down toalpha=2, not only along alpha tending
to infinity. Together with the pole it supplies the lower side of U20.

For2<=alpha<=epsilon logD, the complete physical pivot/chord bound gives

    M(rho)<=(D/L0)^(alpha-1)F_q
                         +(D/L0)^alpha(H3^alpha+K)/D.

Here F_q>=1, finite-count normalization is1+O_m(alpha/D), and
3^alpha/D<=D^(-1/2) by the chosen epsilon. This proves the upper bound
with relative error O_m(D^(-1/2)) throughout that first continuous band.

For epsilon logD<=alpha<=C logD+1, exhaust all actual spectra as follows.
Ifdelta<=h, U10 gives every tail y_i<=W and y_1<=u. By trace,

    M(rho)<=u^alpha/D+W^(alpha-1)<=P_D+W^(alpha-1).

The exact scalar optimizer has F_q~q^alpha/(et alpha) uniformly as the
minimum order tends to infinity. Thus the error divided by F_q is
O_m(alpha(W/q)^alpha), uniformly on this whole interval.

Ifdelta>=h and z_1<=3-eta, the physical chord bound is

    M(rho)<=(D/L0)^(alpha-1)F_q
                     +(D/L0)^alpha[H(3-eta)^alpha+K]/D.

Relative to P_D>=u^alpha/D the exceptional head term is bounded by a
constant times((3-eta)/3)^alpha; its finite normalization correction is
1+O_m(alpha/D). The bottom term divided by max(F_q,P_D)>=F_q>=1 is O_m(1/D).

Finally, ifdelta>=h and z_1>=3-eta, every tail ratio is at most v<q. The
disclosed second physical chord estimate, L1=D-K-1, is

    M(rho)<=y_1^alpha/D+(D/L1)^(alpha-1)F_v+(D/L1)^alpha K/D.

The actual peak divided by P_D is at most(1-h/3)^alpha. The scalar bulk
ratio F_v/F_q is bounded by const_m(v/q)^alpha, by the same exact scalar
asymptotic; the finite normalization correction is again1+O_m(alpha/D).
The bottom term is O_m(1/D) relative to max(F_q,P_D). These three regions
cover every physical spectrum, including delta=0 and all small deficits.

Each exponential gap has order D to the minus epsilon times its gap
logarithm at the interval's lower endpoint. The only extra factors are
fixed constants or powers of logD. By U1 all the exponents, including1/2
from the first band, are at least2chi; logarithmic factors are absorbed
by D^chi. All upper estimates therefore imply U20, uniformly on its full
continuous interval. U21's rounding error is smaller still.
Taking logarithms and dividing byalpha-1>=1 proves U5 for these orders.

## 6. Every higher order and joining the bounded region

At everyalpha>=C logD+1, the previously read sharp-leading theorem proves
M*=P_D, with the exact unique APPT/ASEP pole spectrum. The composite model
also equals the pole there at large D: F_q/P_D tends to0 at C logD+1,
since C>kappa and F_q/P_D~D(q/3)^alpha/(et alpha). Moreover

    (logF_q)'<=logq,
    (logP_D)'=log(D/(D+2))+log3/[1+(D-1)/3^alpha].      (U22)

The first bound follows by differentiating the interior optimum: its
logarithmic numerator derivative is theta_alpha q^alpha logq divided by
1+theta_alpha(q^alpha-1), at most logq; subtracting log(1+t theta_alpha)
can only decrease it. The second displayed quantity increases with alpha and tends to log3 at
C logD+1, because C log3>1. Thus the ratio decreases at every higher real
order, proving F_q<P_D throughout that half-axis. This gives U5 exactly
in the final region. The infinity endpoint is checked in Section7.

For0<alpha<=2, U6 bounds E by B_m with error O_m(1/D). The pole deficit
p_D(alpha) is itself O(1/D) uniformly there: use U12-U15, its single
bounded peak and D-1 normalized tails D/(D+2)=1+O(1/D), whose defects
are O(1/D) uniformly in the bounded-order range. Since B_m>=0,
0<=max(B_m,p_D)-B_m<=p_D. Therefore U5 holds on this entire remaining
region as well. This proof joins the regions without an order-rate gap.

## 7. Exact endpoint coverage

For every actual APPT spectrum, use an arbitrary unit two-Schmidt pure
vector with nonnegative coefficients x,y. Place lambda_1 on its negative
pair, lambda_(D-1) on its positive pair, and lambda_D,lambda_(D-2) on
the two positive diagonal directions. The actual PPT expectation yields

    lambda_D x^2+lambda_(D-2)y^2
                         -(lambda_1-lambda_(D-1))xy>=0.        (U23)

If lambda_D=0, choosing y positive and arbitrarily small forces
lambda_1<=lambda_(D-1). Sorting and trace imply that all first D-1
eigenvalues equal1/(D-1), so no APPT state has rank below D-1.
The missing-one-projector state (I-P)/(D-1) is actually APPT: after every
global unitary P is pure, and its partial-transpose eigenvalues are the
Schmidt squares and the signed pair products, all at most1. Hence
I-P^Gamma is positive. This proves the alpha=0 statement
and all equality spectra in U8. It gives E_(m,n)(0)=log[D/(D-1)]=O(1/D),
while B_m(0)=p_D(0)=0, completing both U5 and U6 at zero.

At infinity, U10's exact peak cap and equality rigidity give U8. Since
q<=2<3D/(D+2) for D>=9, max(B_m(infinity),p_D(infinity)) is exactly
the actual pole deficit. Thus U5 also holds at infinity. This completes
the full-axis and bounded-order theorems, including U7.

## 8. Attribution and verification scope

The known rank-deficient, pole and projection spectra, and the scalar
von Neumann optimization are explicitly credited to the primary literature.
The critical-window ordinary packet supplies actual pivot/circle/chord
inputs; the sharp-leading packet supplies actual projection attainment
and the final all-higher-order pole theorem. Their source bytes and earlier
actual manuscript read ranges are disclosed, not silently enlarged.
The present full physical-set normalization/continuum/endpoint proof needs
its own complete new source-bound ordinary read. Finite checks support
calculations only. No new Lean execution, formal roots, original-paper
audit certification, external human review, submission, priority claim
or independent major-conjecture count is inferred.
