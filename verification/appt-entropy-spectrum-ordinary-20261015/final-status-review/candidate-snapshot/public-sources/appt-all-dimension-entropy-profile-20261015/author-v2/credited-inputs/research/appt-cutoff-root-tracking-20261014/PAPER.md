# Quantitative tracking of the actual APPT cutoff and inverse-log expansions

Yongxian Zhang, South China University of Technology.
14 October2026. Ordinary written mathematics; same APPT research direction.

## 1. Statements on actual states

Fix an integer ell>=3. Throughout set

    q=(ell+1)/(ell-1), t=q-1, a=log(3/q), kappa=1/a,
    R=ell(ell-1)/2, K=ell(ell+1)/2, H=R-1,
    L=logD, b=log(e t kappa), X=kappa(L-logL-b).

Actual dimensions satisfy ell<=m<=n and D=mn. The pole spectrum is
(3,1,...,1)/(D+2), already proved ASEP in the disclosed ordinary input.
For alpha>1 maximizing the normalized moment minimizes Renyi entropy:

    M(rho)=D^(alpha-1)Tr(rho^alpha),
    P_D(alpha)=(D/(D+2))^alpha (3^alpha+D-1)/D,
    F_q(alpha)=max_(0<=theta<=1)
                       [1+theta(q^alpha-1)]/(1+t theta)^alpha.

Define explicit fixed positive constants

    h=t^2/256, W=1+t/4, J=3-2h, eta=t^2/16,
    v=1+sqrt(4eta-eta^2)<q,
    nu=kappa logq=kappa log3-1,
    beta=(1/4)min{1,nu,kappa log[3/(3-eta)],
                  kappa log[1/(1-h/3)],kappa log(3/v)-1}>0.       (T1)

Here W<q and J/W>3/q: after multiplication, the latter reduces to
(9/4)t-t^2(1+t)/128>0, since0<t<=1. These constants are sufficient;
neither their rates nor the dimension threshold are asserted optimal.

**Theorem T.** For all sufficiently large D, the exact scalar equation
F_q(alpha)=P_D(alpha) has a unique solution z_D above X-1, and no further
solution at any higher real order. Uniformly over all actual m>=ell,n,
the pole is the unique APPT spectral maximizer at every real

    alpha>=z_D+D^(-beta).                              (T2)

It also uniquely minimizes ASEP Renyi entropy there. On actual ell-by-n,
an integer-rank APPT projection state beats the pole at
alpha=z_D-D^(-beta). Its ASEP status is not claimed.

The elementary equation

    a w+log(t w)-(w-1)log(1-1/w)=logD, w>1             (T3)

has a unique root w_D whenever D>3t/q. For fixed m>=3, set ell=m and
define the actual eventual cutoff

    A_(m,n)=inf{c>1: at every real alpha>c,
                     the pole is the only APPT optimal spectrum}.

Then as n tends to infinity,

    A_(m,n)=z_D+O_m(D^(-beta))
           =w_D+O_m(D^(-beta)).                        (T4)

This definition assumes no monotonicity at earlier orders. A state's
unitary orbit is understood when saying unique spectrum.

**Theorem E.** Put U=logL+b. At each fixed m>=3,

    A_(m,n)=kappa(L-logL-b)+(kappa U+1/2)/L
       +[(kappa/2)U^2+(1/2-kappa)U+1/(6kappa)-1/2]/L^2
       +O_m((logL)^3/L^3).                            (T5)

More generally every fixed finite inverse-L order has a recursively
determined polynomial correction and its next-order remainder. No
convergence, uniform truncation-order or growing-m assertion is made.
If V is the positive Lambert function, V(x)exp(V(x))=x, then

    A_(m,n)-kappa V(D/(e t kappa))
                          =1/(2logD)+O_m(loglogD/(logD)^2).     (T6)

**Theorem M.** Fix actual m>=3, C>kappa and S>0. Uniformly for every real

    kappa(logD-loglogD)-S<=alpha<=C logD+1,

the maximum over the complete actual APPT set satisfies

    max M(rho)=max{P_D(alpha),F_q(alpha)}[1+O_(m,C,S)(D^(-2beta))]. (T7)

The bulk lower attainment and this envelope are APPT-only. Neither
Theorem M nor the cutoff expansion classifies exact finite transition
optimizers or promotes this refinement to an independent major conjecture.

## 2. Disclosed physical inputs and quantified exhaustion

We use the complete ordinary critical-window proof, its original physical
objects, and the prior sharp-leading all-order theorem. Their source
bytes and actual earlier read ranges are bound separately. In particular,
for every actual APPT spectrum, let B=lambda_(D-K+1)>0, z_i=lambda_i/B,
y_i=D lambda_i, u=3D/(D+2), delta=u-y_1>=0. The earlier proof gives

    z_1<=3, z_R<=q, DB<=D/(D-K+1),
    (z_1-1)^2+(z_2-1)^2<=4,
    y_i>=mu-2delta (i>=2), mu=(D-y_1)/(D-1).           (T8)

The circle is an actual unit three-Schmidt PPT test with six positive
bottom eigenvalues, using this same B; the rank-ell negative R/positive K
test gives the ordered pivot. They are necessary tests, not a sufficient
scalar APPT characterization. Delta=0 forces exactly the pole spectrum.

Fix C>kappa and S>0 and call the full interval in Theorem M I_D.
All its orders tend to infinity, are O(logD), and eventually exceed2.
For0<delta<=h, the disclosed common-pivot circle and tail stability give
all y_i<=W for i>=2 and y_1>=J at sufficiently large D. With our explicit
h, W=1+4sqrt(h) and J/W>3/q. The exact earlier Taylor estimate is

    sum y_i^alpha-[u^alpha+(D-1)(D/(D+2))^alpha]
     <=alpha delta W^(alpha-1)
          [1+(alpha-1)(D-1)-(J/W)^(alpha-1)]<0.         (T9)

Its bracket is negative on the entire I_D and at every higher order:
at the lower endpoint the exponential-to-linear ratio diverges with
positive exponent kappa log(J/W)-1, and its logarithmic derivative is
positive once alpha-1>1/log(J/W). Thus arbitrarily small positive delta
remains strictly controlled; an additive error cannot replace this step.

For delta>=h, divide spectra into z_1<=3-eta and z_1>=3-eta. The exact
physical/chord estimates from the earlier proof are, respectively,

    M<=(D/L0)^(alpha-1)F_q(alpha)
                 +(D/L0)^alpha[H(3-eta)^alpha+K]/D,
                       L0=D-H-K,                     (T10)
    M<=y_1^alpha/D+(D/L1)^(alpha-1)F_v(alpha)
                            +(D/L1)^alpha K/D,
                       L1=D-K-1.                     (T11)

Indeed in the first region all middle ratios lie in[1,q]; in the second,
the circle bounds every tail ratio by v<q. At large D the counts are
positive. We retain the actual peak in T11 rather than a relaxed head.

Uniformly on I_D, finite-count factors equal1+O_(ell,C)(logD/D), and

    P_D=(3^alpha/D)[1+O_(ell,C,S)(logD/D+D/3^alpha)].

Any fixed r in(0,1) has r^alpha=O_(ell,S,r)(D^(kappa logr)L^(-kappa logr))
at the smallest order, and decreases at all larger orders. Also
F_v(alpha)<=const_ell v^alpha/alpha once the interval's minimum is large.
Consequently the error terms in T10, relative to P_D, are bounded by a
constant times logD/D, ((3-eta)/3)^alpha and3^(-alpha). Those in T11 are
bounded by a constant times

    (1-h/3)^alpha, D(v/3)^alpha/alpha, 3^(-alpha).

Here y_1/u=1-delta/u<=1-h/3, since u<=3. Their positive D-decay exponents
include respectively1, kappa log[3/(3-eta)], kappa log3,
kappa log[1/(1-h/3)] and kappa log(3/v)-1. Pole replacement errors add
nu>0. By T1 each exponent is at least4beta; fixed powers of logD are
absorbed by D^(2beta). Thus, uniformly on I_D,

    T10: M<=(1+O(D^(-2beta)))F_q+O(D^(-2beta))P_D,
    T11: M=O(D^(-2beta))P_D.                          (T12)

All constants depend only on ell,C,S. T9/T12 exhaust every physical
spectrum, uniformly in m>=ell, with exact strictness near the pole.

## 3. Exact scalar crossing and actual integer-rank attainment

Writing Q=q^alpha, the earlier exact chord maximizer is

    theta*=(Q-1-alpha t)/[t(alpha-1)(Q-1)] in(0,1),
    F_q=(alpha-1)^(alpha-1)(Q-1)^alpha
                       /[t alpha^alpha(Q-q)^(alpha-1)].          (T13)

The smooth interior optimizer permits differentiation of its value:

    (logF_q)'=theta* Q logq/[1+theta*(Q-1)]-log(1+t theta*)
                    <=logq,
    (logP_D)'=log(D/(D+2))+log3/[1+(D-1)/3^alpha].     (T14)

The first fraction is at most1, since theta*<=1. The displayed (logP_D)'
in T14 increases with alpha and tends uniformly to log3 at I_D's lower
endpoint: D/3^alpha=O(D^(-nu)L^(kappa log3)). Hence at every higher order,
for sufficiently large D,

    (log(F_q/P_D))'<=-a/2<0.                          (T15)

The earlier critical result F_q(X+s)/P_D(X+s)->exp(-as) for each fixed s
brackets a root between X-1 and X+1. Continuity and T15 prove uniqueness
there and throughout the entire higher real axis. Choose S>|kappa b|+3
so these endpoints and their D^(-beta) neighborhoods are inside I_D.

For alpha>=z_D+D^(-beta) in I_D, T15 gives F_q/P_D<=exp(-a D^(-beta)/2).
That strict margin dominates every O(D^(-2beta)) in T12. T9 is already
strict for every delta>0, and T11 is strictly below the pole eventually.
Thus the pole is the only optimizer in this entire band. The prior
sharp-leading theorem, at any fixed C>kappa, supplies every alpha>=C logD+1.
This proves T2 for all higher real orders and all physical m>=ell,n.
ASEP is a subset of APPT, and the credited pole belongs to ASEP.

For actual ell-by-n, take k=floor(D theta*) and
sigma=(I+tQ_k)/(D+tk), with any rank-k projection Q_k. The disclosed
all-unitary negative Schmidt trace is at most(ell-1)/2=1/t, proving APPT
for this actual state. Its moment is precisely the scalar chord value
at theta=k/D. Uniformly on I_D, theta*~1/(t alpha); hence theta>=theta*/2
and1<=k<D once D is large. For
f(theta)=log[1+(Q-1)theta]-alpha log(1+t theta), we have f'(theta*)=0
and, on the interval from theta to theta*,

    |f''(theta)|<=1/theta^2+alpha t^2=O_ell(alpha^2).

Taylor's theorem and |theta-theta*|<=1/D prove the genuine lower bound

    M(sigma)>=F_q exp[-O_ell(alpha^2/D^2)].             (T16)

At alpha=z_D-D^(-beta), T15 makes F_q/P_D>=exp(a D^(-beta)/2).
Since alpha^2/D^2=o(D^(-beta)), T16 strictly beats the pole. An earlier
candidate eventual cutoff cannot exclude that higher-order witness, so
z_D-D^(-beta)<=A_(ell,n)<=z_D+D^(-beta). This uses no early-order
monotonicity. For fixed m, set ell=m to obtain the first part of T4.
Finally T9/T12 and the two actual attaining families T16 and the pole
give T7, since alpha^2/D^2=O(D^(-2beta)).

## 4. The elementary root and controlled implicit inversion

Let G_D(w) be the left side of T3 minus logD. Direct differentiation gives

    G_D'(w)=a-log(1-1/w)>a for all w>1.                (T17)

Its limit at1 is a+logt-logD, negative when D>3t/q, while its limit at
infinity is positive infinity. This proves the claimed unique root.
The exact chord expression T13 and the exact pole give

    log(F_q/P_D)=-G_D(alpha)+E_D(alpha),
    E_D=alpha log(1-q^(-alpha))
       -(alpha-1)log(1-q^(1-alpha))
       -alpha log(D/(D+2))-log[1+(D-1)/3^alpha].        (T18)

On I_D its absolute value is bounded by a constant times
alpha q^(-alpha)+alpha/D+D/3^alpha. Their exponents are nu,1,nu,
up to fixed logarithmic factors, so E_D=O(D^(-2beta)) uniformly.
At alpha=z_D, T18 yields |G_D(z_D)|=O(D^(-2beta)). The global derivative
bound T17 and the mean value theorem imply

    |z_D-w_D|=O(D^(-2beta)),                          (T19)

which proves the second part of T4. No sampled crossing is used.

For w>1 the elementary convergent series, obtained by multiplying the
series of log(1-1/w), is

    (w-1)log(1-1/w)=-1+sum_(j>=1)1/[j(j+1)w^j].

Thus with u=a w_D and b=log(e t kappa), its exact equation is

    u+logu=L-b+sum_(j>=1)a^j/[j(j+1)u^j].             (T20)

In particular u=L-logL-b+O(logL/L), by substitution followed by T17.
For any fixed N, insert u_N=L-U+sum_(j=1)^N d_j(U)/L^j into T20.
The coefficient of L^(-j) contains d_j with coefficient1; every other
term is determined by earlier d_i. Set it to zero successively. Taylor's
remainder for log(1+(u_N-L)/L) and the geometric tail in T20 are bounded
by O_ell,N((logL)^(N+1)/L^(N+1)); u_N>=L/2 eventually. The resulting
exact residual has that bound. The derivative of T20's left-minus-right
is G_D'(kappa u)/a>1, so its root differs from u_N by the same bound.
This proves every fixed finite-order polynomial expansion with a valid
remainder. The recursion gives degree at most j and begins

    d_1=U+a/2,
    d_2=U^2/2+(a/2-1)U+a^2/6-a/2.

Multiplying by kappa yields T5; T4's power error is smaller than every
fixed inverse-log remainder. For T6, the positive Lambert root solves
u+logu=L-b with the series on T20's right deleted. Its first difference
from the actual elementary root is a/(2L)+O(logL/L^2), by T20 and the
derivative tending to1. Multiplication by kappa gives1/(2L); T4 again
absorbs the exponentially smaller-in-L error. This completes the proof.

## 5. Attribution and verification boundary

The preceding critical-window packet supplies T8-T11 and the initial
crossing bracket; the sharp-leading packet supplies the all-higher-order
splice and the actual projection criterion; the disclosed finite product
decomposition supplies the credited ASEP pole. Known inscribed-polytope
and projection families are attributed to the primary literature rather
than counted as new objects. No historical priority certification is made.
This packet requires its own complete new ordinary source-bound read.
Finite symbolic/decimal diagnostics are supporting calculations only;
Windows, optimized Windows and WSL share one implementation. All prior
Lean sources, builds, audit roots and read scopes remain unchanged.
