# Centered Poisson-binomial comparison: parent proof, internal

Let X_p and X_q be sums of L independent Bernoulli variables with parameters
p_i,q_i in [0,1]. Pad the shorter vector with zero parameters when necessary.
Let mu_p,mu_q be their means and D=sum_i |p_i-q_i|. Interpolate coordinates
one at a time. Suppose every law of the other L-1 summands appearing in this
interpolation has variance >=W>0.

Define the centered characteristic function psi_p(t)=E exp(it(X_p-mu_p)).
For one parameter r, its factor is g_r(t)=exp(-irt)(1-r+r exp(it)).
Direct differentiation and Taylor's integral remainder give, for real t,
 |partial_r g_r(t)|
 = |exp(it)-1-it(1-r+r exp(it))|
 <= |exp(it)-1-it| + r |t| |exp(it)-1|
 <= (3/2)t^2.
Every other Bernoulli product has absolute value at most
 exp(-2W sin^2(t/2)) <= exp(-2W t^2/pi^2), |t|<=pi.
Telescoping the coordinate changes therefore gives
 |psi_p(t)-psi_q(t)| <= (3/2)D t^2 exp(-2W t^2/pi^2).
Consequently the real centered Fourier inversion profiles
 f_p(y)=(1/(2pi)) integral_(-pi)^pi psi_p(t) exp(-iyt) dt
satisfy, for every real y,
 |f_p(y)-f_q(y)| <= [3*pi^(5/2)/(16*sqrt(2))] D/W^(3/2)
 < (5/2)D/W^(3/2).
The integral profile is a true point probability only when y+mu_p is an
integer; it is not asserted to be a probability density at other arguments.
The displayed estimate remains a valid analytic intermediate comparison at
all real y.

Important remaining interface: the target comparison evaluates at two
*different* centered arguments, y=0 for the d-law and y=mu_d-k-mu_n for the
n-law. Thus the estimate alone does not solve the problem. A second-order
shift estimate about the mean (including the first-derivative skewness term)
and a lower bound for the integer-mean mode are still required. Uniform
useful constants for W in the specific primitive arrays and the large-s tail
also remain to be established. No real-rootedness assertion follows yet.

## A second-order shift bound, proved directly

Write V=sum r_i(1-r_i), and psi for the centered characteristic function.
For one factor g_r,
 |Im g_r(t)| <= r(1-r)|t|^3/6,
by expanding the two sine terms and cancelling their linear terms. Telescoping
product minus its complex conjugate shows
 |Im psi(t)| <= (V/6)|t|^3 exp(-2(V-1/4)sin^2(t/2)).
The other factors retain variance at least V-1/4. Thus, when V>1/4,
 |f'(0)| <= pi^(9/2)/(16*2^(5/2)) * V/(V-1/4)^(5/2).
For all V>0, differentiating the finite Fourier integral twice gives
 sup_y |f''(y)| <= pi^(5/2)/(4*2^(3/2)) V^(-3/2).
In particular, for V>=1, the first constant including (1-1/(4V))^(-5/2)
is <4 and half the second constant is <1. Hence
 |f(delta)-f(0)| <= (4|delta|+delta^2)/V^(3/2).
These statements concern the real inversion profile; conjugate symmetry makes
it real, so ordinary Taylor's theorem applies for any real delta.

Combining with the centered array comparison and the integer-mean mode lower
bound (via Darroch and Chebyshev), if mu_p=m is an integer, V_q>=1, and
j=m-k is an integer, delta=j-mu_q, then

 |Pr(X_q=j)/Pr(X_p=m)-1|
 <= 7 sqrt(V_p+1) [ (5/2)D/W^(3/2)
                    +(4|delta|+delta^2)/V_q^(3/2) ].

This is a genuine relative centered comparison with explicit assumptions.
It replaces a first-order uncentered shift loss by a centered second-moment
loss. It still requires sharp enough array-specific variance and D estimates,
small-variance treatment, and the large-s marked-series tail. The numerical
constants above have not yet been optimized to close the conjecture's gap.

## Primitive-array parameter distance and centering

For n=d-s, pad the n-array by s zeros. For q<n, p_(n,q)>=p_(d,q).
The means mu_n are increasing in n: when replacing n by n+1,
q/n <= (q+1)/(n+1) for 1<=q<=n-1, so shifting the indices embeds all
old summands below new ones, leaving an additional positive summand.
Consequently the total parameter distance is
 D=mu_n-mu_d+2 sum_(q=n)^(d-1) p_(d,q) <=2sp,
where p=x/(1+x). This is sharper than the source's 3sx bound for large x.

Write e_n=n nu-mu_n, so 0<=e_n<=p. At mu_d=m,
 delta=m-k-mu_n=s nu-k-e_d+e_n,
and hence |delta|<=|k-s nu|+p and delta^2<=2(k-s nu)^2+2p^2.
The centered compound-Poisson moment proved in CENTERED_MAJORANT_LEMMA.md
therefore applies to precisely the required shift, up to a bounded endpoint
correction. The interpolation-variance and large-component bounds are still
unclosed; these observations alone do not establish the target theorem.

## Improvements for the all-variance regime

1. The interpolation condition need not use the source's crude variance
bound. Change coordinates with nonnegative variance increment first, then
those with negative increment. Every intermediate endpoint has total variance
at least min(V_p,V_q). The law of the other coordinates in each step therefore
has variance at least W=min(V_p,V_q)-1/4. This yields the earlier estimate
whenever W>0, irrespective of the parameter ordering of the primitive arrays.

2. Truncating neither Gaussian nor discrete Fourier integrals unnecessarily:
with W>=0, define
 C2(W)=(1/(2pi)) integral_(-pi)^pi t^2 exp(-2W sin^2(t/2)) dt.
The centered comparison is at most (3/2)D C2(W).
For W>0, C2(W)<=min(pi^2/3,
 pi^(5/2)/(4*2^(3/2)*W^(3/2))). Also C2(0)=pi^2/3.
For a single variance V>=0, the shift estimate is
 |f(delta)-f(0)|<=A1(V)|delta|+(1/2)C2(V)delta^2,
where A1(V)<=V*pi^4/30 for all V, and for V>1/4 it is also bounded
by pi^(9/2)/(16*2^(5/2))*V/(V-1/4)^(5/2).
The first universal bound follows by |Im psi(t)|<=V|t|^3/6 with the other
characteristic factors simply bounded by 1. Thus small variance does not
force an artificial blow-up. If min(V_p,V_q)<=1/4, use W=0 instead of the
variance-order improvement.

3. Every integer-valued distribution of finite variance V and largest atom M
satisfies M>=1/sqrt(12V+1). To see this, add independent uniform U on
[-1/2,1/2]. The resulting density is bounded by M and has variance V+1/12.
Among mass-one densities bounded by M, the uniform density M on the interval
of length 1/M centered at the mean minimizes the second moment. Explicitly,
subtract this density and integrate against (t-mean)^2-(1/(2M))^2; both
inside and outside contributions are nonnegative. Its moment is 1/(12M^2).
This proves the assertion. Darroch identifies M with the integer-mean PB
probability. Therefore sqrt(12V_p+1) can replace the earlier
7sqrt(V_p+1) in all relative bounds.

All these are proved auxiliary bounds, not claims of novelty or a full
solution. Next task: combine their sharp x-dependent versions with the marked
identity; rigorously bound the correction mass and tails without losing the
small factors that these bounds were designed to retain.
