# One nondegenerate mixed state at the last boundary, and the local phase diagram

Author: Yongxian Zhang (张永贤), South China University of Technology.
Contact: mxymmxym1@gmail.com. ORCID: 0009-0000-3864-3536.
Date: 2026-10-15. Complete author argument with an exact integer interval
certificate; independent ordinary review is pending. No Lean claim, submission,
or new-major claim. No funding. OpenAI assisted the investigation and writing.
Original text: all rights reserved; third-party attribution and rights remain.

## Scope and exact inputs

Use the scalar problem and notation of NO_ISLANDS.md. All original matrix
statements concern complex density matrices APPT after every global unitary,
m<=n, m tending to infinity, alpha>1, alpha/m tending to c>0 and
3^alpha/(mn) tending to finite r. The previously established value result L and
nearoptimizer result S supply the actual APPT transfer, with the precise sources
bound in CREDITED_SOURCES.json. No matrix definition or quantifier is weakened.

The scalar dependencies, still author-only pending ordinary independent review,
are the exact frozen versions:

    NO_ISLANDS.md
    SHA-256 f7509ff124d76f12855a55705f317c51133c8e1a93fcadc7f230bebd91b8ad16

    LAST_MIXED_BOUNDARY.md
    SHA-256 6e4f77e2bbecbc5e71f426925d444e8e1a9b69d2ffebcbef88badc1f4e87f0a0

The latter includes a self-contained proof of the c>=1 pure bound. No root
collaborator's unreviewed T or small-c lower-onset draft is a dependency.

The computational inputs to THIS proof are:

    critical_exact_intervals.py
    SHA-256 78ab0341d6079ceedb7be01abc9eba8608d50df0ad2136fa53b554a547c6ce1c

    CRITICAL_EXACT_INTERVAL_CERTIFICATE.json
    SHA-256 f9dd26bc8b4769a22aac06d07ba76587da18ccbc0ec62292856fcf1ae7eee878

The certificate is a whole-domain collection of rigorous enclosures, not a
floating-point grid or a search claiming that no omitted point exists. Its
integer interval arithmetic and analytic tails are justified below. Review must
include this explanation, the source, the final certificate and its complete
coverage. None of the author's controls constitutes independent review.

## Theorem

The unique last mixed parameter c_star of NO_ISLANDS satisfies

    519/2000 < c_star < 13/50,
    equivalently 0.2595 < c_star < 0.26.

At c=c_star,r=r_star=b(2c_star)-1, the complete scalar argmax contains
exactly three phase classes: the pole line L=0, the unique pure bulk point
(2,h_b(c_star)), and exactly one interior point (L_star,h_star).

The interior point has negative definite scalar Hessian for F in its two
coordinates. In particular it is nondegenerate. There is a neighborhood of
(c_star,r_star) and one real analytic interior critical point z(c,r) such that

    V(c,r)=max{b(2c),1+r,M(c,r)},
    M(c,r)=F(c,r,z(c,r)).                         (T.1)

For c<c_star sufficiently near c_star there are two real analytic coexistence
curves r_B(c)<r_0(c)<r_P(c). Locally the unique phase is pure bulk below r_B,
mixed between r_B and r_P, and pole above r_P. The boundary at r_B has exactly
bulk/mixed coexistence and the boundary at r_P exactly mixed/pole coexistence.
At c=c_star the two curves meet in the triple point. For c>c_star the complete
pure argmax statement of NO_ISLANDS applies.

Let x_star=L_star/2, K_star=2c_star and

    p_star=P(c_star,L_star,h_star) in (0,1),
    A_star=partial_K W(K_star,x_star)>0.

Then, as c tends to c_star,

    r_B(c)-r_0(c)=2r_star A_star(c-c_star)+O((c-c_star)^2),
    r_P(c)-r_0(c)=-2p_star r_star A_star/(1-p_star)
                               *(c-c_star)+O((c-c_star)^2).

In particular the strict mixed window closes linearly from below:

    r_P(c)-r_B(c)
      =2r_star A_star/(1-p_star)*(c_star-c)+O((c_star-c)^2).

For every fixed limiting pair (c,r) in this neighborhood, the credited theorem S
therefore has respectively one, two, or three explicit scalar phase classes.
At the triple point there are exactly three possible limiting empirical body
laws for actual APPT nearoptimizers. Their full nearoptimizer conditions still
include vanishing J and actual peak loss. Oscillating sequences need not choose
one of the tied laws.

The theorem does not assert global uniqueness of a mixed state at every
0<c<c_star and every r. That remains a separate open task here.

## 1. Scalar formulas needed by the certificate

For t>0 use

    q=t/(exp(t)-1), d=1-q, w=-log q,
    g=w-d=log b, s=w'=1-d/t,
    g'=s d, g''=s'd+s^2 q.

The proof of NO_ISLANDS establishes that q decreases and s,w,g,g' increase
strictly. For K=2c,k=Kx,x=L/2 in (0,1), put

    Delta=g(K)-g(k)>0,        v=w(k)-g(K),
    a=2Kx^2/[3(1-x)],
    W=a+log Delta-log q(k)-log(exp(g(K))-1).

The admissibility restriction is v>0. At an interior crossing tie the unique
h is h=v/k and W=0. Because this is a global minimum of U at fixed K,
one also has W_x=0. The exact derivatives used by the program are

    a_k=(2/3)[(1-x)^(-2)-1],
    a_kk=4/[3K(1-x)^3],
    W_x=K[a_k+s(k)-g'(k)/Delta],
    W_xx=K^2[a_kk+s'(k)-g''(k)/Delta-g'(k)^2/Delta^2].       (1.1)

No derivative of an approximate numerical maximizer is used.

A useful uniform derivative bound is

    0<s'(t)<=1/12                  for every t>0.           (1.2)

For completeness set z=t/2. Then

    s'=1/(4z^2)-1/(4sinh(z)^2)>0.

The upper bound is equivalent to

    z^2 sinh(z)^2-3sinh(z)^2+3z^2 >= 0.

Using sinh(z)^2=sum_(n>=1) a_n z^(2n),
a_n=2^(2n-1)/(2n)!, the coefficients at z^2 and z^4 vanish. For n>=3 the
coefficient is a_(n-1)-3a_n=a_n[(2n)(2n-1)/4-3]>0. The series converges
for every real z and proves (1.2). The program uses the safe whole-domain
interval [0,1/12] for s' and g''=s'd+s^2q.

## 2. Exact interval arithmetic and elementary functions

The scale is S=2^160. An interval I=(lo,hi) means the closed real interval
[lo/S,hi/S], with arbitrary-precision INTEGER endpoints. Addition and negation
are exact; multiplication divides the extrema of the four integer products
by S with floor for the lower bound and ceiling for the upper bound. Inversion
uses the appropriate endpoints of S^2/u, again rounded outward. All denominators
are asserted to exclude zero. Python integers have no finite-word overflow.

There are no binary floating-point operations in this enclosure calculation.
Initial rational constants are enclosed by integer floor and ceiling. Every
subsequent enclosure operation therefore preserves containment by elementary
interval arithmetic.

For an exact dyadic point 0<=t<=2, exp(t) is enclosed by the first 97 terms,
through degree N=96, of its nonnegative Taylor series. Lagrange's remainder is
at most

    9*2^(N+1)/(N+1)!.

This uses exp(2)<9, which follows from exp(1)<3 and the exponential law;
exp(1)<3 follows directly from n!>=2^(n-1) for n>=2 with strict inequality
in the resulting geometric sum. Each term and the rational tail are rounded
outward. Every exponential input in this certificate is checked to lie in
[0,2]. Monotonicity extends point enclosures to input intervals.

For log(t), t>0 is first written as t=2^n y with 1<=y<=2. Range reduction
uses integer shifts and outward rounding. With z=(y-1)/(y+1) in [0,1/3],

    log y=2 sum_(j=0 to N-1) z^(2j+1)/(2j+1)+R,
    0<=R<=9/[4(2N+1)3^(2N+1)],       N=96.

The upper tail follows by replacing every omitted denominator by 2N+1 and
summing the geometric series in z^2. The same formula encloses log 2. Thus
log t=log y+n log 2 is enclosed with outward operations, also for negative n.
Logarithm monotonicity extends point enclosures to intervals. No library
implementation of exp, log, or trigonometric functions supplies a sign.

To enclose q,s,w,g,g' on a t interval, the program uses their proved
monotonicities and the corresponding endpoint formulas. It then encloses
s' and g'' as explained in (1.2). All formulas (1.1) use ordinary outward
interval operations. Their enclosure correctness follows inductively.

## 3. Analytic exclusion of both x tails

All of this section holds uniformly on

    K in [519/1000,13/25].

The certificate proves four elementary one-dimensional constant bounds:

    r_0(13/25)<1/20,
    g'(9/20)>11/100,
    w((13/25)/10)-g(519/1000)<0,
    log 10<5/2.                                             (3.1)

For 0<x<=1/10, monotonicity gives
v=w(Kx)-g(K)<=w((13/25)/10)-g(519/1000)<0. Thus this entire tail is
inadmissible; its constrained minimum is h=0 and U_min=exp(a)r_0>r_0.

For 9/10<=x<1, set delta=1-x<=1/10. Since K>1/2 and Kx>9/20,
convexity of g and (3.1) imply

    Delta>=g'(Kx)K delta>(11/100)(1/2)delta,
    H=Delta/[q(Kx)r_0(K)]>(11/10)delta>delta.

Also a>27/(100delta), so

    W>27/(100delta)+log delta
      >=27/10-log 10>1/5>0.

For the middle inequality the function 27/(100delta)+log delta is decreasing
on 0<delta<=1/10, because its derivative is (delta-27/100)/delta^2<0.
Thus this entire tail cannot contain an interior crossing tie or a strict
mixed value at these K. Endpoints x=0 and x=1 are the two pure classes.

It remains only to cover the compact interval [1/10,9/10].

## 4. What every finite certificate leaf proves

The JSON file records exact rational x endpoints and exact integer bounds
for every leaf. Each of its four covers is generated by recursive rational
bisection. The code verifies that the first and last endpoints are the
requested endpoints, every adjacent leaf shares its endpoint, and the lengths
sum to the full interval. These are covers of intervals, not evaluations at
their centers. Every leaf method has one of the following meanings:

* `inadmissible`: the upper enclosure of v is nonpositive throughout the box;
* `strict_positive_W`: the lower enclosure of W is positive throughout;
* `W_excludes_zero`: the entire W enclosure has one strict sign;
* `Wx_excludes_zero`: the entire W_x enclosure has one strict sign;
* `strict_positive_Wxx_and_admissible`: W_xx has positive lower bound and v
  has positive lower bound throughout the box.

For the fixed-K upper-value cover, the W enclosure is also intersected with
the rigorous mean-value enclosure

    W(K,m)+W_x(K,[l,r])*([l,r]-m),    m=(l+r)/2.

The mean-value theorem justifies this enclosure on each full interval because
W is smooth there. Intersection with the natural formula enclosure is safe.
The derivative box, rather than a derivative at the midpoint, is used.

The exact certificate supplies:

1. At K=519/1000,x=521/1000, v>0 and W<-1/5000. This is a strict mixed
   witness, so K_star>519/1000 by NO_ISLANDS.
2. At K=13/25, a 27-leaf cover of [1/10,9/10] makes every leaf either
   inadmissible or strictly W-positive. On each W-positive leaf its recorded
   lower bound exceeds 1/10000. Together with Section 3, all positive widths
   are strictly below the pure value. The last-boundary interior tie theorem
   therefore gives K_star<13/25.
3. For the entire K interval, a 32-leaf cover of x in [1/10,1/2] and a
   13-leaf cover of x in [11/20,9/10] exclude admissible simultaneous zeros
   W=W_x=0 on every leaf. Every leaf is either inadmissible or has W or W_x
   excluding zero.
4. The single rectangle K in [519/1000,13/25],x in [1/2,11/20] has v>0
   and W_xx>1/10. The certificate also gives W_x<0 on x=1/2 and W_x>0
   on x=11/20 throughout the same K interval.

The final certificate contains 73 covering leaves in these four covers.
They certify all points of their respective boxes. Different covers serve
different claims; no individual leaf is silently reused outside its K scope.
The source and certificate hashes at the start bind the precise inputs used.

## 5. Unique nondegenerate interior tie at the global threshold

By NO_ISLANDS there is one last parameter K_star, and by LAST_MIXED_BOUNDARY
there is an interior crossing tie. By parts 1-2 of Section 4 it lies in the
stated K range. At any such tie, h=v/k is uniquely determined and W=W_x=0.
Section 3 and part 3 of Section 4 exclude all x outside (1/2,11/20).
On that remaining interval, part 4 says W_x is strictly increasing at every
fixed K. Hence at K_star there is at most one zero of W_x, and therefore
exactly one interior tie. It also has W_xx>1/10.

In the notation of NO_ISLANDS, W(K_x,x)=0 and W_K>0. At this unique maximum
of x -> K_x,

    K_x'=0,        K_x''=-W_xx/W_K<0.

Thus the last width is a nondegenerate, unique global maximum of the analytic
fixed-width crossing curve.

For the Hessian assertion let U(K,x,h)=(b(K)-B)/P. At the tie U=r_0 and
its gradient in (x,h) vanishes. Its h second derivative is strictly positive.
The minimized function is U_min=r_0 exp(W), so at the stationary tie

    (U_min)_xx=r_0 W_xx>0.

This is the Schur complement of U_hh in the Hessian of U, by differentiating
the smooth minimizing h=v/k. Therefore Hess U is positive definite. Finally

    F-b(K)=-P(U-r_0)

at the crossing, and the vanishing value and gradient of U-r_0 imply
Hess F=-P Hess U, which is negative definite. The linear coordinate change
L=2x preserves definiteness.

## 6. Reduction to exactly three analytic branches near the triple point

The analytic implicit-function theorem for the nondegenerate interior
stationary point gives a unique analytic z(c,r) near the triple point.
In a sufficiently small scalar neighborhood its Hessian remains negative
definite, so there is at most one stationary maximizer there.

No other global maximizer can enter from elsewhere near the triple point.
Here are the endpoint details, rather than a compactness assertion that
would ignore boundary layers. For c in a compact positive interval and
r in a compact positive interval around r_star, the centered Bernoulli
estimate used in LAST_MIXED_BOUNDARY gives, uniformly near L=0,

    F-(1+r)=B-1-r(1-P)<0               for 0<L<ell_0.

The proof keeps the factor h and treats h=0 separately, exactly as there;
one simply replaces its positive minimum of r_0 by the positive minimum
of the present r interval. Near L=2 the same estimate gives uniformly

    F-b(2c)<=-gamma(2-L)+R exp[-C/(2-L)]<0

with gamma,C>0 and a finite R. The maximizer on L=2 itself is the unique
analytic h_b(c). At h=0 or h=1 with 0<L<2 one has B=1,P<1, so F<1+r;
away from the width endpoints this excludes uniform neighborhoods of
both h faces. On the remaining compact set outside a small interior
neighborhood, the exact triple-point argmax has a strictly positive gap.
Uniform continuity preserves a gap for nearby parameters.

Thus all nearby global maximizers are the pole class, the pure bulk point,
or z(c,r). This proves the exact maximum representation (T.1). In particular
it rules out an additional nearby global mixed branch, rather than merely
constructing one stationary branch.

## 7. Coexistence curves and linear closing of the mixed window

At the interior critical branch, the envelope derivative is

    M_r=P(c,z(c,r)).

At the triple point it equals p_star in (0,1). Therefore the equations
M(c,r)=b(2c) and M(c,r)=1+r define unique analytic curves r_B(c) and r_P(c)
by the analytic implicit-function theorem; the r derivatives of their
defining functions are respectively p_star>0 and p_star-1<0.

For the relative slopes use the pure crossing r_0(c)=b(2c)-1 and the local
crossing excess

    D(c)=M(c,r_0(c))-b(2c).

Holding x=x_star, follow the smooth minimizing h=v/k for U at the pure
crossing. This path need not optimize F away from the triple point, but
at the triple point its derivative is the correct envelope derivative,
since both scalar derivatives of F vanish there. Along this path,

    F-b(2c)=P r_0(c)[1-exp(W(2c,x_star))].

Consequently

    D'(c_star)=-2p_star r_star A_star<0,
    A_star=W_K(K_star,x_star)>0.

Differentiating the two analytic coexistence equations yields

    r_B'-r_0'=-D'/p_star=2r_star A_star,
    r_P'-r_0'=D'/(1-p_star)=-2p_star r_star A_star/(1-p_star).

These derivatives give the expansions stated in the theorem. For c<c_star
sufficiently near the triple point, D(c)>0, and hence
r_B<r_0<r_P. Since M_r stays between zero and one, the two gap functions
have the indicated strict r monotonicities. Formula (T.1) then gives the
complete local pure bulk / mixed / pole diagram and its exact tie sets.
For c>c_star the two analytic zero curves still exist locally, but they
are not global mixed phase boundaries; NO_ISLANDS gives only the pure
envelope there. This distinction is necessary.

## 8. Transfer and limitations

At each fixed limiting pair in the local diagram, S transfers the complete
scalar argmax to actual APPT nearoptimizers with distance-to-argmax, J->0
and actual-peak-loss->0. At the triple point the three scalar classes yield
exactly these three possible subsequential empirical body laws:

    delta_0,
    (1-h_b)delta_{-2h_b}+h_b delta_{2(1-h_b)},
    (1-h_star)delta_{-L_star h_star}
                   +h_star delta_{L_star(1-h_star)}.

All are attainable by the credited construction. Their atom gaps are zero,
two and L_star in (1,11/10), so they are distinct. This is a classification
of limits for the original complex APPT objects, not just scalar candidates.
Tied sequences may alternate. For parameters themselves converging to the
triple point from one side, a claim of unique phase selection would require
control relative to the vanishing phase gap; such a claim is not made here.

The present theorem completes the local critical geometry and the uniqueness
of the last mixed point, in conjunction with the analytic no-islands proof.
It leaves the global mixed branch problem at smaller c open. No finite-
dimensional exact purity, entropy formula, new Lean coverage, or external
priority claim follows. All new texts and the exact certificate must receive
independent ordinary review before being indexed as proved results.
