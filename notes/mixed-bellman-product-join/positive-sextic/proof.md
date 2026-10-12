# A positive sextic homogeneous Bellman envelope

Reader edition of the audited entry 005 continuation, 7 October 2026. Author: mxym. The unchanged original proof, exact certificates, verifier sources, and independent audit are preserved in certificates-and-independent-audit.zip. This public archive retains every original entry and adds only two recovered ancestor package manifests; ARCHIVE_INVENTORY.json records the original and corrected archive hashes and complete contents. This edition supplies the definitions and inherited spectral argument alongside the new sextic proof. Publication priority, optimality, unrestricted-body bounds, human peer review, and proof-assistant formalization are not claimed.

## Status

The certified global inequality is

log Q <= alpha(D-H^2/D)+beta(D-H^4/D^3)+gamma(D-H^6/D^5),

where

alpha=431/10000, beta=9/2500, gamma=197/100000,
T=alpha+beta+gamma=4867/100000.

The new feature is the positive sextic term. This changes the potential family and is not a retuning within the previously obstructed quadratic/quartic family. Its nominal rate bound is exp(1+T)<142693/50000=2.85386. All three certificate components pass exact ordinary and optimized replay: finite rectangles, imbalanced tails, and both-large dimensions. A separate independent reimplementation also passes in both modes, with no mathematical correction required. The full proof follows. The original STATUS.md and independent AUDIT.md inside the archive record the verification scope; AUDIT_SUMMARY.md gives the release-facing summary.

The result concerns the point-generated product/join class C with invertible affine equivalences of full affine hulls. It does not determine its optimum and gives no new lower construction. In particular, the old local quadratic/quartic method floor is not an extremal lower bound.

## Definitions and inherited inputs

Let C be the class generated from a formal point by finitely many Cartesian products, joins, and invertible affine maps between full affine hulls. Each positive-dimensional member is a polytope in its affine hull. The join of A in R^r and B in R^s is the convex hull of {(x,0,0):x in A} and {(0,y,1):y in B} in R^(r+s+1). Rank-dropping affine maps are excluded.

For a full-dimensional d-polytope K, its projection body Pi K has support function equal to the (d-1)-dimensional volume of the orthogonal projection onto a unit direction's perpendicular hyperplane. Set R(K)=|Pi K|/|K|^(d-1). The zero-dimensional projection convention gives R=2 for an interval. For facet area s_i, outward unit normal nu_i, support number h_i, and v=|K|, put u_i=s_i nu_i, b_i=s_i h_i,

P(K)=sum_(|I|=d) |det(u_i:i in I)|=|Pi K|,
S(K)=sum_(|I|=d+1) |det((u_i,b_i):i in I)|,
a(K)=S(K)/(d v P(K)).

The affine invariance, 1/(d+1)<=a<=1, and the exact product/join identities below are inherited from entry 005 v2, Lemma 2.1 and Sections 3-5 and 8. The unmodified pinned paper, spectral supplement, and lower checker/certificate are included in dependencies/v2. Their origin and hashes are in SOURCE_MAP.json. The contribution here is the positive sextic potential and its complete product certificates, adapting the preceding exact tangent, interval-tail, and retained-quartic large-factor framework. No claim of discovery of the Bellman method or the inherited numerical mixed-potential direction is made.

## 1. Exact state calculus and induction

For positive-dimensional K, use the inherited state

d=dim K, D=d+1, H=1/a(K),
g(d)=d^d/d!, Q=a(K)R(K)/g(d).

The point has D=H=Q=1. The inherited identities are

(D,H,Q)(A*B)=(D_A+D_B,H_A+H_B,Q_A Q_B),

and, for r=dim A>=1, s=dim B>=1, n=r+s, h=H_A, j=H_B,

H'=n/(r/h+s/j), D'=n+1,
Q'=Q_A Q_B C x,
C=g(r)g(s)/g(n), x=(s h+r j)/n.

Every positive-dimensional state in C has 2<=H<=D. The upper bound is the inherited a>=1/(d+1). For the lower bound, joining two points gives H=2; joins add H and products preserve a<=1/2, since a' is the dimension-weighted arithmetic mean of the factor a values. Products with a point are redundant.

Define

Phi(D,H)=T D-alpha H^2/D-beta H^4/D^3-gamma H^6/D^5.

It vanishes at the point. For p=2,4,6, weighted Jensen gives

(H_1+H_2)^p/(D_1+D_2)^(p-1)
<=H_1^p/D_1^(p-1)+H_2^p/D_2^(p-1).

Because all coefficients are positive, joins preserve log Q<=Phi.

For products, let

Delta_p=-1+h^p/(r+1)^(p-1)+j^p/(s+1)^(p-1)
           -(H')^p/(n+1)^(p-1).

The exact product requirement is log(C x)<=alpha Delta_2+beta Delta_4+gamma Delta_6.

We certify a stronger inequality by means of the following moments:

G_2=h^2/(r+1)+j^2/(s+1)-(r h+s j)^2/[n^2(n+1)],

G_p=A_p h^p+B_p j^p, for p=4,6,
A_p=1/(r+1)^(p-1)-r/[n(n+1)^(p-1)],
B_p=1/(s+1)^(p-1)-s/[n(n+1)^(p-1)].

Weighted harmonic <= weighted arithmetic and <= weighted p-power mean imply Delta_p>=G_p-1. All A_p,B_p are strictly positive, since r(r+1)^(p-1)<n(n+1)^(p-1), and similarly for s.

The quadratic G_2 is positive definite. Its first diagonal coefficient is positive and its determinant is

rs(3n+2)/[(r+1)n^2(s+1)(n+1)]>0.

Thus the state function

f_(r,s)(h,j)=log(C x)-alpha G_2-beta G_4-gamma G_6+T

is strictly concave on the positive quadrant. Showing f<0 on [2,r+1] x [2,s+1] suffices for product induction. Assume r<=s by symmetry. The next three sections exhaust every integer dimension pair.

## 2. Finite rectangles, r,s<200

There are 19,900 pairs 1<=r<=s<=199. sextic_finite_points.json contains one rational tangent point (h_0,j_0) in each state rectangle, with common denominator 10^10. For each pair, check_sextic_finite.py independently computes the moment values, gradients, exact dimension-logarithm intervals, and the tangent upper bound

f(h_0,j_0)+g_h(b_h-h_0)+g_j(b_j-j_0),

where b_h is r+1 if g_h>=0 and 2 otherwise, and likewise b_j is s+1 or 2.

Concavity makes this a global upper bound on the full real rectangle. The checker verifies strict negativity with uniform upper margin -1/10^6. Coverage, coefficient identity and tangent-point membership are checked exactly. No optimization result is used as a proof decision. The rational-logarithm algorithm is detailed in Section 5.

The worst certified upper bound is at r=s=25, h_0=j_0=137374081947/10^10. Its floating rendering is approximately -0.0000064803879273; only the exact fraction in sextic_finite_report.json is proof evidence.

## 3. Imbalanced tails, r<200<=s

Set z=1/s in (0,1/200], and normalize u=j/(s+1) in [0,1]. The enlarged state box [2,r+1] x [0,1] contains all realizable states.

Define

P_2=(1+r z)^2(1+(r+1)z),
S_2=3+(3r+2)z+r(r+1)z^2.

Exact algebra gives G_2=a h^2+b h u+c u^2, where

a=1/(r+1)-r^2 z^3/P_2,
b=-2r z(1+z)/P_2,
c=r(1+z)S_2/P_2.

For p=4,6, put

P_p=(1+r z)(1+(r+1)z)^(p-1),
a_p=1/(r+1)^(p-1)-r z^p/P_p,
d_p=r(1+z)S_p/P_p,

where the polynomial S_p is explicitly

S_p(z)=[P_p-(1+z)^(p-1)]/(r z).

This quotient is a polynomial, including at z=0. Its coefficient of z^(k-1), for 1<=k<=p, is

[binom(p-1,k)((r+1)^k-1)
 +r binom(p-1,k-1)(r+1)^(k-1)]/r,

with out-of-range binomial coefficients zero. Every coefficient is positive. The sextic_tail_core.py checker constructs these coefficients exactly. Equivalently,

S_4=4+(6r+9)z+(4r^2+9r+6)z^2+(r+1)^3 z^3,

S_6=6+(15r+25)z+(20r^2+50r+40)z^2
 +(15r^3+50r^2+60r+30)z^3
 +(6r^4+25r^3+40r^2+30r+10)z^4
 +(r+1)^5 z^5.

The exact normalized moments are G_p=a_p h^p+d_p u^p. To see the cancellation for d_p, substitute j=(1+z)u/z in B_p j^p; it simplifies to (1+z)[P_p-(1+z)^(p-1)]u^p/(z P_p), which is the displayed expression.

The inherited analytic factorial bound is C<=g(r)e^(-r) sqrt(1+r z). Here is a self-contained proof. Put v_m=m!e^m/(m^m sqrt m). Then

log(v_(m+1)/v_m)=1-(m+1/2)log(1+1/m)<0,

since log t>2(t-1)/(t+1) for t>1; the latter follows by differentiation, with equality at t=1. Direct substitution gives

C=g(r)e^(-r) (v_(r+s)/v_s) sqrt((r+s)/s),

proving the bound.

Consequently f is bounded above by

F_(r,z)(h,u)=log g(r)-r+log[h+r(1+z)u]
 -(1/2)log(1+r z)
 -alpha(a h^2+b h u+c u^2)
 -beta(a_4 h^4+d_4 u^4)
 -gamma(a_6 h^6+d_6 u^6)+T.

The endpoint z=0 is a regular auxiliary limiting parameter, not an infinite-dimensional body. For each fixed real z in [0,1/200], this function is strictly concave in its state variables: its quadratic coefficients give the exact normalized positive-definite G_2, its logarithm is concave, and the positive even-power terms are convex.

The tail certificate partitions [0,1/200] into rational dyadic cells for every 1<=r<=199. Each cell supplies a rational state point (h_0,u_0). Standard exact interval arithmetic encloses a,b,c,a_p,d_p and both state derivatives uniformly on that whole cell. All denominator intervals are checked to exclude zero.

For the quadratic remainder, let a_- and c_- be the lower endpoints, b_*^2 the maximum of the squared b endpoints, and set

m_h=a_-/2,
m_u=c_- - b_*^2/(2a_-).

Both must be strictly positive. Young's inequality then proves, for all real displacements eta,

a eta_h^2+b eta_h eta_u+c eta_u^2
>=m_h eta_h^2+m_u eta_u^2,

uniformly throughout the cell. The log, quartic and sextic terms all have favorable concave Taylor remainders. Therefore

F(p+eta)<=F(p)+grad F(p).eta
          -alpha(m_h eta_h^2+m_u eta_u^2).

The separated one-variable maxima of g eta-alpha m eta^2 are computed exactly at the clipped vertex g/(2alpha m), including zero and both displacement ranges. For interval gradient g, its lower endpoint is used on negative displacements and upper endpoint on positive displacements, which bounds every actual gradient.

check_sextic_tail.py recomputes every cell upper bound and verifies ordered exact coverage without overlap or gap, all constants, rational point membership, and a uniform negative upper margin -1/10^10. Ordinary and optimized replay pass all 157,872 cells, at maximum dyadic depth 11, with byte-identical reports. A separate independent interval/polynomial implementation passes the same full certificate in both modes. The submitted report is sextic_tail_replay.json in the archived candidate directory.

## 4. Both dimensions >=200

This component deliberately discards the favorable sextic term but keeps its constant contribution through T. Its calculations extend the retained-quartic large-factor proof in the supplied source to the new alpha,beta,T. The exact constant verification is check_sextic_large.py.

Put t=r/s in (0,1], tau=1/r<=1/200, B=(s h+r j)/n, q=B^2/r>0. The exact quadratic minimum is

G_2>=k B^2,
k=(3n+2)/(4rs+3n+2).

For example the following nonnegative-square identity proves it, with Delta=4rs+3n+2:

G_2-k B^2=
rs[(s+1)(3r+s+2)h-(r+1)(r+3s+2)j]^2
 /[(r+1)n^2(s+1)(n+1)Delta].

Write

K_2=[3(1+t)+2t tau]/[4+3(1+t)tau+2t tau^2],
K_0=3(1+t)/4,
d(t)=[9+(1003/100)t+(903/100)t^2]/16.

Direct subtraction yields 0<=K_0-K_2<=tau d(t), and hence G_2>=K_2 q.

The quartic estimate is

G_4>=tau(123/125)R(t)q^2,
R(t)=(1+t)^4/[413/250+(21/40)t]^3.

For completeness, multiply the quartic coefficients by r^3 and put v=t/(1+t). At tau=0 they are

a_0=P(t)/(1+t)^4,
b_0=t^4 Q(t)/(1+t)^4,
P=1+4t+6t^2+4t^3,
Q=4+6t+4t^2+t^3.

Their tau derivatives are bounded below by -3 and -3t^4, respectively. Since a_0>=15/16 and b_0>=15t^4/16, both coefficients are at least (1-16tau/5) times their tau=0 values. The b_0 bound follows from the chord lower bound 1-(1+t)^(-4)>=15t/16 on [0,1]. Hölder under h+t j=(1+t)B gives

G_4>=tau(1-16tau/5)
 [P(t)^(-1/3)+Q(t)^(-1/3)]^(-3)q^2.

Now P>=(15/16)(1+t)^4 and Q^2>=16(1+t)^3; the latter difference is t^6+8t^5+28t^4+40t^3+20t^2. The rational inequalities (511/500)^3>16/15 and (63/100)^3>1/4, followed by (1+t)^(5/6)<=1+5t/6, give the displayed R(t). Finally 1-16tau/5>=123/125.

Robbins' factorial bounds give

log(C B)<(1/2)log q+(1/2)log[(1+t)/(2pi)]+sigma/2,

sigma/2<=tau[t/(12(1+t))-200(1+t)/2401].

The correction comes from

sigma=tau[t/(6(1+t))-2/(12+tau)-2t/(12+t tau)],

using tau<=1/200.

Taking the tangent of log q at q_0=2/[3alpha(1+t)] and maximizing the remaining concave quadratic yields

f_(r,s)(h,j)<F_infty+tau E(t),
F_infty=T-1/2-(1/2)log(3pi alpha),

E(t)=t/[12(1+t)]-200(1+t)/2401
 +alpha^2 d(t)^2/[4 beta(123/125)R(t)].

The sextic term was omitted because G_6>0. We certify E(t)<7/50 on the full interval [0,1]. After clearing the positive denominator (1+t)^4 this is equivalent to strict positivity of the degree-seven polynomial

P_E(t)=(7/50)(1+t)^4-t(1+t)^3/12
 +200(1+t)^5/2401
 -[alpha^2/(4beta(123/125))]d(t)^2[413/250+(21/40)t]^3.

check_sextic_large.py computes its eight Bernstein coefficients by exact rational arithmetic and checks every one is positive. The list is in sextic_large_report.json. Bernstein nonnegativity and partition of unity establish positivity on every real t in [0,1].

A Machin alternating-series estimate gives pi>314159/100000. The exact positive Taylor sum through degree 10 verifies

3(314159/100000)alpha sum_(j=0)^10 (901/1000)^j/j!>1.

Thus log(3pi alpha)>-901/1000. Since tau<=1/200,

f<F_infty+(7/50)/200
 <4867/100000-1/2+901/2000+7/10000
 =-13/100000<0.

This covers every positive state h,j for r,s>=200, without boxes.

## 5. Exact logarithms and the rate endpoint

All proof decisions use integers and fractions. For x>0 rational, reduce x=2^k y, 1<=y<=2, and put w=(y-1)/(y+1) in [0,1/3]. Then

log y=2 sum_(m=0)^(N-1) w^(2m+1)/(2m+1)+E_N,
0<=E_N<=2w^(2N+1)/[(2N+1)(1-w^2)].

The same calculation bounds log 2. The endpoints are reversed as required when scaling its interval by negative k. Rational outward rounding enlarges intervals only. The finite verifier uses N=20, the tail verifier N=28. Every sign, inclusion and coverage check stays active under python -O.

The three exhaustive product components pass, so structural induction proves log Q<=Phi for every finite expression. The inherited all-dimensional spectral reduction is briefly recalled here. Put lambda_*=sup Q(K)^(1/(d+1)); the new invariant makes it finite. For every dimension d, R(K)<= (d+1)g(d)lambda_*^(d+1), using a>=1/(d+1); hence the limsup of sup R(K)^(1/d) is at most e lambda_* by Stirling. Conversely fix K of dimension k and write d+1=m(k+1)+q with 0<=q<=k. The m-fold self-join, with a (q-1)-simplex filler when q>0, lies in C_d and has Q=Q(K)^m. Since the filler has Q=1 and a<=1, its root rate tends to e Q(K)^(1/(k+1)). Taking the supremum over fixed K proves existence of the limit and the identity

Gamma_C=e sup_(K in C) Q(K)^(1/(d+1)).

Dividing the new invariant by D gives

log Q/D<=T-alpha(H/D)^2-beta(H/D)^4-gamma(H/D)^6<T,

and hence Gamma_C<=exp(1+T). The exact endpoint is proved by the exponential Taylor sum through degree 12 with the geometric remainder

exp x<=sum_(m=0)^12 x^m/m!+[x^13/13!]/(1-x/14), x=1+T.

check_sextic_large.py verifies this is less than 142693/50000=2.85386. Together with the inherited certified lower construction, this yields 2.8534<Gamma_C<2.85386. It does not make the uncertified decimal rendering of the lower orbit an exact endpoint.

## 6. Structural comparison and limitations

The five-simplex product test now requires

log(189/128)<=(85/11)alpha+(13345/1331)beta
                  +(1724905/161051)gamma.

Its sextic defect coefficient follows directly from 2*6-6^6/11^5-1. It is larger than the quartic defect coefficient; the extra term accommodates the finite simplex bottleneck while the larger quadratic coefficient controls the balanced large-state curvature. The finite full-box worst state moves to dimension pair (25,25) for these rational parameters.

The prior exact local quadratic/quartic obstruction forces T>3046/62500=.048736. Here T=.04867, an exact decrease of 33/500000=.000066 below that obstruction. This does not contradict it: the new potential includes a positive sextic term, and local closure is being proved in that richer family. The previous certified exponent was 39/800=.04875, which is larger than the new T by 1/12500=.00008.

The new profile is not pointwise below the previous one for every H/D. Setting x=(H/D)^2, exact subtraction gives

(Phi_old-Phi_new)/D=(1-x)[8/100000+13x/100000-197x^2/100000].

It has both signs on the state interval. In particular the new potential redistributes allowable slack across normalized states instead of simply subtracting a constant from the old envelope. It should be compared as a new independently closed invariant and through its improved nominal spectral ceiling, without asserting pointwise domination.

Discovery optimization used SciPy and floating point only to select rational tangent points and rational potential coefficients. These searches cannot prove optimality even within the positive sextic family. Exact replay validates the listed candidate if every component passes. Independent mathematical audit and normal/optimized replay remain distinct from proof-assistant formalization or human peer review.
