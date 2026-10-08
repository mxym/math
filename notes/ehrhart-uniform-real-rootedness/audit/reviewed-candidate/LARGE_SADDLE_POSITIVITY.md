# Parent theorem: complementary reverse-saddle range

INTERNAL COMPLETE CANDIDATE, pending independent review. Uses the corrected
majorant smoothing constant c(x)=min(2/3,(1+x)^2/6), not the erroneous larger
constant from an earlier scratch calculation.

Assume d>=1001, mu_d(x)=m is an integer, 1/10<=x<=15. Then [z^m]R_d>0.
All notation and the marked-identity split agree with SMALL_SADDLE_POSITIVITY.md.
The final bound below is checked uniformly on 33 CLOSED rational intervals
covering [1/10,15], not by sampling their endpoints.

## Variance and local comparison

Put v(x)=integral_0^1 x t(2-t)/[2+(x-1)t]^2 dt. This is the variance density;
the factor (2-t) is essential. Its closed form, for x!=1, is
 v=x[2(x+1)log((1+x)/2)/(x-1)^3-(3x+1)/((x+1)(x-1)^2)],
with v(1)=1/6. Also nu=x/(x-1)-2x log((1+x)/2)/(x-1)^2, nu(1)=1/4.
Both v/x and nu/x decrease in x, directly by their integral formulas.
The function g(t)=x t(2-t)/[2+(x-1)t]^2 is nonnegative, unimodal, bounded
by 1/4, and has g(0)=0. Its total variation is at most 1/2-g(1).
Comparison of the right Riemann sum with the integral therefore gives
 jv-1/2<=V_j<=jv+1/2 for all j.

Every certificate interval supplies v>=3/100. Hence dv>=30.03. For s<=d/8,
 n>=7d/8, W=min(V_d,V_n)-1/4>=17dv/20,
 V_n>=6dv/7, sqrt(12V_d+1)<(7/2)sqrt(dv).
In particular W,V_n>20. The sharpened Fourier constants then imply
 sqrt(12V_d+1) C2(W)<(27/10)/(dv),
 sqrt(12V_d+1) C2(V_n)<(27/10)/(dv),
 sqrt(12V_d+1) A1(V_n)<(3/2)/(dv).
These numerical comparisons reduce to squaring positive rational quantities.

The endpoint trapezoid error in mu_d-mu_n-s nu is <1/500: indeed
|f'_x(1)-f'_x(0)|<=15/2 over 0<x<=15, giving an error <=15/(16n),
and n>=7*1001/8. The same prefactor estimates A<5/4 and
|A-1|<((9/4)s+3)/d apply.

## Exact endpoint envelopes on an interval [a,b]

The verifier uses rational enclosures for nu(a),nu(b),v(a),v(b), and exact
p(x)=x/(1+x). Let beta,B1,T1,T2 be upper bounds for the logarithmic majorant
mass, dimension first moment, and the first two periodic extra-dimension
moments, evaluated at b. Their monotonicity follows from that of v_j and q.
All bounds include explicit INFINITE tails, not merely finite sums.

Take v_low=a*v(b)_low/b and v_high=min(1/4,b*v(a)_high/a).
Let Nhi=max_{nu(a)<=t<=nu(b)}t(1-t), Nlo the analogous minimum, and
P_hi,P_lo the maximum/minimum of p(1-p) between the endpoint p values.
Let r be either p(b)-nu(a)_low or the sharper
 p(b)*(p(a)-nu(a)_low)/p(a), whichever is smaller.
The latter is valid because (p-nu)/p=integral 2(1-t)/[2+(x-1)t]dt decreases.
Let t0=p(b)/2 when a>=1 and t0=p(b) otherwise.
For x>=1 the concavity of f_x gives e_j>=p/2; thus t_j=p-e_j<=p/2.

The logarithmic centered mean is bounded by
 M=t0*beta+r*T1.
An upper bound Q for the exponential's normalized centered second moment is
 Nhi*B1+p(b)*max(1-2nu(a)_low,0)*beta
 +max(0,P_hi-Nlo)*T1+t0^2*beta+2*t0*r*T1+r^2*T2+M^2.
This follows from the component Jensen variance estimate proved in the small
saddle argument. An absolute first moment bound is
 U=min(sqrt(Q), 2nu(b)_high*B1+M).
With eps=1/500 the needed shifted moments are bounded by U+eps and
Q+2eps U+eps^2.

Let L be a lower bound for log E. If a<1 use L=-beta. If a>=1, log E increases:
 log E = r0 sum_(j,h) v_j phi(h)/h^2 (r0*q)^((h-1)j), r0=(x-1)/(x+1).
Every factor on the right is nonnegative and increasing. A positive finite
sum at a is therefore a valid lower bound for every x in the interval.
Let Rexp>=exp(beta-L), Iexp>=exp(-L), with exact series enclosures.

The small-component probability and prefactor errors, divided by E, are
bounded by Ksmall/d and Kpref/d, where
 Ksmall=(5/4)Rexp/v_low *[(81/10)p(b)B1+(3/2)(U+eps)
                              +(27/20)(Q+2eps U+eps^2)],
 Kpref=Rexp[(9/4)B1+3beta].

## Majorant tail constants and the remaining terms

verify_majorant_tail_constants.py proves, by finite bases 64..127 and a
single decreasing induction inequality for all s>=128, that h_s<C s^(-5/2)
for s>=64, with C=3/2 on x<=1, C=2 on x<=3, C=4 on x<=7, and C=10 on x<=15.
Its logarithmic b_n bound is proved for all n>=64 using
 n^(5/2)b_n<=A+3A n^(3/2)q_cap^(n/2), decreasing in n>=64.
The displayed endpoint constants and all finite residuals are exact rational
checks. The recurrence proof is in LARGE_COMPONENT_SMOOTHING.md.

For d/8<s<=d/2, the ratio of the primitive maximal atom to the d-mode is <4:
use V_n>=dv/2-1/2, dv>=30, the Gaussian atom bound and pi<4.
Together with A<4, the middle contribution and omitted E tail are bounded by
 306 C Iexp d^(-3/2).
For s>d/2, corrected majorant degree smoothing gives a bound Klarge/d, with
 Klarge = UP*(7/2)*(16/25)*8*sqrt(v_high/(c_low*P_lo))
              *C*B1/(1+a)*Iexp,
 UP=sqrt(4*(22/7)*(1+b))*(1001/1000),
 c_low=min(2/3,(1+a)^2/6).
Here sqrt(pi)/(2sqrt(2))<16/25, sum n||J_n||R^n<=B1/(1+a),
s>d/2 implies s^(-3)<8/d^3, and exp(1/d)<=1001/1000.

All periodic terms with n>=d/2 have total normalized error
<1296 d^3 exp(-d/20)<1/1000 for d>=1001. Use the source norm bound,
P_d R^d>d^(-5/2)/32, reciprocal mode <2sqrt(d), exp(beta)<9/2 and
E^(-1)<9/2. Monotonicity and exp(1)>8/3 reduce the endpoint to a rational
integer inequality.

## Finite covering certificate and conclusion

For each of the 33 intervals, verify_large_x_intervals.py certifies
 (Ksmall+Kpref+Klarge)/1001 +306 C Iexp/(1001*31)+1/1000 <1.
Every term is an upper bound valid on the entire interval and for EVERY
d>=1001. Rational log bounds, algebraic bisection for q, Taylor bounds for
exp, integer square-root bounds, and outward dyadic rounding justify every
scalar enclosure. Floating point is used only to display already-certified
rational bounds, never to accept a bound. The largest reported rational upper
bound is below 0.947 (interval [14,15]); the exact rational value is in the
JSONL certificate. The intervals join without gaps or endpoint exclusions.
Thus |[z^m]R_d/kappa-E|<E and the coefficient is positive.
