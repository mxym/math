# A rank-three debit forced by affine short-label majorants

Let \(N=2x\) be large and even, \(J=xJ_0\) with \(J_0\) a
fixed positive-length subinterval of \([1,4/3]\), and
\(M_N=|J|\mathfrak S(N)\) in the usual Goldbach normalization.
Put \(P=N-y\), and in this note always require \(P\) to
be a genuine prime. Retain the actual squarefree rows
with \(y\in J\), \(P^-(y)>x^\alpha\), where \(\alpha=.25005\)
or \(.265\). Each retained \(y\) has at most three factors
for sufficiently large \(x\). Let \(w(u)=4u(1-u)\) and
\(u_r=(\log r)/(\log y)\) for a prime \(r\mid y\).
The normalized score \(T(y)\) is \(-1\) on primes,
\(w(u_r)\) on a semiprime with \(r\) its smaller prime,
and zero on triprimes. The genuine weighted sum of
\(T(y)\) with weight \(\log P\log y\) is precisely
\(D_w(\alpha)-G\), from the
[central rough Chen comparison](../least_factor_trim_2685/Proof.md).
It is not an estimated signed sum here.

Consider only **fixed, one-short-label affine majorants**
\[
                 C(y)=c+\sum_{\substack{r\mid y,\ r<\sqrt y\\
                                        r\ {\rm prime}}}h(u_r),
\]
where \(c\) is a real constant and \(h\) is a finite real
function of the single angle, with no dependence on the
opponent, other labels or \(N\). It may be any integrable
profile; no regularity of \(h\) is needed for the lower
bound below. A pointwise angular majorant is required to
dominate the prime profile and every semiprime profile
with smaller angle in \((\alpha,1/2)\), not just an
average of those profiles. When used to majorize the
whole true sum also require \(C(y)\ge T(y)\) on the
actual finite-\(x\) boundary profiles (whose log-\(y\)
rather than log-\(x\) angles may lie \(O(1/\log x)\)
below \(\alpha\)). Then the genuine sums of \(C(y)\)
against the prime opponent satisfy
\[
 \liminf_{X\longrightarrow\infty}
  \frac{\displaystyle
   \sum_{X\le x\le2X}\ \sum_{\substack{y\in xJ_0,\ N-y\ {\rm prime}\\
               y\ {\rm squarefree},\ P^-(y)>x^\alpha}}
                       (\log(N-y))(\log y)\,C(y)}
       {\displaystyle\sum_{X\le x\le2X} M_{2x}}
 \ >\
 \begin{cases}
       .660,&\alpha=.25005,\\
       .378,&\alpha=.265.
 \end{cases}                                                     \tag{1}
\]
Here the outer sums are over integers \(x\), with target
\(N=2x\). In particular this majorant class cannot prove a
uniform signed bound \(.250M_N\) or \(.050M_N\) respectively
by bounding its own whole true sum by that number. This
is not a bound from below for \(T(y)\)'s sum, nor an
obstruction to nonlinear labels, signed cancellations or
a different arithmetic approach.

## Proof

The prime profile forces \(c\ge-1\), while the semiprime
profiles force \(h(u)\ge w(u)-c\) at every indicated \(u\).
All three true prime factors of a retained triprime lie
below \(\sqrt y\) for sufficiently large \(x\): the
other two factors have product \(>x^{2\alpha}>\sqrt y\).
Off the angular cutoff collar each of the three angles
belongs to the full range of the **same** semiprime
constraint on \(h\). On those triprimes,
\[
 C(y)\ge \sum_{i=1}^3 w(u_i)-2c\ge\frac52-2c .
\]
Indeed \(\sum u_i=1\), \(1/4\le u_i\le1/2\), and
\(\sum u_i^2\le3/8\) by convexity on that simplex
(the extremal arrangement is \((1/2,1/4,1/4)\)).
Boundary-collar triprimes can be dropped in the lower
estimate if the displayed lower bound is positive,
since \(C\ge0\) there. If it is negative they already
satisfy that lower bound. Thus no limiting step
involving \(h\) itself is needed.

The genuine weighted dyadic masses of the prime profile,
the semiprime score \(w\), and the triprime profile,
relative to \(\sum M_{2x}\), tend respectively to
\[
 1,\qquad \int_\alpha^{1/2}\frac{w(u)}{u(1-u)}\,du=2-4\alpha,
 \qquad I_3(\alpha)=\int_\alpha^{1/3}
                  \frac{\log((1-2u)/u)}{u(1-u)}\,du.           \tag{2}
\]
To be explicit, the mean of \(\mathfrak S(2x)\) on
integer \(x\) is 2 by the ordinary positive divisor
expansion: each odd prime's multiplier \(1+1/(p(p-2))\)
cancels the corresponding twin-prime factor. Thus
\(\sum M_{2x}\sim 3|J_0|X^2\), which is also the area of
the physical region \(2X\le P+y\le4X\),
\(2y/(P+y)\in J_0\). When \(y\) is either a true prime
or a product of genuine odd primes, \(P+y\) is automatically
even, so independent prime counting after summing over
**these actual targets** has no further lattice factor.
Approximate the fixed spatial region by rectangles and
use PNT for the real \(P\). In the product source, fix
all but the largest factor, apply PNT in the largest
factor and then use true prime harmonic measure for
the earlier labels. This yields the ordered angular
density \(du/[u(1-u)]\) for semiprimes. For
triprimes the two small angles range over
\(\alpha\le u\le1/3\), \(u\le v\le(1-u)/2\),
with density \(du\,dv/[uv(1-u-v)]\); integrating the
second gives the last expression in (2). Endpoint,
spatial and repeated-label collars have zero limiting
measure. In particular the \(O(1/\log x)\) cutoff collar
can be enclosed in any fixed positive-width angular
collar before taking the limit. Only these continuous
fixed test profiles are integrated, not the majorant
\(h\). Nothing in this averaging asserts a prime
asymptotic for one fixed target.

Consequently the lower liminf in (1) is at least
\[
 c+(2-4\alpha)+(5/2-2c)I_3(\alpha).
\]
Since \(I_3<.148<1/2\) at both cutoffs, this is
minimum at \(c=-1\). Its minimum is
\(1-4\alpha+(9/2)I_3(\alpha)\). The
[rational certificate](check.py) uses decreasing
positive factors of the last integrand in (2)
and left/right rectangles; each log is enclosed
with its elementary atanh series and geometric
remainder. The strict bounds give (1).

One example outside this class is to use only the
**actual least** short prime: the score that is
\(-1\) on primes and \(w(u_{\min})\) on composites
is still a pointwise majorant. At \(.25005\) its
weighted dyadic mean is below \(.148\), since
its extra rank-three weight is at most \(I_3\).
Another exact option on this rough support is
\[
 T(y)=-1+\sum_i(1+w(u_i))
       -\sum_{i<j}\left(\tfrac23+
                  \tfrac{w(u_i)+w(u_j)}2\right),
\]
where both sums run over the actual short prime
labels. This identity holds on each of the three
ranks separately. The pair term is supported on
real triprimes, and carries a product of two
primes \(>x^\alpha\), beyond the literal square-root
modulus in an additive opening. These two examples
explain the limitation of a one-label treatment;
neither supplies the needed fixed-target sign estimate.

## Why the .250 threshold is useful

The verified start of the [physical semiprime trim](../least_factor_trim_2685/Proof.md)
gives \(G+D_2(.252)>.3001M_N\). Stop its same
Buchstab subtraction at \(a=.25005\) instead.
On \([a,.252]\) its integrand
\(2/[t(1-1.00001(7/32)/2-.00005-2.5t)]\)
is increasing and exceeds \(30.1\), whereas the
rank-three integrand of (2) is below \(3.7\).
The latter follows from \(\log 2<.6932\) and
\(t(1-t)\ge3/16\). Keeping the same \(3.446\) actual
triprime upper gives a raw lower strictly above
\[
  .3001+(.252-a)(30.1-3.446\cdot3.7)=.33393211 .
\]
Since \(w(u)\ge 4a(1-a)-O(1/\log x)\) on the
retained semiprimes, this gives \(G+D_w(a)>.2504M_N\).
A same-target \(D_w(a)-G\le .250M_N\) would imply
\(G>.0002M_N\). The signed dyadic mean is \(-.0002\);
(1) rules out only the stipulated majorizing template
for turning that feasible mean into a uniform bound.
