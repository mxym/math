# Brocard short-prime certificates in shorter windows

Write \(Y=X^\theta\), where \(17/30<\theta\le1\) is fixed. Let \(W_\theta(X,H)\)
count integers \(X<n\le X+Y\) for which some prime \(p=n+r\), \(2\le r\le H\),
has \((\frac{n!+1}{p})=-1\). Such a prime certifies that \(n!+1\) is not a
square. Set
\[
 c_\theta=\min\left\{\theta-\frac{17}{30},\frac{2\theta-1}{3}\right\}.
\]

**Theorem.** Along any sequence of integers \(H\ge2\) satisfying
\(\limsup_{X\to\infty}H\log\log X/\log X\le c_\theta\),
\[
 W_\theta(X,H)=(1+o(1))\frac{(H-1)Y}{2\log X}.
\]
At most \(O_\theta(YH^2/(\log X)^2)\) integers in the window receive two or
more such certificates. If \(H\to\infty\), the least witnessing offset
divided by \(H\) has limiting uniform distribution on \([0,1]\) among the
certified integers.

In particular the dyadic coefficient is \(1/3\), including the limiting
endpoint, instead of the strict \(1/8\) range in the
[earlier dyadic note](FactorBrocardNearPrimeCertificates.md).
For a concrete shorter window, length \(X^{2/3}\) permits coefficient \(1/10\).
This is an asymptotic count of *local witnesses*, not an estimate for the
number of solutions stronger than [Bui–Pratt–Zaharescu](https://arxiv.org/abs/2204.08423),
and not an exhaustive numerical search. The Wilson criterion itself goes
back to [Helou–Haddad](https://doi.org/10.1007/s11139-008-9139-8).

## 1. Square-class compression

Put \(a_r=(r-1)!\), \(A_r=a_r(a_r+(-1)^r)\), and let \(D_r\) be the positive
squarefree part of \(A_r\). The two factors are positive, consecutive and
coprime; they cannot both be squares. Hence \(D_r>1\) and the associated
primitive quadratic character \(\chi_r\) is nonprincipal. Its conductor
\(q_r\) is \(D_r\) or \(4D_r\), according to the fundamental-discriminant rule.
Wilson's theorem gives \(n!\equiv (-1)^r/a_r\bmod p\). Multiplying \(n!+1\)
by the square \(a_r^2\) shows that its symbol at \(p\) equals that of \(A_r\).

The useful conductor bound is
\[
 q_r\le 4\,\prod_{\substack{\ell<r\\\ell\ {\rm prime}}}\ell\,
                 (a_r+(-1)^r),\qquad
 \log q_r\le r\log r+O(r).
 \tag{1}
\]
Indeed the squarefree part of \(a_r\), unlike the factorial itself, divides
the primorial. Chebyshev's bound for the sum of prime logarithms is sufficient
in (1). Also \(\log A_r\le 2r\log r+O(r)\). In the full asserted range
\(A_r<X\) eventually, since \(c_\theta\le1/3<1/2\). So at primes in the
window the symbol is exactly \(\chi_r(p)\), never zero.

The maximum number \(M(H)\) of repetitions of any primitive character among
these \(H-1\) offsets is \(o(H)\). Here is the argument from the dyadic note.
If \(r<s\le4r/3\) and there is a prime \(\ell>2\) in \([r/2,(s-1)/2]\),
then \(2\ell\) is the only multiple of \(\ell\) in \([r,s-1]\) and has
\(\ell\)-adic valuation 1. Since \(\ell<r\), it divides both factorials
and neither shifted factorial. Thus \(v_\ell(A_s)-v_\ell(A_r)=1\) and
\(D_r\ne D_s\). For fixed \(\nu>0\), partition \([\nu H,H]\) into a bounded
number of multiplicative intervals of ratio at most \(4/3\). In each, any
two offsets separated by at least \(\epsilon H\) are distinguished in this
way for all sufficiently large \(H\), by the prime number theorem on the
fixed scale \(H\). The maximum size of a class there is therefore \(o_\nu(H)\).
There are at most \(\nu H\) remaining offsets. Let \(\nu\downarrow0\); the
fundamental discriminant determines the primitive character and square
class uniquely, proving the assertion.

## 2. Character cancellation on \((X,X+Y]\)

First fix a strict coefficient \(c<c_\theta\) and suppose
\(H\le c\log X/\log\log X\). Choose constants \(c<\delta<c_\theta\) and
\(\eta>0\) sufficiently small that, with \(t_0=1-\theta+\eta\),
\[
             3\delta+2t_0<1,\qquad
             \frac{30}{13}(\delta+t_0)<1.
 \tag{2}
\]
Let \(Q=X^\delta,\ T=X^{t_0}\). By (1), \(q_r\le Q\) for all these offsets.
Two different zero-density estimates are used in different ranges:

* [Jutila, *On Linnik's constant*, p. 54 after (3.7)](https://doi.org/10.7146/math.scand.a-11701)
  records the Huxley refinement
  \(N^*(\sigma,T,Q)\ll_\epsilon (Q^3T^2)^{(1+\epsilon)(1-\sigma)}\)
  for \(\sigma\) sufficiently close to 1. Here \(N^*\) sums over all
  primitive characters of conductor at most \(Q\), including any
  exceptional zero. Choose a fixed \(\epsilon>0\) so small that
  \(b_h=(1+\epsilon)(3\delta+2t_0)<1\). Use the bound on a fixed
  closed range \(\sigma_0\le \sigma\le1\), \(1/2<\sigma_0<1\), sufficiently
  close to 1 for this \(\epsilon\).
* [Chen–Gupta–Li, arXiv:2507.08296v2, Theorem 1.2, the all-moduli bound](https://arxiv.org/abs/2507.08296v2)
  bounds the count for one character of conductor \(q\le Q\) by
  \[
  \ll_\epsilon(qT)^\epsilon
    \left((q^{7/3}T^2)^{1-\sigma}+(qT)^{(30/13)(1-\sigma)}\right),
    \qquad 1/2<\sigma<1.
  \]
  Because \(7\delta/3+2t_0<1\) by (2), there is \(b_m<1\) for which
  this is \(O_\epsilon(X^{\epsilon(\delta+t_0)+b_m(1-\sigma)})\).
  We choose the small parameter here independently of the one in the
  first estimate. We need this second estimate only a fixed distance
  from 1. Uniformity of the \(o(1)\) exponent in the cited theorem is
  sufficient; alternatively use a fixed finite mesh of \(\sigma\)'s
  with the same strict margin.

In detail, the weighted aggregate count of near-1 zeros is \(O(1)\):
\[
 \sum_{\substack{\chi\ {\rm primitive}\\\mathrm{cond}(\chi)\le Q}}
 \ \sum_{\substack{|\gamma|\le T\\\beta\ge\sigma_0}}X^{\beta-1}
 \le X^{\sigma_0-1}N^*(\sigma_0,T,Q)
       +\log X\int_{\sigma_0}^1
             X^{\sigma-1}N^*(\sigma,T,Q)\,d\sigma
 \ll 1.
 \tag{3}
\]
For the middle band one can start at any fixed \(\sigma_1>1/2\) with
\(\sigma_1+t_0<1\), which exists by (2). The analogous integration from
\(\sigma_1\) to \(\sigma_0\), but for one character, gives \(o(1)\) uniformly:
choose \(\epsilon(\delta+t_0)<(1-b_m)(1-\sigma_0)/2\) to absorb the
powers of \(X\) and any logarithms. Below \(\sigma_1\) the standard zero
count \(O(T\log(q(T+2)))\) gives \(O(X^{\sigma_1-1}T\log X)=o(1)\).

For smoothing take a fixed smooth compactly supported \(w\) on
\((-1/2,3/2)\) and use \(w_X(u)=w((u-X)/Y)\).
For \(-1/2\le\beta\le2\) its Mellin transform satisfies
\[
 |\widehat w_X(\beta+i\gamma)|
 \ll_{w,k}Y X^{\beta-1}(1+|\gamma|Y/X)^{-k}.
 \tag{4}
\]
Indeed after \(u=X+Yv\) the oscillatory phase is
\(\gamma\log(1+(Y/X)v)\); repeated integration by parts gives (4) with
constants uniform in \(0<Y/X\le1\).
Mellin inversion of \(-L'/L(s,\chi)\), shifting from 2 to \(-1/2\),
gives
\[
 \sum_{m\ge1}\Lambda(m)\chi(m)w_X(m)
   =-\sum_\rho\widehat w_X(\rho)
       +O_w(Y/X+X^{-1/2}\log X)
 \tag{5}
\]
for the nonprincipal primitive characters here. The possible trivial zero
at 0 contributes \(O_w(Y/X)\); on the new line the functional equation
bounds the logarithmic derivative by \(O(\log(q(2+|\Im s|)))\).
Integrating (4) there gives the stated bound, and horizontal terms vanish
by taking heights away from zeros, using the standard unit-interval zero
count. The same count and (4) bound the zeros \(|\gamma|>T\), per
character after division by \(Y\), by
\[
 \ll_{w,k}\frac{X}{Y}(TY/X)^{1-k}\log X
       =X^{1-\theta-\eta(k-1)}O_{w,k}(\log X)=o(1)
\]
for fixed sufficiently large \(k\). The elementary complex-analytic
inputs to (5) are as in [Davenport](https://doi.org/10.1007/978-1-4757-5937-0).

If \(H\to\infty\), (3) contributes \(O_w(YM(H))=o(YH)\) to the sum
of absolute values over the offsets in (5). No exceptional character is
dropped. For bounded \(H\), the characters belong to one fixed finite set.
The Vinogradov–Korobov region at fixed modulus gives \(1-\beta\ge g_X\)
for their zeros up to height \(T\), where \(g_X\log X\to\infty\);
any fixed exceptional real zero is harmless. For example, see the
zero-free-region statement before Corollary 1.4 of
[Chen–Gupta–Li](https://arxiv.org/html/2507.08296v2).
The integral in (3), restricted to these characters, can then stop
at \(1-g_X\), at cost \(O(X^{-(1-b_h)g_X})=o(1)\) including its lower
endpoint term. This yields the same resulting mean bound also for bounded
\(H\). Together the two arguments cover arbitrary sequences of \(H\).

To remove the smoothing, use the prime number theorem in intervals of
length a fixed positive multiple of \(Y\). This follows from
[Guth–Maynard, Corollary 1.3](https://arxiv.org/abs/2405.20552) when that
length is within its upper cut-off. For longer intervals partition at
any fixed exponent strictly between \(17/30\) and \(\min(\theta,0.99)\);
the final shorter piece is negligible even with a trivial bound.
This works for the full window and any fixed-width boundary strips in the
scaled variable. Prime powers contribute \(O(\sqrt X(\log X)^2)=o(Y)\)
per offset. Replace \(\log p\) by \(\log X+O(1)\), using the prime count
in the support. Approximate the interval indicator by smooth weights
equal to it away from boundary strips of relative width \(\xi\); their
total prime contribution is \(O(\xi Y/\log X)\) per character, as an
asymptotic with \(\xi\) fixed, then let \(\xi\downarrow0\). We obtain
\[
 \sum_{r=2}^H\left|\sum_{X<p\le X+Y}\chi_r(p)\right|
                       =o(HY/\log X).
 \tag{6}
\]

## 3. Unions, endpoint and least offset

The window for \(p=n+r\) is shifted by \(r\), which changes at most
\(O(H^2)\) terms in total. By (6), nonvanishing, and the short-interval
prime number theorem, the number of witnessing pairs \((n,r)\) is
\((1+o(1))(H-1)Y/(2\log X)\) for the strict coefficient.

For two offsets with difference \(h>0\), the dimension-two upper-bound
sieve bounds the count of underlying prime pairs by
\[
 \ll_\theta \frac{Y}{(\log X)^2}
          \prod_{\substack{\ell\mid h\\\ell>2\ {\rm prime}}}
                      \left(1+\frac1{\ell-2}\right).
\]
For odd \(h\) the count is zero. For even \(h\), use the divisibility
count \(Y\nu(d)/d+O(\nu(d))\) for the product of two linear forms,
where \(\nu(\ell)=1\) if \(\ell\mid h\), and 2 otherwise. The
dimension-two sieve and uniform convergence of the local correction
away from \(\ell=2\) are as in the dyadic note, with level \(Y^{1/2}\)
and prime cutoff \(Y^{1/20}\) in
[Koukoulopoulos, Theorem 19.1](https://dms.umontreal.ca/~koukoulo/documents/publications/primes.pdf).
The error is \(O(Y^{1/2}\log Y)\), and \(\log Y=\theta\log X\).
The displayed product has bounded mean over \(h\le H\): expand into
divisors and use the convergent product \(\prod_{\ell>2}(1+1/(\ell(\ell-2)))\).
There are at most \(H\) pairs of offsets per difference. The total
overlap is thus \(O_\theta(YH^2/(\log X)^2)\), of smaller order than
the main term. The first two Bonferroni inequalities prove the claimed
asymptotic for the strict coefficient.

For the limiting endpoint, truncate \(H\) at
\(\lfloor(1-\xi)c_\theta\log X/\log\log X\rfloor\) for fixed \(0<\xi<1\).
If this changes \(H\), the difference is at most \((\xi+o(1))H\), and
each lost offset has at most \(O(Y/\log X)\) candidate primes, uniformly.
Letting \(\xi\) tend to zero after \(X\to\infty\) proves the full range.
The upper sieve bound did not depend on the truncation. Finally,
for \(0<u\le1\), the proportion with least offset at most \(uH\) is
\(W_\theta(X,\lfloor uH\rfloor)/W_\theta(X,H)\to u\); at \(u=0\) it
is zero.

If one uses only the near-one estimate (1.8) explicitly numbered in
Jutila's Theorem 1, instead of the stronger p. 54 refinement, the same
proof gives the conservative coefficient
\(\min(\theta-17/30,(2\theta-1)/4)\). Neither statement asserts
optimality of the coefficient, that every nonsolution has a nearby
witness, or that the original Brocard equation is solved.
