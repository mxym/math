# A flat upper cap removes every giant rank from the composite prime-column proxy

This note applies to the [full endpoint composite proxy](../full_endpoint_composite_proxy/Proof.md)
on the same physical two-tag family. Its added branch is a **zero-mean**
one-free-variable sum. It leaves the centered covariance unchanged to
arbitrary logarithmic accuracy, but exactly zeroes the new proxy on
all sufficiently giant physical integers. It does not justify deleting
the old score term-by-term on just that subpopulation.

Let \(x,N=2x,L,\ell,z,T,T^\sharp,K,F_U\) be as in the endpoint
proof, so \(T^\sharp(s)=\max(T(s),x^{.505})\) and
\[
 F_U(y)=-R_z(y)
       \sum_{\substack{sca=y,\ ca>x^{.505}\\a>U(s)}}\mu_2(c)\log s,
 \quad
 R_z(y)=1_{P^-(y)>z},\quad \mu_2=\mu*\mu.
\]
For a fixed \(.505\le\theta<.80\), put
\[
 T_\theta(s)=\min\{T^\sharp(s),x^\theta\},\qquad
 D_\theta(y)=F_{T_\theta}(y)-F_{T^\sharp}(y),\qquad
 R_\theta(y)=K(y)-F_{T_\theta}(y).
\]
Thus \(R_\theta=R^\sharp-D_\theta\), in contrast to the sign of the
preceding full floor lift.

**Theorem.** For fixed \(\theta,\delta,A>0\) in the indicated range,
every \(2\le Q\le x^{\theta-\delta}\), every reduced class \(j\bmod Q\),
and every \(J\subseteq[x,3x/2]\) one has
\[
  \sum_{\substack{y\in J\\y\equiv j\bmod Q}} D_\theta(y)
                    =O_{\theta,\delta,A}((x/Q)L^{-A}).              \tag{1}
\]
(The effect is empty when the original threshold never exceeds the cap.)
The estimate does not need factored \(Q\) or an average over it.
On every physical \(y\in[x,3x/2]\) with a genuine prime factor
\[
                             P^+(y)>x^\theta                      \tag{2}
\]
one has \(R_\theta(y)=0\) exactly, without any squarefree or rank
restriction. Primes and squarefree semiprimes still have zero
score; squarefree triprimes still have nonnegative score, as do
all squarefree rank-four integers with \(P^+(y)\le x^{.505}\).

In the physical two-tag family take \(\theta=.611\), since every
actual \(Q=kp_2p_3\) is at most \(x^{.6092}\) for large \(x\).
Then the arbitrary opposite-row transfer and the corrected
variance formula of the endpoint proof hold with \(R_\theta\)
in place of \(R^\sharp\). The **remaining possible negative
squarefree rank-four range** is exactly narrowed to
\[
                         x^{.505}<P^+(y)\le x^{.611}               \tag{3}
\]
as a necessary condition (not a claim that all of (3) is negative).
There is no equality claim at \(P^+(y)=x^\theta\).

## 1. Exact branch and fixed-modulus elementary floor count

The old \(T\) is always bounded above by \(x^{.918}/s\).
For the two-piece minimum this is immediate, and on its
annulus \(s=x^\sigma,\ .13\le\sigma\le.32\), the exponent
difference is \(-.244+3\sigma/4\le-.004\).
On the only changed \(s\)'s, \(T^\sharp(s)>x^\theta\ge x^{.505}\)
and so \(T^\sharp(s)=T(s)\), \(sT^\sharp(s)\le x^{.918}\).
The changed support is therefore exactly
\[
 D_\theta(y)=-R_z(y)
 \sum_{\substack{sca=y,\ T^\sharp(s)>x^\theta\\
                 x^\theta<a\le T^\sharp(s)}}\mu_2(c)\log s.        \tag{4}
\]
Its \(ca>x^{.505}\) condition already follows from \(a>x^\theta\),
also when \(\theta=.505\). The \(s=1\) term is zero.
Every such \(sc\) is at most \(1.5x^{1-\theta}\).

Equation (4) is again a genuine finite Möbius free-branch
difference if that interpretation is desired. Use the same
five-term finite identity but truncate its short Möbius factors
at \(U=x^{.50}\) instead of \(x^{.24}\).
Now \(U^5>1.5x\), the added positive-log free \(a>x^\theta\)
is unique since \(a>\sqrt{y/s}\), and its complementary
\(c\le1.5x^{1-\theta}<U\). The convolution of the
remaining factors is exactly \(\mu_2(c)\) and the signed
slot coefficient is \(-1\), as before. All earlier
large-free branch formulas remain the same under this change
because their own \(c\)'s lay below the former truncation
as well. This change does not assume that a different
finite decomposition has the same unrestricted summands.

Fix \(s,c\) with \((sc,Q)=1\) and both rough.
The variable \(a\) runs in the exact real interval
\[
         \big(J/(sc)\big)\cap(x^\theta,T^\sharp(s)]
\]
and in the reduced class \(j\overline{sc}\bmod Q\).
Count rough \(a\) by a Bonferroni polynomial of degree
\(\lceil C\ell\rceil\); the next positive degree bounds the
absolute error. Each modulus factor \(m\) in these
polynomials is \(x^{o(1)}\). The factors not coprime to
\(Q\) contribute zero, and for the others the true integer
count differs from interval length divided by \(mQ\)
by at most one. No second free factor or smoothing of
the physical interval is needed. The main relative
sieve error is arbitrarily small in inverse log powers
because of the harmonic factorial tail
\((\sum_{p\le z}1/p)^J/J!\).
The total floor error in (4), even with the next-degree
terms, is at most
\[
 x^{o(1)}\!\!\sum_{sc\le1.5x^{1-\theta}}\!\!
       |\mu_2(c)|\log s\ \ll\ x^{1-\theta+o(1)} .
\]
This is a fixed power smaller than \(x/Q\)
for the stated \(Q\)-range. The main error bounds
sum with the harmonic weight \(1/(sc)\) and at
most fixed powers of \(L\).
The surviving exact free-slot density is \(W_z(Q)/Q\),
with \(W_z(Q)=\prod_{p\le z,\ p\nmid Q}(1-1/p)\).

Change \(a\) to \(y/(sc)\) in the remaining integral.
Its signed harmonic factor at each \(s,y\) is
\[
 \sum_{\substack{y/(s T^\sharp(s))\le c<y/(s x^\theta)\\
                         (c,Q)=1}}
                 \frac{\mu_2(c)R_z(c)}c.                          \tag{5}
\]
Both endpoints in (5) are at least \(y/x^{.918}\ge x^{.082}\)
and at most \(1.5x^{1-\theta}\); otherwise the annulus is
empty. Thus the uniform rough \(\mu_2/c\) Perron estimate
from the previous proofs applies to both prefixes separately,
with no nonzero endpoint residue. The remaining sum
over \(s\) against \(\log s/s\) costs \(O(L^2)\);
the length of \(J\) is at most \(x/2\).
This gives exactly the error in (1), including sharp real
endpoints. There is no modeled prime pair in this argument.

## 2. Physical signs and the unchanged covariance

Every admissible \(r=y/s>x^{.505}\) still qualifies as
\(a=r,c=1\): this was true for \(T^\sharp\), and
\(T_\theta\le T^\sharp\). Every \(T_\theta\) is at least
\(x^{.505}>\sqrt{1.5x}\) for sufficiently large \(x\).
These two facts are all that was used in the endpoint
rank signs. In particular a negative rank-four singleton
charge under \(P^+\le x^{.505}\) still forces its
partner pair to be admitted, and any other nontrivial
free factor in that pair would be an individual true
prime of size at most the floor and so cannot pass.
This reproduces the exact lower-rank claims.

For (2), let \(g=P^+(y)>x^\theta\).
It occurs once, since \(g^2>x^{1.01}>1.5x\).
Every admissible \(s\) excludes \(g\), because
\(s<y/x^{.505}\le1.5x^{.495}<g\).
Every divisor of \(r\) without \(g\) is at most
\(y/g<1.5x^{1-\theta}<x^{.505}\le T_\theta(s)\);
every divisor containing \(g\) is greater than
\(x^\theta\ge T_\theta(s)\).
Thus the included \(a\)'s are exactly those containing \(g\).
Their complementary \(c\)'s are the divisors of \(r/g\), and
\[
 \sum_{c\mid r/g}\mu_2(c)=\mu(r/g)=-\mu(r).
\]
This cancels the raw \(K\)-term at each \(s\), including
nonsquarefree nongiant cofactor cases. It proves (2).

On each tagged actual \(Q=kp_2p_3\) and its unit residue
\(N\bmod Q\), restore the physical \((y,N)=1\) mask as
in the endpoint proof: the removed true rough values have
a prime \(>z\) dividing \(N\). Their count is at most
\(O(xL/(Qz)+L)\); Shiu and Cauchy on the same affine progression
pay \(|D_\theta(y)|\ll L\tau_4(y)\).
No assumption that \(p_2p_3\) is coprime to the common \(k\)
is needed. Sum (1) over the actual tag primes with their
bounded reciprocal harmonic sum to get
\(\Gamma_{D_\theta}(k)=O_A(YL^{-A})\) for every unit \(k\)
in the two-tag case \(\theta=.611\).
Hence every occurrence of \(\Gamma_{R^\sharp}\) in the
preceding prime-column transfer and covariance can be
replaced by \(\Gamma_{R_\theta}\), with the same \(M(k)\)
and the same error. For the arbitrary opposite weights,
use the exact row-envelope and divisor-weight clipping
stated in that proof. Centering and the subtraction of
\(\sum_kM(k)^2\) are unchanged.

If only an untagged progression \(Q=k\asymp\sqrt x\) is
at issue, (1) permits \(\theta=.505\) with a fixed margin.
The remaining cutoff is then the constant \(x^{.505}\).
For squarefree \(y\), its residual has the exact algebraic
parity identity
\[
                      R_{.505}(y)=(1-\mu(y))K(y).
\]
Indeed for the constant cutoff
\(F_{T_{.505}}(y)=-R_z(y)\sum_{a\mid y,a>x^{.505}}(\mu_2*\log)(y/a)\).
The convolution \(\mu_2*\log=\mu*\Lambda\), and on a squarefree
\(b\), \((\mu*\Lambda)(b)=-\mu(b)\log b\), including \(b=1\).
Multiplying by \(\mu(y)=\mu(a)\mu(y/a)\) gives the formula.
This parity conclusion is algebraic; it does not
import the two-tag prime transfer into a different
untagged or one-tag geometry. For the original
two-tag problem the lower fixed exponent \(.505\)
does not yet satisfy the modulus rail of (1).

