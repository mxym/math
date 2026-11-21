# An absolutely localizable odd-composite detector for the true reflected prime pair

All bounds are unconditional and pointwise in the even integer \(P\).
Put \(L=\log P,\ I=[P/3,2P/3],\ X=P/3,\ r=P-n\) and let
\[
 S(P)=2\prod_{\ell>2}(1-(\ell-1)^{-2})
       \prod_{\ell\mid P,\ \ell>2}\frac{\ell-1}{\ell-2}
\]
(the products here and below indexed by \(\ell\) are over primes).
Write \(V(n)=1_{n\ {\rm prime}}\log n\), and
\(G=\sum_{n\in I}V(n)V(r)\). Use a fixed smooth real function \(f\)
of compact support on the real line which on \([0,1]\) is nonincreasing,
is 1 through .49, is 0 from .51 on, and satisfies
\(f(v)+f(1-v)=1\). For example convolve the step \(1_{v\le1/2}\)
with an even smooth probability bump supported on \((-.01,.01)\), then
multiply by a compact smooth cutoff which is identically one on \([0,1]\).
The values at negative arguments only serve Fourier inversion. Define
\[
 U(n)=\log n\sum_{d\mid n}\mu(d)f(\log d/\log n),\qquad
 J(n)=(V(n)-U(n))/2 .                                             \tag{1}
\]
There is **no rank, roughness or target-unit assumption** in (1).

**Theorem.** For \(0<\theta<1,\ b>1,\ 0<\alpha<1/3,\ K\ge1\), put
\[
 {\cal A}=\{n\in I :\ n\text{ squarefree},\ (n,P)=1,\
  P^-(n)>P^\alpha,\ 3\le\omega(n)\le K,\ \omega(n)\text{ odd},
       \ P^+(n)<n^{.51}\}.
\]
For fixed \(\alpha,K\), uniformly along the even targets,
\[
 \frac{G}{4}=\sum_{n\in I}V(n)J(r)1_{\mathcal A}(r)
       -\sum_{n\in I}J(n)1_{\mathcal A}(n)J(r)1_{\mathcal A}(r)
       +O_{f,\theta,b}\big(XS(P)(\alpha^{1-\theta}+b^{-K})\big)
       +o_{f,\alpha}\big(XS(P)\big).                              \tag{2}
\]
The roughness/rank error bounds below are estimates of **total variation
on the discarded physical pairs**. Thus the discarded part remains
small with any multiplier of modulus at most 1, including a coupled
selector depending on both sets of prime factors. The short–short
evaluation in the proof, and hence (2) itself, is *unmasked*. The
constants are not numerical at fixed moderate \(\alpha,K\). For each
fixed \(b>1\) the rank estimate is \(O_{f,b}(b^{-K})\), not uniformly
in \(b\). After normalization one can first choose \(\alpha,K\) for
a desired error and then pass to large \(P\).

## 1. Algebra on the actual integer

A prime has \(U(n)=\log n,\ J(n)=0\) exactly. For squarefree composite
\(n\) of even rank, its complementary divisors have equal Möbius signs.
The cutoff symmetry yields \(U(n)=\tfrac12\log n\sum_{d\mid n}\mu(d)=0\).
For every composite \(n\) with \(p=P^+(n)\ge n^{.51}\), including
nonsquarefree ones, all squarefree divisors containing \(p\) have
zero cutoff; all those without \(p\) divide \(n/p\le n^{.49}\) and
have cutoff one. Here \(p\) occurs once and \(n/p>1\), so \(U(n)=0\).
The raw reflected identity, before estimates, is
\[
 G=4\sum_{n\in I}(V(n)J(r)-J(n)J(r))+\sum_{n\in I}U(n)U(r).
                                                                    \tag{3}
\]
This uses the symmetry of \(I\) under reflection and does not replace
the actual covariance by a product of means.

## 2. An absolute physical two-form estimate

Use the Fourier convention
\(\widehat F(t)=\int F(v)e^{-itv}\,dv\) with inverse measure \(dt/(2\pi)\).
Set \(g_t(p^\nu)=\min(2,|t|\log p/L)\) for \(\nu\ge1\), extending
multiplicatively on coprime arguments. The finite Fourier multiplier
for the weighted squarefree divisors of \(n\) is exactly
\(\prod_{p\mid n}(1-e^{it\log p/L})\); its modulus is \(\le g_t(n)\).
For \(\theta\in(0,1]\), \(b\ge1\) let the multiplicative envelope
\(h_t(p^\nu)=b\,2^{1-\theta}g_t(p^\nu)^\theta\). We use the uniform
two-form estimate (one may choose different fixed parameters on either side)
\[
 \sum_{n\in I}h_t(n)h_w(P-n)
 \ll_{\theta,b} {XS(P)\over L^2}(2+|t|+|w|)^{C_{\theta,b}}.         \tag{4}
\]
Here and below adding/removing an endpoint in applying an interval theorem
costs \(P^{o(1)}\), uniformly in \(t,w\).

For rigor apply [Henriot, Theorem 5](https://arxiv.org/pdf/1102.1643)
in the [corrected version, p. 377](https://doi.org/10.1017/S0305004114000280),
with \(Q_1(T)=T,\ Q_2(T)=P-T,\ Q=Q_1Q_2,\ x=y=P/3\), interval and
coefficient-height exponents \(1/2,1/2\). Both polynomials are primitive,
the degree of the product is 2 and \(\|Q\|=O(P)\). The nonnegative
two-variable product lies in the required growth class uniformly in
\(t,w,P\): each local coprime multiplier is bounded by \(2b\) per
distinct prime on either side; \((2b)^{\omega(m)}\ll_{\delta,b}m^\delta\)
for every fixed small theorem exponent \(\delta>0\), and the exponential
bound in the big prime-factor count is automatic. The zero case of a
multiplicative weight causes no problem in the defining coprime inequality.

The sieve product from the theorem is \(\prod_{2<p\le x}
 (1-(2-1_{p\mid P})/p)\asymp S(P)/L^2\) by Mertens; factors at
\(p\mid P,\ p>x\) alter this by bounded factors (and there are \(O(1)\)
of them). For clarity use the raw sum in corrected Theorem 5, not
a crude loss \(\prod_{p\mid P}(1+C/p)\) on top of this product.
Bound its nonnegative sum by the product of its unrestricted local
series at \(p\le x\). Let \(A=h_t(p),B=h_w(p)\). The local density for
exponents \(i,j\) is at most \(p^{-\max(i,j)}\) if \(i+j>0\):
one of \(p^i\mid n,\ p^j\mid P-n\) already forces this, and the
corrected starred/exact divisibility restrictions can only decrease
the density. This bound is valid at **every** \(p\), including
\(p\mid P\) to arbitrary multiplicity. Since \(A,B\) are constant on
positive powers, the series is at most
\[
 1+\frac{A+B}{p-1}+AB\sum_{k\ge1}(2k-1)p^{-k}
 \le 1+O((A+B+AB)/p).
\]
In particular shared small target primes are priced with the small
factors \(A,B\), not a constant at every such prime. Uniformly
\(\sum_{p\le P} g_t(p)^\theta/p\ll_\theta 1+\log(2+|t|)\).
Indeed with \(T=2+|t|\) split at \(Y=P^{1/T}\); below \(Y\),
partial summation of the Chebyshev upper bound gives
\(\sum_{p\le Y}(\log p)^\theta/p\ll_\theta(\log Y)^\theta\);
above \(Y\) use Mertens, with cost \(O(1+\log T)\), also when \(Y<2\).
As \(A,B\le 2b\), exponentiation proves (4). No zero-free
hypothesis or conjecture on the reflected forms is used.

For \(a=\log n/L\), write \(F_a(v)=a f(v/a)\) so that \(U(n)/L\)
uses \(F_a(\log d/L)\). The \(F_a\)'s are in one bounded Schwartz
family for \(n\in I\); their Fourier envelopes are \(O_{m,f}((1+|t|)^{-m})\)
for every \(m\). Moreover \(F_a-f\) has the same seminorm bounds
times \(O_f(1/L)\), by the mean-value theorem in \(a=1+O(1/L)\).
In each physical pair the kernels may therefore depend on its actual
\(n,r\); absolute Fourier inversion and (4) still apply using these
*uniform* envelopes. On central primes \(V/L\le g_2\); on other inputs
it is zero.

On \(P^-(n)\le P^\alpha\) there is the pointwise estimate
\(g_t(n)\le (|t|\alpha/2)^{1-\theta}h_t(n)\) with \(b=1\):
the ratio at every prime is \((g_t(p)/2)^{1-\theta}\le1\) and at
a smallest prime use \(g_t(p)\le |t|\alpha\). For zero frequency the
statement follows directly. On \(\omega(n)>K\) use
\(g_t(n)\le b^{-K}h_t(n)\) with \(\theta=1\). Combine with (4) and
the Schwartz envelopes, and take the union on either reflected input.
For \(T(n)=|U(n)|+V(n)\) this gives
\[
 \sum_{\substack{n\in I:\ \min(P^-(n),P^-(r))\le P^\alpha\\
                   \text{or }\max(\omega(n),\omega(r))>K}}
       T(n)T(r)
 \ll_{f,\theta,b} XS(P)(\alpha^{1-\theta}+b^{-K}).                 \tag{5}
\]
The same argument without restricting pairs gives \(\sum T(n)T(r)\ll_f XS(P)\).
On the remaining \(P^\alpha\)-rough inputs any square divisor \(p^2>1\)
with \(p>P^\alpha\) occurs on at most \(O(P^{1-\alpha}+\sqrt P)\)
inputs in all; a target prime \(p\mid P,\ p>P^\alpha\) occurs on
\(O(P^{1-\alpha}L+L)\). Thus these exceptions have physical absolute
weight \(o_\alpha(XS(P))\), using \(T(n)T(r)\le P^{o(1)}\).
Since \(|J|\le T/2\), (5) applies to the errors in (2).

## 3. The unmasked short–short reference really vanishes

Let \(D(n)=L\sum_{d\mid n}\mu(d) f(\log d/L)\). The small seminorm
bound for \(F_a-f\), (4), and two applications of Fourier inversion
give
\[
 \sum_{n\in I} \big|U(n)U(r)-D(n)D(r)\big|\ll_f XS(P)/L.           \tag{6}
\]
The actual parity symmetry and the prime atom in section 1 used
\(\log n\), **not** the replacement cutoff in \(D\).

We prove \(\sum_{n\in I}D(n)D(r)\ll_{A,f}PL^{-A}\) for each fixed \(A\).
Use a smooth central window \(W(n/P)\), supported on \(I/P\), equal to
one except in strips of width \(L^{-M}\) at the two ends; fixed derivatives
are \(O_{j,M}(L^{jM})\) and total variation \(O(1)\). The global physical
error, before expanding gcds, is \(O(PL^{10-M/2})\), choosing \(M\)
large: Cauchy on the strips, followed by Cauchy and
\(\sum_{m\le P}\tau(m)^4\ll PL^{15}\). In the smooth divisor expansion,
\(g=(d,e)\) divides \(P\). For \(g>P^{.001}\), the absolute contribution
is \(O(P^{.999+o(1)})\): for \(g\mid P\) require \(g\mid n\), use at most
\(O(P/g)\) physical choices and \(L^2\tau(n)\tau(r)\le P^{o(1)}\), then
sum over \(\tau(P)=P^{o(1)}\) choices.

For fixed smaller squarefree \(g\), put \(Y=P/g,\ d=gd',\ e=ge'\),
\(n=gk,\ r=g(Y-k)\). Nonzero coefficients require \((d'e',g)=1\);
the gcd decomposition requires \((d',e')=1\). The signed coefficient
is the product of \(\mu(d')f(\log(gd')/L)1_{(d',g)=1}\) and its counterpart
in \(e'\), times \(L^2\mu(g)^2\). Each length is at most
\(P^{.51}/g\le Y^{.51}\). In the \(k\) sum impose \(d'\mid k\) and
\(e'\mid Y-k\). Smooth Poisson at this *actual* target gives
\[
 \frac{Y}{d'e'}\sum_{h\in\mathbb Z}
        \widehat W(hY/(d'e'))\,e(hY\overline{d'}/e')
\]
with \(e(t)=e^{2\pi it}\) and the corresponding \(2\pi\)-Fourier convention
for \(W\). No coprimality of \(Y\) and \(d'e'\) is required, since \(d'\)
is inverted modulo \(e'\). Dyadize \(d',e'\sim B,C\). The sum of the
nonzero modes with these independent 1-bounded sequences and fixed \(g\)
is \(O(Y^{1-c})\) for some absolute \(c>0\) (absorbing logs and the
external \(L^2\)). Here are the three regimes for this application of
[Bettin–Chandee, Theorem 1](https://arxiv.org/pdf/1502.00769):

* \(BC<Y^{.99}\): per compatible pair the discrepancy from the zeroth
  frequency is \(O(1)\) by bounded variation.
* \(Y^{.99}\le BC<Y\): use frequency dyads \(h\sim H\ge1\) and smooth
  decay in \(H/(BC/Y)\) to absorb the prefactor \(Y/(BC)\) and the
  spectral factor \((1+YH/(BC))^{1/2}\). Mellin separation of
  \(\widehat W(\pm hY/(d'e'))\) costs only fixed log powers times any
  required frequency decay. At frequency length 1 the two remaining
  powers are \((BC)^{.85}(B+C)^{.25}\),
  \((BC)^{.875}(B+C)^{.125}\) apart from \(Y^{o(1)}\), by the trilinear
  theorem. These are \(\ll Y^{.978+o(1)},Y^{.939+o(1)}\).
* \(BC\ge Y\): use the [complete Poisson/Mellin calculation](../PanSupercriticalShoulder.md),
  with \(Y\) in place of its target and numerator \(\pm Y\). For
  \(s=\log_Y\max(B,C), w=\log_Y\min(B,C)\), the ratios to \(Y\)
  have exponents at most \([19s+14w-17]/20\) and \([8s+7w-8]/8\),
  up to arbitrarily small positive slack. Both are strictly negative
  since \(s,w\le .51+o(1)\).

Sum \(O(L^2)\) dyads and the \(\le\tau(P)\) target gcds; the error
has a fixed power saving (as \(Y\ge P^{.999}\)). For the zero
frequency it remains to bound
\[
  P\widehat W(0)L^2\!
  \sum_{\substack{g\mid P\\g\le P^{.001}}}\frac{\mu(g)^2}{g}
  \sum_{(d',g)=1}\frac{\mu(d')f(\log(gd')/L)}{d'}
  \sum_{(e',gd')=1}\frac{\mu(e')f(\log(ge')/L)}{e'}.                \tag{7}
\]
The last harmonic sum is \(O_{J,f}(L^{-J})\) for every fixed \(J\):
average cutoffs \(e'\le P^v/g,\ .49\le v\le .51\), against \(-f'(v)dv\).
These cutoffs are all \(\ge P^{.489}\). Uniformly for \(P^{.489}\le Z\le P\)
and \(h\le P\),
\(\sum_{e\le Z,(e,h)=1}\mu(e)/e\ll_J L^{-J}\).
Indeed convolve \(\mu\) with the indicator of integers supported on the
primes of \(h\). Up to \(\sqrt Z\) the inner sum is \(O_J(L^{-J-2})\)
by the classical unconditional PNT error and partial summation
(\(\sum_{n\ge1}\mu(n)/n=0\)); the outer reciprocal mass costs
\(h/\phi(h)\ll\log\log(3P)\). Above \(\sqrt Z\), use the trivial inner
bound \(O(L)\) and Rankin with \(1/\log L\): the remaining reciprocal
mass is at most \(Z^{-1/(2\log L)}\prod_{p\mid h}(1-p^{-1+1/\log L})^{-1}\).
The product is at most a fixed power of \(\log L\), splitting \(p\le L\)
and \(p>L\) (separately handle bounded \(p\)); this gives any log saving.
Here \(h=gd'\le P^{.51}\) on support. Finally
\(\sum_{d'\ll P^{.51}}1/d'\ll L\), and
\(\sum_{g\mid P}\mu(g)^2/g\le P/\phi(P)\ll\log\log(3P)\).
This proves the reference claim. Combining (3), (5), (6), (7)
establishes (2).

## What is still missing

For \(n=p_1p_2p_3\) squarefree and \(x_i=\log p_i/\log n\), one has
\(J(n)/\log n=\sum_i f(x_i)-2\ge0\). If at most one \(x_i>.49\)
this follows from the plateau; if two exceed .49 the third is below
.02 and \(x_i+x_j<1\) implies \(f(x_i)+f(x_j)\ge1\).
It equals one on balanced triprimes with all factors below \(n^{.49}\).
On balanced rank-five profiles near \(x_i=1/5\), the empty set,
singletons and pairs are precisely the subsets below .49, giving
\(J(n)/\log n=-3\). Thus even the smooth, bounded-rank,
two-sided polynomially rough remainder has a genuine mixed sign:
for example two balanced triprimes contribute with the opposite
sign from a prime and a balanced triprime. No lower bound comparing
those **actual fixed-target populations** is proved. In particular
(2) neither establishes \(G>0\) nor evaluates this remaining sum.

Smooth Möbius divisor weights and Fourier factorization are established
techniques (see [Goldston–Yıldırım](https://arxiv.org/abs/math/0111212)
and [Tao's smooth divisor sums](https://terrytao.wordpress.com/2015/01/21/254a-notes-4-some-sieve-theory/)).
Also relevant are the [October 2026 follow-up collection](https://github.com/aster2024/openai-math-followups)
using soft almost-prime weights and discussing subpower rough Liouville
signs, and the [sharp-cut reflected parity transfer](../PanCriticalParityTransfer.md).
We use their related topics for comparison, not as analytic inputs.
Here the features needed together are the exactly preserved prime,
exact even-composite cancellation, a zero unmasked short–short reference
at a slightly supercritical half cutoff, and **absolute two-form**
roughness/rank truncation in the uncentered criterion.

**Dated comparison through November 21, 2026.** [Pham, October 30 v1](https://www.preprints.org/manuscript/202610.3061) studies smooth/rough comparison weights, a balanced rough-pair benchmark and separate signed boundary correlations. Its rough-pair comparison is not the unmasked signed short–short evaluation or the joint absolute tail bound in (2). The Guo October 9 project description concerns subpower roughness and specified Liouville signs, not the prime atom retained here; the linked full manuscript was inaccessible and is not used. No priority claim is made for the general Fourier or sieve inputs.
