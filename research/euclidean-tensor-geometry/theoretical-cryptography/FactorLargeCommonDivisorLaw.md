# The large common-divisor law for two shifted primes

**Scope.** An unconditional distribution theorem for the factors of a uniformly sampled product of two distinct primes from one dyadic interval. It does not provide a procedure for recovering factors from a given integer.

Let $X>2$ and draw $p,q$ uniformly as an ordered pair of distinct primes in $(X,2X]$. Write $G_X=\gcd(p-1,q-1)$. Using unordered pairs or their products gives the same law. Define $G_*$ by taking independent prime valuations, with
$$
\Pr(\nu_\ell(G_*)\ge j)=\frac1{\varphi(\ell^j)^2}\qquad(j\ge1).
$$
These specify a finite positive integer almost surely: every exponent is finite almost surely, and $\sum_\ell(\ell-1)^{-2}<\infty$. In particular, $\Pr(d\mid G_*)=\varphi(d)^{-2}$ for every $d$.

## Result

For every fixed $A>0$ there is $B=B(A)>0$ such that, uniformly for real $1\le L\le \sqrt X/(\log X)^B$,
$$
\sum_{d\ge L}\big|\Pr(G_X=d)-\Pr(G_*=d)\big|
\ll_A \frac1{L(\log X)^A}. \tag{1}
$$
Thus the approximation remains valid **relative to the mass of the rare event**, not merely in absolute total variation. It holds in particular throughout $1\le L\le X^{1/2-\varepsilon}$ for fixed $\varepsilon>0$ and sufficiently large $X$. There is an explicit tail constant
$$
C=\prod_\ell\left(1+\frac1{\ell(\ell-1)}\right)
 =\frac{\zeta(2)\zeta(3)}{\zeta(6)}
$$
and, on the same range,
$$
\Pr(G_X\ge L)
=\frac{C}{L}
 +O\!\left(\frac{\log^2(2L)}{L^2}\right)
 +O_A\!\left(\frac1{L(\log X)^A}\right). \tag{2}
$$
On conditioning on $G_X\ge L$ and $G_*\ge L$ respectively, the two integer-valued laws differ by $O_A((\log X)^{-A})$ in total variation. In particular, when $L=L(X)\to\infty$ in the stated range, $G_X/L$ given $G_X\ge L$ converges to the Pareto law with survivor function $1/u$ for $u\ge1$. For the same range the statements also hold if the two primes are independently sampled **with** replacement: the coupling gives total variation at most $1/M$, where $M$ is the number of available primes.

## Proof of the weighted comparison

Throughout, $\varphi$ is Euler's totient, $\tau$ the divisor-counting function, and $\mu$ the Möbius function. For $U\ge2$, we use the elementary bounds
$$
\sum_{t\le U}\frac{\tau(t)}{\varphi(t)}\ll \log^2(2U),\quad
\sum_{t\le U}\frac{\tau(t)^2}{\varphi(t)}\ll\log^4(2U),\quad
\sum_{t>U}\frac{\tau(t)}{\varphi(t)^2}\ll\frac{\log^2(2U)}{U}. \tag{3}
$$
For the first two, the truncated sums are bounded by Euler products over $\ell\le U$ with factors $1+2/\ell+O(\ell^{-2})$ and $1+4/\ell+O(\ell^{-2})$, respectively. For the third, the Euler product for $\sum_{t\le V}\tau(t)(t/\varphi(t))^2/t$ is likewise bounded by $O(\log^2(2V))$. On each interval $(V,2V]$ one extra factor $1/t\le1/V$ gives the third bound after summing dyadically. These estimates use Mertens' bound $\prod_{\ell\le U}(1-1/\ell)^{-1}\ll\log(2U)$, which also gives $1/\varphi(t)\ll \log(2t)/t$.

The exact identity $\Pr(G=d)=\sum_{k\ge1}\mu(k)\Pr(dk\mid G)$ follows from Möbius inversion, with absolute convergence here by (3) or finite support. Summing the difference over $d\ge L$ and then using at most $\tau(t)$ divisors for each $t=dk$ bounds the left side of (1) by
$$
\sum_{t\ge L}\tau(t)\left|\Pr(t\mid G_X)-\frac1{\varphi(t)^2}\right|. \tag{4}
$$

Write $M=\pi(2X)-\pi(X)\asymp X/\log X$ and $n_t=\pi(2X;t,1)-\pi(X;t,1)$, so that
$$
P_t:=\Pr(t\mid G_X)=\frac{n_t(n_t-1)}{M(M-1)}.
$$
Put $Y=\sqrt X/(\log X)^b$ for $b$ chosen below. For $t\le X^{3/4}$, Brun–Titchmarsh on $(X,2X]$ gives $n_t/M\ll1/\varphi(t)$ and $P_t\ll1/\varphi(t)^2$. For $X^{3/4}<t\le X$, the trivial bound $n_t\le 1+X/t$ gives $P_t\ll(\log X)^2/t^2$. For $t>X$, $P_t=0$: $t$ would otherwise divide a nonzero $p-q$ of absolute value $<X$. Using (3) and $\varphi(t)\le t$, the portion of (4) with $t>Y$ is therefore
$$
\ll\frac{(\log X)^2}{Y}+\frac{(\log X)^4}{X^{3/4}}. \tag{5}
$$

For $t\le Y$, set $E_t=|n_t-M/\varphi(t)|$. In this range $E_t\ll M/\varphi(t)$ by the same Brun–Titchmarsh bound. For any $D>0$, choose $b=b(D)$ by Bombieri–Vinogradov to have
$$
\sum_{t\le Y} E_t\ll_D X/(\log X)^D. \tag{6}
$$
Indeed, apply the prime-counting form to each endpoint $X,2X$ (reducing the available level by a fixed factor if necessary), and replace the logarithmic-integral main term by $M$ using the prime number theorem with arbitrary logarithmic saving and $\sum_{t\le Y}1/\varphi(t)\ll\log(2Y)$.

Since $P_t-(n_t/M)^2=-\frac{(n_t/M)(1-n_t/M)}{M-1}$, for $t\le Y$ we get
$$
\left|P_t-\varphi(t)^{-2}\right|
 \ll \frac{E_t}{M\varphi(t)}+\frac{1}{M\varphi(t)}.
$$
The second term summed against $\tau(t)$ is $O((\log X)^2/M)$. For the first, use $1/\varphi(t)\ll \log(2X)/L$ for $t\ge L$ and then Cauchy–Schwarz:
$$
\begin{aligned}
\sum_{t\le Y}\tau(t)E_t
 &\le \left(\sum_{t\le Y}E_t\right)^{1/2}
       \left(\sum_{t\le Y}\tau(t)^2 E_t\right)^{1/2}\\
 &\ll_D \left(X/(\log X)^D\right)^{1/2}
              \left(M(\log X)^4\right)^{1/2}.
\end{aligned}
$$
Multiplication by $\log(2X)/(LM)$ gives $O_A(1/(L(\log X)^A))$ on taking $D>2A+7$. The correction for distinct sampling is negligible in the stated range. Finally, $B>b+A+2$ absorbs (5) into the same estimate. This proves (1).

## Tail of the Euler-product model

For odd $\ell$, the probability of valuation zero is $c_\ell=1-(\ell-1)^{-2}$, and for any prime $\ell$ and $j\ge1$ the exact valuation probability is $(\ell+1)\ell^{-2j}/(\ell-1)$. The valuation at $2$ is positive. Let $C_0=\prod_{\ell\ge3}c_\ell>0$. Thus the model is supported on the even integers, with mass
$$
\Pr(G_*=d)=\frac{3C_0}{d^2}
  \prod_{\substack{\ell\mid d\\\ell\ge3}}(1+\beta_\ell),\qquad
\beta_\ell=\frac{2\ell-1}{\ell(\ell-2)}.
$$
Write $\beta(a)=\prod_{\ell\mid a}\beta_\ell$ on odd squarefree $a$ and zero otherwise, with $\beta(1)=1$. The product over primes dividing $d$ is $\sum_{a\mid d}\beta(a)$. For $V\ge2$ one has $\sum_{a\le V}\beta(a)\ll\log^2(2V)$ by the Euler product as $\beta_\ell=2/\ell+O(\ell^{-2})$, hence $\sum_{a>V}\beta(a)/a\ll\log^2(2V)/V$. Since all $a$ here are odd, the number of even multiples of $a$ up to $V$ is $\lfloor V/(2a)\rfloor$. Consequently,
$$
\sum_{d\le V}d^2\Pr(G_*=d)
 =V\,\frac{3C_0}{2}\prod_{\ell\ge3}(1+\beta_\ell/\ell)+O(\log^2(2V))
 =CV+O(\log^2(2V)).
$$
The last equality uses $c_\ell(1+\beta_\ell/\ell)=1+1/(\ell(\ell-1))$, the factor $3/2$ at $2$, and
$(1-\ell^{-6})/((1-\ell^{-2})(1-\ell^{-3}))=1+1/(\ell(\ell-1))$. Partial summation gives model tail $C/L+O(\log^2(2L)/L^2)$; the convention $\ge L$ instead of $>L$ is immaterial in that error, by applying the formula for the strict tail at $\lceil L\rceil-1$ (or bounding the small thresholds separately). The model tail is bounded below by $c/L$ uniformly, from this asymptotic and positivity at every finite threshold. Normalizing (1) therefore gives the claimed conditional total variation and limiting law.

An integrated consequence for any fixed $0<\theta<1/2$ is
$$
\mathbb E\min(G_X,\lfloor X^\theta\rfloor)=C\theta\log X+B_*+o(1),\qquad
B_* = C\gamma_{\rm E}+\sum_{k\ge1}\big(\Pr(G_*\ge k)-C/k\big).
$$
Here $\gamma_{\rm E}$ is Euler's constant. This follows by summing the tail errors in (1) with $A>1$, and using the summability of $\log^2(2k)/k^2$. It does not estimate the contribution beyond the proven cutoff to the untruncated first moment.

## Comparison and verification

- [Vishnoi, *GCD of p−1, q−1 for Random p, q*, Theorem 3.1](https://repository.gatech.edu/bitstreams/45c41db8-3355-45d1-909a-21d433282ff3/download) gives a finite upper bound for primes sampled up to an endpoint. [Dieulefait and Jiménez Urroz, *Small primitive roots and malleability of RSA moduli*, preprint Proposition 2](https://arxiv.org/abs/0801.0030) and [Luca, Ralaivaosaona and Jiménez Urroz, *On pseudoprime RSA moduli*, proof of Theorem 2.1](https://doi.org/10.1007/s13370-025-01338-1) use upper estimates for large common divisors. In the balanced range of (1), this note gives the leading constant and controls the conditional distribution, not merely its tail order.
- [Fan and Pomerance, *Shifted-prime divisors*](https://arxiv.org/abs/2401.10427) study weighted least-common-multiple sums and select pairs of shifted primes with large common divisors. Equation (1) concerns the frequency and full tail distribution for uniform pairs.
- The analytic inputs are [Bombieri, *On the large sieve*](https://doi.org/10.1112/S0025579300005313) and [Montgomery and Vaughan, *The large sieve*](https://doi.org/10.1112/S0025579300004708). In particular, no independence assertion is assumed for prime progressions with moduli in the estimated range.
- The [small exact checker](verify_factor_common_divisor_law.js) verifies the counting, inversion and Euler-factor identities on fixed toy data. It does not verify the analytic estimates or perform integer factorization.
