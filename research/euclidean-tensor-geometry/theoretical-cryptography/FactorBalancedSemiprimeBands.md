# Counts of semiprimes in thin ratio and product bands

An almost-all theorem for primes in short intervals can count pairs of primes in a thin band without requiring every *prime-centered* interval to be typical. The transfer below smooths both coordinates, then uses the short section lengths of the band to preserve the relative size of the error. Applied with the Guth–Maynard short-interval scale, it extends the published near-diagonal range for products of two proportional primes.

## Results

Fix $R>1$ and let $1\le r_1<r_2\le R$. Write $\Delta=r_2-r_1$, and count distinct prime products with $r_1<q/p\le r_2$. The ordering $p<q$ means each product is counted once. Define
$$
I(a,b;r_1,r_2)
 =
 \iint_{\substack{t,v\ge2,\ a<tv\le b\\r_1<v/t\le r_2}}
 \frac{dt\,dv}{\log t\log v}.
$$
All logarithms are natural. For fixed $\epsilon,A>0$:

1. **Thin ratio band, cumulative product count.** Uniformly for $\Delta\ge x^{-13/30+\epsilon}$,
   $$
   \#\{pq\le x:r_1<q/p\le r_2\}
    = I(0,x;r_1,r_2)+O_{R,\epsilon,A}(\Delta x(\log x)^{-A}).
   \tag{1}
   $$
   In particular the leading term is $2x\log(r_2/r_1)/(\log x)^2$, with relative error $O_R(1/\log x)$. For $r_1=1$, Saad Eddin–Suzuki (2020), Theorem 3, gives the asymptotic in the range $r_2-1>x^{-5/12}$ up to $r_2\le3/2$. The new range extends this when $0<\epsilon<1/60$. The uniform thin-band statement is not obtained by subtracting two cumulative estimates with errors tied to their larger widths.
2. **Short product band, fixed ratio band.** For fixed $r_1,r_2$ and $x^{17/30+\epsilon}\le K\le x$, every sufficiently large real $x$ satisfies
   $$
   \#\{x<pq\le x+K:r_1<q/p\le r_2\}
    = I(x,x+K;r_1,r_2)+O_{R,\epsilon,A}(K(\log x)^{-A}).
   \tag{2}
   $$
   The leading term is $2K\log(r_2/r_1)/(\log x)^2$.
3. **Conditional product-band refinement.** Assume the Riemann hypothesis and keep $r_1,r_2$ fixed. Put $T=\sqrt x$ and $w=K/T$. Uniformly for $K\le x$ and $w/(\log T)^2\to\infty$, the left side of (2) equals
   $$
   I(x,x+K;r_1,r_2)
       +O_R\!\left(\frac{K}{(\log x)^2}
                    \left(\frac{(\log T)^2}{w}\right)^{1/3}\right).
   \tag{3}
   $$
   In particular there is an asymptotic when $K/(\sqrt x(\log x)^2)\to\infty$. This does not claim an asymptotic at a fixed multiple of $\sqrt x(\log x)^2$, any explicit small constant for a lower bound there, or an unconditional assertion at that length.

These are distribution theorems about a family of products. They do not give a method to recover the factors of a specified integer.

## The smoothing step

Let $X$ be a factor scale. Every coordinate being integrated is in $[cX,CX]$ for fixed $0<c<C$, and the fixed constants $c,C$ are chosen to include the boundary shifts as well. For $0<\eta<1$ put
$$
F_\eta(t)=\frac{\#\{p:t<p\le(1+\eta)t\}}{t\log(1+\eta)},\qquad L(t)=\frac1{\log t}.
$$
A prime $p$ contributes the kernel $\mathbf1_{p/(1+\eta)\le t<p}/(t\log(1+\eta))$, whose integral is exactly one. If the averaging rectangle for every prime pair in a region $\Omega$ lies in a region $\Omega^+$, and every averaging rectangle meeting $\Omega^-$ comes from a pair in $\Omega$, then
$$
\iint_{\Omega^-}F_\eta(t)F_\eta(v)\,dt\,dv
\ \le \#\{(p,q)\in\Omega\}\
\le \iint_{\Omega^+}F_\eta(t)F_\eta(v)\,dt\,dv.
\tag{4}
$$
This follows by expanding the nonnegative kernels and does not require a pointwise prime estimate. Boundary equalities of the integration variables can be ignored as null sets.

Suppose that every horizontal and vertical section of $S=\Omega^\pm$ has length at most $B_0$. If
$$
\|F_\eta-L\|_{L^2([cX,CX])}\ll E\sqrt X/\log X ,
$$
then, uniformly in $S$,
$$
\left|\iint_S(F_\eta(t)F_\eta(v)-L(t)L(v))\,dt\,dv\right|
   \ll \frac{B_0 X}{(\log X)^2}(E+E^2).
\tag{5}
$$
Indeed, each linear term is bounded using section length, $L\ll1/\log X$, and Cauchy–Schwarz in one variable. The product of the two errors is bounded using $2|e(t)e(v)|\le |e(t)|^2+|e(v)|^2$ with $e=F_\eta-L$. Its integral is at most $B_0\|e\|_2^2$. The use of $B_0$ rather than $X$ is the relative saving in a thin band.

## The analytic input

Unconditionally, for each fixed $B,\gamma>0$, whenever $\eta X\ge X^{2/15+\gamma}$ and $\eta=o(1)$, one may take
$$
E=O_{B,\gamma,c,C}\big(\eta+(\log X)^{-B}\big).
\tag{6}
$$
To justify this, use the quantitative form of the almost-all short-interval prime number theorem at the Guth–Maynard exponent, as recorded by Matomäki–Radziwiłł–Shao–Tao–Teräväinen, equation (1.5) and the discussion following it. For each fixed length $h$ between $X^{2/15+\gamma/2}$ and a dyadic interval's base, the discrepancy for $\sum_{t<n\le t+h}(\Lambda(n)-1)$ is $O(h(\log X)^{-D})$ apart from real starting points of measure $O(X(\log X)^{-D})$, for arbitrary $D$. Work on finitely many dyadic intervals to cover $[cX,CX]$.

For multiplicative lengths $\eta t$, use a mesh covering $[c\eta X,C\eta X]$ with spacing $O(\eta X(\log X)^{-B-2})$, choosing slightly wider endpoints, still comparable to $\eta X$. The mesh is of logarithmic-power size and the lengths still belong to the fixed-length theorem's range for large $X$. A union bound with $D$ large makes the exceptional measure $O(X(\log X)^{-2B-4})$. Positivity of $\Lambda$ and the bracketing lengths give discrepancy $O(\eta X(\log X)^{-B})$ outside the union, simultaneously at lengths $\eta t$. On the exceptional set the trivial normalized discrepancy is $O(\log X)$, which is enough for the required $L^2$ error. Passing from $\psi$ to $\vartheta$ costs only $O((h/\sqrt X+1)(\log X)^2)$ at length $h$ for $t\asymp X$: for each exponent $m\ge2$, the interval contains at most $O(h X^{1/m-1}+1)$ possible integer $m$th powers, and there are $O(\log X)$ exponents. This cost is negligible compared with $h(\log X)^{-B}$ in the polynomial range. We obtain
$$
\|\vartheta((1+\eta)t)-\vartheta(t)-\eta t\|_2
 \ll \eta X^{3/2}(\log X)^{-B}.
$$
Every prime in the increment has logarithm between $\log t$ and $\log t+\log(1+\eta)$. Dividing the increment by $t\log(1+\eta)\log t$ therefore gives $F_\eta$ with relative discrepancy $O(\eta/\log X)$. The main term after division differs from $L(t)$ by $O(\eta/\log X)$. This proves (6).

Under RH, Chirre–Hagen, Theorem 3, gives for all sufficiently large $X$ and small $\eta$ the bound
$$
\int_1^{CX}\big(\vartheta((1+\eta)t)-\vartheta(t)-\eta t\big)^2\,dt
  \ll_C \eta X^2\log^2(2/\eta).
$$
Using the same division, we may instead take
$$
E=O_{c,C}\!\left(\eta+\frac{\log(2/\eta)}{\sqrt{\eta X}}\right).
\tag{7}
$$

## Application 1: narrow ratio bands

Take $T=\sqrt x$ and split the smaller coordinate into dyadic ranges $X<p\le2X$ below $T$. Retain those down to a cutoff comparable to $T/(\log T)^D$, with $D$ chosen large in terms of the required precision. The target region on one such range has $pq\le x$ and ratio between $r_1$ and $r_2$. On the integration variables, expansion replaces the smaller-coordinate limits by $X/(1+\eta),2X$, the ratio limits by $r_1/(1+\eta),r_2(1+\eta)$, and leaves $tv\le x$. Erosion uses $X,2X/(1+\eta)$, ratio limits $r_1(1+\eta),r_2/(1+\eta)$, and $tv\le x/(1+\eta)^2$. The inclusions required in (4) follow because each prime coordinate is between its integration variable and $(1+\eta)$ times that variable. Thus a product changes by at most a factor $(1+\eta)^2$, and a ratio by at most a factor $1+\eta$ in either direction.

If $\eta\ll\Delta$, both regions have sections of length $O_R(\Delta X)$ in each direction. The area between expanded and eroded regions is $O_R(\eta X^2)$: the moved coordinate or ratio boundaries sweep strips of width $O_R(\eta X)$; a moved product boundary, if it meets these comparable coordinate ranges at all, has $x\asymp_R X^2$ and sweeps a strip of the same width as one varies the other coordinate. No minimum area on an individual dyadic block is needed.

Choose $\eta=\Delta/(\log X)^F$ with $F$ large. Since $\Delta\ge x^{-13/30+\epsilon}=T^{-13/15+2\epsilon}$ and $X\asymp T$ up to logarithmic factors, $\eta X\ge X^{2/15+\epsilon}$ for all retained dyadic scales and sufficiently large $x$. Equations (4)–(6) and the area difference give an error $O_{R,\epsilon,A}(\Delta X^2(\log X)^{-A})$ on each retained block. Summing them is a geometric sum at scale $T$.

It remains to dispose of the small-coordinate tail. For fixed integer $p\le T/(\log T)^D$, the ratio interval has length $\Delta p$ and at most $\Delta p+1$ integer choices. In an off-diagonal ratio band there may be a choice even when $\Delta p<1$, so the rounding term must not simply be discarded. Summing the crude upper bound over **all integers** up to the cutoff gives $O(\Delta T^2(\log T)^{-2D}+T(\log T)^{-D})$. The second term is smaller than any fixed logarithmic fraction of $\Delta x$, since $\Delta T\ge T^{2/15+2\epsilon}$. The discarded integral is $O_R(\Delta T^2(\log T)^{-2D})$. Choose $D$ large enough and this proves (1).

## Applications 2 and 3: short product bands

Here every prime coordinate is comparable to $T=\sqrt x$ because the ratio band is fixed and $K\le x$. Write the expanded product interval as $(x/(1+\eta)^2,x+K]$ and the eroded one as $(x,(x+K)/(1+\eta)^2]$. The ratio limits are expanded or eroded as above. In $(z,\rho)=(tv,\log(v/t))$, one has $dt\,dv=\tfrac12 dz\,d\rho$. The area difference is therefore $O_R(\eta x)$, and all sections have length $O_R(K/T)$ for $\eta x\ll K$; indeed one can bound both directions by the product interval width divided by a coordinate comparable to $T$.

Unconditionally take $\eta=(K/x)(\log T)^{-F}$ with large $F$. The hypothesis $K\ge x^{17/30+\epsilon}$ gives $\eta T\ge T^{2/15+\epsilon}$ for all sufficiently large $x$. Use (6) and the boundary area estimate in (4)–(5) to obtain (2). Under RH put $d=((\log T)^2/w)^{1/3}$ and take $\eta=dK/x$. For the stated regime $d=o(1)$ and $\eta=o(1)$, with $\log(2/\eta)=O(\log T)$ and $\eta T=dw$. Equation (7) gives $E=O(d)$; the area error is $O_R(dK)$. This proves (3).

Finally the area main term can be evaluated in the same variables: the integrand is
$$
\frac{2\,dz\,d\rho}{(\log z)^2-\rho^2},\qquad
 \log r_1<\rho\le\log r_2.
$$
The cumulative integral has $4e^\rho\le z\le x$ because $t\ge2$; the product-band integral has $x<z\le x+K$ for sufficiently large $x$. Integration in $z$ gives respectively $2x\log(r_2/r_1)/(\log x)^2$ and $2K\log(r_2/r_1)/(\log x)^2$, with relative error $O_R(1/\log x)$, uniformly including a shrinking ratio band.

## Comparison and reproducible checks

- [Saad Eddin and Suzuki, *On the distribution of products of two primes*, J. Number Theory 214 (2020), Theorem 3](https://doi.org/10.1016/j.jnt.2020.04.018): the published comparison for the $r_1=1$ cumulative count. The new exponent is a consequence of sharper prime-density input plus an explicit transfer, not a new bound for zeta zeros.
- [Guth and Maynard, *New large value estimates for Dirichlet polynomials*](https://arxiv.org/abs/2405.20552) and [Matomäki, Radziwiłł, Shao, Tao and Teräväinen, *Higher uniformity of arithmetic functions in short intervals II*, §1.1, (1.5)](https://doi.org/10.1007/s00222-026-01408-6): the almost-all short-interval scale and its quantitative logarithmic form.
- [Chirre and Hagen, *On Goldbach numbers in short intervals*, Theorem 3](https://doi.org/10.1007/s40993-026-00767-6) gives the conditional mean square. [Henriksson's preprint on balanced semiprimes](https://hexagonmath.org/2611.00808v1) gives an explicit lower bound at a fixed multiple of the RH scale; (3) is an asymptotic in the different diverging-multiple regime.
- [Exact finite geometry checks](verify_balanced_semiprime_bands.js) test all boundary directions and the product/ratio transform on small rational grids. They take no external target and are not evidence for the analytic prime estimates.
