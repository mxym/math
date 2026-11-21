# A genuine semiprime transfer eliminates every false prime leg

Let $P$ run through even integers, $L=\log P$, $m=P-n$, $F=nm$, and use a fixed nonnegative smooth central weight $W(n/P)$ supported in $(1/3,2/3)$. Write $X=P\int W$ and $\mathfrak S(P)$ for the ordinary Goldbach singular series. Use the **literal** coupled quadratic detector $K_0(F)=\sum_{d\mid F}\mu(d)(\log F-2\log d)_+^2$ and its proven [squarefree signed first moment](https://github.com/mxym/math/commit/5190f4df). Choose $0<d_0<d_1<1/2$ and a fixed smooth $0\leq f\leq1$ equal to 1 on $[0,d_0]$ and zero on $[d_1,\infty)$. Put
$$
 \Phi_f(n)=\sum_{d\mid n}\mu(d)f(\log d/L),\qquad
 T_2(n)=\begin{cases}8\log q\log s&n=qs,\ q<s\text{ prime},\\0&\text{otherwise}.\end{cases}
$$
There is **no** lower bound on $q$, roughness proviso, or hypothesis on Goldbach representations. Define
$$
  D(F;n,m)=K_0(F)-T_2(n)\Phi_f(m)-T_2(m)\Phi_f(n).
$$

**Theorem.** The actual squarefree first moment of $D$ is $8X\mathfrak S(P)+O_A(PL^{-A})$ for every $A>0$ (fixed shapes). On distinct prime pairs $D=4\log n\log m$. On **every** squarefree central row consisting of a prime $p$ and a composite $m$ of *any* rank,
$$
             D=-(1+\mu(m))(\log(m/p)_+)^2\leq0 .
\tag{1}
$$
On two genuine semiprime legs $D\leq0$. On two triprime legs $D=0$. Thus any missing positive mass not due to a true prime pair must lie in composite against composite, with neither a semi/semipair nor a tri/tripair providing it. This is not a bound on the net composite contribution. Unlike subtraction of unconditioned marks of all factors, the correction uses an actual arithmetic indicator of a semiprime leg.

## A squarefree transfer at fixed subhalf support

We prove $\sum W(n/P)\mu^2(F)T_2(n)\Phi_f(m)\ll_A PL^{-A}$. The same statement holds after reflection. The input is [Motohashi's induction principle](https://www.jstage.jst.go.jp/article/pjab1945/52/6/52_6_273/_article/-char/ja): the convolution of two functions satisfying its divisor bound, small-modulus Siegel–Walfisz condition, and maximal-prefix Bombieri–Vinogradov estimate again satisfies the last estimate to level $1/2$ with logarithmic losses. For the function $\theta(p)=\log p$ on primes and zero otherwise, the divisor/log growth is harmless (or first use the bounded prime indicator and recover the log weights on a dyadic factor interval by partial summation and maximal-prefix differences); the other conditions are the ordinary prime number theorem in progressions and Bombieri–Vinogradov. For clarity on the log weights, the prime indicator restricted to any interval in a dyadic range obeys the same maximal errors by prefix differences. On two polynomially long ranges apply the prime-product dispersion form [here, proof of Theorem 3.2](https://doi.org/10.1007/s40993-017-0089-3), followed by independent partial summation. If one factor is at most $P^\xi$, with $0<\xi<(1-2d_1)/4$, fix that prime and use ordinary BV for the other one: at modulus $P^{d_1+o(1)}$ the length $\gg P^{1-\xi}$ still gives a fixed level margin. Sum the resulting errors with the harmonic weights of the short primes. This gives the weighted convolution estimate with arbitrary log accuracy for the fixed subhalf levels needed here, including prefixes on the central range.

On distinct semiprimes $T_2$ is four times $\theta*\theta$. Its exceptional prime squares have negligible physical contribution: $O(P^{1/2+o(1)})$ while summing divisor labels at one actual $m$. They can also be omitted in reduced-class principal averages at cost $P^{1/2+o(1)}$ after summing reciprocally over the moduli. The same bound follows for their total discrepancy at the *particular target residue* in the application below, since each admissible modulus divides the nonzero $P-p^2$ and there are only $P^{o(1)}$ such divisors. The physical support is central, so $P-p^2\neq0$.

Keep the source coprime to $P$. Here are details making the uniformity in the varying target explicit. First delete from each prime sequence the primes $\ell\mid P$, $\ell\le L^C$, by expansion. The term with a single such factor is a prime sequence at length $\asymp P/\ell$, with weight $\log\ell$; a reduced residue mod $h$ is either incompatible or is shifted by $\bar\ell\bmod h$. Ordinary maximal BV at $h\le P^{d_1+o(1)}$ suffices, as does its principal reduced-class average. The term with two such deleted factors is absent centrally for large $P$. Source inputs divisible by a target prime $\ell>L^C$ can be removed with arbitrary log accuracy after choosing $C$ large: their population is at most $P\,(\log P)^{1-C}$. Cauchy and fixed divisor moments control all physical label multiplicities and log weights on these inputs. For principal reduced-class contributions the same deletion costs at most this population times a fixed power of $L$ (all modulus weights are summed reciprocally, and $T_2\ll L^2$). Thus we may use the full reduced source $T_2(n)1_{(n,P)=1}$ in the physical and model calculation. The argument does not assert a uniform maximal BV theorem over arbitrary nonunit residues.

On this source $\mu^2(F)=\mu^2(m)$ and $(m,P)=1$. Open $k^2\mid m$ with coefficient $\mu(k)$, truncate to $k\leq L^{B}$, and keep $(k,P)=1$. The removed population with any square divisor on this side beyond the trim is $O(PL^{-B}+\sqrt P)$, so Cauchy with the fixed divisor moments of the original and truncated multiplicities gives arbitrary log savings. Restrict $d$ in $\Phi_f$ to $(d,P)=1$. Write $d=e b$ with $e\mid\operatorname{rad}(k)$, $(b,kP)=1$. Its exact joint progression on the source is $n\equiv P\bmod k^2 b$, a reduced residue. It is sufficient to replace that progression sum by its corresponding coprime average divided by $\varphi(k^2b)$, integrated against the physical weight $W$. This follows from the indicated BV estimate, since $k^2 b\leq L^{2B}P^{d_1}$; at each fixed $k,e$ the moduli $k^2b$ are distinct and the extra weights are bounded. Partial summation handles $W$, and the polynomial-log number of $k,e$ is absorbed by choosing the BV accuracy after $B$.

Reverse the order in that principal term, keeping the actual $n$ of the semiprime source. The inner $b$-sum has the form
$$
 \sum_{(b,Pkn)=1}\frac{\mu(b)}{\varphi(b)}
     f\big((\log b+\log e)/L\big),
\tag{2}
$$
times $\mu(e)/\varphi(k^2)$, with $n$ coprime to $k$. This reversal preserves the genuine source instead of assigning it an unverified local density. For $H=Pkn\le P^3$ (hence even), the Mellin series of the coefficients of (2) is
$$
 \prod_{p\nmid H}\left(1-\frac{p^{-s}}{p-1}\right)
           =\zeta(1+s)^{-1}\mathcal H_H(s).
$$
For $\Re s\geq-c/\log L$, the generic normalized factors converge absolutely, with the finitely many small factors bounded, and the target/unit deletions cost $(\log L)^{O(1)}$ by splitting $p\mid H$ at $L$. No lower bound for $\mathcal H_H$ is needed. For a fixed compact family of smooth shapes $F_e(t)=f(t+\log e/L)$, flat at the origin since $e\le L^B$, use $F_e(t)=\int_t^\infty(v-t)F_e''(v)\,dv$. The linear log-hinge sum at radius $P^v$ has constant residue $\mathcal H_H(0)$ independent of $v$ and error $O_A(L^{-A})$ on the common positive-power support of $F_e''$; this is the usual Mellin inversion of $Y^s/s^2$ with the classical zeta zero-free contour at height $\exp(c\sqrt L)$. Dividing by $L$ and using $\int F_e''=-F_e'(0)=0$ gives arbitrary log saving in (2). Source mass bounded by $PL^2$ and all remaining reciprocal/$k,e$ factors by powers of $L$ finish the proof.

The same proof applies with a genuine source which is a product of a fixed number of distinct primes in fixed positive-power windows, with bounded piecewise Lipschitz exponent weights times a fixed power of $L$, provided its ordinary maximal BV estimate is available. For an indicator of three distinct primes in such windows use [Theorem 3.2 on prime-product distributions](https://doi.org/10.1007/s40993-017-0089-3), or the maximal-prefix convolution proof just cited. For bounded Lipschitz weights use a product mesh of width $L^{-C}$ in the normalized exponents, applying prefix differences to the separate prime intervals (uniform log errors) and summing its polynomial-log number of boxes. The approximation error is negligible after choosing $C$ because original physical multiplicity has fixed divisor moments. Fixed polynomial cutoff factors dividing $P$ are negligible by the maximum divisor bound.

## What remains on the first composite populations

For a prime leg the [exact coupled identity](https://github.com/mxym/math/commit/5190f4df) gives (1), since $\Phi_f(p)=1$ and on a squarefree composite its full quadratic difference vanishes except at rank 2, where it equals $T_2(m)$. For every squarefree semiprime $n=ab$ at least one factor exceeds $P^{d_1}$ centrally for large $P$, so $\Phi_f(n)=1-f(\log a/L)\geq0$ with $a$ the smaller factor. The uncorrected $K_0$ vanishes at even total ranks 4 and 6, proving the two stated signs.

Here is the explicit semi×triprime score in homogeneous exponent coordinates; no asymptotic for the number of these rows is assumed. Normalize each leg's prime logs by its *own* log, so the semiprime has $(t,1-t)$ and the triple has $(x,y,z)$ summing to 1. Replacing both leg log totals by $L$ in $K_0/L^2$ costs $O(1/L)$ uniformly, since central logs differ from $L$ by $O(1)$ and there are only 32 terms. Put
$$
 S_{xyz}(t)=\sum_{J\subseteq\{1,2,3\}}(-1)^{|J|}
                         (t-\textstyle\sum_{j\in J}x_j)_+^2 .
$$
This is twice the product $xyz$ times the density of the sum of independent uniforms on $[0,x],[0,y],[0,z]$. Thus $S(t)=S(1-t)$ and $0\leq S(t)\leq t^2$: for the last inequality omit the upper side constraints in the inclusion-exclusion formula for the planar cross-section of the positive octant simplex. The contribution in $K_0/L^2$ from the divisor labels on the triple, with neither semiprime factor present, is $4S(1)=0$; with exactly one present it is $-4S(t)-4S(1-t)=-8S(t)$, and with both it vanishes. Consequently the corrected homogeneous score on these rows is
$$
   -8S_{xyz}(t)-8t(1-t)\Phi_f(m)+O_f(1/L).
\tag{3}
$$
In particular if $d_0=.49,d_1=.499$ and all three triple exponents lie in $[.02,.49]$ away from the endpoints, all singleton values are 1 and all pair values zero, giving $\Phi_f(m)=-2$ there (exactly on the corresponding $L$-normalized windows). The genuinely positive score is $16t(1-t)-8S(t)$: it is strictly positive for interior $t\le1/2$, not a favorable sign on this class. If a triple has one large factor above $P^{d_1}$ and the product of the other two is below $P^{d_0}$, the exact flat sum is zero and the leading score is the favorable $-8S(t)$. These opposite populations are at the **same** prescribed target. Neither their relative frequency nor the upper sign of their difference is inferred.

## Comparison

[Chan’s November preprint](https://aixiv.science/pdf/aixiv.261111.000001v1.0.pdf) gives a prime-or-semiprime result by a different comparison. [Arneth’s October reflected-prime reduction](https://zenodo.org/records/23560521) leaves a separate fixed-target signed estimate. The zero-mean transfer here tests an actual semiprime source against a short divisor weight and eliminates the false prime leg of this coupled detector. It does not yield a pointwise upper for the remaining composite–composite signed mass or establish priority.
