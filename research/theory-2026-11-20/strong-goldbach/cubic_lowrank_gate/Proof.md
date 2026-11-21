# The unguarded cubic low-rank balance at a prescribed even integer

Let $P$ be even, $I=[P/3,2P/3]$, $L=\log P$, $X=|I|\mathfrak S(P)$ with the ordinary Goldbach singular series. All reflected pairs $x+y=P$ are ordered, central and units modulo $P$. Write $G(P)$ for their true prime-pair weight $(\log x)(\log y)$. On a squarefree $y$ with normalized prime logarithms $u_i=\log r_i/\log y$, define
$$ A(y)=\sum_{S\subseteq[\omega(y)]}(-1)^{|S|}(1-2\sum_{i\in S}u_i)_+^3.$$
Put
$$ H_{234}(P)=L^2\sum_{\substack{x\ {\rm prime},\ y\ {\rm squarefree}\\2\le\omega(y)\le4}} A(y). $$
This is a **single nonnegative, unguarded** observable: no lower bound on a prime factor, no bank, no native-score cutoff parameter and no average over $P$ in its definition. A true prime $x$ is required, not a quotient made prime by a tag.

**Pointwise theorem and sufficient condition.** Uniformly through all sufficiently large even $P$,
$$ 5.9415 < \frac{G(P)+H_{234}(P)}{X} <6.183.                           \tag{1} $$
In particular a uniform upper $H_{234}(P)\le5.9415 X$ for all sufficiently large even $P$ would give a positive proportion of the Goldbach reference for each such target (the lower estimate has strict slack). That **upper is not proved**. The actual weighted dyadic mean of $H_{234}/X$, i.e. the ratio of sums, is
$$ 3+\tfrac32\zeta(3)+(6-\pi^2/3)\log2-\pi^2/6=5.03667\ldots .         \tag{2} $$
Thus the sufficient upper is about 18 percent above the mean. Almost-all information does not establish the required all-target upper.

There is a second, disjoint whole-opponent comparison for the [physical cubic high–high sector](https://github.com/mxym/math/commit/3334f60c). Precisely, let $J=J_{3,\theta}$, fix $2<a<b$, $s=2\delta$, and let $\mathcal H$ be the $P^s$-rough integers with no prime factor in $(P^{a\delta},P^{b\delta}]$. On the same orientation as the [giant-composite lower](https://github.com/mxym/math/commit/3334f60c), the *complementary* nongiant source satisfies
$$
 \liminf_{\delta\downarrow0}\liminf_{\theta\downarrow0}\liminf_{P\to\infty}
 \frac1X\sum_{\substack{x,y\in\mathcal H\\P^+(x)\le\sqrt x}} J(x)J(y)>1.69 .        \tag{3}
$$
No bound on rank or sign of $y$ is imposed. Adding (3) to the one-oriented giant lower is not a new estimate on goldbach pairs: the combined lower is weaker than the bound for the full cell already implied by $G\ge0$.

### 1. Angular inputs and normalization

We use only the **angular integrals** in [Cubic Even Tail Upper, §4, (4)–(5)](https://github.com/mxym/math/commit/7d102436) and [Cubic Signed Rank Budget, §§2–3](https://github.com/mxym/math/commit/ff5e928b), not their anchored prime-quotient theorems or their singular series constants. To specify the input, write $d\sigma_k=du_1\cdots du_{k-1}/(k!\prod_i u_i)$ on the simplex $\sum u_i=1$. Write $A_k$ for the pointwise score with $k$ factors and $I_k=\int A_k d\sigma_k$. At ranks 2,3,4 the score is nonnegative. On rank two the exact formula for the smaller exponent $t$ is $1-(1-2t)^3$, **not** $4t(1-t)$; on rank three it is $24u_1u_2u_3$. The fourth finite difference is nonnegative by positivity of the distributional fourth derivative of the truncated cubic. All odd ranks $\ge5$ vanish by complementary subsets, since the difference of opposite cubic hinges is a polynomial of degree three. Rank six is nonpositive (the even box spline has a maximum at the center and its second derivative there is nonpositive), and
$$
 -I_6<.0405,\qquad
 \sum_{\substack{k\ge8\\ k\ {\rm even}}}\int |A_k|d\sigma_k<.0155,\qquad
 \sum_{\substack{k\ge8\\ k\ {\rm even}}}\int (-A_k)_+d\sigma_k<.00775.   \tag{4}
$$
For the last inequality the signed even-tail sum is nonnegative by its decreasing alternating coefficients. These bounds include the Fourier prefactors and the factorial for unlabelled genuine prime products. The rank-six assertion follows, for example, by dividing the cited certified bound $.037481$ by its stated $4.8(\log(7/5)-.1408)$, not by copying that anchored value into (4). In particular all negative ordinary angular mass resides in the nongiant region by (3) of the giant proof, and totals less than $.04825$.

The signed even-rank coefficients sum to $3$; the nonzero odd coefficients are $I_1=1,I_3=2$ (see the cited signed rank budget, §3). Thus the total signed composite angular mass is $5$, including all high ranks. Absolute summability follows already from (4) and finiteness of the fixed-rank integrals.

### 2. Unguarding the prime test

Use $\Pi=L1_{\rm prime}$ and $F_0=L1_{\mathcal H}\sum_{d\mid n}\mu(d)(1-2\log d/L)_+^3$. The [actual no-mark prime test](https://github.com/mxym/math/commit/88cb4c61) gives $\langle\Pi,F_0\rangle/X=6+o_*(1)$, with $P\to\infty$ at fixed $\delta$ and then $\delta\downarrow0$. At fixed $\delta$, all nonsquarefree rough inputs cost $O(P^{1-s}+\sqrt P)$ unweighted plus a fixed-$\delta$ bound on the scores per row, and replacing $L$ in the cubic argument by $\log y$ costs $o_{P;\delta}(X)$ using the doubly rough upper sieve. At prime $y$, the resulting term is exactly $L^2$, and replacing these prime weights by $(\log x)(\log y)$ costs $o(X)$ by the usual two-form prime upper sieve. On squarefree composite $y$ the resulting term is exactly $L^2 A(y)$ with $x$ genuinely prime.

For each **fixed** $s>0$ only finitely many ranks occur. Apply [fixed-rank angular prime domination](https://github.com/mxym/math/commit/2fdd6ea0) to the positive and negative parts of $A_k$ on $\mathcal H$ for each $k$. This gives factor $C=200/53$ times the corresponding ordinary angular integral in target-normalized limsup. Fixed exponent cutoffs, giant cut if needed, and bank endpoints are Jordan boundaries of zero measure; an arbitrarily small upper angular envelope suffices. Ordinary primes in polynomial slots have the simplex density $d\sigma_k$, by PNT. In the resulting **positive** integrals one may discard the guards and enlarge to all ranks via (4). No claim of a log-uniform BV constant in growing rank is needed: $s$ was fixed while taking the target limsup. If $D$ is the true contribution with ranks at least five on this guarded prime test, then
$$ -C(.04825)\ \le\ \liminf_* D/X\ \le\ \limsup_* D/X\ \le\ C(.0155). $$
The $\mathcal H$-guarded nonnegative rank $2,3,4$ sum is no larger than $H_{234}$, already giving the lower bound. For the upper bound one must show that the *actual prime-paired rows* omitted by the guard are small.

For that purpose put $\xi=b\delta$ and mark a genuine $r\le P^\xi$ dividing a squarefree $y$. For $\delta$ sufficiently small $\xi<.05$. Multiple marked primes may be overcounted as we estimate absolute mass. Write $y=r v$ so $r\nmid v$; if $r\mid P$ there are no unit rows. Using the compact cubic Fourier extension of [the giant proof, §3](https://github.com/mxym/math/commit/3334f60c), the exact own-log factor-product is bounded under the integral by
$$ a_t(r)\prod_{\ell\mid v}a_t(\ell),\qquad
 a_t(\ell)=\min(2,2|t|\log\ell/L),\qquad |\widehat g(t)|\ll(1+|t|)^{-4}. $$
The factor of two covers $\log y$ uniformly on the central interval; no $y$-dependent phase is factored outside a sum. For the true prime $x=P-rv$ use the upper majorant $1_{P^-(P-rv)>P^{.01}}$ (one may keep squarefreeness there in this upper since the original input is prime). Test the primitive forms $v,P-rv$ by [Henriot, Theorem 3](https://arxiv.org/pdf/1102.1643) and its [erratum](https://doi.org/10.1017/S0305004114000280) on intervals of length $\asymp P/r$. Their product has discriminant $P^2$; put zero at every prime dividing $P$ on both legs, so all nontrivial bad local factors vanish. At $r\nmid P$ there is just one root rather than two, changing the usual local factor by a bounded factor ($r$ is odd). Coefficient size $O(P)$ satisfies the theorem's range at this interval length. The first Euler sum is bounded by $2\log(2+|t|)+O(1)$ as in the giant proof, and the second, restricted to $P^{.01}<p\le P$, is $O(1)$. Higher prime powers are set to zero for both tests. One obtains, with constants independent of $\xi,r,P,t$,
$$
 \sum_{v\ {\rm in\ range}}\prod_{\ell\mid v}a_t(\ell)\,
     1_{v,\,P-rv\ {\rm squarefree\ units}}\,
     1_{P^-(P-rv)>P^{.01}}
 \ \ll\ \frac{\mathfrak S(P)P}{r L^2}(2+|t|)^2 .
$$
The extra factor at the opened prime has $\sum_{r\le P^\xi} a_t(r)/r\ll \sqrt{|t|}\sqrt{\xi}$, by the square-root bound and prime Mertens partial summation. Both Fourier integrals at 0 and infinity converge. Thus the total $L^2$-weighted loss on actual omitted low-rank pairs is $O(\sqrt{\xi})X$. This estimate is independent of which of the three ranks was retained and in fact bounds the indicated squarefree absolute cubic mass in all ranks. It proves the needed unguarding after letting $\delta\downarrow0$. Consequently
$$
 6-C(.0155)\ \le\ \liminf_P (G+H_{234})/X
 \le\limsup_P (G+H_{234})/X\ \le\ 6+C(.04825).
$$
These rational constants strictly exceed $5.9415$ and are strictly below $6.183$, respectively, giving (1) with room.

### 3. The disjoint nongiant source

On this source, decompose the true signed angular response on squarefree composites as $A=A^+-A^-$ with $A^\pm\ge0$. For each finite $R$ keep ranks up to $R$ and impose $\mathcal H$ on each leg. On these ranks at fixed $\delta$, then $\theta\downarrow0$, the native source can be replaced by $-L A$ in the ordered bilinear sum (fixed-$\delta$ absolute replacement in the giant proof). For either nonnegative source $Q=L A^\pm$ with the given masks, the actual mixed transfer against $F_0$ gives $m_Q M_0+o_*(1)$ in units $X$, $M_0\to6$. Indeed §2 of the giant proof applies verbatim with a bounded number of polynomial prime slots: choose the largest slot as the Siegel–Walfisz prime; the complementary product has at least one factor of exponent $\ge s+o(1)$, and both slots are polynomial. Weights are piecewise Lipschitz, with finite hyperplane walls (taking a positive part preserves Lipschitz bounds). Source size is $O_R(L)$, so the absolute two-form shoulder proof has cost $O_R(s\log^4(1/s))X$ with no restriction on the opposing rank. The true prime test is between zero and $C m_Q X+o_{P;\delta}(X)$ by upper sieve. The signed comparison on these ranks is therefore bounded below in the limits by
$$ (6-C)(m_R^+-m_R^-)-C m_R^-, $$
where $m_R^\pm$ are the unguarded ordinary angular integrals of the nongiant sources. The removal of angular faces in these **ordinary** integrals uses absolute integrability at each fixed rank. Let $R\to\infty$ at the end: the actual still omitted terms in this signed *pair sum* are $O_c(c^{-R})X$ in iterated limsup by (2) of the giant proof, a true bilateral bound and not an ordinary angular approximation. The full signed difference is $5-6\log2$, since the giant source has exact mass $6\log2$, all of it positive. Using (4) gives the oriented lower $(6-C)(5-6\log2)-C(.04825)>1.69$. This proves (3).

### 4. Actual dyadic normalization and comparisons

For $Y\le P\le2Y$ take the ratio of $\sum_{2\mid P}H_{234}(P)$ and $\sum_{2\mid P}X(P)$. The denominator is asymptotic to the area of the region $x+y\in[Y,2Y]$, $1/3\le x/(x+y)\le2/3$ in the positive $(x,y)$-plane: the mean of $\mathfrak S(P)$ across even integers is 2 by its positive squarefree-divisor expansion and absolute sum of the mean coefficients. Partial summation handles $|I_P|$. For fixed minimum exponent cutoff $\kappa>0$ the numerator on this region has independent prime $x$ and genuine $k$-prime product $y$, $k=2,3,4$; both are odd so no additional parity factor occurs. A finite polygon mesh, last-prime PNT on each macroscopic interval and harmonic PNT on the remaining slots give the same area times $\sum_{k=2}^4\int_{\min u_i>\kappa}A_k d\sigma_k$. Use positive upper and lower polygon meshes and then their vanishing boundary area. On the polygon $L/\log Y=1+O(1/\log Y)$ uniformly and replacing $P^\kappa$ by $Y^\kappa$ moves a null angular boundary. Cases of a common prime with $P$ on a compact interior cost a power: because $x$ is prime and $y\asymp x$, the only possible multiples are $y=x$ or $2x$, neither contributes on this compact rank $2,3,4$ support for large $Y$. Repeated polynomial-size factors likewise cost a power. Remove arbitrarily small prime factors in the **actual numerator** by the preceding uniform $O(\sqrt\kappa)X$ estimate, and use dominated convergence for its model.

The second-rank integral is $1+2\log2$ by the giant formula, the third is $2$. For rank four, integrate the sharp-threshold law of [Rank Sine, (1)](https://github.com/mxym/math/commit/5aeca28b) against $6(1-2v)^2dv$ on $0<v<1/2$. The identity follows also under the regularized measure multiplying $\prod u_i^{w-1}$, first integrating in the compact $v$-variable: for the exchange at $w=0$, pair subsets across the minimum $a$; the $v$-measure of the resulting change is at most $2^4a$, and $\int_{\Sigma_4}a\,du/\prod u_i<\infty$ (order the minimum and choose a largest coordinate). Writing $t=\log((1-v)/v)$, $h(t)=\operatorname{sech}^2(t/2)$, the integral is
$$ I_4=\frac1{12}\int_0^\infty [h(t)+2h''(t)](t^3-\pi^2 t)\,dt
       =\tfrac32\zeta(3)+(4-\pi^2/3)\log2-\pi^2/6.$$
Here $h''=h-\tfrac32 h^2$; $\int t h=4\log2,\ \int t^3 h=18\zeta(3)$ follow by integration by parts from $h=-4(d/dt)(1+e^t)^{-1}$ and the exponential series (or Abel damping at 0). Two integrations by parts give $\int th''=1,\ \int t^3h''=24\log2$. This proves (2).

The earlier [quadratic low-degree reduction](https://github.com/mxym/math/blob/main/research/theory-2026-11-20/strong-goldbach/QuadraticLowDegreeReduction.md) already gives a two-rank sufficient upper test roughly 11 percent above its respective reference, on a different interval and with different kernels. Here the rank-four term is real, the surcharge is about 18 percent on this specific observable, and both sides of the unconditional bracket concern the same unrestricted $H_{234}$. The concurrent Chan positive majorant discussed in [Angular Prime Domination](https://github.com/mxym/math/commit/2fdd6ea0), if valid, dominates smooth bounded-rank positive sources, not at the roughly 1.18 multiplier over the ordinary reference that would suffice here. No asserted improvement from Chan or unverified parity cancellation is used. Arneth's [October cubic prime minorant](https://zenodo.org/records/23477014) uses generalized von Mangoldt functions to vanish on squarefree semiprimes and isolates a missing correlation; it is not imported here. The cubic angular tail bounds are reused with explicit credit rather than claimed afresh. In contrast to [the prime-quotient cubic budget](https://github.com/mxym/math/commit/ff5e928b), the tested opposing source in (1) is a single genuine prime, and (1) would require an **upper** on $H_{234}$, not a lower in an unrelated anchor normalization.
