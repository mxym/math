# Second moments of the sharp half-divisor score

Use $A_k=A_{k,1/2}$ and the simplex measure of the [signed rank law](https://github.com/mxym/math/commit/5aeca28bc339a9a27fa1200758e45a71ed2b1ce2). Write
$$ J_k=\frac1{k!}\int_{\sum u_i=1,\ u_i>0} A_k(u)^2\frac{du_1\cdots du_{k-1}}{\prod_i u_i}. $$
Then $J_k=0$ for even $k$, whereas for **every odd $k\ge1$**
$$ J_k=\frac{(2^{k+2}-2)\zeta(k+1)}{\pi^2}.                    \tag{1} $$
Thus in arbitrarily large odd ranks the absolute mass grows at least as a constant times $\sqrt{k}$, although the signed masses are factorially small. For the actual flat symmetric Goldbach score, even after restricting **both** physical ranks to $[2,R]$, both signs in the true dyadic reflected interaction have mass $\gg R^3$ in the ordered limits below. This sharp-cut phenomenon disappears in absolute one-variable rank means for a fixed smooth cutoff, as shown in §4. None of these statements establishes the sign of any prescribed target's full correlation.

## 1. Two Fourier variables

The even assertion follows by complementing subsets. The integral is finite at each fixed $k$ by $|A_k|^2\le2^k|A_k|$ and the face-integrability proof of the signed rank law. As there, multiply the integrand by $\prod_i u_i^w$, take radial Gamma coordinates $y_i>0$ and send $w\downarrow0$ at the end. Write $J_{k,w}$ for the regularized moment. For each $y$, the alternating Heaviside test for half the total has the damped Fourier representation
$$
 A_k\left(\frac y{\sum y_i}\right)
 =\frac{2^k(-1)^{(k-1)/2}}{\pi}
   \lim_{b\downarrow0}\int_0^\infty e^{-bt}\prod_i\sin(t y_i)\frac{dt}{t}\quad(k\ \text{odd})
$$
off the zero subsums with signs. Indeed test the sign of $\sum_{i\notin S}y_i-\sum_{i\in S}y_i$; its constant one-half term cancels. The sum over signs of the exponentials factors as $\prod 2i\sin(t y_i)$. The integrated damped expression is bounded uniformly in $b,y$ at each fixed $k$ by the finite signed sum of arctangents. Thus it may be squared and integrated in the Gamma measure by dominated convergence.

Write $C_w(t)=\Gamma(w)\operatorname{Re}(1-it)^{-w}$ and take $0<w\le1/2$. Integrating first over $y$ with the damping still present factors each coordinate's sine product into $[C_w(t-s)-C_w(t+s)]/2$. For fixed $b,w$ Fubini is valid: if one frequency is small, use $|\sin(t y_i)|\le t y_i$ for that factor, and exponential damping at large frequencies. On $t\ge0$ the function $C_w$ is decreasing, since
$$
 -C_w'(t)=\Gamma(1+w)(1+t^2)^{-(1+w)/2}\sin((1+w)\arctan t)
     \ \ll\ \min(t,t^{-1-w}).
$$
The last bound is uniform in $w$. Evenness and monotonicity make the resulting integrand nonnegative; remove both Fourier dampings by monotone convergence. Symmetrize the positive frequency quadrant, writing $r=s/t$ in the half $0<s<t$. Altogether
$$
 J_{k,w}=\frac{2^{k+1}}{\pi^2 k!\,\Gamma(kw)}
   \int_0^1\int_0^\infty D_w(t,r)^k\frac{dt}{t}\frac{dr}{r},\qquad
 D_w=C_w((1-r)t)-C_w((1+r)t).                              \tag{2}
$$
Boundary sets in $y$ and $r$ have measure zero. This argument covers $k=1$ also.

## 2. The diagonal ray and its integrable logarithm

For fixed $0<r<1$ and $t\ge T_r$, factorizing each Gamma power as in the signed rank law gives, uniformly as $w\downarrow0$,
$$
 t^w D_w(t,r)=\Gamma(w)\cos(\pi w/2)
      [(1-r)^{-w}-(1+r)^{-w}]+O_r(t^{-1}).
$$
Its constant tends to $b(r)=\log((1+r)/(1-r))$. Since $\int_{T_r}^\infty t^{-kw}dt/t=T_r^{-kw}/(kw)$, the inner integral in (2) divided by $\Gamma(kw)$ tends to $b(r)^k$. Contributions on a fixed finite $t$-interval vanish after this division.

For domination in $r$, use the derivative bound above. On $t\le1$, $D_w\ll rt^2$. On $t\ge1$ the universal derivative upper $C h^{-w-1}$ gives
$$ t^w D_w(t,r)\ll\int_{1-r}^{1+r} h^{-w}\frac{dh}{h}
 \ \ll\begin{cases}r,&r\le1/2,\\ (1-r)^{-w} b(r),&r>1/2.\end{cases} $$
For $w\le1/(2k)$, the resulting $r$-envelope for the normalized inner integral is integrable against $dr/r$: it is $O_k(r^k)$ near zero and $O_k(1+(1-r)^{-1/2}b(r)^k)$ near one. Thus pass to the limit under the $r$-integral. Substitution $h=b(r)$ gives $dr/r=dh/\sinh h$, so
$$
 \int_0^1 b(r)^k\frac{dr}{r}
   =2 k!\sum_{j\ge0}(2j+1)^{-k-1}
   =2k!(1-2^{-k-1})\zeta(k+1).
$$
Inserting into (2) proves (1). Checks: $J_1=1$, and $J_3=\pi^2/3=-2I_3(1/2)$ since $A_3\in\{0,-2\}$ almost everywhere.

## 3. Unbounded masses of both reflected signs on the bounded-rank sector

At each point define $p_j$ as the proportion of $j$-element subsets meeting the strict half test. Removing a random element couples successive layers, proving $1=p_0\ge\cdots\ge p_k=0$. Summing by parts and using the partial alternating binomial sum yields
$$
 A_k=\sum_{j=0}^{k-1}(p_j-p_{j+1})(-1)^j\binom{k-1}{j},
 \qquad |A_k|\le M_k:=\binom{k-1}{\lfloor(k-1)/2\rfloor}.
$$
For odd $k$ equality in this bound is attained at equal coordinates. If $H_k$ denotes the integral of $|A_k|$ with the same measure as $J_k$, then $H_k\ge J_k/M_k$. In particular
$$
 H_k\ge \left(\frac{8}{\pi^2}\sqrt{\frac\pi2}+o(1)\right)\sqrt{k}\quad(k\to\infty\ \text{odd}) .             \tag{3}
$$
The absolute and signed angular means for each bounded rank transfer to actual squarefree prime products, with a $\log x$ weight and roughness cutoff $P^{\theta^2}$, as first $P\to\infty$ then $\theta\downarrow0$ (signed rank law §2).

Specifically take the actual score $K_{\theta,R}$, $X_P$, $I_P$ and true even dyad $\mathcal P_N$ of [the parent theorem](https://github.com/mxym/math/commit/bf13a6e1d1a9b35bdea274481e7a9c4e2d26a1b8). Let $B^{\le R}_\pm(P)$ count the positive/negative parts of its product on $(x,P)=1$, $x\in I_P$, **only when both ranks are between 2 and $R$ inclusive**. Set
$$ H_R^*=\sum_{k=2}^R H_k,\qquad D_R^*=-\sum_{k=2}^R I_k(1/2). $$
The two ordinary sign means on these ranks in the ordered $P,\theta$ limits are $(H_R^*\pm D_R^*)/2$. By the true paired dyadic calculation in the signed rank law §4, with the same target-dependent cutoffs, target units, ordered pairs and singular-series normalization,
$$
 \lim_{\theta\downarrow0}\lim_{N\to\infty}
 \frac{\sum_{P\in\mathcal P_N} B^{\le R}_\pm(P)}
      {\sum_{P\in\mathcal P_N}X_P}
 =\frac{(H_R^*)^2\pm(D_R^*)^2}{2}.                         \tag{4}
$$
Now $D_R^*\to1$ by (1) of the signed rank law. Summing (3) over odd ranks gives $\liminf H_R^*/R^{3/2}\ge(8/(3\pi^2))\sqrt{\pi/2}$. Consequently for **each sign** the left side of (4), divided by $R^3$, has liminf as $R\to\infty$ at least $16/(9\pi^3)$. The difference of the unscaled two limits in (4) tends to one. This does not contradict the signed mean of the *whole* score tending to zero: the higher ranks remain and the limits are not uniform in $R$. It also does not price a true target's signed residual by replacing it by the product of ordinary means.

## 4. Fixed smooth cutoffs behave differently

Take $f\in C_c^\infty(\mathbb R)$ and define $A_{k,f}=\sum_S(-1)^{|S|} f(\sum_{i\in S}u_i)$. With the Fourier convention $f(s)=\int\widehat f(t)e^{its}dt$, factorization gives
$$ |A_{k,f}|\le \int|\widehat f(t)|\prod_i\min(2,|t|u_i)dt. $$
For $p=1,2$ let $Q_{k,p}(f)$ be the integral of $|A_{k,f}|^p$ in the measure of $J_k$. Convexity bounds the $p$-th power by $\|\widehat f\|_1^{p-1}\int|\widehat f(t)|\prod_i\min(2,|t|u_i)^pdt$. Choose a largest coordinate, so $u_j\ge1/k$. Bound $1/u_j\le k$ and its numerator by $2^p$, and relax each other coordinate independently to $(0,1)$. Summing the $k$ possible labels yields
$$
 Q_{k,p}(f)\le\frac{2^p k^2\|\widehat f\|_1^{p-1}}{k!}
 \int |\widehat f(t)|[C_p+2^p\log^+|t|]^{k-1}dt .
$$
Indeed $\int_0^1\min(2,|t|u)^pdu/u\le C_p+2^p\log^+|t|$. For every fixed $b>0$, $\sum_k b^kQ_{k,p}(f)<\infty$ by the rapid decay of $\widehat f$. This is a statement about one fixed smooth weight. The norms need not be uniform for cutoffs sharpening with $R$. In particular this last estimate is **not** a fixed-target signed comparison, a price for replacing the sharp half weight in its calibrated ledger, or a Goldbach bound.
