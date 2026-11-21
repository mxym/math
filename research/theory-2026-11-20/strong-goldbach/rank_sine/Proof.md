# The signed rank law for a sharp divisor threshold

A sharp cutoff in a Möbius divisor sum has an exactly computable signed mass at each fixed number of prime factors. At the square-root cutoff these masses are the coefficients of a sine. Applied to the actual symmetric Goldbach score, the law exhibits a signed unit escaping every fixed rank and gives quantitative lower bounds on **both** signs of its reflected interaction, averaged over true even targets. It gives no one-sided bound for the signed correlation at a prescribed target and does not prove Goldbach positivity.

## 1. An angular integral

For $0<v<1$, $k\ge1$, let $\Sigma_k=\{u_i>0:\sum u_i=1\}$, with ordinary coordinates $u_1,\ldots,u_{k-1}$ (unit mass when $k=1$). Define
$$
 A_{k,v}(u)=\sum_{S\subseteq[k]}(-1)^{|S|}\mathbf1_{\sum_{i\in S}u_i<v},
 \qquad
 I_k(v)=\frac1{k!}\int_{\Sigma_k} A_{k,v}(u)\frac{du_1\cdots du_{k-1}}{\prod_i u_i}.
$$
The integrand is absolutely integrable for each fixed $k,v$, and
$$
 I_k(v)=\frac{\operatorname{Im}\big[(\log((1-v)/v)+i\pi)^k\big]}{\pi k!},
 \qquad
 \sum_{k\ge1}I_k(v)z^k=\left(\frac{1-v}{v}\right)^z\frac{\sin(\pi z)}{\pi}.
 \tag{1}
$$
At $v=1/2$, $I_k=\sin(k\pi/2)\pi^{k-1}/k!$. The absolute integrability assertion is made separately in each dimension; it does not assert summability of integrals of absolute values over all dimensions.

**Integrability.** Order the coordinates so that one specified coordinate is the minimum $a$. Pair subsets differing in that coordinate. Unless $A_{k,v}=0$, the sum of some subset of the remaining coordinates lies in $[v-a,v)$; the sum of its complement among those remaining lies in $(1-v-a,1-v]$. If $a<\min(v,1-v)/(2k)$, both groups contain a coordinate at least $\min(v,1-v)/(2k)$. For $k=2$ this is already impossible; for $k\ge3$ choose one such coordinate in each group. Fix $a$ and the other $k-3$ coordinates. The first chosen coordinate varies in an interval of length at most $a$; the second is then determined by the simplex constraint. Their reciprocal product is bounded. The resulting absolute integral from $a\le h$ is
$$
 \ll_{k,v}\int_0^h(1+\log(1/a))^{k-3}\,da
$$
because the fixed coordinates are each at least $a$, and $|A_{k,v}|\le2^k$. We sum over finitely many choices of labels and subsets. The complementary domain is compact away from the coordinate faces. The assertion at $k=1$ is immediate.

**Evaluation.** For $w>0$ replace $1/\prod u_i$ in $I_k$ by $\prod u_i^{w-1}$, defining $I_{k,w}$. Dominated convergence gives $I_{k,w}\to I_k$ as $w\downarrow0$. Radial coordinates $y_i=r u_i$ with density $e^{-\sum y_i}\prod y_i^{w-1}dy_i$ give the factor $\Gamma(kw)$ times the regularized simplex integral. For a fixed $S$ the angular inequality is
$$ Y_S=v\sum_{i\notin S} y_i-(1-v)\sum_{i\in S}y_i>0. $$
Use $\mathbf1_{Y>0}=1/2+\lim_{b\downarrow0}\pi^{-1}\int_0^\infty e^{-bt}\sin(tY)dt/t$ away from $Y=0$; the integral equals $\arctan(Y/b)$. Equality sets are null; the constant cancels in the alternating sum. For fixed $b$ one may integrate first in $y$: near zero in $t$ dominate the sine by $t\sum y_i$, and at infinity use the damping. The Gamma integrals factor in every coordinate. Thus
$$
 I_{k,w}=\frac{1}{\pi k!\,\Gamma(kw)}\operatorname{Im}
       \int_0^\infty B_w(t)^k\frac{dt}{t},\qquad
 B_w(t)=\Gamma(w)\big[(1-ivt)^{-w}-(1+i(1-v)t)^{-w}\big].
 \tag{2}
$$
We have removed $b$ by absolute convergence on this last side: for fixed $w>0$, $B_w=O(t)$ at zero and $O(t^{-w})$ at infinity. All complex powers use the principal logarithm. Uniformly for $0<w\le1/2$ and $t\ge T_v$ with $T_v$ fixed sufficiently large,
$$
 t^w B_w(t)=C_w+O_v(1/t),\quad
 C_w=\Gamma(w)\big[v^{-w}e^{i\pi w/2}-(1-v)^{-w}e^{-i\pi w/2}\big]
       \longrightarrow \log((1-v)/v)+i\pi .
$$
This follows by factoring $\mp i c t$ in each power (relative error $O_v(w/t)$); $w\Gamma(w)$ is bounded. On $0\le t\le T_v$, $|B_w(t)|\ll_v t$ by differentiating both powers. The error in the integral in (2) after subtracting $C_w^k\int_{T_v}^\infty t^{-kw}dt/t$ is therefore $O_{k,v}(1)$ as $w\downarrow0$. The extracted integral is $T_v^{-kw}/(kw)$ and $kw\Gamma(kw)\to1$. This proves (1).

Two direct checks: $I_2(v)=\log((1-v)/v)$ follows by integrating the two-coordinate step function. Averaging $v$ uniformly gives $\int_0^1\mathbf1_{s<v}dv=1-s$, whose alternating finite difference vanishes for every $k\ge2$. The corresponding generating function averaged for $|\operatorname{Re}z|<1$ is $\Gamma(1+z)\Gamma(1-z)\sin(\pi z)/\pi=z$. This uses all thresholds, including those above the square root; it is not a distribution theorem at those levels.

## 2. Transfer to genuine weighted integers

Consider squarefree $x$ of rank $k$ (the number of prime factors) in any fixed proportional interval $cN\le x\le dN$ with $0<c<d$. Weight each by $\log x$ times a bounded piecewise-continuous function $f(u)$ of its logarithmic prime factors $u_i=\log p_i/\log x$, symmetric in the $k$ labels, with all $u_i>\eta>0$. We use functions whose discontinuities lie in a fixed finite union of affine hyperplanes of measure zero on the simplex. Then the weighted sum divided by $(d-c)N$ tends to
$$
 \frac1{k!}\int_{\Sigma_k,\,\min u_i>\eta} f(u)\frac{du_1\cdots du_{k-1}}{\prod u_i}.      \tag{3}
$$
Indeed select $k-1$ labelled primes, product $b$, then sum the last by PNT in $[cN/b,dN/b]$ where it is at least a fixed power of $N$. More precisely partition the first $k-1$ exponent axes $\log p_i/\log N$ at fixed mesh; $u_k=1-\sum_{i<k}\log p_i/\log N+O_{c,d,k}(1/\log N)$. On interior cells the factor $\log x/\log p_k$ is approximated by $1/u_k$. PNT weighted by $\log p_k$ contributes $(d-c)N/b$ with relative $o(1)$ uniform when $N/b\ge N^{\eta/2}$. The other harmonic prime sums converge by Mertens to $\prod_{i<k}du_i/u_i$. Boundary cells have vanishing limiting measure as mesh tends to zero using the same positive envelope. Fixed-$\eta$ repeated prime labels cost $O_{k,\eta}(N^{1-\eta/2}\log N)$, by the bound for multiples of a large prime square and bounded labelled multiplicity; divide by $k!$ for distinct labels. The $k=1$ case is ordinary PNT. Replacing a fixed exponent cut with one shifted by $O_{c,d,k}(1/\log N)$ leaves the same main by positive envelopes. On fixed roughness, a unit condition excluding prime divisors of any one $P\asymp N$ costs $o(N)$ in these one-variable sums: the bounded number of such divisors $>N^{\eta/2}$ each divides $O(N^{1-\eta/2})$ inputs. These are natural means, not claims about distribution in reflected pairs for any prescribed $P$.

Taking $f=A_{k,v}$ in (3) and then $\eta\downarrow0$ gives the actual signed prime-rank law (1). Its positive and negative parts individually have finite limiting angular means by section 1.

## 3. An escaped signed unit in the flat symmetric score

Use exactly the score $K_{\theta,R}$ of [Removing genuine bounded even ranks](https://github.com/mxym/math/commit/bf13a6e1d1a9b35bdea274481e7a9c4e2d26a1b8), not a pointwise sign-replaced surrogate. Here $P$ is even, $I_P=[P/3,2P/3]$, $\eta=\theta^2$, $W=P^\eta$, $A=P^\theta$, $D=P^{1/2-\theta}$ and $R\ge3$ is fixed. The score is zero except on squarefree $W$-rough composites. At ranks $2\le k\le R$ it equals $-(\log x)A_{k,1/2}(u)$; at higher ranks it equals
$$ -\sum_{d|x,\ d\le D}\mu(d)\big(\log x-\mathbf1_{d\le A}\log d\big). $$
For each fixed $R,\theta$ its positive and negative parts have well-defined ordinary means $m_+(\theta,R),m_-(\theta,R)$, in units of the full interval length, by (3). Indeed all ranks are at most $1/\eta+O(1)$, and after division by $\log x$ each high-rank score is piecewise affine in $u$ with finitely many subset-cut hyperplanes. The parameters $W,A,D$ have exponents relative to $x$ differing from their displayed $P$-exponents by $O(1/\log P)$; moving them makes no change in the limiting means. This works on any fixed proportional interval inside $x\asymp P$.

Sections 1–2 of the linked proof give $m_+-m_-\to0$ as $\theta\downarrow0$ at fixed $R$. Specifically its decomposed unmodified signed tail costs at most $2\eta^{-1}\rho(\theta/\eta)$ in limsup and its bounded-rank replacement costs $O_R(\theta(1+\log(1/\eta))^R)$; squareful rough rows are negligible at fixed $\theta$. Subtract the fixed-rank means just computed. With $m_{>R}(\theta,R)$ the signed ordinary mean restricted to ranks $>R$, we obtain
$$
 \lim_{\theta\downarrow0}m_{>R}(\theta,R)=\sum_{k=2}^R I_k(1/2),
 \qquad \lim_{R\to\infty}\lim_{\theta\downarrow0}m_{>R}(\theta,R)=-1.       \tag{4}
$$
The last equality uses (1) at $z=1$ and $I_1=1$. In every $m$ the large-target limit was already taken at fixed $\theta,R$. This is a signed unit in this exact family of scores, not uniformity when rank, roughness and target vary together.

## 4. True adverse and favorable interactions in dyadic target averages

Let $K=K_{\theta,R}$, $X_P=|I_P|\mathfrak S(P)$, and $B_\mp(P)=\sum_{x\in I_P,(x,P)=1}(\mp K(x)K(P-x))_+$. Thus $B_-$ is the adverse contribution taken positively, $B_+$ the favorable one. Write $\mathcal P_N=\{P\in[N,2N]:2|P\}$. At every **fixed** $R,\theta$ one has
$$
 \lim_{N\to\infty}\frac{\sum_{P\in\mathcal P_N}B_-(P)}{\sum_{P\in\mathcal P_N}X_P}=2m_+m_-,
 \qquad
 \lim_{N\to\infty}\frac{\sum_{P\in\mathcal P_N}B_+(P)}{\sum_{P\in\mathcal P_N}X_P}=m_+^2+m_-^2.        \tag{5}
$$
The same product formula holds upon prescribing the two ranks and the two signs. It does not require any conjecture about fixed additive target.

To prove it, sum over integer pairs $(x,y)$ in the polygon $N\le x+y\le2N$, $(x+y)/3\le x\le2(x+y)/3$. Both nonzero weights are on odd integers, so $P=x+y$ is automatically even. On fixed roughness the scores are $O_{\theta,R}(\log N)$. Pairs failing $(x,P)=1$, equivalently $(x,y)=1$, cost $O_{\theta,R}(N^2\log^2N\sum_{r\ge N^{\eta/2}}r^{-2})=o(N^2)$, by counting pairs sharing a prime. For the remaining unrestricted product averages, replace the two score cutoffs by their own argument exponents in each coordinate, as in section 3. For a fully uniform justification, at fixed $\theta,R$ every changed tuple in a given coordinate lies in an $O_{\theta,R}(1/\log N)$ angular seam (including the rough edge); its weighted total is $o(N)$ by (3) and first using any fixed wider seam. The other coordinate has a uniform positive envelope of total $O_{\theta,R}(N)$ by (3) applied to the finitely many ranks, bounded score and relaxed rough edge $\eta/2$. The product error is therefore $o(N^2)$, **not** inferred by multiplying $o(N)$ by $N\log N$. Approximate the polygon from above and below by finite unions of grid rectangles. On each rectangle the nonnegative product factors and (3) applies in each coordinate. The boundary rectangles' limiting mass tends to zero with their area by the same positive envelope. The area is $\int_N^{2N}(s/3)ds$.

Finally $\sum_{P\in\mathcal P_N}X_P\sim\int_N^{2N}(s/3)ds$: on even targets $\mathfrak S(P)=2C_2\prod_{p|P,p>2}(1+1/(p-2))$, where $C_2=\prod_{p>2}(1-1/(p-1)^2)$. Its mean on the even integers is $2$, since $\prod_{p>2}(1+1/[p(p-2)])=1/C_2$. Justify averaging the positive divisor expansion by $\sum_d g(d)/d<\infty$ for $g(d)=\mu^2(d)\mathbf1_{2\nmid d}\prod_{p|d}(p-2)^{-1}$, using initial intervals where $\lfloor x/d\rfloor/x\le1/d$; then subtract prefixes and apply partial summation. This proves (5).

For $R\ge5$, let $B_{-,35}$ restrict the adverse sum to the two orientations of ranks $3,5$. By (1), the limiting positive rank-three mean is at least $\pi^2/6$ (indeed it equals this), and the negative rank-five mean at least $\pi^4/120$. Thus
$$
 \liminf_{\theta\downarrow0}\lim_{N\to\infty}
 \frac{\sum B_{-,35}(P)}{\sum X_P}\ge\frac{\pi^6}{360}>2.67.       \tag{6}
$$
The sums here and below are on $\mathcal P_N$. More generally the fixed positive-score rank means give
$$
 \liminf_{\theta\downarrow0}m_+(\theta,R)\ \ge b_R:=\sum_{\substack{3\le k\le R\\ k\equiv3\ (4)}}\frac{\pi^{k-1}}{k!}.
$$
Since $m_+-m_-=o_R(1)$ in that limit, (5) yields for **each** sign
$$
 \liminf_{R\to\infty}\liminf_{\theta\downarrow0}\lim_{N\to\infty}
 \frac{\sum B_\pm(P)}{\sum X_P}
 \ \ge\ 2\left(\frac{\sinh\pi}{2\pi}\right)^2>6.75.                 \tag{7}
$$
Here $\lim b_R=(\sinh\pi-\sin\pi)/(2\pi)$. Equations (5) and (7) concern true paired populations. Their *difference* in the fixed-parameter dyadic limit equals $(m_+-m_-)^2$, which tends to zero at fixed $R$ as $\theta\downarrow0$. Nothing here converts the dyadic limits to a favorable sign at a prescribed target. In particular a uniform bound pricing all negative contributions alone below the parent theorem's near-unit reserve is impossible for this flat family.

For related but different problems, see the [Dirichlet law for factorizations](https://www.cambridge.org/core/journals/mathematical-proceedings-of-the-cambridge-philosophical-society/article/abs/dirichlet-law-for-factorisation-of-integers-polynomials-and-permutations/4FDE4EF96DCEFEAAE9CA9B3A365DBDA8) and [Friedlander–Iwaniec on the asymptotic sieve](https://arxiv.org/abs/math/9811186). The integral evaluation above is independent of a zero-free hypothesis and the numerical checks; no priority claim is needed.
