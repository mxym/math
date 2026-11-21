# Two large, offsetting physical channels at every even target

A large positive part of a signed Goldbach identity need not be available to pay the rest. In a calibrated mixed divisor identity we exhibit, for **each prescribed sufficiently large even target**, two disjoint composite-by-composite channels with arbitrarily large opposite signed totals in singular-series units. They use the *same* nonnegative first-leg subweight. Their net is smaller than a stated Dickman boundary signal. This is a theorem about the method, not a lower bound for prime pairs. The detector degree is allowed to depend on the desired magnitude; there is no assertion of divergence for a single fixed detector.

Write $I=[P/3,2P/3]$, $L=\log P$, $X_P=|I|\mathfrak S(P)$, with the usual ordered binary singular series, and $\langle C,D\rangle=\sum_{x\in I,(x,P)=1}C(x)D(P-x)$. Let $\Pi=L1_{\rm prime}$ and $m_C=|I|^{-1}\sum_{x\in I,(x,P)=1}C(x)$. We use the physical score $J_k$ of the [common-sign construction, formulas (1)–(2)](https://github.com/mxym/math/commit/74d3b0e858f37c871ca0ba6d7b732d0bebaf06b9). In particular it vanishes on primes, non-squarefree integers and integers with a factor $\le P^{\theta^2}$. On squarefree rough composites having $\le k$ prime factors it is the ideal own-log response
$$
 J_k(x)=-(\log x)\sum_{d\mid x}\mu(d)(1-2\log d/\log x)_+^k.
$$
On higher ranks it uses the original short linear patch $d\le P^\theta$ and the upper cutoff $P^{1/2-\theta}$. All scores share these cuts. Split $J_2$ into $J_{2,\mathcal L}$ on $P^{\theta^2}<P^-\le P^{2\theta}$ and $J_{2,\mathcal H}$ on $P^->P^{2\theta}$. For each fixed $R$ the full mixed calibration is
$$
 G(P)=X_P+\langle J_R,J_2\rangle+o_*(X_P),                                      \tag{1}
$$
where $G$ is the true central two-prime count with the two logarithms and $o_*(1)$ means a vanishing limsup in the order $P\to\infty$ and then $\theta\downarrow0$. We justify the mixed version below.

**The physical marks.** Use the three disjoint exponent intervals $B_i=[b_i-10^{-5},b_i]$ with $(b_1,b_2,b_3)=(.18,.218,.092)$; exponents here mean $\log r/L$. Write $d=r_1r_2r_3$ with $r_i$ genuine primes in those intervals, $A=\sum_i\log r_i/L$, and put
$$
 d\mathcal H(a)=\prod_{i=1}^3 da_i/a_i,\qquad
 h_0=\int_{\prod B_i}d\mathcal H(a)>0.
$$
For a large fixed integer $u$ set $s=.01/u$ and $R=u^4$. On squarefree $x$ with $P^-(x)>P^s$ let $b(x)$ count the indicated tuples with $d\mid x$, and put $b=0$ otherwise. This is a count, not an indicator. Since $x\le P$ there are at most $5,4,10$ choices in the three respective slots, so $w(x)=b(x)/200$ belongs to $[0,1]$. Set $H(x)=Lb(x)$ and
$$
 J(u)=\int_{\prod B_i}\rho((.5-\textstyle\sum a_i)/s)\,d\mathcal H(a),
 \quad h_0\rho(1.003u)\le J(u)\le h_0\rho(u),                             \tag{2}
$$
where $\rho$ is Dickman's function. We use $J(u)$ for a positive precision scale, not for an arithmetic score.

**Theorem.** The ordinary mass $m_H$ has a limit $M_u$ with $M_u\sim h_0 e^{-\gamma}/s$ as $u\to\infty$. For the very same first-leg subweight, the two normalized signed sums satisfy
$$
\begin{aligned}
 200\,\langle wJ_R,J_{2,\mathcal H}\rangle/X_P&= 3M_u+E^+(P,\theta,u),\\
 200\,\langle wJ_R,J_{2,\mathcal L}\rangle/X_P&=-3M_u+E^-(P,\theta,u),\\
 \lim_{u\to\infty}\frac{\limsup_{\theta\downarrow0}\limsup_{P\to\infty}
      (|E^+|+|E^-|)}{J(u)}&=0.                                             \tag{3}
\end{aligned}
$$
In particular for any fixed $A_0>0$ choose $u$ large (and $R=u^4$), then $\theta$ sufficiently small, then $P$ sufficiently large depending on both: the first signed sum exceeds $A_0 X_P$ and the second is below $-A_0 X_P$. Their supports are disjoint by the cut on the *second* summand, and both actual summands are composite on every nonzero contribution. Only one orientation is taken. There is no bound for the rest of (1) sufficient to imply Goldbach.

## 1. The actual prime versus three marks, to boundary precision

The required external over-root result is [Maynard, *Primes in arithmetic progressions to large moduli III*, Theorem 1.2](https://arxiv.org/html/2006.08250#S1); the weaker Theorem 1.1 would not suffice on sparse prime slots. For $x=P/3$ and $2P/3$ in that theorem take the exponent parameters
$$
 \delta=.0001,\qquad (\log_x Q_1,\log_x Q_2,\log_x Q_3)=(.398001,.010098,.092001).
$$
They sum to $.5+\delta$ and satisfy strictly $40\delta<\log_xQ_2<1/20-7\delta$ and
$.1+12\delta-\log_xQ_2<\log_xQ_3<.1-4\delta-(3/5)\log_xQ_2$. Use $q_1=r_1r_2,\ q_3=r_3$, and the **entire** real squarefree linear-sieve label $q_2=j\le P^{.01008}$. The strict endpoint room absorbs $x/P$ at both cuts. The common residue $P\bmod q_1j$ and the compatible $P\bmod q_1jr_3$ lie in the theorem's two successive suprema when $(q_1jr_3,P)=1$. Each $(q_1,q_3)$ has at most one such factorization into the distinct specified prime bands. The theorem sums absolute discrepancies with arbitrary log saving, hence treats both signs of the sieve coefficients without any density loss on the sparse subfamilies. Its first two factors are not being replaced with arbitrary residues for the same prime. Taking the difference of the two endpoint formulas gives the actual central prime count.

For fixed $d$ on target units, sift $P-p$ at primes $\ell\le P^s$ not dividing $P$; they are disjoint from $d$. In the prime principal the local density is $1/(\ell-1)$, zero for target divisors, and the initial mark factor is $1/\varphi(d)$. Use actual upper and lower dimension-one Rosser weights at level $P^{.01008}$; the multiplicative model is bounded between $f(v)+o_P(1)$ and $F(v)+o_P(1)$ times the sifted product, $v=1.008u$. Uniform upper dimension follows from the ordinary Mertens inequality (deleting target primes only decreases the reciprocal product). The sharper relative error here is
$$
 \Delta(v)=F(v)-f(v)=2e^\gamma\rho(v-1)/v,
$$
not the coarser general fundamental-lemma estimate. It follows by the linear-sieve delay equations and $f\le1\le F$; see the [dimension-one gap derivation](https://github.com/mxym/math/commit/ca6fa82f0bbb5ceecdc9abd84c29f8e3457d0215). The sifted density is $(1+o_{P;s}(1))e^{-\gamma}\mathfrak S(P)/(sL)$ by Mertens. The omitted target factors larger than $P^s$ change its convergent singular correction by $1+O(L/P^s)$. Summing $1/\varphi(d)$ gives $h_0+o_{P;s}(1)$ by prime Mertens in the three fixed exponent intervals; deleting labels dividing $P$ costs $o(1)$ uniformly. These statements concern the local-model factors, not an independence assumption on physical prime pairs.

Discard any surviving nonsquarefree $P-p$ at fixed $s$ by the physical bound $\sum_{P^s<\ell\le\sqrt P}(P/\ell^2+1)\ll P^{1-s}+\sqrt P$, with bounded mark multiplicities and log weights. A true prime $p\mid P$ contributes negligibly (at most $O(L)$ choices); every other prime gives a target-unit complement. Thus
$$
 \limsup_{P\to\infty}\left|
 \langle H,\Pi\rangle/X_P-h_0e^{-\gamma}/s\right|
 \le h_0(e^{-\gamma}/s)\Delta(1.008u).                                      \tag{4}
$$

For the ordinary mean open $x=dm$ and apply the standard Buchstab asymptotic on the central interval for $m$, at fixed $u$; its argument stays in a compact subset of $(1,\infty)$, uniformly in all three labels. Ordinary prime Mertens on those labels gives
$$
 M_u=\int_{\prod B_i}\frac1s\omega((1-\textstyle\sum a_i)/s)\,d\mathcal H(a).
$$
Squareful rows and nonunits here cost a power at fixed $s$ by square or target-prime divisibility; only target primes $>P^s$ can occur on physical rough rows. The roughness of $m$ is exactly the roughness of $x$, since all marks exceed $P^s$. The standard convergence of Buchstab's function to $e^{-\gamma}$ has factorial error here: on $[1,2]$ the range has diameter $1/2$, each subsequent unit interval remains in the previous range by $v\omega(v)=n\omega(n)+\int_n^v\omega(t-1)dt$, and its diameter contracts by at least $1/n$ using $\omega'(v)=(\omega(v-1)-\omega(v))/v$. Thus $|M_u-h_0e^{-\gamma}/s|\ll h_0/(s\lfloor50u\rfloor!)$, since $(1-\sum a_i)/s\ge51u$.

For precision in (4) no numerical Dickman extrapolation is needed. From $t\rho(t)=\int_{t-1}^t\rho(v)dv$ and monotonicity, $\rho(t)\le1/\lfloor t\rfloor!$, and for fixed $\lambda=.001$, $\rho(t)\ge(\lambda/t)\rho(t-1+\lambda)$ for $t>1$. Iterating the latter gives $\rho(t)\ge(\lambda/t)^{\lceil t/(1-\lambda)\rceil}$ for $t>1$. Since $1.003/.999<1.008$, the factorial upper at $1.008u-1$ beats the elementary lower at $1.003u$ by $\exp(-c u\log u)$ for sufficiently large $u$. The Buchstab error is still smaller. Consequently (4) gives the actual $\langle H,\Pi\rangle/X_P=M_u+o_u(J(u))+o_{P;u}(1)$ in the sense of ordered limsups. A bare square-root level with the same three labels need not give this stated precision.

## 2. Mixed calibration and the native high/low responses

For clarity the previously established [bounded-rank source transfer](https://github.com/mxym/math/commit/bf13a6e1d1a9b35bdea274481e7a9c4e2d26a1b8) applies to a finite sum of smooth or piecewise log-Lipschitz bounded weights on products of genuine primes of fixed positive exponents, including positive and negative parts. Cut comparisons are made on independent prime boxes, not by postulating BV for an arbitrary source. For a fixed such score $C$, in the same rough cuts as above, the relevant consequences are
$$
 \frac{\langle C,J_{2,\mathcal H}\rangle}{X_P}=\frac{\langle C,\Pi\rangle}{X_P}-4m_C+o_*(1),
 \qquad
 \frac{\langle C,J_{2,\mathcal L}\rangle}{X_P}=3m_C+o_*(1).                 \tag{5}
$$
Here and below the ordinary source mass includes its $L$ normalization. To recall the estimates, write $F_t=L1_{P^->P^t}\sum_{d\mid n}\mu(d)\phi(\log d/L)$ with $\phi=1-v$ up to $\theta$, then $(1-2v)^2$ to $.5-\theta$, zero afterwards. The two native responses before the bounded-rank semiprime correction are respectively $\Pi-F_{2\theta}$ and $F_{2\theta}-F_{\theta^2}$. On the true bounded-rank source first open the signed $d$ and sieve below the chosen $P^t$ with a fixed square-root power gap. For $t=\theta^2$ use $d\le P^{.5-\theta}$, sieve level $P^{\theta/2}$; for $t=2\theta$ use $d\le P^{.5-K\theta}$, level $P^{K\theta/2}$, $K=\log(1/\theta)$. Divisor-weighted convolution BV on the actual prime factors gives the source mass times the normalized signed principal
$$
 \frac{e^{-\gamma}}{t}\int\phi(t v)\,d\rho(v)
$$
including the unit atom (replace the upper endpoint by the indicated one). This tends to $1$ for $t=\theta^2$ and to $4$ for $t=2\theta$ by integration by parts and $\int_0^\infty\rho=e^\gamma$. The dimension-one sieve errors $O_C(t^{-2} z^{-z/2})$ at $z=1/(2\theta)$ or $K/4$, and the upper-end Dickman tails, tend to zero. On the removed high shoulder $P^{.5-K\theta}<d\le P^{.5-\theta}$ the weight is $O(K^2\theta^2)$. Choose a fixed $0<\kappa<\min(.001,s/3)$ below the prime factors of $C$; take $\theta$ small relative to $\kappa$. On the **first bank**, $\ell\le P^{2\theta}$, sieve **both** quotient forms $b$ and $P-db$ simultaneously (two distinct forbidden residues for $\ell\nmid P$, one for $\ell\mid P$, as $d$ is $P^{2\theta}$-rough and a target unit). On the disjoint **second bank**, $P^{2\theta}<\ell\le P^\kappa$, sieve only $P-db$; it has one forbidden residue unless $\ell\mid d$, in which case it has none. Use nonnegative dimension-two and dimension-one upper divisor sums, respectively, both of level $P^{.08}$. Their product majorizes the required sifted indicator. The first-bank Euler product is $\ll\mathfrak S(P)/(2\theta L)^2$; the second is $\ll (2\theta/\kappa)\prod_{\ell\mid d,\ \ell>P^{2\theta}}(1-1/\ell)^{-1}\ll 2\theta/\kappa$ uniformly for large $P$ at fixed $\theta$. The model sieve ratios are bounded uniformly since both level-to-limit ratios are large. CRT at $(j_1,j_2)$ gives at most $2^{\omega(j_1)}$ residue classes and hence a total floor error $O(P^{.16+o(1)})$ per $d$. Thus the required bound is $\ll_\kappa\mathfrak S(P)P/(d\theta L^2)+O(P^{.16+o(1)})$, charging the actual bounded-rank source by its bounded amplitude and roughness. This sieves the second form on *both* banks, not only on the higher range. The rough $d$ harmonic on this log strip is $O(K)$ by the one-dimensional upper sieve on successive dyads. Thus its normalized contribution is $O_C(K^3\theta)$. The correction restoring the ideal rank-two score has ordinary and reflected cost $o_*(1)$ against these fixed rough profiles: it is supported on genuine semiprimes and has normalized size $O(\theta)$, at most $O(t_1+\theta^2)$ when the smaller exponent $t_1<\theta$. Opening that smaller prime and upper-sieving its prime cofactor and the opposite fixed-rough source gives the ordinary $dt_1/t_1$ harmonic with this amplitude: the patch at $t_1\le\theta$ costs $O(\theta)$ and the upper seam at $1/2-O(\theta)$ costs $O(\theta^2)$ even using the bound over the full fixed-length central band. These estimates prove (5), with limits in the stated order; there is no claim of uniformity in the rank of the source.

For (1), the mixed score $(J_2+J_R)/2$ has the same calibrated diagonal identity $G=X_P+\langle(J_2+J_R)/2,(J_2+J_R)/2\rangle+o_*(X_P)$. Indeed the [proof for the patched scores](https://github.com/mxym/math/commit/74d3b0e858f37c871ca0ba6d7b732d0bebaf06b9) first uses the common short linear coefficients and treats *any* bounded, piecewise smooth replacement in the medium polynomial convolution: its signed principal and ordinary change are $O_R(\theta^{-2}\rho(1/\theta))$, and its absolute mass is polynomial in $1/\theta$. The averaged medium weight has exactly these properties. On ranks $\le R$ the average of the two replacement corrections is itself a fixed-rank true source supported on composites with normalized magnitude $O_R(\theta)$; ranks $3,\ldots,R$ have only the $J_R$ correction. Its ordinary absolute mass and the actual mixed and square replacement errors go to zero by the cited bounded-rank argument. Polarizing this diagonal identity with the two original ones gives (1). This uses the common *patched* calibration, not the derivative at zero of the unpatched power of degree $R$.

Now $\Omega(x)\le1/s<R$ on the source for large $u$. Every nontrivial divisor has own-log exponent $\ge s$ there. It follows from the *actual* ideal score on that rank, with no uncovered high-rank class, that
$$
 b(x)J_R(x)=-H(x)+E(x),\qquad |E(x)|\le
 [2^{\lceil1/s\rceil} e^{-2Rs}+O_u(1/L)] H(x).
$$
The constant $1/\log x$ normalization introduces no varying roughness threshold. $H$ and $E$ are fixed finite sums of bounded-rank sources for (5), since the rank, all squarefree factor choices, the distinct mark bins and the minimum exponent are fixed after $u$; their cuts have finite angular boundaries. The harmless $O_u(1/L)$ difference can also be removed by two-form upper sieve on the rough supports at each fixed $\theta$. For the prime test of $E$ use physical positivity and (4), not an assumption of independence; for the *signed* $E$ against $J_{2,\mathcal H}$ or $J_{2,\mathcal L}$ use (5) to avoid any exploding absolute norm of the latter as $\theta\downarrow0$. The exponential term divided by $s$ is $o(\rho(1.003u))$, since $R=u^4$. Substitution in (5) now gives (3). The two large signed quantities nearly cancel on recombination; nothing is inferred about the unweighted total by keeping only the positive one.

## 3. Optional comparison with a prime-free angular model

This last calculation is not needed for (1)–(5). It explains the finer error scale. On ordinary squarefree integers put $\psi(n)=-\mu(n)\sum_{p\mid n,\ p>\sqrt n}\log p/\log n$, and zero otherwise. Thus $|\psi|\le1$ and $\psi=1$ on primes. The formal factorized angular reference tilted by $1-\psi(x)\psi(y)$ is nonnegative and puts zero on the two-prime cell. It is not a construction of an integer sequence satisfying a distribution theorem.

The signed ordinary marginal in the marked bank satisfies
$$
                         m_{H\psi}\ \longrightarrow\ -J(u).                \tag{6}
$$
Indeed the large prime is unique and different from the marks. Write $x=dmp'$; then $\psi(x)=-\mu(m)\log p'/\log x$ and $m$ is $P^s$-rough with $\log m/L<.5-A+O(1/L)$. All factors of $m$ are below the smallest mark as $m\ll P^{.01003}$. Ordinary PNT on $p'$ cancels its logarithm, leaving $-\sum_m\mu(m)/m$ times $1/d$. The moving terminal strip $m\asymp\sqrt P/d$ of bounded ratio costs $o_{P;u}(1)$ harmonically by a one-form rough upper sieve; elsewhere the prime interval has fixed endpoint ratio. Target factors and rough squareful rows have negligible ordinary contribution as above. By finite squarefree prime-simplex expansion with Mertens, the cumulative signed rough reciprocal on $m$ tends to $\rho((.5-A)/s)$, uniformly in this compact range of arguments for fixed $u$. For example its alternating integral has unit atom and derivative $v\rho'(v)=-\rho(v-1)$. Summing the three genuine marks proves (6).

In particular the formal reference would predict $\langle H,\Pi\rangle/X_P$ to be $M_u+J(u)$ (ordinary prime and $\psi$-prime marginals both equal $1$), rather than (4). Equivalently the net native mixed bank in (3) is nearly zero whereas this particular tilt predicts a nonzero discrepancy. For the latter observation, the ordinary $J_2$ mean tends to zero and its $\psi$-marginal to $1$: on the patched rough divisor source $F_{\theta^2}$ open the large prime outside the short divisor $d$. The $\mu(d)^2$ leaves an unsigned rough $d$ harmonic with limiting atom and Buchstab density in $v=\log d/(\theta^2L)$, multiplied by $\phi(\theta^2v)\rho(1/(2\theta^2)-v)$ from the signed cofactor. This tends to zero, since $\omega\le1$, the quadratic vanishes to order two at the endpoint and the complementary Dickman tails decay factorially (and likewise for the unit atom). The semiprime replacement has vanishing ordinary absolute mass. Formula (6) and the uniform approximation $bJ_R\simeq-H$ then give the tilted net $-J(u)+o_u(J(u))$ in the normalization of (3). This comparison does not refute prime-free models in general and supplies no margin for the unknown total. The substantive unconditional comparison is between the two disjoint physical signed sums in (3).
