# A signed cofactor pairing and an unconditional polynomial bulk with positive slack

Let $P$ be a prescribed even integer, $L=\log P$, $I=[P/3,2P/3]$, $q=P-p$ on true primes $p\in I$, $X_P=\mathfrak S(P)|I|$, and
$$ G=\sum_{p\in I,\ q\ \mathrm{prime}}(\log p)\log q . $$
The strongest result below is **unconditional** and concerns the signed sum
$$
 \mathcal H(P)=
 \sum_{\substack{p\in I,\ p\ {\rm prime}\\P^-(P-p)>P^{.001}}}
 (\log p)\!\!\sum_{\substack{tb=P-p\\ t>P^{.3},\ b>P^{.003}}}
            \mu(t)\log b.                                               \tag{1}
$$
No additional conditions on $t,b$ are imposed (their roughness is automatic); neither variable is subpolynomial. We prove that for all sufficiently large even $P$,
$$ G>\mathcal H(P)+0.0043X_P.                                          \tag{2}$$
In particular $\mathcal H(P)\ge-0.0043X_P$ at every sufficiently large even $P$ would suffice for large-even Goldbach. We do **not** bound $\mathcal H(P)$ from below. Prime $q$ has no term in (1). The point of (2) is the strict margin on the genuine remaining signed polynomial bulk, not positivity of the complete statistic.

We also give the exact per-row absolute law behind the pairing at a moving squared cutoff (§1); it applies on the same $z$ and weights as the [tagged high-cofactor reduction](https://github.com/mxym/math/commit/6bd046d4). The second, polynomial result (2) does not use its conditional tagged-family estimate.

## 1. What cancellation buys at the full moving square cutoff

Take $z=\exp(L^{.05})$ and $t>P^{.3}$ as in the cited moving truncation. Put $\mu_z(t)=\mu(t)1_{P^-(t)>z}$, and let $B_z(b)$ be $\log b$ on $z$-rough $b$, $\log r$ if $r$ is its sole distinct prime $\le z$, and zero otherwise. For $1\le U\le2$ fixed let $R_U(q)=\sum_{tb=q,\ b\le z^U}\mu_z(t)B_z(b)$; here $t>P^{.3}$ is automatic. Then for each prescribed large even $P$,
$$
 \frac1{X_P}\sum_{p\in I}(\log p)|R_U(q)|
   =e^{-\gamma_E}[3-2U+(U+2)\log U]+o(1).                            \tag{3}
$$
If absolute values are taken on **each divisor term** instead, the right side is $e^{-\gamma_E}(1+U\log U)+o(1)$. At $U=2$ this last number exceeds 1 whereas (3) is strictly below 1. These are true $|\mu|$/signed masses, not just rough-sequence majorants.

Discard all $q$ with a square of a prime $>z$ as a divisor. Their number is $\ll P/z+\sqrt P$, and Hölder with fixed divisor moments shows the discarded cost is $O_A(PL^{-A})$ with the divisor and log weights here. **Small squares are not discarded this way.** On a $z$-rough row outside this exception $q$ is squarefree, and all nonzero $b\le z^U$ are primes $s\in(z,z^U]$. Their signs $\mu(q/s)$ agree. Their total normalized mass is $e^{-\gamma_E}(U-1)+o(1)$: mark $s|q$, sieve $q$ on primes $\le z$, and use $\sum_{z<s\le z^U}\log s/(s-1)=(U-1)\log z+o(\log z)$.

Rows with at least two distinct primes $\le z$ give zero since every such factor divides $b$. On the remaining rows write $q=r^j u$ with $r\le z$ prime, $j\ge1$, and $u$ squarefree, $z$-rough. Unless $r^j\le z^U$ all terms vanish. The allowed $b$ are $r^j$ and $r^j s$ with $s|u$ prime and $z<s\le z^U/r^j$. Every nonzero $B_z(b)$ equals $\log r$, and putting $s$ in $b$ flips the sign. Thus **on this same physical row**
$$ |R_U(q)|=\log r\,|1-N|,\qquad N=\#\{s|u:\ s\text{ prime},\ z<s\le z^U/r^j\}. $$
The unpaired absolute sum instead has $1+N$. Use $|1-N|=N-1+2\mathbf1_{N=0}$.

Here are the joint conditional estimates. Put $V_P(Y)=\prod_{h\le Y,h\nmid P}(1-1/(h-1))$, so $V_P(Y)=(1+o(1))e^{-\gamma_E}\mathfrak S(P)/\log Y$ uniformly for $z\le Y\le z^2$. Marks dividing $P$ force an exceptional prime source $p|P$ and cost $P^{o(1)}$. Given $r^j|q$, a prime $h\le Y$, $h\nmid P$, has conditional density $1/(h-1)$ in the quotient $q/r^j$ if $h\ne r$, **but $1/r$ if $h=r$**, by $\phi(r^j)/\phi(r^{j+1})$. Thus the base multiplier $1/\phi(r^j)$ times the rough product for $u$ is exactly
$$ V_P(Y)\frac1{r^j}\frac{r-1}{r-2}, $$
where $r$ is odd. A further mark $s>z$ for $N$ adds $1/(s-1)$ relative to the $Y=z$ main. The zero-count term is the conditional rough sieve with $Y=\max(z,z^U/r^j)$, **in the same progression** at $r^j$; its ratio to the original rough main is $1/T+o(1)$, $T=\log Y/\log z$. The first moment multiplier is $\log T+o(1)$ by Mertens including the target omissions. No independence or Poisson conjecture is used.

Explicitly the positive linear upper/lower sieves with level $D=P^{.20}$ have relative error smaller than every fixed log power by the fundamental lemma since $\log D/\log(z^2)\gg L^{.95}$. All congruences for the sieving variable $h|u$ and its squarefree test modulus $d$ can be read as $p\equiv P\bmod r^j d$ (or $r^j s d$); $d$ may contain $r$, giving the conditional density just computed. Maximum modulus $P^{.2+o(1)}$ leaves a fixed BV gap. Each modulus has divisor-bounded multiplicity, including the choice of a prime power dividing it. Maximal Bombieri–Vinogradov and Cauchy with the elementary complementary divisor moment bound absorb that multiplicity, the logarithms, and all signed combinations of the actual positive counts. The source weight is $\log p$ on true primes: one may subtract the proper-power error per source modulus here because of the fixed square-root gap. The scheme also gives the rough-row calculation above. Total unsigned main budgets are at most log powers; hence none of the summed remainders survives after division by $X_P$.

All $j\ge2$ cost $o(X_P)$ even in the **unpaired** mass: $\sum_{r,j\ge2}\log r\,(r-1)/(r^j(r-2))=O(1)$, the $s$-harmonic multiplier is $O(1)$, and $V_P(z)/\mathfrak S(P)\ll1/\log z$. For $j=1$, with $a=\log r/\log z$, the measure $\sum_{r\le z,r\nmid P} (\log r)(r-1)/(r(r-2)\log z)$ tends to $da$ on $[0,1]$; omitted target weight is $O(\log(2L)/\log z)$ by splitting divisors at $L^2$. Therefore the singleton main is $e^{-\gamma_E}\int_0^1 [\log T-1+2/T] da$ with $T=\max(1,U-a)$; for unpaired weights it is $e^{-\gamma_E}\int_0^1(1+\log T)da$. Adding the rough-row mass and integrating gives (3) and its unpaired counterpart, including both endpoints.

## 2. Recalibration with a genuine polynomial rough cutoff

From now on put $\eta=.001$, $Z=P^\eta$, $g=.3$, $Y=P^g$, and retain **only** $Z$-rough $q$. All true central prime partners survive. On such a row the exact identity is $\Lambda(q)=\sum_{tb=q}\mu(t)\log b$. Write $S_0$ for the true prime-source sum of the terms $t\le Y$ on these rough rows. We prove
$$ \limsup_{P\to\infty,\ 2|P}|S_0/X_P-1|
 \le 300000\Delta(100)+702/300!,\qquad
 \Delta(s)=2e^{\gamma_E}\rho(s-1)/s.                                   \tag{4}$$
In estimating $S_0$, $t$ is automatically squarefree in nonzero terms and has all prime factors $>Z$. Given $t|q$, $(t,P)=1$, its condition is the ordinary rough sieve on primes $\le Z$ distinct from all factors of $t$. The conditional main per $t$ is $|I|V_P(Z)[L-\log t+O(1)]/\phi(t)$ (with sign $\mu(t)$). Use dimension-one linear sieve at $D=P^{.10}$, hence $s=100$. The normalized error of either positive sieve bound relative to its model is at most $\Delta(100)+o(1)$ since $F(s)-f(s)=\Delta(s)$ and $f\le1\le F$; see [the linear-sieve inputs and gap derivation](https://github.com/mxym/math/commit/ca6fa82f) and Friedlander–Iwaniec, *Opera de Cribro*, Ch. 11. All target deletions only improve the uniform dimension bound. The absolute sum of the model multipliers is at most $(1+o(1))300000X_P$: use $L V_P(Z)/\mathfrak S(P)\to e^{-\gamma_E}/\eta$, and $\sum_{P^-(t)>Z,\; t\le Y}\mu^2(t)/\phi(t)\le\prod_{Z<r\le Y}(1+1/(r-1))=(1+o(1))g/\eta$. Total absolute progression remainders are $O_A(PL^{-A})$ by the same divisor-weighted BV, now $tD\le P^{.4}$. Physical $O(1)$ variation of $\log(q/t)$ is negligible with these fixed cuts; use the positive upper sieve. Removing source divisors of $P$ costs $P^{o(1)}$.

To calculate the signed model, the harmonic measure $\mu(t)/\phi(t)$ on $v=\log t/\log Z$ tends to $\delta_0+\rho'(v)dv$ on $[0,300]$. This is the signed exponential convolution of $-\mathbf1_{v\ge1}dv/v$: choose distinct primes by Mertens, divide by the factorial of their number, and distinguish one boundary coordinate to get $v\rho'(v)=-\rho(v-1)$. All cutoffs are fixed; restoring target primes above $Z$ and ignoring ties costs $o(1)$ in the harmonic model by $L/Z$ and $\sum_{r>Z}r^{-2}$. See [full rough inversion, §3](https://github.com/mxym/math/commit/6f877f72) for the same measure and its Laplace integral. Integration of $(1-\eta v)$ yields normalized main
$$ \frac{e^{-\gamma_E}}\eta\left[(1-g)\rho(g/\eta)+\eta\int_0^{g/\eta}\rho(v)dv\right]. $$
Since $\int_0^\infty\rho=e^{\gamma_E}$ and $\rho(j)\le1/j!$, the distance from 1 is at most $702/300!$. This proves (4). There is no appeal to the binary conjecture or to the conditional cofactor-tag comparison.

## 3. Cubic cutoff on the remaining rough rows

Let $C(q)=\sum_{tb=q,\ b\le Z^3}\mu(t)\log b$ on $Z$-rough $q$. Here $t>Y$ is automatic since $q\asymp P$. We claim
$$ \limsup_{P\to\infty,\ 2|P}
 \frac{\sum_{p\in I,\ q\ Z\text{-rough}}(\log p)|C(q)|}{X_P}
 \le e^{-\gamma_E}(4\log2-1)+8\Delta(100).                             \tag{5}
$$
Squareful rough $q$ again have negligible total divisor-weighted cost since any bad square is above $Z^2$. For squarefree $q$, $\mu(t)=\mu(q)\mu(b)$. Mark one prime $r$ of $b$ to pay its $\log r$ part of $\log b$. After $r$ is marked, the other factors of $b$ have product $\le Z^3/r<Z^2$ and all exceed $Z$, so there is either none or exactly one such prime. This gives the pointwise bound
$$ |C(q)|\le\sum_{\substack{r|q\\ Z<r\le Z^3}}(\log r)|1-N_r|,\quad
 N_r=\#\{s|q/r:\ s\text{ prime},\ Z<s\le Z^3/r\}. $$
The triangle inequality is used across the marks $r$, **after** keeping the opposite signs of the two cofactor lengths with that mark. No equality of the two sides is required in (5).

Put $v=\log r/\log Z$, $T=\max(1,3-v)\in[1,2]$. For each marked $r|q$ open $N_r-1+2\mathbf1_{N_r=0}$. The baseline has model $|I|V_P(Z)/\phi(r)$. The first moment also marks $s$ and has multiplier $\sum_{Z<s\le Z^3/r,\ s\nmid Pr}1/(s-1)=\log T+o(1)$ uniformly. The zero term sieves the actual cofactor $q/r$ to $Z^T$ in the progression $p\equiv P\bmod r$. If $r\le Z^T$ its own conditional density is $1/r$ rather than $1/(r-1)$, changing the rough product relatively by $1+O(1/r)$; equivalently one may separately omit the square $r^2|q$. The ratio to the baseline is $V_P(Z^T)/V_P(Z)=(1+o(1))/T$ up to that uniform negligible correction. Source primes dividing $P$ and omitted target prime labels make negligible errors. The uniformity here follows from $Z\le Z^T\le Z^2$ and the Mertens product plus $O(L/Z)$ target-tail correction.

Choose $D=P^{.20}$ throughout. The composite moduli for the marked first moment are $rsd\le Z^3D=P^{.203}$, and those for the wider zero sieve are $rd\le Z^3D$ including any repeated $r$. All have divisor-bounded multiplicity and all positive sieve levels have $s\ge100$. Thus the absolute error of the **combined** three signed terms, in units $X_P$, has limsup at most $8\Delta(100)$. Indeed the model coefficients after the $r$ sum are at most $e^{-\gamma_E}$ times the integrals over $1<v\le3$ of $1$, $\log2$ and $2$ respectively, whose sum is $<8$. The nonnegative upper and lower sieve weights price these positive counts separately; no absolute discrepancies beyond the valid BV level are assumed. Finally weighted prime Mertens gives the multiplier $dv$ from $\sum_{Z<r\le Z^3,r\nmid P}\log r/(r-1)$ after division by $\log Z$. The resulting upper main in (5) divided by $e^{-\gamma_E}$ is
$$
 \int_1^3[\log T-1+2/T]dv
   =1+\int_1^2(\log s-1+2/s)ds=4\log2-1.
$$
This proves (5). In particular (5) does not assume cancellation of the remaining Möbius sign on shifted primes.

Subtracting the aggregate short-cofactor absolute bound from the lower bound for $S_0$, with the true proper powers on $Z$-rough rows removed at cost $P^{1/2+o(1)}$, gives (2). For the explicit slack use $\rho(j)\le1/j!$ and $e^{\gamma_E}<2$ to get $\Delta(100)\le4/(100\cdot99!)$. The companion **check.py**, valid also under Python optimization, verifies with rationals $e^{-\gamma_E}(4\log2-1)<0.9956$ and the total errors in (4)–(5) below $10^{-8}$. It uses $H_{4096}-\log4097<\gamma_E$, the atanh series with a geometric upper tail for positive logarithms, and a finite exponential lower sum. The certified margin strictly exceeds $0.0043$ before the vanishing asymptotic errors.

The two reductions use **different roughness regimes**. In §1 the subpower $z$ is below the JLL banks, so the moving-square sector is disjoint from their hit cofactors. In (1) the fixed polynomial $Z$ is eventually above every such bank, so that conditional gate removes nothing further. The cofactor in (1) can still be prime or composite, and this argument gives no sign control on its remaining interaction with $\mu(t)$.

The point of (1) is the cofactor cut at the **prescribed physical roughness** $Z=P^{.001}$. Starting instead with $P^{.003}$-rough rows would make the same polynomial cofactor threshold automatic whenever $\log b\ne0$, but would delete the actual rows with a prime factor between these two cuts.
