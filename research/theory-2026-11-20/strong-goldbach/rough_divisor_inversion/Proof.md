# A full smooth-divisor sum with arbitrary small rough part, and its prime-free upper remainder

Let $P$ run through prescribed large even integers, $L=\log P$, $I=[P/3,2P/3]$, and $X_P=|I|\mathfrak S(P)$, where $\mathfrak S$ is the ordinary binary Goldbach singular series. Write $q=P-p$ on a row with $p\in I$ prime. Use either the weight 1 or one of the nonnegative [neutral predecessor tag weights](https://github.com/mxym/math/commit/51304b57) $W(q-1)=\mathcal V^{-1}\sum_{a\in\mathcal A}1_{a|q-1}$. Here $a$ is a product of one prime from each of a fixed number $K$ of disjoint banks in $[\exp(L^{.1}),\exp(2L^{.2})]$, all prime to $P(P-1)$, with reciprocal mass between $1/4$ and $1/2$ per bank, and $\mathcal V=\sum_a1/a$. All estimates are uniform in such a choice; their averages are allowed. Put $dM(p)=(\log p)W(q-1)$ as a discrete counting weight.

Fix $0<g<b<b'<1/2$, let $f$ be a fixed smooth function on $[0,\infty)$ identically 1 on $[0,b]$ and 0 on $[b',\infty)$, and set $z=P^\eta$. Throughout, $\eta>0$ is sufficiently small relative to these fixed data. Take $P\to\infty$ **first**, then $\eta\downarrow0$. The statements below use
$$ E(\eta)=\eta^{-2}\exp\{-c\eta^{-1}\log(1/\eta)\}, $$
where $c>0$ may depend on $1/2-g$ and $b-g$. The error bounds allow an additional $o_\eta(1)$, uniform in the target at each fixed $\eta$, and constants depending on the fixed cuts, $f,K$. No uniformity at an unspecified moving $\eta(P)$ is required.

Write $\mathcal T=\{t:\mu^2(t)=1,\ P^-(t)>z\}$, including 1. Put $w_t=\log(t)/L$. On a row with $t|q$, define the nonnegative weight
$$B_t(q)=
\begin{cases}
 \log(q/t), & q\text{ has no prime factor }\le z,\\
 \log r, & q\text{ has exactly one distinct prime factor }r\le z,\\
 0, & \text{otherwise}.
\end{cases}$$
There is no squarefreeness hypothesis on $q$. Put $M_t=\sum_{p\in I,\ t|q}dM(p) B_t(q)$ (all source sums in this note are over true primes). Let $\gamma_E$ denote Euler's constant, and put $G=\sum_{p\in I}dM(p)\Lambda(q)$.

**Theorem.** (i) Even with an absolute value taken **separately for every rough part**, the full upper smooth-divisor tail satisfies
$$
\frac1{X_P}\sum_{\substack{t\in\mathcal T\\t\le P^g}}
\left|\sum_{\substack{p\in I\\t|q}} dM(p)
\sum_{\substack{k|q\\P^+(k)\le z}}\mu(k)\log\frac q{tk}\,[1-f(w_t+\log(k)/L)]\right|
\ll E(\eta)+o_\eta(1). \tag{1}
$$
Take $P^+(1)=1$. Since $t$ and $k$ are coprime, $tk|q$. No upper bound is imposed on $tk$ other than the actual $q$. In particular arbitrary bounded multipliers on $t$ are allowed; (1) is not an absolute bound on individual smooth divisors $k$.

(ii) Write $u=g/\eta$ and use Dickman's $\rho$. There is a literal signed decomposition
$$
\frac{G}{X_P}=C_{\eta,g}+\frac1{X_P}
\sum_{\substack{t\in\mathcal T\\t>P^g}}\mu(t)M_t
+O(E(\eta))+o_\eta(1),\qquad
 C_{\eta,g}=e^{-\gamma_E}\left[(\eta^{-1}+1-u)\rho(u)+\int_0^u\rho(v)\,dv\right].
\tag{2}
$$
Here $C_{\eta,g}=1+O_g(E_1(\eta))$, with $E_1$ of the same form as $E$ after decreasing $c$ if necessary. Every $M_t\ge0$; on an actual prime $q$ the only upper divisor is $t=q$, and $B_q(q)=0$. Thus the upper remainder, whose sign is **not** known, is supported on actual nonprime rows with at most one distinct small prime. $G$ differs from the two-prime log-weighted count by $P^{1/2+o(1)}$ from proper powers (there are $O(\sqrt P L)$, and $W\ll_K L^K$). An upper remainder uniformly greater than $-(1-\kappa)X_P$ for one fixed $\kappa>0$ and arbitrarily small fixed $\eta$ would imply large-even Goldbach; we do not have such a bound. The full remainder may cancel the main.

## 1. Exact physical pooling and its conditional first moment

Expanding smooth squarefree divisors gives **exactly**
$$\sum_{k|q,\ P^+(k)\le z}\mu(k)\log(q/(tk))=B_t(q),\qquad
 \Lambda(q)=\sum_{t\in\mathcal T,\ t|q}\mu(t) B_t(q). \tag{3}$$
For a nonempty set of small prime labels the constant cancels; the first logarithmic moment is $\log r$ precisely for a singleton and vanishes for two or more labels. Powers of $r$ do not create extra labels. The second assertion follows by uniquely splitting the squarefree divisor in $\mu*\log$ into rough and smooth parts. In particular the complete sector whose divisor has at least one factor $>z$ is $\Lambda(q)-B_1(q)\le0$ pointwise: for a prime power $h^j$ equality or the inequality follows directly by comparing $\log h$ to the displayed cases.

We prove the stronger estimate
$$
\sum_{\substack{t\in\mathcal T,\ t\le P^g\\(t,P)=1}}
\left|\frac{M_t}{X_P}-\frac{e^{-\gamma_E}}{\phi(t)}
       \big[(1-w_t)/\eta+1\big]\right|\ll E(\eta)+o_\eta(1).
\tag{4}
$$
Primes $p|P$ can be removed at a total cost $P^{o(1)}$ in (1)–(4), including all their divisor sums: $W\ll L^K$, $\tau(q)^2=P^{o(1)}$, and there are $O(L)$ such $p$. In fact $q=P-p$ may have multiple divisors containing the exceptional $p$, but this bound counts them all. Other source rows force $(t,P)=1$.

For fixed $a,t$, admissible underlying primes satisfy $p\equiv P-1\bmod a$ and $p\equiv P\bmod t$. Here $(a,t)=1$ and both residues are units. To count rough rows, sieve $q$ on primes $h\le z$ not dividing $aP$. Their conditional prime density is $g(h)=1/(h-1)$; at primes dividing $a$ the value $q=1\bmod h$ is already safe, and at primes dividing $P$ the only anomalous source prime was removed above. To impose a singleton $r$, take $r\le z$, $r\nmid aP$, $r|q$, with multiplier $1/(r-1)$, and sieve all other eligible labels, omitting $r$ from the sieve. Thus, relative to the common rough product $V_{aP}(z)=\prod_{h\le z,\ h\nmid aP}(1-1/(h-1))$, the multiplier for the marked rows is **exactly** $1/(r-2)$. This counts every higher valuation at $r$, not only valuation one. All sieving products are coprime to the rough $t$. There is never an extra $t/\phi(t)$ local correction besides the base $1/\phi(t)$ in the prime progression density.

Here are details of the *joint absolute* approximation. Take $\lambda=(1/2-g)/3$, level $D=P^\lambda$, and $s=\lambda/\eta$. For small $\eta<\lambda$ the largest complete modulus $at r j$, $j\le D$, is $\le P^{g+\eta+\lambda+o(1)}<P^{1/2-c_g}$. The unmarked case omits $r$. Upper/lower fundamental-lemma weights with modulus $j$ and $|\lambda_j^\pm|\le1$ approximate each nonnegative count, with relative model error $O(s^{-s/2})$. The dimension-one product hypothesis is uniform since removing primes only helps, 2 is absent, and the full odd-prime product over $v\le h<w$ is at most a constant times $\log(2w)/\log(2v)$ by Mertens. See Friedlander–Iwaniec, *Opera de Cribro*, Lemma 6.11, also [Kurlberg–Lester–Rosenzweig, Theorem 2.2](https://www.cambridge.org/core/journals/forum-of-mathematics-sigma/article/superscars-for-arithmetic-point-scatters-ii/3CCB969E058792C1803466AE0EF29136). All progression errors, even after absolute values before summing $a,t,r,j$, contribute $O_A(PL^{-A})$ for every fixed $A$. Indeed the combined modulus has at most $\tau(at r j)^{O(1)}$ reconstructions, each a unit CRT residue. Use maximal Bombieri–Vinogradov over residues and endpoints, with divisor weights absorbed by Cauchy from the arbitrary-log estimate and the trivial bound $O(L(P/m+1)+P/\phi(m))$ for a discrepancy at modulus $m$. Prime (rather than von Mangoldt) weights are also allowed: across $m\le P^{1/2-c_g}$ the trivial $O(\sqrt P L^2)$ per modulus removes powers with a power saving even after divisor weights. Other logarithmic factors cost at most $O(L^2)$; $\mathcal V$ is bounded below. BV and partial summation handle the central endpoints. Removing $p|P$ at the progression-theorem stage causes no issue: the trivial $O(L^2)$ cost per reconstructed term is still power-saving over all eligible moduli. No prime-pair distribution enters.

The Euler evaluations, uniform in $P,a$, are
$$
 V_{aP}(z)=\frac{e^{-\gamma_E}\mathfrak S(P)}{\eta L}(1+o_\eta(1)),\quad
 \sum_{r\le z,\ r\nmid aP}\frac{\log r}{r-2}=\eta L+o_\eta(L),\quad
 \mathcal V^{-1}\sum_a\phi(a)^{-1}=1+o(1).
$$
The first follows by comparison with $\prod_{h\le z}(1-1/h)$; missing target factors above $z$ cost $O(L/z)$ and the tags contribute $O_K(\exp(-L^{.1}))$. For the middle formula, the denominator change from $r$ costs $O(1)$ after 2 is excluded; primes of $P$ up to $L^2$ cost $O(\log(2L))$, and larger ones cost $O(1/L)$ since their log sum is at most $L$. Tag exclusions are negligible. On the central rough rows replace $\log(q/t)$ by $(1-w_t)L+O(1)$, with the same upper sieve bounding the rounding error. Finally $\sum_{t\in\mathcal T, t\le P^g}1/\phi(t)\ll_g1/\eta$ by the Euler product for $z<h\le P^g$. The two sieve inequalities sandwich each row count; summing their endpoint discrepancies and relative errors as just bounded proves (4), since $s^{-s/2}\ll\exp(-c_g\eta^{-1}\log(1/\eta))$. In particular (4) is not an absolute bound on a conditional *model* in place of the data.

## 2. Entire upper tail beyond the low model

Write $M_t^f$ for the expression defining $M_t$ in (3) with $f(w_t+\log k/L)$ inserted in its smooth sum. Ordinary maximal BV applies simultaneously to every $a,t,k$ here: $atk\le P^{b'+o(1)}$, $(t,k)=1$, and $(a,k)=1$ is necessary. Partial summation handles $\log(q/(tk))$; its variation is $O(1)$ on $I$. The total absolute progression error, summed over $t$ before applying signs, is $O_A(PL^{-A})$ by the same divisor multiplicity argument. Restoring $(a,k)=1$ in the main only costs, per factor $1/\phi(t)$, $O_K(L^2\exp(-L^{.1}))$ by a harmonic absolute Euler product and summing the $K$ possible forbidden primes. Unit exceptions for the target are kept in the main.

For $w\in[0,g]$, put $F_w(v)=(1-w-v)f(w+v)$, $v\ge0$. The signed two-moment and rough convolution calculation in [Signed smooth-modulus sectors, §§2–3](https://github.com/mxym/math/commit/488c8f84) gives
$$
\frac{M_t^f}{X_P}=\frac{A_\eta(w_t)+o_\eta(1)}{\phi(t)}
     +\text{jointly summable progression error},\quad
 A_\eta(w)=-F_w'(0)-\eta^{-1}\int_0^\infty F_w'(v)\omega(v/\eta)\,dv.\tag{5}
$$
Here and below $\omega$ is extended by zero on $[0,1)$. For clarity, factor $c_P(k)1_{P^+(k)\le z}=(c_P*h)(k)$, $c_P=\mu/\phi$ on units modulo $P$ and zero elsewhere, $h(r^j)=(r-1)^{-j}$ on primes $r>z$, $r\nmid P$. The whole $c_P$ moments are $0,-\mathfrak S(P)$, with tails beyond $\exp(L^{.1})$ smaller than any power of $1/L$ uniformly in $P$. Taylor against $F_w(v+\log k/L)$ gives $-\mathfrak S(P)F_w'(v)/L+o(1/L)$ uniformly; no vanishing of $F_w$ at zero is needed because all arguments are nonnegative. The error from $\log(1-p/P)$ in $\log(q/(tk))$ is $O_\eta(\mathfrak S(P)/L)+o_\eta(1)$ per normalized local main before summing $1/\phi(t)$, by the same expansion with test $f(w+v)$. The limiting $h$-measure is $\delta_0+\eta^{-1}\omega(v/\eta)dv$, with bounded compact mass at fixed $\eta$. Uniformity over $w\in[0,g]$ follows from uniform derivatives and sup-norm compactness of the family of translated tests and their derivatives. This proves (5), **including the atom at zero**. Sources of (5) are the stated elementary Euler/convolution calculation and the ordinary prime distribution theorem, not distribution at the full modulus $tk$ in (1).

For the secondary constant, let $c_0=e^{-\gamma_E}$. We have
$$
 \int_0^\infty [\omega(y)-c_0]dy=c_0-1,\qquad
 \int_U^\infty |\omega(y)-c_0|dy\ll \exp\{-c_1 U\log U\}\quad(U\ge 4).
 \tag{6}
$$
Indeed $1+\int_0^U\omega(y)dy=(U+1)\omega(U+1)$ for $U\ge1$. The delay equation gives $|\omega'(v)|\le v^{-1}\int_{v-1}^v|\omega'(y)|dy$ for $v>3$, hence factorial decay by successive intervals. The limit of $\omega$ is $c_0$, for example from the Laplace transform $\exp(\int_1^\infty e^{-sx}dx/x)$ of the convolution measure; its leading pole at $s=0$ is $c_0/s$. These facts give (6), including the $-1$ from the atom. Now $F'_w(0)=-1$ and $F'_w(v)=-1$ for $v\le b-g$. Subtract the constant $c_0$ in the integral in (5). Its constant-density piece is $c_0(1-w)/\eta$, since $F_w(0)=1-w$. The leftover integral may use $F'_w=-1$ everywhere at a cost $\ll_f\exp(-c(b-g)\eta^{-1}\log(1/\eta))$ for small $\eta$ by (6). Thus
$$
 A_\eta(w)=1+c_0(1-w)/\eta+(c_0-1)+O_{f,b-g}(\exp(-c_{b-g}\eta^{-1}\log(1/\eta))).
$$
The secondary is $c_0$, not $1$. Summing the difference from (4) with its $1/\phi(t)$ factor proves (1).

## 3. The signed rough part and its genuinely nonnegative physical price

For fixed $\eta,g$, the signed harmonic measure on $v=\log(t)/\log z$ of $\mu(t)/\phi(t)$, $t\in\mathcal T$, $(t,P)=1$, has weak limit on $[0,u]$
$$ d\mathcal D(v)=\delta_0+\rho'(v)dv. $$
Indeed replacing $1/(h-1)$ by $1/h$, reinstating primes of $P$ above $z$, and allowing repeated coordinates in the convolution each cost $o_\eta(1)$ in total variation on this compact range, by $\sum_{h>z}h^{-2}\ll1/z$, $\sum_{h|P,h>z}1/h\ll L/z$, and the bounded unsigned harmonic Euler product. For each number of labels $j\le u$ their limit is $(-1)^j/j!$ times the convolution of $j$ copies of $\mathbf1_{v\ge1}dv/v$, by Mertens; endpoints $u>1$ have no limit atom. The cumulative signed function is 1 up to 1, and satisfies $v\rho'(v)=-\rho(v-1)$ by distinguishing one factor on the boundary. These are Dickman's initial data and equation. In particular $\rho$ is positive, decreasing beyond 1: the identity $v\rho(v)=\int_{v-1}^v\rho(s)ds$ for $v\ge1$ excludes any finite first zero and gives factorial decay. Also $\int_0^\infty\rho(v)dv=e^{\gamma_E}$: its Laplace transform is $s^{-1}\exp(-\int_1^\infty e^{-sx}dx/x)$ by the signed exponential convolution, and taking $s\downarrow0$ gives the assertion.

Therefore (4), now summing with the genuine signs $\mu(t)$, evaluates the normalized small-$t$ sum to within $O(E(\eta))+o_\eta(1)$ by
$$
 c_0\int_{[0,u]}(\eta^{-1}+1-v)d\mathcal D(v)
 =c_0\left[(\eta^{-1}+1-u)\rho(u)+\int_0^u\rho(v)dv\right].
$$
The claim that this is $1+O_g(E_1(\eta))$ follows from the factorial tail and $u=g/\eta$. Subtracting this actual small-$t$ contribution from (3) proves (2). This is an **absolute-scale approximation** to the small-$t$ partial sum at each fixed even target; the upper sum is left whole, with no averaging of its signs. In particular at $t=1$, (4) prices all smooth divisors together, even when their product exceeds $P^{1/2}$; the raw nonsmooth sector is precisely $G-M_1$, not a second independently positive main. Its magnitude before centering must not be compared to an individual size mask.

The only distribution input is classical Bombieri–Vinogradov below a fixed-gap square-root level; neither it nor a smooth-modulus improvement is applied to the unrestricted upper sum. The lower-range identity is a truncated rough Möbius inversion, not a new one-dimensional sieve or a lower bound for the prime pairs. Related [rough cofactor law](https://github.com/mxym/math/commit/5b025c9e) and [signed smooth over-root sectors](https://github.com/mxym/math/commit/488c8f84) analyze other cuts. This estimate pools all smooth divisors at each individual small rough part, including unrestricted large products, and states explicitly which actual parity-signed remainder is not estimated.
