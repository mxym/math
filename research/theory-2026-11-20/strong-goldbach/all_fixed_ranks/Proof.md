# A positive-mean signed detector with no adverse bounded-rank sector

Fix an integer $r\geq3$, not growing with the target. Let $P$ run through even integers, $L=\log P$, $F=n(P-n)$, and $W\geq0$ be fixed, smooth, nonzero and supported compactly inside $(1/3,2/3)$. Write $X=P\int W$ and $\mathfrak S(P)=2\prod_{p>2}(1-(p-1)^{-2})\prod_{2<p\mid P}(p-1)/(p-2)$. The filter below depends on $r$; all its shape constants are fixed **before** $P$ tends to infinity. Rank means the total number of prime factors of the physical squarefree product $F$, across both sides.

Use the sharp or fixed-smooth quadratic detector $K$ of the [coupled critical product theorem](https://github.com/mxym/math/commit/5190f4df). For example
$$
K(F)=\sum_{d\mid F}\mu(d)(\log F-2\log d)_+^2 .
$$
We use only its already proved squarefree first moment $8X\mathfrak S(P)+O_A(PL^{-A})$, and that its actual two-prime value is $4\log n\log(P-n)$. The new part is an explicit signed correction of zero mean that charges *every* nonprime pair of total rank at most $r$, up to negligible errors.

**Theorem.** There are an explicit smooth function $0\leq\psi\leq1$, an exponent $0<a<1$, and a constant $C_r>0$ such that, setting
$$
J_\ell(F)=\sum_{d\mid F}\mu(d)\psi\left(\frac{\log d}{\log\ell}\right),\qquad
M(F)=L^2\!\!\!\sum_{\substack{\ell\mid F,\ \ell\ {\rm prime}\\
                          \exp(\sqrt L)\leq\ell\leq\sqrt P}}
        \left(\frac{\log\ell}{L}\right)^a J_\ell(F),\qquad
D_r(F)=K(F)-C_r M(F),
$$
one has, for every $A>0$,
$$
\sum_n W(n/P)\mu^2(F)D_r(F)=8X\mathfrak S(P)+O_{A,r,W}(PL^{-A}).
\tag{1}
$$
On genuine distinct prime pairs $D_r=4\log n\log(P-n)$. On every other squarefree row of rank at most $r$ with least prime factor at least $\exp(\sqrt L)$, one has **pointwise $D_r\leq0$**. Even on including the smaller least factors, the total positive part on the nonprime rows of rank at most $r$ is $o_r(X\mathfrak S(P))$. In particular, writing $G$ for the ordered, weighted, log-prime Goldbach sum,
$$
4G+\sum_{\substack{n:\ F\ {\rm squarefree}\\\omega(F)>r}}
        W(n/P)\,(D_r(F))_+
\ \geq\ (8-o_r(1))X\mathfrak S(P).
\tag{2}
$$
Thus if a growing sequence of counterexamples exists, the **actual** positive leakage must supply at least $(8-o_r(1))X\mathfrak S(P)$ above *any prescribed fixed* total rank, for its corresponding detector. We do not bound that tail, allow $r=r(P)$, assert uniform total variation as $r$ grows, or infer Goldbach positivity.

## Logarithmic profile design

Choose $\epsilon=(100r2^r)^{-1}$. Take a fixed smooth nonincreasing cutoff $H:\mathbb R\to[0,1]$, equal to 1 on $(-\infty,0]$ and zero on $[1,\infty)$ (for instance the normalized tail integral of $\exp(-1/[s(1-s)])1_{0<s<1}$). Set $T=(1+\|H'\|_\infty)/\epsilon$, $v_0=e^{-T}/4$, and, for $t>0$, $\psi(t)=H(\log(t/v_0)/T)$; set $\psi(0)=1$. Thus $\psi=1$ near zero, $\psi=0$ for $t\geq1/4$, and $|t\psi'(t)|\leq\epsilon$. Write $B=\max(1,\|\psi'\|_\infty)$ and choose $a=\min(1/2,\log(2)/[1+\log(B/\epsilon)])$. In particular
$$
\min(\epsilon,Bu)\leq 2\epsilon\,u^a\quad(0<u\leq1).
\tag{3}
$$
Indeed the maximum after division by $u^a$ is at $u=\epsilon/B$.

On a squarefree row write $x_i=\log p_i$ in increasing order, $x=x_1$, and let $y=\log\ell$ for any prime tag of the row. If $m=\omega(F)\leq r$, pair divisor subsets by the first bit (the smallest prime). The empty subset of the *other* bits gives $1-\psi(x/y)\geq0$. Each other subset has log-sum $s\geq x$; its paired difference has absolute value at most
$$
\min\{ Bx/y,\ \epsilon\log((s+x)/s)\}\ \leq\ \min\{Bx/y,\epsilon\}.
$$
These bounds, (3), and the nonnegative empty pair give
$$
(y/L)^a J_\ell(F)\geq -2^r\epsilon(x/L)^a.
\tag{4}
$$
For the absolute bound include the empty subset and use $|1-\psi(x/y)|\leq Bx/y$, giving $|(y/L)^aJ_\ell(F)|\leq2^{r-1}B(x/L)^a$ (as $x\leq y$). At the smallest tag itself, $J_{p_1}(F)=1$ exactly: every divisor other than 1 has $\log d/\log p_1\geq1$. If either side is composite its smallest prime is at most $\sqrt{2P/3}<\sqrt P$. Thus whenever this tag is retained, summing (4) yields $M(F)\geq(1-r2^r\epsilon)L^2(x/L)^a$. Pairing the smallest bit in $K$ itself, the hinge has derivative bounded by $5L$ on the actual arguments, also under the fixed symmetric smoothing, so $|K|\leq 10\cdot2^r Lx$. Hence one may take $C_r=32\cdot2^r$; since $0<x/L<1$, this proves the pointwise assertion.

If the smallest prime was omitted, $x<\sqrt L$ instead. The preceding absolute bounds give $|D_r(F)|\ll_r L^{2-a/2}$. The price after summation is negligible by the uniform counting estimate below. The omitted diagonal $n=P/2$ on prime pairs changes $G$ by at most $O_W(L^2)$. No sieve inference is made from the sign of a row at unbounded rank.

## Exact zero mean of the tags

Uniformly for any multipliers $|\gamma_\ell|\leq1$ on the displayed tags,
$$
\sum_n W(n/P)\mu^2(F)\!
  \sum_{\ell\mid F}\gamma_\ell J_\ell(F)\ll_{A,W,\psi} PL^{-A}.
\tag{5}
$$
Here and in this proof a tag always means a prime in the displayed range. Prove this even with arbitrary signs; the $L^2$ in (1) costs only a power of the logarithm. On squarefree rows we may and do exclude from the outset all primes dividing $P$ from both the tags and the divisor labels. Indeed $\mu^2(F)=1_{(n,P)=1}\mu^2(n)\mu^2(P-n)$. In particular $2$ is not a tag. Every $d$ in $J_\ell$ is at most $\ell^{1/4}$; hence $\ell\nmid d$.

As in the coupled product proof, open the two squarefree indicators by $k^2\mid n$, $j^2\mid P-n$ with coefficients $\mu(k)\mu(j)$. Trim to $k,j\leq(\log P)^{B_1}$ while still retaining the unit condition; there one can require $(kj,P)=(k,j)=1$. The absolute contribution lost is $O_A(PL^{-A})$ for sufficiently large $B_1(A)$. Indeed the number of inputs with some square divisor beyond the trim on either leg is $\ll P L^{-B_1}+\sqrt P$. Cauchy with $\sum_{m\leq P}\tau(m)^h\ll_h P L^{2^h-1}$ bounds all multiplicities, including both the tag and divisor sums and truncated square indicators, by a fixed power of $\tau(n)\tau(P-n)$ in the corresponding moment. No positivity of the signed weight is needed.

Next expand the unit condition by $\sum_{c\mid(P,n)}\mu(c)$, and assign the distinct primes of the squarefree $d$ and the tag $\ell$ to their roots $n=0,P$ modulo the prime. Keep only compatible CRT systems after adjoining $c,k^2,j^2$. For each such single progression, the ordinary smooth sum equals its integral density times $X$ with error $O_W(1)$ by bounded variation. The sum of all errors is $O(P^{5/8+o(1)})$: there are at most $P^{1/2}$ tags, $P^{1/8}$ divisor labels per tag, $2^{1+\omega(d)}=P^{o(1)}$ assignments, $\tau(P)=P^{o(1)}$ choices of $c$, and polylogarithmically many square labels. This elementary estimate is sufficient even without a power saving for any individual large progression.

Restore all $k,j$ in this *model* with arbitrary log accuracy. To see absolute convergence uniformly, assign $d=ab$ to its two sides and first assign $\ell$ to the first side. When compatible, its density, including $c\mid n$, is at most
$$
\frac{(a,k)(b,j)}{c k^2 j^2 a b}\frac{(\ell,k)}{\ell}.
$$
This uses $\ell\nmid d$, $(d\ell kj,P)=1$, and squarefreeness of $d$; when $\ell\mid j$ the assignment is incompatible. For the other tag side swap $k,j$ accordingly. The sum of $(\ell,k)/\ell$ over the tags is $O(\log L+\omega(k))$, even if a restored square label contains a tag. The harmonic sums over $a,b$ cost $O(L^2 2^{\omega(k)+\omega(j)})$ by factoring out the divisors of their respective radicals. Summing $1/c$ over divisors of $P$ costs $O(\log L)$. The remaining tails $\sum_{k>T}2^{\omega(k)}(1+\omega(k))/k^2\ll T^{-1}(\log(2T))^{O(1)}$ give the required accuracy.

For one tag let $D_{P,\ell}(s)$ denote the density-weighted Dirichlet series in the untagged divisor variable, omitting prime $\ell$ entirely. After restoring the squarefree conditions it is the product of the generic local factors
$$
1-2p^{-1-s}-2p^{-2}(1-p^{-s})\quad(p\nmid P,\ p\ne\ell)
$$
and the target factors $1-1/p$ at $p\mid P$. These follow by averaging over $n\bmod p^2$: for unit target primes $p$ the probabilities of valuations 0 and 1 are $1-2/p$ and $2/p-2/p^2$, and at $p\mid P$ the physical unit condition leaves one factor $1-1/p$. The missing tag contributes the external constant $b_\ell=2/\ell-2/\ell^2$ (valuation exactly 1), independent of the divisor label. Thus $D_{P,\ell}(s)=\zeta(1+s)^{-2}H_{P,\ell}(1+s)$ with $H$ holomorphic and $\ll(\log L)^{O(1)}$ for $\Re(s)\geq-c/\log L$. As in the coupled theorem, divide the generic factors by $(1-p^{-1-s})^2$; absolute convergence controls all generic factors and the omitted large prime. At $p\mid P$, the extra terms cost only $(\log L)^{O(1)}$ by splitting those primes at $L$: below $L$ use Mertens, and above $L$ use $\omega(P)\ll L$ and $p^{-1+c/\log L}\ll 1/L$. This estimate also holds on vertical lines at large height.

If $a_d$ are the coefficients of $D_{P,\ell}(s)=\sum_d a_d d^{-s}$, the quadratic Mellin integral gives
$$
\sum_d a_d\log_+^2(Y/d)=2H_{P,\ell}(1)+O_{A,\psi}(L^{-A})
$$
uniformly for $Y=\ell^v$, $v_0\leq v\leq1/4$. Here $\log Y\geq v_0\sqrt L$. For explicit contours, truncate $2Y^s/s^3$ on $\Re(s)=1/\log Y$ at height $\exp(c_1\sqrt{\log Y})$ where the absolute Euler series costs a power of $L$. Shift to $\Re(s)=-c_2/\sqrt{\log Y}$ inside the classical zeta zero-free region and the preceding strip; the left and horizontal errors are $O(L^{O(1)}\exp(-c_3\sqrt{\log Y}))$. The only residue comes from the double zero at $s=0$. The large constant $v_0^{-1}$ is fixed for each $r$.

Three integrations by parts give, for $t\geq0$, $\psi(t)=-\frac12\int_t^\infty(v-t)^2\psi'''(v)\,dv$. The support of $\psi'''$ lies in $[v_0,1/4]$ and $\int\psi'''=0$ because $\psi$ is flat at both ends. Using the last quadratic formula under this integral, divided by $(\log\ell)^2$, the constant term cancels **exactly**. The resulting one-tag model is $O_{A,\psi}(X b_\ell L^{-A})$. Summing $b_\ell\ll1/\ell$ proves (5). No claim about cancellation of the absolute divisor coefficients is used.

## A uniform bounded-rank count on the actual two forms

The needed elementary consequence of the upper sieve is
$$
\#\{P/3\leq n\leq2P/3:\mu^2(F)=1,\ \omega(F)\leq r\}
   \ll_r \mathfrak S(P)\frac{P}{L^2}(1+\log L)^r.
\tag{6}
$$
Set $z=P^{1/(100(r+1))}$, and let $b$ be the *full* product of prime factors of $F$ up to $z$. Then $b\leq z^r<P^{.01}$, $b$ is squarefree and coprime to $P$, and there are $2^{\omega(b)}$ root classes modulo $b$. On each class retain the requirement that every $p\leq z$ not dividing $b$ is absent from $F$. The [standard upper-bound sieve](https://www.numdam.org/article/AST_1975__24-25__281_0.pdf) on that single progression, at (say) level $D=P^{1/3}$, gives
$$
\ll_r \frac P b\prod_{\substack{p\leq z\\p\nmid b}}\left(1-\frac{\rho_P(p)}p\right)+O(P^{1/3+o(1)}),\qquad
\rho_P(p)=\begin{cases}1&p\mid P,\\2&p\nmid P.\end{cases}
$$
Indeed on the progression all compatible squarefree submodulus root errors are $O(2^{\omega(d)})$ by CRT; upper sieve remainder coefficients are divisor-bounded and their total up to $D$ is $D^{1+o(1)}$. Sieve dimension at most two holds uniformly since each prime has at most two roots (at 2 only one) and $\log D/\log z>30$. By Mertens the product including all $p\leq z$ is $\ll\mathfrak S(P)/(\log z)^2$; deleting at most $r$ odd factors costs at most $3^r$. Sum $2^{\omega(b)}/b$ for $\omega(b)\leq r$ by Mertens, which costs $O_r((1+\log L)^r)$. Even the total of all the absolute errors is $\ll P^{.35}$ for large $P$. This proves (6), and the dropped-small-tag contribution is $O_r(P\mathfrak S(P)L^{-a/2}(1+\log L)^r)=o_r(X\mathfrak S(P))$, completing (2).

**Interpretation.** The very small logarithmic slope is used on *nonempty* subset pairs only. Applying a uniform small error to the empty pair would destroy the unit gain at the smallest factor. The first-moment cancellation comes from the flat second derivative at the origin, not from a distribution theorem for actual primes at large additive shifts. Neither a finite computation at bounded rank nor the family (2) controls the residual unbounded-rank sign.

## Related work and replay

[Arneth’s October cubic minorant](https://zenodo.org/records/23477014) similarly separates an exact low-rank shape from a required arithmetic estimate; its uniform signed correlation is posed as a condition. [Chan’s November (1+1.75) preprint](https://aixiv.science/pdf/aixiv.261111.000001v1.0.pdf) supplies a positive sieve for a different prime-or-semiprime representation, not a bound for this signed high-rank tail. The companion [exact replay](replay.py) checks the finite algebra, local factors, and exponent margins, not the cited asymptotic estimates. These comparisons do not assert priority.
