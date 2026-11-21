# A nonempty prime-or-semiprime long-cofactor family for the same-cofactor switch

Let $P$ be a sufficiently large even integer, $L=\log P$, $Y=P^{1/25}$, $A=P^{24/25}$, $\mathcal L=\{\ell\text{ prime}:Y\le\ell\le1.01Y,\ \ell\nmid P\}$, $J=[.41A,.42A]$. Write $\mathfrak S(P)=2\prod_{p>2}(1-1/(p-1)^2)\prod_{p>2,\ p\mid P}(p-1)/(p-2)$ and
$$
 {\cal T}=\frac{\mathfrak S(P)\,|\mathcal L|\,|J|}{L\log A},
$$
where $|J|=.01A$ denotes interval length. This reference is $\asymp\mathfrak S(P)P/L^3$.

**Theorem.** At least $.03{\cal T}$ pairs $(a,\ell)\in J\times\mathcal L$ have $a\ell$ squarefree, $p=P-a\ell$ prime, $P^-(a)> A^{1/10}$, and $a$ either a prime or a product of two primes. For each fixed $B\ge1$ and $0<\eta<1$, one can choose a fixed $\epsilon(\eta)>0$ so that at least a $(1-\eta)$ fraction of **this restricted prime-witness family** admits at least $c_\eta Y/L^{B+4}$ distinct prime alternatives $\ell'$ on its *same* $a$ with $|\ell'-\ell|\le Y/L^B$ and
$$
 m'=P-a\ell'\text{ squarefree},\quad M(m')=\sum_{d\mid m',\,d<\sqrt{m'}}\mu(d)<0,\qquad
 P^\epsilon<P^-(m')\le P^+(m')<\sqrt {m'}.
$$
In particular $m'$ has odd rank at least 3. Both rows $P=p+a\ell=m'+a\ell'$ are literal integer equations. This does not assert abundance of **prime** $a$ separately, or of **exactly semiprime** $a$ separately, and is not binary Goldbach. The original [unrestricted-cofactor transfer](https://github.com/mxym/math/commit/a75fffda) by itself does not prove this result because its absolute error was compared to a larger witness population.

## 1. Tagged three-term Chen inequality

Put $z=A^{1/10},\ y=A^{1/3},\ \theta=479/1000$. A row is $a\in J,\ell\in\mathcal L$ with $p=P-a\ell$ prime and $P^-(a)>z$. Set $T_0$ equal to the number of these rows, $T_1$ to their sum of the number of prime divisors $r$ of $a$ in $(z,y)$, and $T_2$ to the number of rows $a=rst$ with primes $z<r<y\le s\le t$. We may enforce squarefreeness throughout, or discard its failures on the rough rows at $O(P^{1-.095+o(1)})$: their counting multiplicities are bounded by fixed divisor powers and some $r>z$ has $r^2\mid a$ (summing such $a\le A$ costs $O(A/z+\sqrt A)$). On these rows $\ell<z$, so $\ell\nmid a$ automatically. Boundary equalities at $y$ may be included on the large side.

On every squarefree row of rank at least 3 at least one factor of $a$ is below $y$ since $a<A=y^3$. If at least two are below $y$, the half-charge per such prime already removes the row. If exactly one is below $y$, there are exactly three factors since $a<y^3$, and the special triple supplies the other half-charge. Rows of rank at most 2 receive a weight at most 1. Hence the wanted prime-occupancy count is at least
$$
 T_0-\tfrac12 T_1-\tfrac12 T_2-o({\cal T}).
 \tag{1}
$$
This is the classical Chen three-term switch, now with a **prescribed genuine short prime slot** counted as a pair $(a,\ell)$. See [the explicit original Chen weight and triple region used in the Lean project](https://subfish-zhou.github.io/goldbach-lean/blueprint/chap-chen.html). A Chen theorem with both summands in *unit* classes, such as [Lu–Cai (1999), Theorem 2](https://www.sciengine.com/doi/pdf/03a08bd295a7445caf69b311ec916e9c), cannot simply be applied to force a zero residue for $P-p$.

## 2. The two prime-progression estimates

For fixed $\ell$ let $X_\ell=(\ell-1)^{-1}\int_{P-.42A\ell}^{P-.41A\ell} dt/\log t=(1+o(1))|J|/L$ uniformly. In $T_0$ use the dimension-one lower linear sieve at $A^\theta$ for $a$, omitting primes dividing $P\ell$. A prime dividing $P$ cannot divide $a$ because $p>P/2$; the omitted $\ell$ dividing $a$ costs $O(P^{1-1/25+o(1)})$ over all rows, even if upper-sieve/divisor multiplicities occur. At $r\nmid P\ell$ the reduced model density is $g(r)=1/(r-1)$. The physical condition $d\mid a$ is the **prime** progression $p\equiv P\bmod \ell d$. Similarly for $T_1$, condition on $r\mid a$ and use the upper sieve with level $A^\theta/r$, whose density main is $X_\ell/\varphi(r)$ and whose physical moduli are $\ell r d$. The $r$ is above $z$, so it does not enter $d$. Cases $r\mid P$ are empty.

All these moduli are $\ll Y A^\theta=P^{.49984}$ times an absolute constant. The total errors of replacement are $O_E(PL^{-E})$ for any fixed $E$ by ordinary prime Bombieri–Vinogradov, **maximal in prefix**, so the varying two interval endpoints are allowed. An individual modulus has at most $\tau(q)^2$ exposed $(\ell,r)$ choices; we do not assume it has a unique tag among its divisors. The fixed divisor-weighted form follows by Cauchy from ordinary BV with upgraded log accuracy and the trivial discrepancy bound $O(P/\varphi(q))$ for $q\le P^{.4999}$, using the standard reciprocal divisor moments. Thus the variable $r$-dependent levels and coefficients introduce no unsupported distribution result. The necessary dimension bound on the Euler product follows by Mertens and only improves when primes are omitted. The lower/upper functions $f,F$ below are those of the ordinary one-dimensional linear sieve (see, e.g., [Friedlander–Iwaniec, *Opera de Cribro*, Ch. 11](https://doi.org/10.1090/coll/057)). They provide uniform $o(1)$ in the normalized sieve main for $s$ in the fixed compact ranges here. The model sifting product is
$$
  \prod_{q\le z,\ q\nmid P\ell}(1-1/(q-1))
    =(1+o(1))\,e^{-\gamma}\mathfrak S(P)/\log z .
$$
Here and below product variables in sieve products are primes. Target primes above $z$ change the completed singular factor by $o(1)$ uniformly ($\sum_{q\mid P,\,q>z}1/q\le O(L/z)$); the marked $\ell$ contributes a $1+o(1)$ correction. Partial summation in $z<r<y$ (prime Mertens with $\varphi(r)^{-1}$ in place of $r^{-1}$) gives
$$
 T_0/{\cal T}\ge 10e^{-\gamma} f(10\theta)-o(1),\qquad
 \frac{T_1}{2{\cal T}}\le
   5e^{-\gamma}\int_{1/10}^{1/3}F(10(\theta-t))\frac{dt}{t}+o(1).
 \tag{2}
$$

## 3. Switched four-prime source and its principal normalization

For $T_2$ switch to the genuine source $n=\ell r s t$, with the prescribed slots, leaving $P-n$ to be upper-sieved. Take its sifting cutoff $z'=P^{249/1000}$, and level $D'=P^{499/1000}$. All target primes may be omitted from the sifting set; restricting the physical source to $(n,P)=1$ is automatic when $P-n$ is prime, and for upper-bounding one may instead include nonunit sources in the majorant. They are negligible (one of the four prime factors, all $\gg P^{.039}$, then divides $P$). The complementary prime was above $P/2$, so it survives this sieve.

The four prime slots have an ordinary prime-product BV estimate at $D'$ by [Motohashi (1976), Theorem 2, pp. 273–274](https://www.jstage.jst.go.jp/article/pjab1945/52/6/52_6_273/_pdf/-char/en): for a fixed number of primes in arbitrary **own-product-log** exponent boxes, the resulting indicator satisfies his absolute maximal-prefix BV property (C), uniformly in the exponent endpoints, up to $\sqrt P/L^{B_0}$. To be explicit about using absolute prime windows and the product constraint $rst\in J$, split the central product $n$ into relative intervals of width at most $L^{-H}$ and the four sorted $\log p_i/\log n$ into grids of width $L^{-H-2}$, with any fixed $H>3$. Retain every cell containing a permitted tuple; this is a majorant via the actual nonnegative sieve divisor sum (also adequate to bound the prime indicator directly). Each coordinate in a retained cell is within a relative factor $1+O(L^{-H})$ of its permitted interval or boundary; likewise the product $rst$. The $\ell$ prime is separated from the others, the order is $\ell<r\le s\le t$, and sorted bin **multisets** count each source once, including two identical bins. On the original squarefree source unique factorization identifies a single ordered triple; repeated prime cases in the enlargement cost $O(P^{1-.039+o(1)})$, even with divisor weights. Define half-open boundaries by arbitrarily small endpoint perturbation on the finite range. Polynomially many cells and two prefixes for $n$ are paid by increasing Motohashi's log accuracy. This argument keeps the full factor restrictions until after a genuine distribution estimate; it is not BV for a prime times an arbitrary long cofactor.

Reverse the reduced-class averages and apply the upper linear sieve with $g_n(q)=1/(q-1)$ at $q\nmid nP$, zero otherwise. By the same dimension bound and Mertens normalization it gives per source
$$
  (1+o(1))\frac{e^{-\gamma}\mathfrak S(P)}{\log z'}F\!\left(\frac{\log D'}{\log z'}\right)
    =\bigl(2/.499+o(1)\bigr)\frac{\mathfrak S(P)}{L}.
$$
Indeed the source has only four polynomially large prime factors, changing its local product by $1+o(1)$ uniformly, and $F(s)=2e^\gamma/s$ for $s\le3$ in the usual normalization. The linear-sieve **upper weights independent of $n$** provide this bound for the varying deleted local probabilities; the dimension hypothesis is uniform. This proves the actual transfer from the four-prime source to an upper bound for $T_2$.

The number of sources in the enlarged region is at most
$$
 (I+o(1))\,|\mathcal L|\,|J|/\log A,\quad
 I=\int_{1/10}^{1/3}\frac{du}{u}\int_{1/3}^{(1-u)/2}
                      \frac{dv}{v(1-u-v)}
   =\int_{1/10}^{1/3}\frac{\log(2-3u)}{u(1-u)}\,du .
$$
For fixed $r,s$, the largest prime ranges in $J/(rs)$ with $t\ge s$; dropping the latter condition for the length upper bound changes the upper estimate only in the favorable direction. Prime PNT on the full intervals of fixed relative width gives at most $(1+o(1))|J|/[rs\log(A/(rs))]$ uniformly, including the harmless relative endpoint enlargement. The potential $s$ satisfy $s\le\sqrt{(.42+o(1))A/r}$, with $s\ge(1-o(1))A^{1/3}$ and $r$ in the stated enlarged window. Prime Mertens in the two exponent variables, for a compact positive-power domain with boundary of zero measure, yields the integral. The slight enlargement of the $\ell$-interval likewise changes its genuine prime count by $o(|\mathcal L|)$ by squeezing and the PNT. In particular
$$
                    T_2/(2{\cal T})\le I/.499+o(1).
 \tag{3}
$$
This factor is in the *same* normalization as (2); there is no loss or gain of a $\log A/\log P$ from the switch.

## 4. Directed numerical certificate

Set $s_0=10\theta=4.79$. In (2) the usual delay-equation solutions give
$$
 e^{-\gamma} F(w)=\frac2w\left(1+{\bf1}_{w>3}\int_2^{w-1}\frac{\log(v-1)}v\,dv\right)\quad(0<w\le4),
$$
and
$$
 e^{-\gamma}f(s_0)=\frac2{s_0}\left(\log(s_0-1)+
       \int_3^{s_0-1}\frac{du}u\int_2^{u-1}\frac{\log(v-1)}v\,dv\right).
$$
Subtracting the two right-hand main terms in (2) and reversing the two non-elementary integrations gives
$$
 C_0-\frac1\theta\int_2^{s_0-2}\frac{\log(t-1)}t
                \log\!\frac{(t+1)(s_0-t-1)}{s_0-1}\,dt,\qquad
 C_0=\frac{\log((s_0-1)(3\theta-1))}{\theta}.
$$
For instance the elementary term in the upper integral is $\int_{1/10}^{1/3}dt/[t(\theta-t)]$; for its non-elementary term at fixed inner variable $v$ the $t$-range ends at $\theta-(v+1)/10$. These give exactly the displayed simplification. The accompanying rational verifier takes a lower bound for $C_0$ and upper bounds for this last integral and $I/.499$ (1024 rectangles, directed rational logarithms via the $\operatorname{atanh}$ series and its geometric remainder). With Python optimizations enabled it certifies the final lower constant
$$
 \frac{4196921349}{125000000000}>.0335>.03 .
$$
The margin absorbs the $o(1)$ errors in (1)–(3). No conjectured numerical distribution or prime search is used.

## 5. Restricting the cofactor switch at the correct source density

In [the source-uniform cofactor proof, equation (1) and its derivation](https://github.com/mxym/math/commit/a75fffda), the multipliers $|\alpha_{a,I}|\le1$ are arbitrary for each long cofactor and short log bin $I$ of width $\le Y/L^B$. Before summing long cofactors, the error bound is the product of the per-source rough sieve factor $V_{a\ell P}(P^\epsilon)$ and
$$
 \rho(1/(2\epsilon))+O\bigl(\epsilon^{-1}u^{-u/2}\bigr)+o_\epsilon(1),\qquad
 u=1/(200\epsilon).
$$
The distribution error has arbitrary log savings. Insert into the long multiplier the actual indicator of the $z$-rough, squarefree prime-or-semiprime cofactors here. On them $a/\varphi(a)=1+o(1)$ and
$$
 \#\{a\in J:P^-(a)>z,\ \Omega(a)\le2\}\ll A/\log A .
$$
For two factors this follows by summing $O(A/[r\log A])$ over $z<r\ll\sqrt A$, with bounded reciprocal sum. Thus $\sum_{a,\ell} V_{a\ell P}(P^\epsilon)\ll\mathfrak S(P)P/(\epsilon L^3)$ on these sources: use $V\ll(P/\varphi(P))/(\epsilon L)$, $P/\varphi(P)\ll\mathfrak S(P)$, and $O(Y/L)$ short primes. The refined total absolute cofactor/bin error is at most $(K'(\epsilon)+o_{\epsilon,B}(1))\mathfrak S(P)P/L^3$ with $K'(\epsilon)\to0$. This matches the proven **restricted** prime occupancy; simply applying the earlier all-cofactor error $K(\epsilon)P/L^2$ would not suffice.

As in the cofactor proof, if $N_p,N_-$ count the true prime and strict rough-negative witnesses in an admissible cofactor/bin cell, $(N_p-2^{1/\epsilon}N_-)_+$ is bounded by its absolute signed error. The cells with $N_p\le Y/L^{B+4}$ contribute $O(P/L^4)$ prime witnesses even on counting all $O(A L^B)$ possible cells. First select fixed $\epsilon$ making the total error negligible compared with the required $\eta$ fraction of the lower bound, then let $P$ grow. This gives the stated number of distinct switches in each retained prime witness's own bin. The error argument also supplies an upper bound of order $\mathfrak S(P)P/L^3$ for prime occupancy by (2) with the upper sieve in place of the lower. The union of ranks 1 and 2 on the long leg is essential: neither a uniform independent primality assertion nor an exact-odd/even rank selection follows from the argument.
