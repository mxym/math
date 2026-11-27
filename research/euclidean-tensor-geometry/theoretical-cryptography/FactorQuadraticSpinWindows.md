# Short-window double oscillation for quadratic spin of balanced semiprimes

The statistic here is a class-group condition on $dpq$, with distinct primes $p,q$ of comparable size and $d=-4$ or $-8$. It does not give information sufficient to recover a factor of a given semiprime.

## Results

Let $F=\mathbb Q(\sqrt f)$ with $f=-1,-2,$ or $2$. Let $\mathcal P,\mathcal Q$ be sets of rational primes at most $M,N$, respectively, which split in $F$. For each $p,q$ choose a prime ideal of norm $p,q$, respectively, and generators $w_p,z_q$ of the chosen ideals. The choices on the two sides need not coincide. For each $p$ let $J_p$ be an arbitrary interval of the ordered $q$-values. For any $|a_p|,|b_q|\le 1$ and $\epsilon>0$,
$$
 \left|\sum_{\substack{p\in\mathcal P,\ q\in\mathcal Q\cap J_p\\p\ne q}}
   a_p b_q\left(\frac{z_q}{(w_p)}\right)\right|
 \ll_{F,\epsilon} (MN)^\epsilon \sqrt{(M+N)\,|\mathcal P|\,|\mathcal Q|}.
 \tag{1}
$$
Here the symbol is the quadratic residue symbol in $F$. An empty support gives zero. Thus for two balanced dyadic prime ranges $\asymp X$ the error is $O_\epsilon(X^{3/2+\epsilon})$, including a hard interval cutoff $T<pq\le T+Y$ and the restriction $p<q$. If the two prime ranges instead have lengths $H_1,H_2\ge1$ inside $[X,2X]$, the bound is $O_\epsilon(X^{1/2+\epsilon}\sqrt{H_1H_2})$. The estimate is for separable weights subject to arbitrary row intervals, not for an arbitrary matrix of weights.

Here is a class-group consequence for the two imaginary cases. Fix $d\in\{-4,-8\}$, $0<\eta<1$, and $0<\epsilon<1/5$, and let
$$
 (1+\eta)X^2\le T,\qquad T+Y\le(4-\eta)X^2,\qquad
                       Y\ge X^{9/5+\epsilon}.
 \tag{2}
$$
Use the weighted area
$$
 V(T,Y)=\iint_{\substack{X<u<v\le2X\\ T<uv\le T+Y}}
                            \frac{du\,dv}{\log u\,\log v}.
$$
Count distinct products $pq$ satisfying $X<p<q\le2X$, $T<pq\le T+Y$, $p,q\equiv1\bmod4$. Write $K_{p,q}=\mathbb Q(\sqrt{dpq})$, and denote its class group by $\mathrm{Cl}(dpq)$. The number of these products with $4$-rank equal to $2$ is asymptotic to $V(T,Y)/32$. Among these rank-$2$ products, those that have an unramified cyclic extension of degree $8$ of $K_{p,q}$ containing $\mathbb Q(\sqrt d,\sqrt{pq})$ number
$$
                  \left(\frac1{128}+o(1)\right)V(T,Y). \tag{3}
$$
Both asymptotics are uniform in (2); $V(T,Y)\asymp_\eta Y/(\log X)^2$. In particular the specific extension exists for a proportion tending to $1/4$ of the rank-$2$ family in every such window. The proportion with $8$-rank at least $1$ is **at least** $1/4-o(1)$, not claimed equal to $1/4$; other genus directions are not counted.

### Comparison

[Milović's Proposition 8 and Theorem 2](https://arxiv.org/abs/1512.08034) give a double-oscillation estimate and an unwindowed asymptotic over $pq\le x$. In a balanced norm box of relative side length $\Delta$, the stated bilinear bound there is $O(\Delta^{13/12}X^{23/12}\log X)$ when the number of prime-ideal factors is fixed. For prime norms, (1) gives $O_\epsilon(\Delta X^{3/2+\epsilon})$ on the common domain, and in fact for every $\Delta X\ge1$ (the earlier proposition assumes norm thickness at least of order $\sqrt X$). In particular the exponent at fixed $\Delta$ changes from $23/12$ to $3/2+\epsilon$, and the relative side lengths at which the bound saves a power over the volume extend from $X^{-1/11+\epsilon}$ to $X^{-1/2+\epsilon}$. The relevant new application is uniform localization of the designated cyclic extension in balanced product windows. The $9/5$ exponent in (2) comes from separately supplying primes in a fixed Frobenius class; the signed estimates themselves hold even for shorter windows, regardless of the available number of primes. Neither the unrestricted $1/4$ lower bound nor the algebraic extension criterion is claimed new.

## 1. A compatible quadratic Hecke family

The three listed fields have class number one; this also follows from the Minkowski bound (at most $(2/\pi)\sqrt{|D_F|}$ in the imaginary quadratic case, and $\frac12\sqrt{D_F}$ in the real quadratic case). All ideals in the real case admit totally positive generators because $1+\sqrt2$ has opposite signs in the two real embeddings, and $-1$ reverses both signs. The dyadic prime $\mathfrak t$ is unique.

Choose a generator $g_{\mathfrak p}$ for every odd prime ideal, totally positive if real, and extend multiplicatively to generators $g_{\mathfrak a}$ of all odd integral ideals. For squarefree odd $\mathfrak a$ let $\chi_{\mathfrak a}$ be the primitive quadratic Hecke character associated with $F(\sqrt{g_{\mathfrak a}})/F$, with the trivial character when the extension is trivial. Its infinite type is trivial. On an odd ideal coprime to $\mathfrak a$, its value is $(g_{\mathfrak a}/\cdot)$, with the usual zero convention at a prime dividing $\mathfrak a$. The map $\mathfrak a\mapsto [\mathfrak a]=[g_{\mathfrak a}]$ into the dyadic local squareclass group $F_{\mathfrak t}^\times/F_{\mathfrak t}^{\times2}$ is a homomorphism into a finite group; all chosen generators of odd integral ideals are local units at $\mathfrak t$. Finiteness also follows directly from Hensel's lemma, since every unit congruent to $1$ modulo $\mathfrak t^j$ with $j>2v_{\mathfrak t}(2)$ is a local square.

If $\mathfrak a,\mathfrak b$ are coprime, odd and squarefree, Hilbert reciprocity gives
$$
 \chi_{\mathfrak a}(\mathfrak b)
 =\chi_{\mathfrak b}(\mathfrak a)\,
                  (g_{\mathfrak a},g_{\mathfrak b})_{\mathfrak t}.
 \tag{4}
$$
Indeed at any odd finite prime where both generators are units the local symbol is $1$. At an odd prime of $\mathfrak a\mathfrak b$, one valuation is $1$ and the other $0$, giving precisely the residue symbol of the unit, and the archimedean symbols are trivial by the chosen signs. The correction in (4) depends only on the two squareclasses. If the squareclasses coincide, $g_{\mathfrak a}g_{\mathfrak b}$ is a local square at $\mathfrak t$; its Kummer character is unramified there, and at each prime dividing $\mathfrak a\mathfrak b$ it is tamely ramified with conductor exponent $1$. There is no other ramification. Thus $\chi_{\mathfrak a}\chi_{\mathfrak b}$, as a Hecke character, has conductor exactly $\mathfrak a\mathfrak b$. With the single dyadic prime excluded, this verifies the reciprocity and conductor requirements of a quadratic Hecke family in [Goldmakher–Louvel, Definition 1 and Theorem 1.1](https://arxiv.org/abs/1112.1642).

### 2. From the large sieve to interval-restricted rows

Apply that theorem and Cauchy–Schwarz to two sets of prime ideals of norms in $[1,M]$, $[1,N]$, with arbitrary coefficient vectors $A,B$. With $\varepsilon_0>0$, it bounds the unconstrained bilinear form for $\chi_{\mathfrak q}(\mathfrak p)$ by
$$
         O_{F,\varepsilon_0}\bigl((MN)^{\varepsilon_0}
                 \sqrt{M+N}\,\|A\|_2\|B\|_2\bigr),
 \tag{5}
$$
renaming the exponent after taking a square root. If the specified generator $z_q$ equals $u_qg_{\mathfrak q}$, where $u_q$ is a unit, partition $\mathcal Q$ by the finitely many classes of $u_q$ modulo squares of units. On each piece the extra symbol $(u_q/\mathfrak p)$ is a row weight of magnitude at most $1$. This proves (5) also for the requested generators, up to a field-dependent constant. The denominator generator only specifies its ideal. Removing pairs of equal rational prime norms costs at most $|\mathcal P\cap\mathcal Q|$ for the unit-bounded weights, which is at most $\sqrt{|\mathcal P||\mathcal Q|}$.

To restrict the $q$-values for each $p$, write an interval as a difference of two prefixes in a common ordering of $\mathcal Q$. Pad this ordering up to the next power of two. The canonical dyadic decomposition of a prefix uses at most one column block at each depth. At that depth, assign each participating row to the unique column block used by that row. The column sets $C_j$ and row sets $R_j$ of the resulting rectangles are separately disjoint. Applying (5) on each rectangle and Cauchy–Schwarz to $\sum_j \sqrt{|R_j||C_j|}$ costs at most $\sqrt{|\mathcal P||\mathcal Q|}$ times the coefficient in (5). There are $O(\log(2|\mathcal Q|))$ depths. Absorb this factor into the arbitrarily small exponent by starting with smaller $\varepsilon_0$. This proves (1). The same argument with the rational [Heath-Brown quadratic large sieve, Theorem 1](https://doi.org/10.4064/aa-72-3-235-275) proves (1) for the kernel $(q/p)$. The joint norm or product cutoffs in the result only change the endpoint of each row interval, not the analytic inequality.

## 3. The two oscillating signs

For $d=-4,-8$ set $f=d/4$, $F=\mathbb Q(\sqrt f)$. For primes $p,q\equiv1\bmod8$, normalize $w=w_p$ and $z=z_q$ to be squares modulo $4\mathcal O_F$ as in Milović, equation (6). For $f=-1$, write $p=a^2+b^2$ with odd $a$ and $4\mid b$, and change the overall sign to obtain $a\equiv1\bmod4$. For $f=-2$, write $p=a^2+2b^2$ with odd $a$ and even $b$. If $b\equiv0\bmod4$ use $a\equiv1\bmod4$; if $b\equiv2\bmod4$ use $a\equiv3\bmod4$, giving the square $(1+\sqrt{-2})^2\bmod4$. Both conjugate choices are valid. Such generators exist because the primes split and the rings are principal.

Use
$$
 A(p,q)=\left(\frac qp\right),\qquad
 B(p,q)=\left(\frac{\bar w}{(w)}\right)\left(\frac z{(w)}\right).
$$
For distinct prime norms these take values in $\{\pm1\}$. The mixed product $AB$ obeys the same bound as $B$: since $z\bar z=q$ and the residue field of $(w)$ has size $p$, multiplication by $A$ simply replaces $z$ by $\bar z$ in the second symbol. The first factor in $B$ is a bounded row weight. Quadratic reciprocity over $\mathbb Q$ identifies $A=1$ with $p$ a square modulo $q$. Thus, on any fixed subsets of $p,q\equiv1\bmod8$ further cut by row intervals, each of the four joint sign pairs $(A,B)$ occurs $\tfrac14$ times the total supply plus an error bounded by (1), by expanding $(1+sA)(1+tB)/4$. In particular, the oscillation estimate is not an assertion of uniform sign distribution on an individual prime pair.

Choose $\vartheta=1+i$ for $d=-4$ and $\vartheta=\sqrt{-2}$ for $d=-8$; both have norm $2$. Set
$$
       \sigma(p)=\left(\frac{\vartheta}{(w_p)}\right).
$$
This is independent of the prime ideal above $p$, because multiplying the two conjugate symbols gives $(2/p)=1$ for $p\equiv1\bmod8$. By Milović's equation (4), equation (5), Proposition 3, and equations (15)–(19) and (37) for these two $d$:
* among $p,q\equiv1\bmod4$, $4$-rank $2$ is equivalent to $p,q\equiv1\bmod8$ and $A=1$;
* in that rank-$2$ family, the stated unramified $C_8$ direction occurs if and only if $\sigma(p)\sigma(q)=1$ and $B=1$.

In particular the two extra conditions concern one specific genus direction. The second equivalence uses the form $\alpha=\bar w z$; the multiplication by $(\bar w/(w))$ must not be replaced by $(w/(w))$.

## 4. Prime supply and the uniform window

For each such $F$, put $E=F(\sqrt{\vartheta},\sqrt{\bar\vartheta})$. It is Galois over $\mathbb Q$, of degree $8$: both factors $\vartheta,\bar\vartheta$ have odd dyadic valuation, their product is $2$, and $2$ is not a square in either imaginary $F$. The two squareclasses are independent, so $\operatorname{Gal}(E/F)$ is the abelian group of order $4$. Moreover $E$ contains $F(\sqrt2)=\mathbb Q(\zeta_8)$, and for an unramified prime $p\equiv1\bmod8$, $\sigma(p)=1$ precisely when $p$ splits completely in $E$. Thus among all rational primes, each of the sets
$P_s=\{p:p\equiv1\bmod8,\ \sigma(p)=s\}$, $s=\pm1$, has density $1/8$.

[Thorner, Theorem 1.1 with modulus $1$](https://arxiv.org/abs/1405.5486) supplies short-interval asymptotics for complete splitting down to lengths $X^{4/5+\epsilon'}$ at endpoints $\asymp X$. Indeed the identity class meets the abelian subgroup of index $2$, so the degree of the fixed field in the theorem is at most $2$. Discarding prime powers, which contribute $O(\sqrt X\log^2 X)$, and applying partial summation gives the prime count $\frac18\int dt/\log t$ in such intervals with relative error $o(1)$, uniformly. For $P_-$, subtract the completely split count from the count for $p\equiv1\bmod8$; the latter has density $1/4$ and at least the same range by applying the same result to the abelian field $\mathbb Q(\zeta_8)$. At ordinary lengths, the same expected densities hold by the prime ideal theorem or by the same Chebotarev result.

For each $p\in(X,2X]$ the $q$-interval, enforcing the product window and $p<q$, has length at most $Y/X$. Discard the rows whose interval length is less than $X^{4/5+\epsilon/2}$: even by counting integers in their intervals and allowing all $O(X)$ rows, they contribute $O(X^{9/5+\epsilon/2})=o(Y/(\log X)^2)$. In the surviving rows apply the uniform prime asymptotic with $\epsilon'=\epsilon/2$. The row main term for the $P_t$ supply is $F_0(p)/8$, where
$$
 F_0(u)=\int_{\max(X,u,T/u)}^{\min(2X,(T+Y)/u)}
                    \frac{dv}{\log v},
$$
with the integral set to zero if its upper bound is smaller. Putting back the main terms for discarded rows costs $o(Y/(\log X)^2)$. The function $F_0$ has supremum $O(Y/(X\log X))$ and total variation of the same order. To see the variation, split at the finitely many intersections of the endpoint functions and at interval disappearance. The only pair of moving endpoints not forced by opposite monotonicity or by one constant is $(T/u,(T+Y)/u)$. There the integral equals $u^{-1}\int_T^{T+Y} dt/\log(t/u)$, which decreases for $t/u>e$. Each piece is therefore monotone. Partial summation with the ordinary Chebotarev prime count for $P_s$ shows that the supply of pairs with $(\sigma(p),\sigma(q))=(s,t)$ is
$$
                   \frac1{64}V(T,Y)+o\bigl(Y/(\log X)^2\bigr).
 \tag{6}
$$
For uniform comparability of the weighted area, write it, before the logarithmic weights, as
$\int_T^{T+Y}\int_{\max(X,t/(2X))}^{\sqrt t}du\,dt/u$.
The inner interval is contained in $[X,2X]$, and its logarithmic length is bounded above and away from zero for all $t/X^2\in[1+\eta,4-\eta]$. Including the two logarithmic weights proves the comparability.

Summing (6) over all four pairs gives total $V/16+o(V)$. The oscillation of $A$ halves this for rank $2$, since $O_\epsilon(X^{3/2+\epsilon/2})=o(V)$. Summing (6) over $s=t$ gives $V/32+o(V)$ before the two oscillating signs. Joint equidistribution takes a quarter of that for $A=B=1$, giving (3).

The companion verifier checks the two symbol identities and normalizations on fixed small prime lists, as well as the row-prefix decomposition and sign extraction. It does not test the asymptotic error or enumerate the class groups.
