# Opposite logarithmic first-crossing contributions strictly above the square root

This is a fixed-target application of [Maynard, *Primes in arithmetic progressions to large moduli III: uniform residue classes*, Theorem 1.2](https://arxiv.org/pdf/2006.08250) ([accepted version](https://ora.ox.ac.uk/objects/uuid%3Ada3b7279-d413-4ab1-962e-afa5d67507c2)). The distribution theorem is an input; its level is not improved. The moduli here already exceed $P^{1/2}$ *before* the auxiliary sieving modulus is attached, and have a prime factor larger than $P^{.15}$. The argument does not extend ordinary Bombieri–Vinogradov or assume that these are smooth moduli.

For each prescribed even $P$ put $L=\log P$, $I=[P/3,2P/3]$, $X_P=|I|\mathfrak S(P)$ with the usual binary singular series. On genuine primes $p\in I$ write $q=P-p$, $dM(p)=(\log p)W(q-1)$, with $W=1$ or one of the fixed neutral predecessor tag weights in the [rough inversion](https://github.com/mxym/math/commit/6f877f72). The latter weight is $\mathcal V^{-1}\sum_A1_{A|q-1}$ on squarefree products of a fixed number $K$ of disjoint subpower prime tags, excluded from $P(P-1)$, with $\sum_A1/\phi(A)=(1+o(1))\mathcal V\asymp_K1$.

Fix $x_0=10^{-6}$, $0<\lambda<x_0$, $g=1/2-\lambda/2$, $y=P^g$, and any fixed $z=P^\eta$ with $0<\eta<\lambda$. Take $P\to\infty$ first, then $\lambda\downarrow0$. The next two subpartitions of the upper rough-divisor residual are independent of $\eta$ once $\eta<\lambda$.

**First-crossing rule.** In a squarefree $z$-rough divisor $t|q$, $t>y$, take $m$ to be the first product exceeding $y$ when the prime factors of $t$ are taken in descending order. Thus $r=P^-(m)>z$ and $m/r\le y<m$. Conversely these conditions and $m|q$ characterize possible prefixes: take $t=m$ or append factors $z<\ell<r$ from $q/m$. On pooling **every** such continuation in the genuine upper residual $\sum_{t|q,t>y,P^-(t)>z}\mu(t)B_t(q)$ from the cited inversion, the contribution at a prefix is exactly $\mu(m)J_r(q/m)$, where
$$
 J_r(n)=\begin{cases}
 \log n,& n\text{ has no prime factor }<r,\\
 \log h,& h\text{ is its only distinct prime factor }<r,\\
 0,&\text{otherwise}.
 \end{cases}
$$
Indeed $B_t(q)$ already pools all factors $\le z$ of the smooth divisor with weight $\mu(k)\log(q/(tk))$. Appended and smooth factors now run jointly through **all** squarefree divisors below the prime cutoff $r$ (all their prime factors $<r$), coprime to $m$. The zero/one-label identity follows by inclusion–exclusion. There is no valuation-one requirement on $h$, or on factors of $m$ inside the actual $q$.

**Two explicit angular families.** Below all exponents refer to $P$. In both families, retain prefixes $m=r B C n$ with
* $\lambda\le x=(\log r)/L\le x_0$, $m/r\le y$, and **$m>P^{1/2}$**;
* $C$ prime of exponent $c\in[.076,.078]$;
* $n$ squarefree, all its prime factors $>P^\kappa$, $\kappa=.15$.

In family 1, $B$ is prime with exponent $b\in[.029,.031]$. In family 2, $B=B_1B_2$ with one prime from each of the exponent ranges $[.0129,.0131]$, $[.0169,.0171]$. Denote the family number by $j=1,2$, write $b$ for the **sum** of the $j$ individual exponents, and write $d\sigma_j$ for the product of $dv/v$ over those $j$ bands and the $C$ band. All the indicated prime regions are disjoint; $r,B,C,n$ are uniquely determined by $m$ in a given family. The log exponent of $n$ lies in $(.390,.396)$ up to harmless endpoints (more precisely between $.5-x_0-.031-.078$ and $.5-.029-.076$), so it can have **one or two** prime factors, and both possibilities have positive limiting volume. In particular the signs are not selected by taking a single fixed parity of $m$.

Put
$$ Z_j=\sum_{p\in I}dM(p)\sum_{\substack{m|q\\m\text{ in family }j}}\mu(m)J_{P^-(m)}(q/m),\qquad
 c_j=\frac{e^{-\gamma_E}}2\int
 \frac{\rho((1/2-b-c)/\kappa-1)}{1/2-b-c}\,d\sigma_j>0. $$
Here $\rho$ denotes Dickman's function. The same physical $q$ can be counted in different branches; these are disjoint *divisor branches* because their actual $t$ have distinct descending prime prefixes. This is unlike an assertion about row-disjoint sets.

**Theorem.** With fixed $K$, in the stated order of limits,
$$
 \frac{Z_j}{X_P}=(-1)^{j+1}c_j\log(1/\lambda)+O(1)+o_\lambda(1),\qquad j=1,2. \tag{1}
$$
Precisely, for every fixed $\lambda$ the limsup over even targets of the absolute difference from the displayed leading term is bounded by a constant independent of $\lambda$; dependence on the displayed fixed bands and $K$ is allowed. The opposite signed contributions grow in magnitude on the natural scale even though the prefixes all lie in $P^{1/2}<m\le P^{1/2+x_0}$. They need not measure all, or a favorable fraction, of the total signed residual. No lower bound on Goldbach follows.

## 1. Actual prime distribution on the union moduli

Conditional on $m|q$ and $A|q-1$, where $(m,P)=1$ and $(A,m)=1$, the prime source is in one unit class modulo $Am$. Source primes dividing $P$ cost $P^{o(1)}$ even with absolute divisor and tag weights. Tag factors are $<r$ for large $P$ at fixed $\lambda$ and none lie in $m$. To count zero small labels in $q/m$, sift primes $h<r$, $h\nmid AP$. Their density is $1/(h-1)$ since none divide $m$. To count the singleton at $h$, impose $h|q$ with multiplier $1/(h-1)$, sieve out the *other* primes $<r$ and weight by $\log h$. Relative to the common rough product $V_{AP}(r)=\prod_{h<r,h\nmid AP}(1-1/(h-1))$, the marked multiplier is exactly $1/(h-2)$. All valuations at the marked prime are retained. At primes of $A$ the actual value of $q$ is 1, while target primes cannot divide $q$ away from the removed source exceptions.

Take the sieve level $D=P^{.00005}$. Its squarefree modulus $d$ and the optional singleton $h$ are disjoint from each other, $A$ and $m$. In each endpoint progression estimate the uncolored union modulus is
$$ k=Amhd=Q_1'Q_2'Q_3',\qquad Q_1'=A r n h d,\quad Q_2'=B,\quad Q_3'=C, $$
where $h=1$ in the unmarked case. It satisfies $k\le P^{.500052+o(1)}$. For a central prime-count endpoint $X\asymp P$, use $\delta=.0002$ in Maynard III, Theorem 1.2. Partition $B,C$ into dyadic packets with **upper** endpoints $Q_2,Q_3$. Set $Q_1=X^{1/2+\delta}/(Q_2Q_3)$. Then $Q'_1\le4P^{.500052+o(1)}/(Q_2Q_3)\le Q_1$. In exponents of $X$, up to $o(1)$, the possible $Q_2$ range is $[.029,.031]$, the $Q_3$ range is $[.076,.078]$. They strictly satisfy all of the theorem's inequalities
$$
 40\delta<\log_X Q_2<1/20-7\delta,\qquad
 1/10+12\delta-\log_X Q_2<\log_X Q_3<1/10-4\delta-(3/5)\log_X Q_2.
$$
Indeed the outer $Q_2$ limits are $.008,.0486$; the most restrictive lower and upper $Q_3$ limits are $.0734,.0806$. The product of the **chosen bounds**, not necessarily that of the actual factors, is exactly $X^{1/2+\delta}$. Only $O(L^2)$ packets are spent.

For completeness the residue can be handled even with the unaveraged predecessor-tag weight. Color each prime in the tag bank independently red/blue, retaining data if primes of $A$ are red and all other bank primes of $k$ are blue. In each coloring prescribe $P-1$ at red primes and $P$ at all others not dividing $P$; prescribe $1$ at primes of $P$. This is a single everywhere-unit integer CRT class on the finite set of possible prime factors. It is fixed **before** all $Q'_3$, so its residue on $Q'_1Q'_2$ is independent of $Q'_3$, exactly as required by Maynard. Invalid reconstructions are just discarded in absolute bounds. The retention probability for each admissible tuple is $2^{-\omega_{\rm bank}(k)}$ since $k$ is squarefree. Reweighting by its inverse costs at most $\tau(k)$; the possible reconstructions of $A,m,h,d$ and all slots cost at most $\tau(k)^{O_K(1)}$. We use Maynard's sum-of-absolute-errors assertion on the one fixed branch. Cauchy absorbs divisor powers: the sum with any fixed additional divisor power of the **trivial** prime discrepancy, $O(P/k+1+P/\phi(k))$, is $O(PL^{O_K(1)})$, including the triple factorizations since they too are divisor-bounded. Maynard's arbitrarily strong logarithmic saving on the other Cauchy factor pays both multiplicities and the packet count. This proves a total progression error $O_A(PL^{-A})$ even after summing its absolute value over the actual data. The input is for counts of **true primes**, so no summation of an $O(\sqrt P)$ prime-power error per over-root modulus is needed. Partial summation on the central interval with the same bound at each prefix gives the log weight; ordinary PNT replaces the principal prime count by its integral, with summed errors bounded using $\sum_{k\le P}\tau(k)^{O_K(1)}/\phi(k)\ll L^{O_K(1)}$.

Write $w=\log m/L$. The conditional main for a prefix after tag normalization, in units $X_P/\phi(m)$, is
$$ e^{-\gamma_E}\left[(1-w)/x+1\right]. \tag{2}$$
The zero-label sieve gives the first summand from $V_{AP}(r)=(1+o_\lambda(1))e^{-\gamma_E}\mathfrak S(P)/(xL)$ and $\log(q/m)=(1-w)L+O(1)$. The second comes from $\sum_{h<r,h\nmid AP}\log h/(h-2)=xL+o_\lambda(L)$, by Mertens and the uniform $O(\log(2L))$ target-divisor loss. Primes of $m$ do not affect either product since $r$ is the least and is strictly excluded from the sieve. Tag deletions are negligible uniformly. These estimates hold jointly with the absolute progression-error budget above. The absolute error per model weight in (2), besides those progression errors and $o_\lambda(1)$ at fixed $\lambda$, is bounded by a fixed constant times $[1+1/x]\Delta(.00005/x)$ with $\Delta(s)\ll s^{-s/2}$. Use positive upper/lower fundamental-lemma sieves separately for the zero-label and singleton counts (Friedlander–Iwaniec, *Opera de Cribro*, Lemma 6.11). The dimension-one constant is uniform, since omitting primes cannot increase the full odd-prime Mertens product. The sieve parameter is at least 50 and tends to infinity as $x\downarrow0$.

## 2. Signed angular calculation and uniform leading coefficient

At fixed $\lambda$, all prime exponents used in $m$ are bounded below by $\lambda>0$. Replacing $1/\phi(m)$ with $1/m$ on squarefree $m$, ignoring equal labels in the limiting integrals and restoring target-excluded primes cost $o_\lambda(1)$ in the absolute harmonic model: use $\sum_{r>P^\lambda}r^{-2}$, $\sum_{r|P,r>P^\lambda}1/r\ll L/P^\lambda$ and the bounded compact Euler products. The reciprocal-prime measures tend to $dv/v$ by Mertens, with the usual $1/k!$ for unordered primes in $n$; sharp band boundaries have zero measure. The maximum number of labels in $n$ is two. For $u=\log n/L$ in our actual range the signed density is exactly
$$
 d_\kappa(u)=-\frac1u+\frac12\int_\kappa^{u-\kappa}\frac{dv}{v(u-v)}
 =\frac{-1+\log((u-\kappa)/\kappa)}u
 =-\frac{\rho(u/\kappa-1)}u, \qquad 2\kappa<u<3\kappa. \tag{3}
$$
Thus one- and two-prime residuals are both present. Formula (3) could equivalently be read as $\rho'(u/\kappa)/\kappa$. The unsigned density has a plus instead of the first minus, and is uniformly bounded on our compact range. Both signed and unsigned densities are Lipschitz there. Also $\rho(u/\kappa-1)=1-\log(u/\kappa-1)>1-\log(1.7)>0.4$ on the stated bands.

Set $u_0=1/2-b-c$. The defining cut $P^{1/2}<m\le rP^g$ is exactly
$$ u_0-x<u\le u_0-\lambda/2. $$
All other exponents in $m$ are much larger than $x$, so $r$ is its actual least prime. The outer factor $rBC$ has sign $(-1)^j$ (there are $j+2$ distinguished primes). The full signed integral resulting from (2) is
$$
 (-1)^j e^{-\gamma_E}\int d\sigma_j\int_\lambda^{x_0}\frac{dx}x
 \int_{u_0-x}^{u_0-\lambda/2}
       d_\kappa(u)\;\frac{1-b-c-u}{x}\,du .                         \tag{4}
$$
Indeed $w=x+b+c+u$, so $[1-w]/x+1=(1-b-c-u)/x$. The actual marked-singleton $+1$ on its own contributes only $O(1)$ uniformly because the $u$ interval has length at most $x$. In the absolute sieve-error calculation the same shrinking width and bounded unsigned density give a bound
$$ C\int_\lambda^{x_0}\Delta(.00005/x)\,dx/x=O(1), $$
even independently of $\lambda$. The same holds if the smooth positive dominating function $C s^{-s/2}$ is used for $\Delta(s)$. Thus no fixed relative error times $\log(1/\lambda)$ is hidden in (4). All distribution and weak convergence limits at fixed $\lambda$ are taken before this uniform integral estimate.

At each fixed $b,c$, the inner integral equals
$$
 \tfrac12d_\kappa(u_0)\left(1-\frac{\lambda}{2x}\right)+O(x)
$$
uniformly by the Lipschitz estimate, since $1-b-c-u_0=1/2$. Integrating with $dx/x$ yields $\tfrac12 d_\kappa(u_0)\log(1/\lambda)+O(1)$; in particular the lower-end subtraction contributes only $O(1)$. Substitution of (3) proves (1) with the asserted signs and positive constants.

These two signed sectors include different numbers of macro prime slots and thus can partially offset each other or be offset by other branches. No claim is made that this exhausts the angular regimes beyond the ordinary square-root rail. In contrast to the [whole-row minimal crossing reserve](https://github.com/mxym/math/commit/ca6fa82f), the partition here is by the unique prefix of a divisor, not by a property solely of $q$. Neither the signs nor the diverging scale justify a lower bound for the aggregate omitted parity sum.
