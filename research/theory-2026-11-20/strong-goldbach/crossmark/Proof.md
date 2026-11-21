# Cross-mark cancellation at the same polynomial cofactor cutoff

Use exactly the notation and normalization of the [signed cofactor pairing](https://github.com/mxym/math/commit/186ebdd0e0ec86283ca25ace98b005384097ad5e): $P$ is a prescribed large even integer, $I=[P/3,2P/3]$, $p$ runs over true primes in $I$, $q=P-p$, $Z=P^{.001}$, $X_P=|I|\mathfrak S(P)$. Let $G=\sum_{p,\;q\text{ prime}}(\log p)\log q$, and retain *without changing the population, cutoffs or weights*
$$
 H=\sum_{p,\,P^-(q)>Z}(\log p)
   \sum_{tb=q,\,t>P^{.3},\,b>Z^3}\mu(t)\log b.
$$
Then, unconditionally at every sufficiently large even $P$,
$$ G>H+.0090X_P. $$
This improves the previous $.0043$ for **the same** $H$. It is a saving in the cofactor charge, not an estimate from below for $H$ and not a two-prime existence theorem.

## The deleted charge

As in the cited proof §§2–3, after discarding squareful $Z$-rough rows at cost $P^{1-c}$ for some $c>0$ (fixed divisor/log weights and Hölder), the short-cofactor row sum is $C(q)=\sum_{tb=q,\, b\le Z^3}\mu(t)\log b$. For each mark $r|q$ with $Z<r\le Z^3$, let $N_r$ count the *other* prime factors $s|q$ with $Z<s\le Z^3/r$. All eligible cofactors $b>1$ have one or two factors. Thus
$$ C(q)=\mu(q)\sum_r w_r,\qquad w_r=(\log r)(N_r-1). $$
The preceding proof bounds $|C(q)|$ by $T(q)=\sum_r|w_r|$. Set $A=(Z,Z^{3/2}]$, $B=(Z^2,Z^3]$. On squarefree $Z$-rough rows with exactly three prime factors in $A$ and exactly one in $B$, each of the three $A$ marks has at least two neighbors by the product bound $Z^3$; the $B$ mark has none. Therefore $\sum_r(w_r)_+\ge3\log Z$ and $\sum_r(-w_r)_+\ge2\log Z$, regardless of primes in the gap or above $Z^3$. Subtracting $2\min(\sum_r(w_r)_+,\sum_r(-w_r)_+)$ from $T(q)$ gives $|C(q)|$. On this event the overcharge is at least $4\log Z$.

## A direct lower sieve for exactly these four marks

Put $\lambda=\log(3/2)$, and write $E$ for the weighted prime count $\sum \log p$ on this event. Open three distinct unordered primes in $A$ and one prime in $B$; let $d$ be their product. Marks dividing $P$ can only occur when $p|P$ and have negligible cost. Given $d|q$, exclude every prime in $\{h\le Z\}\cup A\cup B$ other than the four selected marks and target divisors. This is a single positive dimension-one sieve of the source progression $p\equiv P\pmod d$. Its conditional density at a tested prime $h$ is $1/(h-1)$, since $h\nmid Pd$. There is exactly one selection on an event row and none survives on all other rows; squares of a selected prime can be discarded afterwards. With or without the squarefree condition the weighted error from such squareful rough rows is negligible even after marking, by the same divisor-moment argument. Deleted target primes in the roughness test cannot divide $q$ on actual rows with $p\nmid P$.

Use positive linear sieve bounds with level $D=P^{.31}$ and largest sieving prime $Z^3$. Thus $s=\log D/\log(Z^3)>103$, and every progression modulus obeys $dD\le P^{.3175}$. Omitting primes only improves the usual dimension-one product upper condition. The relative upper/lower sieve error with respect to the displayed Euler model is bounded in limsup by $\Delta(100)=2e^{\gamma_E}\rho(99)/100$, as in the cited proof (linear sieve $f(s)\le1\le F(s)$ and $F(s)-f(s)=2e^{\gamma_E}\rho(s-1)/s$). All actual remainders summed in absolute value are $O_C(P(\log P)^{-C})$ for fixed $C$ by maximal Bombieri–Vinogradov with a fixed divisor-power multiplicity; the residue is the true target. The modulus determines all choices up to a divisor-power bound, and the strict gap from $P^{1/2}$ allows the prime-power subtraction.

With $V_P(Z)=\prod_{h\le Z,\ h\nmid P}(1-1/(h-1))$ over primes, the main for a fixed collection is $|I|V_P(Z)/\phi(d)$ times the product at unmarked primes of $A\cup B$. This last product is $(1+o(1))(2/3)^2$: Mertens gives reciprocal prime masses $\lambda$ on each band, while squared factors, the four deleted labels, or omitted $h|P$ cost $o(1)$ uniformly (the last have $h>Z$). Likewise $\sum_d1/\phi(d)=(1+o(1))\lambda^4/3!$, with the same error controls for equal labels. Since $V_P(Z)\sim e^{-\gamma_E}\mathfrak S(P)/\log Z$, we get
$$ \liminf_{P\to\infty,\,2|P}\frac{(\log Z)E}{X_P}
 \ \ge\ e^{-\gamma_E}\frac49\frac{\lambda^4}6(1-\Delta(100)). $$
Only true source primes have been counted. No Poisson law, independence hypothesis, or parity assumption on the other prime factors is used.

## Combining estimates

The proof at the cited commit gives the low-$t$ normalized calibration error $300000\Delta(100)+702/300!$, and the upper bound for $\sum(\log p)T(q)/X_P$ is $e^{-\gamma_E}(4\log2-1)+8\Delta(100)+o(1)$. Subtracting the true event saving gives
$$
 \liminf\frac{G-H}{X_P}\ge
 1-e^{-\gamma_E}\left(4\log2-1-\frac{16}{9}\frac{\lambda^4}{6}\right)
 -300009\Delta(100)-702/300!.
$$
The event error costs less than $\Delta(100)$ here. The independent rational script proves the right side strictly exceeds $.0090$; it also directly checks the marked-sum formula on a finite exact synthetic control. Only the stated cubic cofactor cutoff is used.
