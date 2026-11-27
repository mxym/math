# Growing admissible constellations in the primorial sieve

Let $P(x)=\prod_{p\le x}p$. A tuple $0=h_1<\cdots<h_r$ is **admissible** when $\nu(p)=\#\{h_j\bmod p\}<p$ for every prime. An internal occurrence is a start $a\in[1,P(x)-1-h_r]$ such that the integers coprime to $P(x)$ in $[a,a+h_r]$ are exactly $a+h_1,\ldots,a+h_r$.

The [original positive-occurrence theorem](FactorErdos854PrescribedGaps.md) works for fixed $r$ at the Ford–Green–Konyagin–Maynard–Tao long-cover scale. The following strengthens it in both the number of prescribed positions and the number of occurrences.

**Theorem.** Put $L=\log x$ and $G(x)=xL\log_3 x/\log_2 x$. Uniformly for integers $2\le r\le 10^{-3}\sqrt L/\log L$:

1. For every fixed $0<\eta\le1/2$ there is $c_\eta>0$ such that each admissible tuple with $h_r\le c_\eta G(x)$ has at least $\exp((1-\eta-o(1))x)$ distinct internal occurrences.
2. If $1\ll\omega(x)\le\log_2 x$ is any function tending to infinity, an absolute $c>0$ suffices for all $h_r\le cG(x)/\omega(x)$, with at least $\exp((1-o(1))x)$ distinct internal occurrences. Since $\log P(x)\sim x$, the latter bound has the largest possible leading coefficient in the logarithm of the count.

The statement is about primorial coprimes, not actual prime constellations. It gives no comparison with the actual maximal primorial gap, and does not settle [Erdős #854](https://www.erdosproblems.com/854).

## Uniform cover transfer

Suppose $x/\log x\le y\le x/2$, and the classes $b_p\bmod p$ for $p\le y$ cover $[1,Y]$, where $x\le Y\le xL^2$. Set
$$
s=\sqrt L,\quad w=e^s,\quad M=\lfloor Y/L^2\rfloor .
$$
Assume $h_r\le Y-M$. We will obtain $\exp(\vartheta(x)-\vartheta(y)-o(x))$ internal occurrences, where $\vartheta(z)=\sum_{p\le z}\log p$. All error estimates below are uniform in $y,Y,r$ and the offsets in these ranges.

### Safe shifts for the small primes

Among $1\le m\le M$, let $\mathcal A$ be the shifts for which every $m+h_j$ avoids $b_p\bmod p$ for all $p\le w$. The forbidden classes of $m$ have density $g_p=\nu(p)/p$ modulo $p$, where $0<g_p<1$ and $\nu(p)\le r$. Put $S=\sum_{p\le w}g_p$. Mertens gives $S\le r(\log s+O(1))\le s/1000$ once $x$ is sufficiently large. Also
$$
-\log\prod_{p\le w}(1-g_p)
\le
\vartheta(2r)+r\sum_{2r<p\le w}\frac1p+2r^2\sum_{p>2r}\frac1{p^2}
\le s/100.
$$
Indeed $1-g_p\ge 1/p$ for small $p$, and $-\log(1-g_p)\le g_p+2g_p^2$ beyond $2r$. The first and third bounds are $O(r)=o(s)$, and the middle term is bounded by $r(\log s+O(1))\le s/1000$.

Let $J$ be the largest odd integer at most $\log M/(4\log(2rw))$, so $J=(1/4+o(1))s$. For any selected set of primes the count of simultaneously forbidden shifts differs from $M\prod g_p$ by at most $\prod \nu(p)$ by CRT. Summing these errors over orders at most $J$ in the odd Bonferroni lower bound costs $O((J+1)(rw)^J)=O(M^{1/3})$. The tail discarded from the main-term product is at most the sum of $S^\ell/\ell!$ over $\ell>J$. Its first term is at most $(eS/(J+1))^{J+1}$, and the consecutive-term ratio is eventually at most $1/2$. As $S/(J+1)\le (0.004+o(1))$, the full tail is at most $e^{-s/2}$ for large $x$. Comparing with the product and counting error gives
$$
|\mathcal A|\ge \tfrac12 M e^{-s/100}.
$$

### Delete conflicts and repair using large primes

For a uniform $m\in\mathcal A$, a class at any $w<p\le y$ covers a prescribed position with probability at most $r(M/p+1)/|\mathcal A|$. If all such conflicting classes are removed, each deletion uncovers at most $Y/p+1$ positions. Thus the expected number of uncovered positions is at most
$$
\ll r e^{s/100}\left(\frac Yw+(1+Y/M)\log x+\frac xM\right)=o(x/L).
$$
This follows by summing $(1/p+1/M)(Y/p+1)$ using integer reciprocal and reciprocal-square sums. In particular the first term loses $e^{-0.99s}$ up to powers of $L$, and the other terms grow as $x^{o(1)}$. Choose a shift with no more than this many uncovered positions. Its interval $[m,m+h_r]$ lies in $[1,Y]$.

For each uncovered nonprescribed position $n$ in this interval, at most $r$ primes $q\in(y,x]$ are forbidden for a repair. For each $h_j$, the nonzero integer $n-m-h_j$ has absolute value at most $Y<y^2$, so at most one such $q$ divides it. The reserve has $\pi(x)-\pi(y)\gg x/L$, and $r=o(x/L)$, so distinct allowed primes can be assigned greedily, one to each of the $o(x/L)$ repairs. Assign that prime the residue $n\bmod q$. Give each deleted class any new residue avoiding all prescribed positions, which exists by admissibility.

Hold every repaired and retained class fixed. For each as-yet unused prime $q\in(y,x]$, all $q-\nu(q)$ residues avoiding the prescribed positions can now be chosen independently. The CRT translates each completed cover to one distinct start modulo $P(x)$, via $t\equiv-b_p\bmod p$ and $a\equiv t+m\bmod P(x)$. The logarithm of the number of choices is at least
$$
\vartheta(x)-\vartheta(y)-o(x).
$$
Indeed, at most $o(x/L)$ assigned reserve primes have been removed from the free product, each costing at most $L$. Replacing every remaining $q$ by $q-\nu(q)$ costs at most $2r\sum_{y<q\le x}1/q\le 2rx/y=o(x)$ in its logarithm. At most $h_r+1$ start residues fail $1\le a\le P(x)-1-h_r$. Subtracting these cannot affect the exponential lower bound, since $\vartheta(x)-\vartheta(y)\ge(1/2-o(1))x$. This proves the uniform transfer.

## Choosing the reserve cutoff

Use the residue-covering conclusion of [Ford, Green, Konyagin, Maynard and Tao, equation (1.1)](https://www.ams.org/journals/jams/2018-31-01/S0894-0347-2017-00876-2/S0894-0347-2017-00876-2.pdf) at $y$. Its lower bound permits a covered length $Y$ of order $y\log y\,\log_3 y/\log_2 y$. With $y=\eta x$ for fixed $\eta$ or $y=x/\omega(x)$ as above, one has $x\le Y\le xL^2$, and $Y-M=(1-o(1))Y$. The prime number theorem gives $\vartheta(x)-\vartheta(\eta x)=(1-\eta+o(1))x$ in the first case and $\vartheta(x)-\vartheta(x/\omega(x))=(1+o(1))x$ in the second.

[Holt's v5, Theorem 1.1](https://arxiv.org/html/2608.26384v5) has an exact population model once initialized at a stage whose next prime exceeds half the constellation's span. It gives fixed-constellation asymptotics, but this initialization constraint is not met at the current stage for spans much larger than $x$. [Tucker's Atlas v3](https://zenodo.org/records/22919682) has exact CRT lift counts for covering assignments. The new assertion here is the uniform existence of repairable assignments with many independent free classes for every admissible tuple in the stated ranges, without requiring its span to be $O(x)$.

The [fixed verifier](verify_factor_erdos854_growing_constellations.js) runs 770,285 exact assertions, including 51,300 CRT completions over four repaired fixtures with four prescribed points. It checks odd Bonferroni bounds, full products of choices at selected free primes and the literal finite-list boundary. It does not validate asymptotic sieve constants.
