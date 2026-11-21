# Critical rank tilt on the true prime slice: a subpower-cofactor theorem and a signed threshold

For an even integer $P$, put $L=\log P$, $H=\log\log P$, and restrict $m=P-p$ to $P/3\le m\le2P/3$, with $p$ a genuine prime. Let $G(P)$ count these central ordered Goldbach representations. Write $\mathfrak S(P)=2\prod_{w>2}(1-1/(w-1)^2)\prod_{w\mid P,\ w>2}(w-1)/(w-2)$, with products over primes. Define the polynomial and its real signed test by
$$
 Z_P(u)=\sum_{p+m=P}^{\rm central}\!\mu^2(m)(u/H)^{\Omega(m)-1},\qquad
 J_P(u)=(1-u\partial_u) Z_P(u).
$$
Only $p$ is required prime in $Z_P$. Use the polynomial convention $0^0=1$. An individual squarefree rank $k$ in $J_P$ receives $(2-k)(u/H)^{k-1}$. In particular $J_P(u)\le G(P)$ at real $u\ge0$; semiprimes contribute identically zero.

**Theorem.** Fix $A>0$, $R>0$, and let $D=\exp(L/H^A)$. Put $T_{P,d}=\#\{p,q\text{ primes}:p+dq=P,\ P/3\le dq\le2P/3\}$. Uniformly in every sufficiently large even $P$ and complex $|u|\le R$,
$$
 Z_P(u)=\sum_{\substack{d\le D\text{ odd, squarefree}\\ (d,P)=1}}
    (u/H)^{\Omega(d)}T_{P,d}
   +O_{A,R}\!\left(\frac{\mathfrak S(P)P}{L^2}\frac{\log H}{H}\right).
 \tag{1}
$$
The same holds after any fixed number of complex derivatives on a compact disk, including for $J_P$ after applying its operator to both sides. In particular **all** rows having a second prime factor $\ge P^\epsilon$ (any fixed $\epsilon>0$), or more generally whose proper cofactor after removal of the largest prime exceeds $D$, have negligible *absolute* tilted mass at the natural prime-pair scale. Lower populations with two polynomial-scale factors, such as the [two-axis parity corners](https://github.com/mxym/math/commit/2f9bfe36), do not by themselves sample that limiting signed mass. No assertion is made that ranks are distributed independently at a given target.

There is an exact averaged sign threshold. Locally uniformly for complex $u$, as $X\to\infty$,
$$
 \frac{2\log^2X}{X^2}\sum_{X<P\le2X,\ P\ {\rm even}}Z_P(u)\ \longrightarrow e^u,
 \qquad
 \frac{2\log^2X}{X^2}\sum_{X<P\le2X,\ P\ {\rm even}}J_P(u)\ \longrightarrow(1-u)e^u.     \tag{2}
$$
Thus for **every fixed real $u>1$** a positive proportion of even targets in every sufficiently large dyadic interval have genuinely negative $J_P(u)$, of size $\gg_u\mathfrak S(P)P/L^2$ in absolute value. No uniform positive-sign theorem of this form is possible there. For $0\le u<1$, a positive proportion have genuinely positive $J_P(u)$ on that scale, but (2) is not a pointwise Goldbach statement. No sign is inferred at $u=1$. Even below the threshold the off-prime charge cannot be discarded uniformly: the same normalized dyadic mean of $G(P)-J_P(u)$ tends to $1-(1-u)e^u>0$ for every $u>0$.

## 1. Uniform upper estimate for genuine prime pairs with one multiplier

For any $d$ which can occur on opening $m=dq$ by its largest prime $q$, outside the true Goldbach diagonal, we have $d$ odd and $(d,P)=1$. Indeed $p$ is an odd prime of size comparable to $P$; if $p\mid P$ then, in the indicated closed central range and for large even $P$, necessarily $p=P/2$ and $m=p$. The diagonal belongs to $d=1$. For $U=P/d$, a uniform Brun–Selberg dimension-two upper bound is
$$
 T_{P,d}\ll \frac{\mathfrak S(P)U}{\log^2(2U)}\frac{d}{\varphi(d)}.                 \tag{3}
$$
Here $q$ is constrained to $[U/3,2U/3]$, and $p=P-dq$ to the stated central interval. For clarity, apply the elementary upper sieve on the integer variable $q$ to the pair of primitive forms $q,P-dq$. The number of forbidden classes at a prime $w$ is 2 for $w\nmid Pd$ and 1 for $w\mid Pd$ (at 2 use even $P$ and odd $d$). Take sifting limit $U^c$ with a small fixed $c>0$, e.g. $1/50$ as the exponent, and level $U^{1/2}$. The dimension-two product hypothesis follows from Mertens uniformly since omitting a root only improves it. The total elementary remainder in the upper sieve is $\ll U^{1/2}\log^{O(1)}(2U)$ by counting classes with error $O(\nu(e))$ for squarefree moduli and divisor-bounded sieve weights. Both true primes exceed the sifting limit for sufficiently large $U$; bounded $U$ is harmless trivially. The product at $U^c$ is $\ll \mathfrak S(P)\prod_{w\mid d,w>2}(w-1)/(w-2)\,/\log^2(2U)$; completing omitted target factors only increases it. The last extra factor is $\ll d/\varphi(d)$ by the convergent product of $1+O(w^{-2})$ ratios. This proves (3) with an absolute implied constant, without a prime tuple asymptotic. For the sieve see [Friedlander–Iwaniec, *Opera de Cribro*](https://doi.org/10.1090/coll/057).

On an actual rank-$k$ row $q\ge m^{1/k}\ge(P/3)^{1/k}$, hence $\log(2P/d)\gg L/k$. This is crucial: substituting $L$ without the rank cost could fail for $d$ close to $P$. For squarefree $m$, summing (3) over $d$ of rank $k-1$ for which some such row exists gives the quantitative all-rank bound
$$
  N_k(P)\ll \frac{\mathfrak S(P)P}{L^2}\,
       \frac{k^2(H+C)^{k-1}}{(k-1)!}.                                                \tag{4}
$$
Indeed the harmonic weight is $1/\varphi(d)$ and $\sum_{w\le P}1/(w-1)\le H+C$. The $(k-1)!$ divides the full sum over distinct primes, and extending that sum to repeated tuples is an upper bound, not a unique-factorization assumption. In particular $|Z_P(u)|+|J_P(u)|\ll_R\mathfrak S(P)P/L^2$, and the normalized tail beyond any $K$ on $|u|\le R$ is at most $C\sum_{k>K} k^3(2R)^{k-1}/(k-1)!$ for $P$ large.

## 2. A true subpower cutoff at each target

For $k\le H$ and $d>D$, some prime $w\mid d$ exceeds $\exp(L/H^{A+1})$. Its reciprocal sum up to $P$ is $O_A(\log H)$ by prime Mertens. Mark one such occurrence in (4); now the normalized weighted bound at rank $k\ge2$ is
$$
 \ll_A k^2\frac{R\log H}{H}
         \frac{(2R)^{k-2}}{(k-2)!}.
$$
The same estimate with $k^3$ works for $J_P$. The remaining ranks $k>H$ contribute $o_R(1/H)$ by the factorial tail. These are estimates for absolute weights; no target averaging has been used. For $d\le D$, $q$ is automatically bigger than $d$, so the positive integer $dq$ with a counted $q$ has exactly one such largest prime and is squarefree whenever $d$ is. Conversely every retained squarefree row has this unique decomposition. This proves (1), including the convention $d=1$. Uniformity on slightly larger disks gives the claimed derivative bounds by Cauchy's integral formula.

The statement uses squarefree $m$ deliberately. It does not infer $\mu^2(m)=1$ at a composite. In fact (1) would have the same normalized leading expansion if one removed $\mu^2(m)$ while still using $\Omega$ with multiplicity. To see this, opening one largest occurrence gives the same $k^2$ cost; without squarefreeness use the absolute Euler bound
$$
 \sum_{w\mid d\Rightarrow w\le P}\frac{v^{\Omega(d)}}d\frac d{\varphi(d)}
  =\prod_{w\le P}\left(1+\frac{w}{w-1}\frac{v}{w-v}\right)\ll_R1,
 \qquad v=4(R+1)/H<1/2 .
$$
Weighted ranks $k>H$ now cost $O_R(2^{-H})$ after absorbing any fixed polynomial in $k$; for lower ranks a marked $w>\exp(L/H^{A+1})$ costs $O_A(v\log H)$. For $d\le D$, a repeat can occur only inside $d$; marking a square $w^2\mid d$ costs $O(v^2\sum_w 1/w^2)$. This is an optional extension, not used in the theorem.

## 3. The true averaged law and threshold

Put $L_X=\log X$, $H_X=\log\log X$. On the dyadic interval use the common cutoff $D_X=\exp(L_X/H_X^{A+1})$ in place of $D$; (1) and the same absolute estimate with $A+2$ allow the replacement uniformly. Replace the tilt denominator $H$ by $H_X$; $H-H_X=O(1/L_X)$ and (4) or the derivative bound controls this change. To sum the error in (1), note that
$$
 \sum_{X<P\le2X,\ P\ {\rm even}}\mathfrak S(P)^2\ll X.
$$
Indeed expand the square as a positive sum over odd squarefree divisors with local coefficient $((w-1)/(w-2))^2-1=O(1/w)$, use $\#\{P\le2X:d\mid P\}\le2X/d$, and complete the convergent Euler product. In particular the mean error is $o(X^2/L_X^2)$.

For each fixed odd squarefree $d\le D_X$, the summed $T_{P,d}$ simply counts *two independent genuine primes* $p,q$ with $(x,y)=(p/X,dq/X)$ in the polygon $1<x+y\le2$, $(x+y)/3\le y\le2(x+y)/3$. The lower endpoints of the two prime ranges are polynomially large, $p,q>d$, so $P=p+dq$ is even and $(P,d)=1$ automatically. The area is $\int_1^2 t\,dt/3=1/2$. By ordinary PNT on fixed mesh boxes in the polygon and squeezing the boundary,
$$
 \sum_{X<P\le2X,\ P\ {\rm even}}T_{P,d}
  =(1/2+o(1))\frac{X^2}{dL_X^2}
$$
uniformly: $\log (X/d)=(1+o(1))L_X$ on the entire common range. Fix the arbitrarily fine mesh first, then let $X$ grow. The error remains small after weighting by $|u/H_X|^{\Omega(d)}$ since the reciprocal Euler sum below is bounded on fixed disks.

Finally the product $\prod_{2<w\le D_X}(1+u/(H_X w))$ tends uniformly to $e^u$, since $\sum_{2<w\le D_X}1/w=H_X-(A+1)\log H_X+O(1)$ and the second Taylor remainder is $O_R(H_X^{-2})$. Omitting the product terms with $d>D_X$ changes it by $O_R(1/H_X)$: in absolute value use $1_{d>D_X}\le(\log d)/\log D_X$ and the marked Euler estimate $\sum_{w\le D_X}(\log w)/w\ll\log D_X$. This gives (2) for $Z_P$; local uniform convergence and differentiation give the assertion for $J_P$. The same pair count at $d=1$ gives the claimed mean for $G(P)$.

For example, at $u>1$ the negative part of $J_P$ must sum to $\gg_u X^2/L_X^2$. The targets with $-J_P\le c_u\mathfrak S(P)P/L^2$ contribute at most a small fraction if $c_u>0$ is sufficiently small, by the first moment bound on $\mathfrak S$. On the remainder use $|J_P|\ll_u\mathfrak S(P)P/L^2$, Cauchy–Schwarz and the bounded second moment to obtain $\gg_u X$ such even targets. The positive case is identical with the sign reversed.

Consequently a promising fixed-$u$ positive proof using this specific minorant must work on the $u\le1$ side and control the *actual* small-$d$ kernels; the formula cannot promote a positive dyadic mean to an individual sign. Even merely a positive lower for the nonnegative $Z_P(u)$ on the natural scale for every large $P$ would, by (1), force $P=p+dq$ with a subpower multiplier and $p,q$ central in the above scaled sense. Existing signed populations carrying a fixed-power second factor do not establish that statement.
