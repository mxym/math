# Root-free pair-count bounds at 75–76 and 129–132 kissing points

A hypothetical 76-point kissing code in $\mathbb R^6$ has **at most 17 antipodal pairs**; a 132-point code in $\mathbb R^7$ has **at most 37**. The complete set of improvements below imposes no root system, integrality, transversality, or assumptions on any remaining points.

| Dimension | Points | Previous upper bound on pairs | New upper bound on pairs | $10^7 h$ |
|---:|---:|---:|---:|---:|
| 6 | 75 | 22 | **20** | 89 |
| 6 | 76 | 20 | **17** | 406 |
| 7 | 129 | 49 | **47** | 39 |
| 7 | 130 | 47 | **44** | 162 |
| 7 | 131 | 46 | **41** | 157 |
| 7 | 132 | 45 | **37** | 111 |

The last column is exact: in the indicated row, even one pair **more** than the new bound is impossible if all those disjoint pairs satisfy $\|x+y\|\le2h$ on the unit sphere. The pairs need not be exactly antipodal. This is a restriction on distance distributions, not a reduction of the unrestricted kissing-number upper bound.

The comparison column comes from the [earlier tradeoff](KissingAntipodalTradeoffSixSeven.md). For 73 and 127 points the [19-point energy theorem](KissingNineteenPointEnergy.md) gives at most 26 and 53 pairs. We do not improve the 74- or 128-point rows here.

## Four uniform energy bounds

Let $f(t)=t^4-t^2/4$. For any $q$ kissing points $y_1,\ldots,y_q$ in dimension at most seven, define their mean ordered energy, **including the diagonal**, by
\[
 E_q=\frac1q\sum_{i,j=1}^q f(y_i\cdot y_j).
\]
Each of the following upper bounds is unconditional on the chosen $q$-point set.

| $q$ | Exact upper bound $U_q$ | Strict threshold used |
|---:|---|---|
| 33 | $24746907619329667/15000000000000000$ | $33/20$ |
| 40 | $16658530157187769/10000000000000000$ | $5/3$ |
| 47 | $524322162503271/312500000000000$ | $47/28$ |
| 56 | $2099404735107247/1250000000000000$ | $42/25$ |

The [standalone verifier](verify-kissing-higher-cardinality-energy.js) contains four sets of rational Gram factors and scalar coefficients. Each gives a positive semidefinite [Bachoc–Vallentin three-point kernel](https://arxiv.org/abs/math/0608426) for dimension seven and hence works in all lower dimensions by isometric embedding. The exact inequalities are those in the [19-point certificate derivation](KissingNineteenPointEnergy.md#the-energy-certificate), with the chart's own $q,\epsilon,\eta$. In particular a symmetric three-point polynomial $S$ has nonnegative ordered triple sum; the auxiliary scalar kernel $h_0$ has nonnegative ordered pair sum. The verifier proves $S(a,b,c)\le g(a)+g(b)+g(c)+\epsilon$ on the entire kissing triple Gram domain, and $f(t)+h_0(t)+3S(1,t,t)+3(q-2)g(t)\le B+\eta$ on $[-1,1/2]$. Diagonal, repeated-index and distinct-index contributions give exactly $U_q$ as in the linked derivation. The proof uses rational polynomial expansion and outward-rounded integer Bernstein subdivision, not a conclusion drawn from grid samples.

## Why this bounds the number of marked pairs

Write $P=36$ in dimension six and $P=63$ in dimension seven. If $p$ exact pairs are marked and $q$ points remain, put $s=P-p$. Select one representative per marked axis with weight one and give each residual point weight $s/q$. The constant Gegenbauer coefficient of $f$ in the **ambient** dimension is $f_0=3/(4P)$, and its other coefficients are nonnegative. Hence its weighted ordered energy is at least $f_0 P^2$. Every nondiagonal term involving a marked axis has $|t|\le1/2$, so $f(t)\le0$. Consequently
\[
 f_0P^2\le 3p/4+(s^2/q)E_q,\qquad E_q\ge 3q/(4s).
\]
For the table choose $s=15,18,21,25$ respectively at $q=33,40,47,56$. Each required lower bound is strictly larger than the certified $U_q$. Marking an exact number of pairs does not assert it is the full antipodal count: any surplus pairs remain in the residual code.

For the tolerance, write marked pairs as $m_i\pm r_i e_i$, with $e_i$ unit and $\|m_i\|\le h$. The [straightening argument](KissingNearAntipodalTail.md#1-straightening-the-marked-pairs-without-moving-the-residual-code) gives $(e_i\cdot e_j)^2\le A=((1/2+h^2)/(1-h^2))^2$ and $(e_i\cdot y)^2\le C=(1/2+h)^2/(1-h^2)$ for unmarked points $y$. Put $\phi(v)=v(v-1/4)$. The same weights now require
\[
 3s/4-(s^2/q)U_q-p(p-1)\phi(A)-2ps\phi(C)\le0.
\]
The replay checks strict positivity at the displayed rational $h$ values. These radii are certified tolerances, not asserted optimal.

**Replay:** `node verify-kissing-higher-cardinality-energy.js`. No packages, optimizer or network access are needed. A separate implementation also recomputed the energy bounds using closed-form Gegenbauer expansions and a reversed-coordinate Bernstein subdivision.
