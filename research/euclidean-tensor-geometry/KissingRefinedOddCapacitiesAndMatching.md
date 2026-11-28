# At most nine uncovered points at size 129, unconditionally in dimension seven

**Theorem.** In every $60^\circ$ unit-vector code in $\mathbb R^7$ of size **128**, there are at least **59 disjoint pairs** with scalar product strictly less than $-1/2$. At size **129**, there are at least **60**. Thus at most ten or nine points, respectively, remain uncovered. Prior guarantees were 58 and 59. These are genuine matchings, not fractional matchings or pairs of exact antipodes. There is no assumption of symmetry, integrality, exact antipodes, or a prescribed root subsystem; the existence of either hypothetical code is not asserted.

Together with the [127-point result](https://github.com/mxym/math/blob/1a6fdc1dc8d4a4a1df7aef313b34e9c21b472400/research/euclidean-tensor-geometry/KissingNinePointCapacityAnd127Matching.md) and [129–132 barrier bounds](https://github.com/mxym/math/blob/c36c642c5f6984e670f9ba2368f4bfafb5b966d7/research/euclidean-tensor-geometry/KissingOddComponentBarriers.md), the certified matching sizes at $N=127,\ldots,132$ are now $58,59,60,60,61,62$. The unrestricted cardinality upper bound remains [Tomar's 132](https://www.mefyi.com/papers/kissing-numbers-five-seven/).

## Sharper local capacities

For $f(t)=t^4-t^2/4$ define $C(X)=\min_{p\ge0,\sum p_i=1}\sum_{ij}p_ip_j f(x_i\cdot x_j)$. In **any ambient dimension**, the following hold for every $60^\circ$ code of the indicated size:
\[
 |X|=5:\ C(X)\le .252,\qquad
 |X|=7:\ C(X)\le .202,\qquad
 |X|=9:\ C(X)\le .163.
\]
These decimals are exact rationals. The [sharp heptagon construction and analysis](KissingSharpHeptagonalCapacity.md) show, without numerical optimization, that the optimal unrestricted seven-point constant is at least $0.200850277798\ldots$; thus this particular input cannot be improved to $1/5$. The exact unrestricted constant is not claimed.

Put a strong edge on each pair with product $<-1/2$. No triangle is possible, since the squared length of a sum of three pairwise strong vectors would be negative. An independent $a$-set, with uniform weights, gives $C\le3/(4a)$. On five vertices, if there is no independent triple the strong graph and its complement are triangle-free. Every vertex has two neighbors: three neighbors would be an independent triple, and the complement gives the same upper bound for nonneighbors. The graph is therefore a pentagon. On seven vertices it suffices to cover graphs with independence number at most three. On nine vertices it suffices to cover graphs with independence number at most four. The [preceding exact census and maximal-barrier reduction](https://github.com/mxym/math/blob/1a6fdc1dc8d4a4a1df7aef313b34e9c21b472400/research/euclidean-tensor-geometry/KissingNinePointCapacityAnd127Matching.md) leave nine seven-vertex graphs and 170 factor-critical nine-vertex graphs. For a non-factor-critical remaining nine-vertex case, dropping the barrier leaves $7+1$ or $5+1+1$; each reciprocal sum, $1/.202+4/3$ or $1/.252+8/3$, is strictly larger than $1/.163$. Cross-component costs are nonpositive, so inverse-capacity weighting proves the desired bound there as well.

The [refined local verifier](verify-kissing-refined-small-capacities.py) calls the byte-pinned [continuous Gram-cell oracle](https://github.com/mxym/math/blob/1a6fdc1dc8d4a4a1df7aef313b34e9c21b472400/research/euclidean-tensor-geometry/verify-kissing-nine-gram-cells.py) at the new targets. It proves affine probability-weight majorants on closed boxes of Gram entries, using integer PSD cuts, exact angle propagation, and exact box extrema. Approximate optimizers only propose multipliers; they cannot accept a leaf. In our replay, the five-point tree visited 8,871 nodes, with 4,435 integer-dual leaves and one incompatible leaf. All seven-point trees together visited 29,749 nodes (14,879 dual leaves); all nine-point trees visited 30,134 nodes (15,151 dual leaves and one incompatible leaf). The largest nine-point tree had 959 nodes. These counts document a replay, not acceptance conditions.

## Disjoint-pair conclusion

In dimension seven the constant harmonic coefficient of $f$ is $1/84$ and the degree-two and degree-four coefficients are positive. For the odd factor-critical components outside a maximum Tutte–Berge barrier $T$ (tied by largest $t=|T|$), assigning each component inverse-cost mass shows that its component bounds $c_i$ must satisfy $\sum_i1/c_i\le84$. Each component is a singleton or has odd size at least five. On a singleton $c_i=3/4$; for larger components use the above bounds or uniform energy charts. A certified uniform per-point cost $U_q$ gives, by averaging over $q$-subsets, $c_k\le [3/4+(k-1)(U_q-3/4)/(q-1)]/k$ for $k\ge q$.

The [reciprocal-barrier replay](verify-kissing-128-129-reciprocal-barriers.js) verifies 22 additional or improved rational three-point charts, at
\[
q=11,29,31,39,41,49,51,53,55,57,61,65,67,69,71,73,75,77,79,81,85,89 .
\]
The positive kernels are those of [Bachoc and Vallentin](https://arxiv.org/abs/math/0608426). The exact polynomial combination is checked by outward dyadic Bernstein subdivision on the continuously feasible ordered Gram triples; each rational cost is rounded **up** to millionths. The other fixed inputs are precisely the published [127-point verifier](https://github.com/mxym/math/blob/1a6fdc1dc8d4a4a1df7aef313b34e9c21b472400/research/euclidean-tensor-geometry/verify-kissing-127-reciprocal-barrier.js) and its cited predecessors.

If a matching of size $m$ cannot be found, the number $o$ of components satisfies $o\ge t+N-2(m-1)$ and $o\equiv N-t\pmod 2$. If $s$ components are singletons, delete $T$ and add the $s$ opposites: this is a legal code of size $N-t+s$, so $s\le132-N+t$. For each size $k$, round the best lower bound for $10^6/c_k$ **down**. An unbounded-part dynamic program gives the least total charge for all choices of $t,o,s$ and all nonsingleton odd parts of size at least five, summing to $N-t-s$ in exactly $o-s$ parts:

| $N$ | assumed matching number at most | minimum charge | minimizing $(t,o,s)$ |
|---:|---:|---:|---:|
| 128 | 58 | 84,163,752 | $(0,12,4)$ |
| 129 | 59 | 84,011,113 | $(0,11,3)$ |

Both exceed 84,000,000, a contradiction. No assumption that the chart bounds or component bounds are sharp appears in this argument.

**Replay** (Python with NumPy, SciPy and threadpoolctl, plus standard Node.js):
~~~sh
python3 verify-kissing-refined-small-capacities.py census
python3 verify-kissing-refined-small-capacities.py 5
python3 verify-kissing-refined-small-capacities.py 7
python3 verify-kissing-refined-small-capacities.py 9
node verify-kissing-128-129-reciprocal-barriers.js
python3 verify-kissing-heptagon-extrema.py
~~~
The three Gram commands accept a final class index for parallel or selective replays. Failure to close any cell is a failure, not a proof. The pinned predecessor Python file must be in the same directory.
