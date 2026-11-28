# The rank-nine minimum for a nonunimodal independence polynomial is 19

Let $N(r)$ and $N_{\mathrm{conn}}(r)$ denote the minimum orders of a graph and a connected graph, respectively, with independence number $r$ whose independence polynomial is not weakly unimodal. Then
\[
 \boxed{N(9)=N_{\mathrm{conn}}(9)=19.}
\]
This closes the $18$–$19$ bracket in the [preceding rank-nine note](https://github.com/mxym/math/blob/044f8d449dc56affb511cf58e5e718067b8e43fb/research/euclidean-tensor-geometry/theoretical-cryptography/IndependencePolynomialFiniteFollowups.md). The new part is an order-18 exclusion; the connected order-19 witness is the same one as there. No classification of order-19 witnesses or claim about other ranks is made.

Work in the complement $H$ and write $f_i(H)$ for its number of $i$-cliques. These are the independence coefficients of the original graph. The earlier exact rank-nine coefficient envelope shows that the only possible first post-drop rise when $n=18$ is $f_5>f_4$. The preceding edge-to-triangle bound at $n=18,r=9$ gives $f_2-f_3\le-19$, and $f_2\ge36>18=f_1$. Thus the only possible obstruction to unimodality is
\[
 f_3>f_4<f_5.
\tag{1}
\]
The new lemma below rules out (1) for any graph on 18 vertices containing a $K_9$, even without assuming that its maximum clique has order 9. The envelope uses the Frankl–Füredi–Kalai bounds for flag complexes through [Frohmader](https://pi.math.cornell.edu/~froh/flagcomp.pdf) and [Moon–Moser](https://real.mtak.hu/201267/); its exact replay is available with the companion option below.

## 1. The clique deficit

Fix a nine-clique $K$ and let $U=H-K$ (nine vertices). For an outside clique $S$ let $d(S)$ be its number of common neighbors in $K$. Its contribution to $f_i(H)$ is $\binom{d(S)}{i-|S|}$. Binomial coefficients are zero if the lower index is negative or larger than the upper index.

For outside cliques of orders $1,2,3$, the maxima of their per-clique contributions to $f_3-f_4$ are $2,1,1$ respectively. Let the deficit functions relative to these maxima be
\[
 \ell_1(d)=2-\binom d2+\binom d3,\qquad
 \ell_2(d)=1-d+\binom d2,\qquad
 \ell_3(d)=d .
\]
Put $L_i=\sum_{|S|=i}\ell_i(d(S))$ for $i=1,2,3$, and $L=L_1+L_2+L_3$. With $F=f_2(U)+f_3(U)-f_4(U)$, exact expansion gives
\[
 f_3(H)-f_4(H)=-24+F-L .
\tag{2}
\]
Here $-24=\binom93-\binom94+2\cdot9$, and every outside four-clique contributes $-1$ to the difference. Signed Zykov symmetrization gives $F\le54$. Indeed, when two false-twin classes are nonadjacent, a clique cannot meet both, and replacing the lower-contributing class by clones of the other cannot decrease a linear combination of clique counts. This preserves every existing false-twin class, merges at least two, and ends in a complete multipartite graph. Evaluate $F$ by the coefficients of $\prod_i(1+a_i x)$ for the 30 unordered partitions $(a_i)$ of nine. The maximum 54 is attained for $(3,3,3)$.

Hence $f_3(H)>f_4(H)$ implies $L\le29$. In that case a singleton has $d\le7$ ($\ell_1\ge30$ at $d\ge8$); an edge has $d\le6$ (at $d\ge7$ its own deficit and the two endpoint deficits total at least $15+2\cdot16$); a triangle has $d\le5$ (at $d\ge6$ its own deficit and its three edge deficits total at least $6+3\cdot10$).

## 2. The second slope is bounded by integer shadows

Write $\beta_i(d)$ for the contribution of an outside $i$-clique to $f_5-f_4$. For $i=1,2,3$ they are
\[
 \beta_1(d)=\binom d4-\binom d3,\quad
 \beta_2(d)=\binom d3-\binom d2,\quad
 \beta_3(d)=\binom d2-d.
\]
The core itself contributes zero. The contribution from types 4 and 5 is
\[
 f_5(U)-f_4(U)+\sum_{|Q|=4}d(Q)
 \ \le\ \sum_{a\in K} f_4(U_a),
\tag{3}
\]
where $U_a$ is the induced graph on those outside vertices adjacent to $a$. The inequality uses $f_5(U)\le f_4(U)$: each 5-clique has five 4-faces, while each 4-clique has at most five extensions because $|U|=9$. Moreover $\sum_a f_3(U_a)=L_3$.

For a nonnegative integer $t$ let $\partial(t)$ denote the Kruskal–Katona lower bound for the 2-shadow of a family of $t$ triples, and $C_4(t)$ the maximum number of four-sets all of whose triples belong to a family of $t$ triples. For the canonical expansion $t=\binom{v_3}3+\binom{v_2}2+\binom{v_1}1$ with strictly decreasing active upper indices (omit zero remainder terms), the two formulas replace each lower index $j$ by $j-1$ and $j+1$ respectively. These are the usual colex form of the Kruskal–Katona theorem; see [Katona, *A theorem of finite sets*](https://real.mtak.hu/21121/). Apply the second bound to the **disjoint union of separate copies** of the nine graphs $U_a$. Tags distinguishing the copies make the total number of triples the sum $L_3$ rather than the number of distinct outside triples; each four-clique in a copy has all four of its triples present in that copy. Thus the right side of (3) is at most $C_4(L_3)$.

For each $d\ge1$ let $t_d$ count the outside triangles with common-neighbor count exactly $d$, and define $e_d$ similarly for edges. The necessary conditions for the slope bound are:
* $L_3=\sum_{d=1}^5 d t_d\le29$. Only $e_3,\ldots,e_6$ have to be enumerated: they cost $1,3,6,10$ units of $L_2$ respectively, and all other edge costs are nonnegative.
* At each threshold $j=2,3,4,5$, the edges with $d\ge j$ contain the 2-shadow of the triangles with $d\ge j$. Hence
\[
 \sum_{d\ge j}e_d\ge\partial\!\left(\sum_{d\ge j}t_d\right).
\]
At threshold 2 one may set $e_2$ to the smallest nonnegative value compatible with this inequality, for the purpose of an **upper** bound: its gain is $-1$ and its deficit is zero. Edges with $d=0,1$ have zero gain.
* For $j=3,4,5,6$, let $b_j$ be the least nonnegative integer with $\binom{b_j}2\ge\sum_{d\ge j}e_d$. Those edges require at least $b_j$ vertices whose own $d$ is at least $j$. Define $b_7=0$ in the enumeration, since no constraint at threshold 7 is needed. Impose $b_j-b_{j+1}$ nested requirements of minimum singleton degree $j$. They can be assigned to distinct vertices by sorting actual singleton degrees in descending order. The maximized sum of $\beta_1$ on these required vertices, subject to remaining deficit at most $29-L_3-\sum_{d=3}^6 e_d\ell_2(d)$, is an upper bound on the actual total: the other singletons all have $\beta_1\le0$. Optimize the sum by trying the integer degrees from each required minimum through 7, subtracting the corresponding singleton deficit at each step.

The resulting integer upper bound is
\[
 C_4(L_3)
 +\sum_{d=1}^5t_d\beta_3(d)
 +\sum_{d=2}^6e_d\beta_2(d)
 +\text{the optimized singleton sum}.
\]
The companion checker enumerates all nonnegative tuples within the indicated deficit budgets, discards only impossible threshold/vertex assignments, and gives maximum **0** (107,010 test pairs of tuples; 22,066 survive the shadow and singleton feasibility conditions). In fact the bound is at most $-1$ whenever $L_3>0$. This uses just table values for triple families of size at most 29. No unlabeled graph generation, solver, numerical tolerances or assumptions on which relaxations can be attained are needed. This proves the stated 18-vertex lemma and rules out (1).

## 3. The exact minimum and its witness

If a graph of order less than 18 and independence number 9 were nonunimodal, adding mutually adjacent vertices that are also adjacent to every original vertex until order 18 would preserve the independence number. Only the coefficient of $x$ changes, and it remains smaller than the coefficient of $x^2$, which is at least $\binom92$. Thus any strict drop and subsequent strict rise would remain. The order-18 exclusion rules this out.

For the connected upper witness, take in $H$ a $K_{10}$ with one edge removed. Outside this core place a complete tripartite graph with three vertices per part. Each part has a uniform core neighborhood given by the triples $\{a,b,d\}$, $\{b,c,e\}$, $\{a,c,f\}$ respectively, where all six anchors are distinct and none is an endpoint of the missing core edge. The clique vector is
\[
 (1,19,98,193,191,196,140,64,17,2),
\]
so the complement has independence number 9 and a strict valley. It is connected: an unused core vertex is adjacent in the complement to every outside vertex, and each anchor has an outside complement neighbor. This proves both equalities.

**Replay.** Run `python3 -O verify_independence_polynomial_rank_nine_minimum.py` to check the signed objective, the slope upper bound, and the witness by direct enumeration of all its subsets. Add `--with-envelope` next to the preceding `verify_independence_polynomial_finite_followups.py` to replay the order-18 coefficient envelope as well.
