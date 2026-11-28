# Two small fixed-rank results for independence polynomials

Let \(N(r)\) and \(N_{\rm conn}(r)\) be the minimum orders of a graph and a connected graph, respectively, with independence number \(r\) and a nonunimodal independence polynomial. We prove
\[
18\ \le\ N(9)\ \le\ N_{\rm conn}(9)\ \le\ 19.
\]
We do not decide order 18. We also classify all 16-vertex, independence-number-five graphs with nonunimodal independence polynomial: there are exactly four isomorphism types, all connected, and exactly 12,732,720 on a fixed labeled vertex set. These specialize the earlier [minimum-order](IndependencePolynomialMinimumOrder.md), [order-15 uniqueness](IndependencePolynomialOrder15Uniqueness.md) and [order-16 allowed ranks](IndependencePolynomialOrder16Ranks.md) results. The order-16 classification concerns only rank five. It is not a classification at ranks six or seven, nor a result restricted to well-covered graphs.

We work in the complement \(H\), with \(f_j(H)\) its \(j\)-clique count. A strict drop followed by any strict rise characterizes failure of weak unimodality.

## 1. Finite arithmetic certificate

The [companion Python checker](verify_independence_polynomial_finite_followups.py) independently implements the same necessary-conditions envelope as the order-15/16 proofs. It uses the [Frankl–Füredi–Kalai upper bounds for colored complexes applied to flag complexes via Frohmader](https://pi.math.cornell.edu/~froh/flagcomp.pdf), and [Moon–Moser's consecutive clique-ratio inequality](https://real.mtak.hu/201267/). The two constraints and the deterministic replay are explained here to distinguish them from a graph enumeration.

* For fixed order \(n\) and clique number \(r\), take the colex order on the subsets of the labels \(0,\ldots,n-1\) with no repeated residue modulo \(r\). For a given count \(y=f_k\), the colored upper bound \(U_k(y)\) is the number of \((k+1)\)-sets whose largest \(k\)-subset lies among the first \(y\) \(k\)-sets. The code orders masks numerically, which is colex, and the largest \(k\)-subset of a \((k+1)\)-set is obtained by removing its smallest label. Colored colex can be taken in the first \(n\) labels: the colex of \(k\)-sets on the infinite residue coloring exhausts those labels before adding the next one, and the maximum number of \(k\)-faces of an \(r\)-colored complex on \(n\) vertices is attained by the balanced coloring.
* For \(x=f_{k-1}, y=f_k\), the lower bound is \(f_{k+1}\ge\lceil(k^2y^2-nyx)/((k^2-1)x)\rceil\). For the ratio inequality, count extensions \(d(Q)\) of each \((k-1)\)-clique \(Q\) to a \(k\)-clique. Its square counts ordered pairs of such extensions. For each \(k\)-clique \(T\), the sum of \(d(Q)\) over its \(k\) codimension-one faces is at most \(n+(k-1)d(T)\): a vertex not adjacent to all of \(T\) is counted at most once. Thus \(k^2y^2/x\le\sum_Q d(Q)^2\le ny+(k^2-1)f_{k+1}\), by Cauchy–Schwarz and summing over \(T\). The triangle bound below is its \(k=2\) case. For each edge count \(m=f_2\) another lower bound on each rank comes from a fixed \(r\)-clique \(K\). Enumerate the sorted outside-to-\(K\) degree list \((d_i)\) with \(0\le d_i<r\); the number \(e=m-\binom r2-\sum_i d_i\) of outside edges is then fixed. Count cliques with zero or one outside vertex exactly. For two outside vertices use the \(e\) smallest entries in the list of pair common-neighbor lower bounds \(\max(0,d_i+d_j-r)\); this underestimates every corresponding clique count. For triangles also count the internal outside lower bound \(\max(0,\lceil(4e^2-q^2e)/(3q)\rceil)\), \(q=n-r\), and separately apply the same bound to all of \(H\). Take independent minima for each rank over the admissible degree lists. These are valid lower bounds even when the different minima cannot all occur together.
* A state stores the current coefficient, whether a drop and then a rise have been seen, and the largest predecessor that reaches that state. For fixed \(y>0\) the Moon–Moser lower bound weakens monotonically as \(x\) increases; the other bounds do not depend on \(x\). Consequently retaining only the largest predecessor cannot discard a needed continuation. The list of recorded first rises is a superset: some may not lie on a path reaching the final rank.

The exact outputs used here are:

| \((n,r)\) | Edge counts surviving this envelope | First post-drop rise and its lower endpoint |
|:--|:--|:--|
| \((16,5)\) | 14 or 15 | \(f_3>f_2\) only |
| \((17,9)\) | 44 edge counts (64 through 107) | \(f_5>f_4\) only, \(f_4\ge175\) |
| \((18,9)\) | 58 edge counts (62 through 119) | \(f_5>f_4\) only, \(f_4\ge175\) |

All nonempty clique counts are positive for \(k\le r\), since \(K\) itself contributes. The integer checker requires no optimizer or numerical tolerances.

## 2. Rank nine: order 17 is impossible

The prior [order-16 rank result](IndependencePolynomialOrder16Ranks.md), together with earlier exclusions at smaller orders, already rules out \(n\le16\). At \(n=17\), the previous sharp edge-to-triangle bound gives \(f_2-f_3\le36-84+16+8=-24\), while \(f_2\ge36>17\). Thus a surviving \(f_5>f_4\) must follow a strict \(f_3>f_4\). (The same reasoning at \(n=18\) gives \(f_2-f_3\le-19\), so the same strict valley is necessary there.)

Fix a nine-clique \(K\), and write \(U=H-K\), of order eight. For each clique \(S\) in \(U\), let \(d(S)\) be its common-neighbor count in \(K\). A nonempty \(S\) contributes \(\binom{d(S)}{j-|S|}\) to \(f_j(H)\), with negative lower arguments interpreted as zero. For \(|S|=1,2,3\), its contribution to \(f_3-f_4\) is at most \(2,1,1\), respectively. Let \(L_i\) be the sum of deficits from these maxima at outside size \(i\), and set \(L=L_1+L_2+L_3\). With \(F=f_2(U)+f_3(U)-f_4(U)\), this gives
\[
f_3(H)-f_4(H)=-26+F-L.
\]
Here \(-26=\binom93-\binom94+2\cdot8\), and each outside four-clique contributes \(-1\). By signed Zykov symmetrization as in the order-16 proof, we have
\[
F\le40,\qquad 3F+f_5(U)\le120.
\]
Both exact maxima are obtained by evaluating the numbers \(f_i(U)\) as the coefficients of \(\prod_j(1+a_jx)\) for the 22 integer partitions \((a_j)\) of eight. Signed symmetrization applies because both objectives are linear in clique counts, and replacing the lower-contribution of two nonadjacent false-twin classes by clones of the higher does not decrease the objective. The contribution per vertex is constant in each class, and no clique can meet both classes. The merge preserves previously obtained twin classes, so a finite sequence reaches a complete multipartite graph.

If \(f_3-f_4\ge1\), then \(L\le F-27\le13\). A singleton with \(d\ge7\) has deficit at least 16, and an edge with \(d\ge7\) has deficit at least 15. A triangle with \(d\ge5\) would force each of its three edges to have deficit at least six. Thus \(d\le6\) for singletons and edges, and \(d\le4\) for triangles. On these finite ranges:
* the singleton contribution \(\binom d4\) to \(f_5(H)\) is at most \(1+3\ell_1\);
* the edge contribution \(\binom d3\) is at most \(3\ell_2\);
* the triangle contribution \(\binom d2\) is at most \(3d/2\), where \(d=\ell_3\);
* the sum of four-clique contributions \(d(Q)\) is at most \(5L_3/4\), because each triangle extends to at most five outside four-cliques, each such four-clique contains four triangles, and each of their \(K\)-neighborhoods contains that of \(Q\).

In total \(f_5(H)\le126+8+3L+f_5(U)\le134-81+120=173\), in contradiction to \(f_5>f_4\ge175\).

## 3. A connected rank-nine witness at order 19

In \(H\), take \(K_{10}\) with one edge removed and an outside complete tripartite graph with three vertices in each part. In the core choose six distinct anchors \(a,b,c,d,e,f\), not endpoints of the missing edge. Give each vertex in the three parts the respective core neighborhoods \(\{a,b,d\},\{b,c,e\},\{a,c,f\}\). The pair intersections have size one and the triple intersection is empty. Thus a clique using an outside vertex has size at most four. The full vector is
\[
(1,19,98,193,191,196,140,64,17,2).
\]
In the complement each outside part is a clique, every unused core vertex meets every outside vertex, and each anchor has a complement neighbor in at least one outside part. Hence the complement is connected.

## 4. The four types at order 16 and rank five

Let \(K\) be a five-clique of \(H\). The envelope gives \(m=f_2\in\{14,15\}\) and \(f_3>m\). Write \(c\) for the number of edges crossing \(K\) and the outside, and \(e\) for the number of edges in the outside, so \(e+c=m-10\). There must be at least \(m-9\) triangles meeting the outside.

Triangles with a single outside vertex number \(\sum_u\binom{d_u}2\); a triangle with two outside vertices uses an outside edge and can be counted at most \(\lfloor c/2\rfloor\) times per such edge. In at most five edges the maximum number of triangles is two, attained by \(K_4\) with one edge removed; any three distinct triangles contain at least six edges in their union. For at most four and at most two edges the maxima are respectively one and zero.

For \(m=14\), the respective bounds for \(c=0,1,2,3\) from these observations are \(1,1,3,4\), less than the five needed. Thus \(c=4,e=0\), and the only way to reach five is to put all four edges at one outside vertex (every split has at most three one-outside triangles). This is \(K_6\) with one edge removed together with ten isolates.

For \(m=15\), the respective bounds for \(c=0,1,2,3\) are \(2,1,5,5\), less than six. At \(c=4,e=1\), a split of the four cross edges gives at most three one-outside triangles and at most two two-outside triangles, so all four edges share an outside endpoint. At \(c=5,e=0\), there cannot be a degree-five outside vertex since \(\omega(H)=5\). A split other than \(4+1\) gives at most four triangles. In both admissible cases the graph is \(K_6\) with one edge removed and then an additional edge of one of three types: disjoint from the six-vertex core; attached at an endpoint of its missing edge; or attached at one of its other four vertices. All remaining vertices are isolates. The core is the unique 2-core; the three attachments have distinct types under its automorphism group, and the 14-edge type is separate.

Their clique vectors are \((1,16,14,16,9,2)\) for the 14-edge type and \((1,16,15,16,9,2)\) for all three 15-edge types. Each complement is connected (in particular, every \(H\) here has an isolated vertex). On 16 fixed labels there are \(\binom{16}6\binom62=120120\) choices for the core. Its extra edge, when present, has \(\binom{10}2=45,\ 2\cdot10=20,\) or \(4\cdot10=40\) possibilities, respectively. The numbers of labeled graphs are therefore \(120120,\ 5405400,\ 2402400,\ 4804800\), with sum \(12732720\).

These are finite small-order theorems, not a solution of any broad unimodality conjecture. The unrestricted \(18\)-vertex rank-nine case is unresolved by this certificate.
