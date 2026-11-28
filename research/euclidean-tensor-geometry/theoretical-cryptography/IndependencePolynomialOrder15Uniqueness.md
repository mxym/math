# The unique order-15 independence-polynomial witness, and two fixed-rank minima

**Theorems.**

1. The only simple graph on 15 vertices with a nonunimodal independence polynomial, up to isomorphism, is the complement of a copy of \(K_6\) with one edge removed and nine added isolated vertices. There are exactly \(75{,}075\) labelled witnesses. This graph is connected and threshold.
2. For independence number exactly three, the minimum order of a simple graph with a nonunimodal independence polynomial is **33**. For independence number exactly four it is **19**. These minima do not change if the graph is required to be connected.

The [earlier minimum-order proof](IndependencePolynomialMinimumOrder.md) established the minimum order 15 over all simple graphs and exhibited the witness. The additions here are its uniqueness and the two fixed-independence-number results, not another proof of a new unrestricted minimum. The finite check uses exact integer arithmetic in Python, not Lean. The fixed-rank proofs below are independent of the finite uniqueness check.

Use the complement \(H\) of the graph in question, and let \(f_j\) be the number of its \(j\)-cliques, with \(f_0=1\), \(f_1=n\), and \(r=\omega(H)\). Failure of weak unimodality means a strict drop followed later by a strict rise; a flat interval in between is permitted. For \(r\le2\) there is no failure.

## 1. Initial reduction for the classification

For a fixed \(n,r,m=f_2\), use the integer lower and upper bounds of Sections 2–3 of the preceding note. In brief:

- Frohmader's [face-vector theorem](https://pi.math.cornell.edu/~froh/flagcomp.pdf), together with [Frankl–Füredi–Kalai](https://doi.org/10.7146/math.scand.a-12231), gives the colex upper bound \(Q_k(a)\) on \(f_{k+1}\) at \(f_k=a\). Label the vertices \(0,\ldots,n-1\), color by residue modulo \(r\), and order admissible \(k\)-sets (distinct colors) by binary mask. Each admissible \((k+1)\)-set is available if all of its \(k\)-subsets occur among the first \(a\) masks. This bound does not assert that \(H\) is \(r\)-colorable. Only these \(n\) labels are needed because the balanced complex with the same vector has \(n\) vertices; equivalently, the colored-colex upper bound bounds the counts on the first \(n\) labels inductively from \(f_1=n\).
- The [Moon–Moser inequality](https://real.mtak.hu/201267/) gives \(f_{k+1}\ge\lceil(k^2a^2-nab)/((k^2-1)b)\rceil\) at \((f_{k-1},f_k)=(b,a)\).
- A fixed maximum clique \(K\) leaves \(q=n-r\) outside vertices. For each sorted degree list \(D\in[0,r-1]^q\), use \(e=m-\binom r2-\sum D\) as the number of edges among them, ignoring lists for which \(e<0\) or \(e>\binom q2\). For rank \(j\ge3\) count all cliques with zero or one outside vertex and lower bound the cliques with two outside vertices by the \(e\) smallest pair contributions \(\binom{\max(0,d_s+d_t-r)}{j-2}\), where the two degrees refer to distinct positions of \(D\). At rank 3 also use the Moon–Moser triangle bound in the outside graph and in the whole graph. Minimize over the lists at each rank independently. These are valid simultaneous lower bounds even though their attaining lists need not agree.

Start at \(f_2=m\), with one of three flags: no drop, a drop and no later rise, or both a drop and a later rise. For a fixed \(m,a\) and flag retain only the largest preceding \(b\); the only one of the interval bounds that depends on \(b\) is nonincreasing in \(b>0\). Every realizable next step therefore remains admissible. At an admissible first rise after a drop, log its source rank and count \((k,a)\). Such logging can include prefixes that do not reach rank \(r\), which only enlarges the remaining candidate set. If a real counterexample exists, its edge count \(m\) admits a terminal flag with both steps at rank \(r\), and its own first-rise source is among the logged ones.

The accompanying exact checker uses direct colored colex (all immediate subfaces) and a descending-predecessor interval envelope. For \(n=15\) it gives:

| \(r\) | Terminal edge counts \(m\) | Logged first rise after a drop |
|---|---|---|
| 5 | 14 | \(f_2=14\) to \(f_3\) |
| 6 | 63–67 | \(f_3<m\) to \(f_4\), 12 pairs \((m,f_3)\) |
| 7 | 50–61 | \(f_3<m\) to \(f_4\), 48 pairs \((m,f_3)\) |
| 9 | 70–82 | \(f_4\) to \(f_5\) |

No other \(r\) reaches that terminal flag.

## 2. Eliminate clique numbers six, seven and nine

For \(r=6,7\), write \(U=V(H)\setminus K\), \(q=|U|\), and \(D\) for its sorted cross degrees as above. Put \(e=m-\binom r2-\sum D\). Write \(t=f_3\), \(u=f_3(H[U])\), and \(S=\sum_{ij\in E(H[U])}|N(i)\cap N(j)\cap K|\). The triangle count requires
\[
S=t-\binom r3-\sum_{d\in D}\binom d2-u.
\]
The exact check runs over \(D\) and over all integers \(u\) between the Moon–Moser triangle lower bound and the ordinary Kruskal–Katona upper bound from \(e\) edges. It rejects \(S\) below the sum of the \(e\) smallest values of \(\max(0,d_i+d_j-r)\) over distinct pairs.

The maximum clique size implies that for an outside edge its common neighborhood in \(K\) has size at most \(\min(d_i,d_j,r-2)\). Let \(c_1,\ldots,c_e\) be the \(e\) largest such caps over all outside pairs, in descending order. After sorting the actual \(e\) common-neighbor sizes decreasingly the \(i\)-th cannot exceed \(c_i\): a value above that cap would require at least \(i\) pairs of cap above it. Let \(B(c,S)\) be the greatest \(\sum_i\binom{x_i}{2}\) over integers \(0\le x_i\le c_i\) with sum \(S\). The checker computes it by allocation dynamic programming, allowing all values at each cap. It rejects \(S>\sum c_i\). This also verifies the bound without relying on greedy majorization: filling descending caps to total \(S\) does in fact attain the maximum, since its \(j\)-th prefix sum is \(\min(S,\sum_{i\le j}c_i)\), which dominates every sorted feasible vector, and \(\binom{x}{2}\) is convex.

Count four-cliques by the number of vertices in \(U\).

- Zero or one: exactly \(\binom r4+\sum_{d\in D}\binom d3\).
- Two: at most \(B(c,S)\).
- Three: for each \(z\in K\) examine \(H[N(z)\cap U]\). In their disjoint union there are \(S\) edges, so the contribution is at most the ordinary Kruskal–Katona triangle upper bound from \(S\). Each edge extends to at most \(q-2\) triangles in its own graph, also giving \(\lfloor(q-2)S/3\rfloor\). Finally, each of the \(u\) outside triangles has at most \(\min(r-3,d_{(3)})\) common neighbors in \(K\), where \(d_{(3)}\) is the third-largest entry of \(D\). The bound \(r-3\) uses the maximality of \(r\), and the smallest degree among any three is at most \(d_{(3)}\). Take the minimum of the three bounds.
- Four: take the smaller of the ordinary Kruskal–Katona four-clique bound from \(u\) triangles and \(\lfloor(q-3)u/4\rfloor\).

Summing and maximizing over the lists and counts gives a bound for each \((m,t)\). Across the nonempty relaxed cases, the maximum of this bound minus \(t\) is \(-11\) for \(r=6\) and \(-2\) for \(r=7\). In particular \(f_4>f_3\) is impossible.

For \(r=9\), fix its nine-clique \(K\); the six outside vertices form \(U\). The contribution of \(K\) to \(f_3-f_4\) is \(84-126=-42\). For an outside \(j\)-clique with \(d\) common neighbors in \(K\), its additional contribution is \(\binom d{3-j}-\binom d{4-j}\), using zero for negative ranks. For \(j=1,2,3\) this is bounded above by \(2,1,1\), respectively, and for \(j=4\) it is \(-1\). Therefore
\[
f_3-f_4\le -42+6\cdot2+\binom62+f_3(H[U])-f_4(H[U])
 =-15+f_3(H[U])-f_4(H[U]).
\]
If \(f_3(H[U])\le15\) this is nonpositive. Otherwise \(U\) is missing at most one edge: two missing edges spoil at least seven of the twenty triples. It then has at least nine four-cliques, so the bound is at most \(-15+20-9<0\). Also \(f_3\ge84>m>15\) in the terminal range. Thus there is no drop before the only candidate rise, \(f_4\) to \(f_5\), and this rank is excluded.

## 3. The surviving clique number five

Here \(m=14\) and \(f_3>14\). Fix a five-clique \(K\). There are four edges outside it and at least five triangles not wholly within it. Let \(c\) be the number of cross edges, and \(e=4-c\) the number of edges within \(U\). Triangles with exactly one outside vertex are at most \(\binom c2\); those with two are at most \(e\lfloor c/2\rfloor\), since two endpoints of an outside edge each need a cross edge per common neighbor in \(K\). There is at most one triangle entirely outside \(K\) because \(e\le4\), and none if \(e<3\). For \(c=0,1,2,3\), the sum is at most \(1,1,3,4\), respectively. So \(c=4\), \(e=0\). If the four cross edges have more than one endpoint in \(U\), they give at most three triangles; hence they all meet the same outside vertex.

This is exactly \(K_6\) with one edge removed, plus nine isolated vertices. Its clique vector is \((1,15,14,16,9,2)\), and its complement is connected. The complement is threshold since its six non-universal vertices form one edge and four isolates (constructed with isolated and universal additions), followed by nine universal additions. The two endpoints of the missing edge in the six-vertex core and the four other core vertices uniquely specify a labelled copy, giving \(\binom{15}{2}\binom{13}{4}=75{,}075\).

## 4. Fixed independence numbers three and four

In the colored-colex edge prefix the first edge count \(m\) permitting more than \(m\) triangles is 32 for three colors, and 18 for four colors. Here is a direct verification of both small thresholds. At the end of a label's edge block the graph is complete multipartite on the labels used so far; between such ends its only new edges join one new vertex to earlier admissible neighbors in increasing label order. Newly supported triangles are the different-color pairs among those neighbors.

For three colors and at most nine labels, each triangle edge has at most three choices of third vertex, so the triangle count is at most the edge count. At nine labels the full prefix is \(K_{3,3,3}\), with 27 edges and 27 triangles. For the next label the six admissible neighbors alternate two colors; at \(d\) new edges the triangle increment is \(\lfloor d^2/4\rfloor\). This exceeds \(d\) for the first time at \(d=5\), giving \(m=32\), \(f_3=33\).

For four colors, the first four labels give \(K_4\), with six edges and four triangles; every preceding prefix has at most as many triangles as edges. The fifth label adds at most three edges, and its \(d\) new edges give \(\binom d2\le d\) new triangles. The sixth label, starting from nine edges and seven triangles, has successive triangle increments \(0,0,1,3,5\) at \(d=0,1,2,3,4\); none exceeds the edge count in total. Starting from the resulting 13 edges and 12 triangles, the seventh label has increments \(0,0,1,3,5,8\) at \(d=0,1,2,3,4,5\). The first strict excess is at \(d=5\), giving \(m=18\), \(f_3=20\).

For \(r=3\) the only possible valley requires \(n>f_2<f_3\), so \(n\ge33\). For \(r=4\) and \(n\le18\), the same valley is impossible because \(f_2<n\) would give \(f_2\le17\). If the first rise after a drop is from \(f_3\) to \(f_4\), then \(f_3\le f_2\le153\): a drop before the final rise, without an earlier rise after that drop, forces \(f_3\le f_2\). Use a four-colored complex with the same face vector, by Frohmader. Its four-faces can be viewed as ordered four-tuples, one coordinate per color. The four projections obtained by omitting a color consist of disjoint color-pattern subsets of its triangles, so their sizes sum to at most \(f_3\). The discrete [Loomis–Whitney inequality](https://doi.org/10.1090/S0002-9904-1949-09320-5) and AM–GM give \(f_4^3\le(f_3/4)^4\), hence \(f_4\le f_3\) whenever \(f_3\le256\). There is again no valley.

For order 33, take the complement of \(K_{4,3,3}\) with one edge deleted between the parts of size four and three, and with 23 isolates added before complementation. The clique number is three and the coefficients are \((1,33,32,33)\). For order 19 take the complement of \(K_{2,2,2,1}\) with twelve isolates similarly added, giving clique number four and coefficients \((1,19,18,20,8)\). In both instances the added isolates give universal vertices in the intended graph, so it is connected.

## Checks and comparison

Run `python3 verify_independence_polynomial_order15_uniqueness.py` with Python 3.9 or newer. The checker uses only the standard library. It recomputes the colex tables by checking every immediate subface, sweeps the numerical recurrence, checks the outside allocation by integer dynamic programming, and counts the witness cliques directly. The initial numerical reduction follows the original order-14 proof; the new residual cases use sharper allocation bounds. The examples of [Alavi–Malde–Schwenk–Erdős](https://www.renyi.hu/~p_erdos/1987-33.pdf) and the earlier 16-vertex threshold example of [Levit–Mandrescu](https://arxiv.org/abs/1007.0880) concern existence, while the [recent forest result](https://arxiv.org/abs/2610.07943) has a different graph-class scope. None of the checks here is a claim about all well-covered graphs or about possible ranks beyond the ones stated.
