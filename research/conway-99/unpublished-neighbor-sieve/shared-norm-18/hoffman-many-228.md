# Extreme G(2,28) incidences among original Hoffman cocliques

Let \(\mathcal C\) be any family of maximum (22-site) cocliques whose distinct intersections have size 1 or 8. In particular all original-seven-class-zero such cocliques qualify at Seidel rank 36: the class pairing gives intersection 1 modulo seven, and intersection 15 would give a norm-14 Fano difference, universally excluded at that rank. Put \(c_C=-1_C\).

**Extreme-angle cap.** For each actual charge-two cost-28 field b there are at most four C in the family with \(b\cdot c_C=15\). If four occur, *none* contains any positive point of b. This is a real graph statement and assumes no bound on the count of other charged or neutral shells.

Such b is necessarily unit: a positive entry ≥2 permits subtracting the true site field d_i, producing a charge-one field of cost at most 15; a negative entry ≤−2 permits adding d_i, producing charge three of cost at most 31. Both violate the standard charge minima. Write P,N for its positive and negative supports, of sizes 3 and 25. At v∈N the charge equation Ab=−4b−4·1 gives d_N(v)=d_P(v). At p∈P it gives d_N(p)=8+d_P(p), so 2e(N)=24+2e(P)≥24. Furthermore
\[
\sum_{v\in N}\binom{d_N(v)}2=\sum_{v\in N}\binom{d_P(v)}2\le2\binom32=6,
\]
using the global common-neighbor cap for each positive pair. Consequently at least 18 negative vertices are nonisolated in G[N], since d≤1_{d>0}+binom(d,2).

Each C with angle 15 contains 15+|C∩P| negative sites. Two such C,D must meet in eight: b−c_C−c_D has charge −2 and norm 28+44−2·15−2·15+2|C∩D|=12+2|C∩D|, below the mass floor 22 when their intersection is one. If five occur, define k_v=#selected cocliques through negative v, and d=Σ|C∩P|≥0. Then Σk_v=75+d and Σ binom(k_v,2)≤80. Expanding at three gives
\[
\sum_v(k_v-3)^2+5d\le10.
\]
Since the squared deviations dominate their absolute values and their signed sum is d, at most five negatives have k_v≤2. These sites must cover every negative edge, because two sites with counts ≥3 share one of the five independent sets. But their total internal degree is ≤5+6=11, below e(N)≥12.

Suppose there are exactly four such cocliques, and write n_i for the number of negatives of occupancy i. Now Σk_v=60+d, Σbinom(k_v,2)≤48. The tangent through k=2,3 gives
\[
3n_0+n_1+n_4+2d\le3,
\]
and thus d≤1. If d=1, no occupancy-zero site exists and n_1+n_4≤1. If n_1=0, at least 11−n_4≥10 negative vertices have occupancy ≥3 and all are isolated, contradicting the 18 nonisolates. If n_1=1 then n_4=0 and n_3=12, of which at most three see the lone occupancy-one vertex, again leaving at least nine isolated. This proves d=0 at cap four.

**Actual and averaged budgets.** The graph-wide count of pairs (C,t), with C in the original family and t an oriented norm-twenty field with t·c_C=−7, is at most four times the actual positive-charge cost-28 population. The same correspondence also respects each extension, as follows.

 Fix a maximal extension H and pool uniformly the M>0 original cocliques from the qualifying family. Let K228(15) be the averaged number of eligible fields b at this angle, with the same folded-population factor as W228. Each extreme incidence bijects to t=b−c_C of charge zero, cost20, and dot t·c_C=−7. Conversely any such t gives b=t+c_C. A true original coclique changes no terminal seven residue; the folded multiplicity is therefore identical on the two sides. Thus
\[
M K020(-7)=M K228(15)\le4W228.
\]
The same holds after averaging H. If K^{P>0} is the subset with C∩P_b nonempty, the stronger left side M[K228(15)+(1/3)K^{P>0}] also satisfies this bound: any field yielding even one such extra-counted incidence has at most three extreme incidences. No conclusion about existence of the five-type branch follows from this inequality alone.

## Four true original cocliques meeting pairwise in eight

Any family as above of M≥20 cocliques contains a four-clique in its intersection-eight graph. With d_x=#members through graph point x, Cauchy (Σd_x)^2≤99Σd_x² yields mean degree at least (5M−27)/9>8. Choose C with at least nine neighbors. Four pairwise nonadjacent neighbors would cut four 8-subsets out of C with pairwise intersections at most one. Their union has size ≥32−6=26>22, impossible. Thus the neighborhood graph has independence number ≤3. If nine of its vertices induced a triangle-free graph, all degrees would be ≤3; odd order forces some degree ≤2. Its six or more nonneighbors contain a triangle or an independent triple (R(3,3)=6); the former is impossible and the latter with the chosen vertex is an independent four. Therefore a triangle exists among the neighbors of C, giving four actual pairwise intersection-eight cocliques in the original family. By the [previously proved three-coclique theorem](hoffman-triple-eight.md) every triple intersection in this four-set has size 3 or 4.
