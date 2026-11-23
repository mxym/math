# A fifteen-overlap Hoffman pair gives exactly 3,780 nominal norm-18 vacancies

Let a collection of M true Hoffman 22-cocliques be pairwise compatible (pair intersections congruent to 1 modulo 7). For a coclique C let E(C) consist of ordered seeds (o,Q) in which o lies outside C, Q is four mutually nonadjacent neighbors of o and |Q∩C|≥3. At any rank, a 15-overlap pair C,D has **exactly 686 common** such seeds and hence 3,780 in its union. Moreover that union is disjoint from E(B) for all other cocliques B in the collection. Thus a Fano in the original zero class need not be excluded in the many-Hoffman vacancy bound.

Indeed each outsider o has four neighbors in C occupying four different pairs of the seven-edge matching on N(o). There are 29 admissible Q (one containing all four; choose the three retained in 4 ways and the remaining non-C site in 7 ways). Thus |E(C)|=77·29=2,233. If |C∩B|=1 their seed sets are disjoint: each would require at least three of the same four sites, including at least two common sites.

For |C∩D|=15 let Y=C∩D, P=C∖D and Z=D∖C, and O the 70 points outside C∪D. Each y∈Y has all 14 neighbors in O, each pair from Y has both common neighbors there; writing h(o)=|N(o)∩Y| gives Σh=210, Σbinom(h,2)=210 and hence Σ(h−3)²=0. So every o∈O has three shared neighbors and exactly one neighbor x in P and y in Z. No shared site can be adjacent to x or y by coclique independence. Every common seed center is in O. Eight choices for Q contain the three shared neighbors, since their three matching edges leave four unused pairs in N(o). The remaining choices must use exactly two shared neighbors and both x,y, giving three if x,y are nonadjacent and zero if adjacent. The P-Z graph has 28 edges: every point of P has four neighbors in D, none in Y. Each such edge has exactly one cap; that cap cannot belong to C or D by independence, and each o∈O caps at most one P-Z edge because it has exactly one contact from each. Thus the exact number shared is 70·8+(70−28)·3=686.

By the [Fano endpoint intersection table](../../marked-coset-shells/README.md) every third Hoffman coclique has unordered intersections with C,D from `{(1,1),(0,2),(3,6),(6,10),(9,14),(4,5),(7,9)}`. Compatibility of all three leaves only (1,1). In particular the 15-overlaps are a matching, and no seeds from a pair are covered by another member of the collection. This argument does not assume automorphisms or the absence of Fanos.

Write p for the number of 15-overlap pairs and m=M−2p. For remaining unpaired members every pair intersects in 1 or 8, and a pair meeting in eight has at most 234 common seeds by the [many-Hoffman count](hoffman-vacant-n18-seeds.md). Thus the full union E satisfies
```
E ≥ 3780p + ceil(2233² m / (2233+234(m−1)))     (remaining term 0 for m=0).
```
Alternatively its total pair-collision count is ≤686p+234 binom(m,2)≤234 binom(M,2) whenever M≥3, since for p>0, 2M−2p−1≥3 and 3·234≥686. By Cauchy, the earlier lower bound `E≥ceil(2233² M/(2233+234(M−1)))` therefore holds unchanged.

For the graph-wide norm-18 application use M **original zero-class** cocliques, which are compatible with every neutral field. If U226=0 then every norm-18 field is orthogonal to each such coclique, so its positive-root negative-parent seeds miss E by the [many-Hoffman argument](hoffman-vacant-n18-seeds.md). If N16=U127=0 every seed carries at most six fields, giving `9N18 ≤ 6(55440−E)` for the true antipodally oriented graph population. The seed-union count itself does not assume any shell vanishes. Pairwise compatibility of a different collection alone does not establish orthogonality to all graph norm-18 fields.

See also the [soft bound on actual norm-18 flags](hoffman-soft-vacancy.md), which allows all three exception shells to be present.
