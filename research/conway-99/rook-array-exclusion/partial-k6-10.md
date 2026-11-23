# No Berge pentagon of good prism mates in a Conway 99-graph

**Theorem.** An \(\operatorname{SRG}(99,14,1,2)\) cannot contain ten pairwise disjoint triangular fibers indexed by the edges of \(K_6-C_5\) such that disjoint index pairs carry a perfect matching between the two triangles and intersecting index pairs carry no edges. Consequently its good-prism parallel-block incidence graph has **no cycle of length ten**.

Indeed, a Berge pentagon comprises five distinct graph triangles \(T_i\) and five distinct grid-parallel blocks, one per consecutive pair. Within each block, let \(U_i\) denote its third line. The ten distinct triangle marks have the \(K_6-C_5\) pattern by the explicit Gram calculation in [the thirteen-fiber argument](partial-k6.md#a-global-consequence-for-pentagons-of-good-prisms): one labeling is \(T=(12,34,15,23,45)\), \(U=(56,26,46,16,36)\). An inner product \(1\) is disjoint anticompleteness, and \(-2\) is a disjoint prism. The finite exclusion below assumes **only** the ten labeled triangles and their stated adjacency pattern. In particular it never assumes that a secondary prism is bad, or that any graph automorphism exists. No lower bound on the number of pentagons is asserted, and the full existence problem remains open.

## Core assignments and their coverage

Index the missing abstract edges as \(01,12,23,34,40\); the sixth abstract point is 5. Among the ten present index edges, each of five completed perfect matchings gives a nine-site rook grid. As in [the eleven-fiber proof](partial-k6-11.md), its three cross matchings are consistent ternary identifications: a site seeing both of two prism fibers must select matched rung endpoints. A vertex outside a rook grid sees precisely one of its nine sites, since all grid pairs have their common-neighbor quotas saturated and the nine sites send 90 edges to the remaining 90 vertices.

Represent each completed triple by a latent ternary coordinate identifying its three fiber labels. Retain the five remaining disjoint fiber pairs as individual ternary matchings. The connected graph of identifications has 15 nodes and 20 edges. Fixing the tree matchings to the identity leaves six independent \(S_3\) permutations. All \(6^6=46,656\) possibilities are thereby covered. For a pair of anticomplete fibers with three intermediate fibers matching both, the three induced site permutations cannot agree at any site, since that would give three common neighbors. Exactly 8,606 assignments pass these guards; simultaneous conjugation reduces them to 1,567.

There is a further relabeling by the dihedral group of the removed abstract 5-cycle. To apply a relabeling, map each fiber and each latent triple node to its image, transfer each edge permutation (inverting if its recorded orientation reverses), and regauge along the fixed tree. Explicitly, if \(p_i\) is the product carrying the root coordinate to node \(i\) on the relabeled tree, then the normalized matching on \(ij\) is \(p_j^{-1}m_{ij}p_i\). Its value on each tree edge is rechecked to be the identity. Take the least simultaneous conjugate and then the least over these ten relabelings. The checker verifies that every canonical key is the minimum member of its actual bucket and that the claimed orbit sizes match all bucket members. This gives 185 representatives: three of size 1, two of size 2, 48 of size 5, and 132 of size 10 (with these sizes taken among the 1,567 simultaneous-conjugacy representatives). This is a choice of coordinates only.

## Exact contact tables

A vertex outside the 30-site core touches at most one site per graph triangle. It must touch exactly one in each of the five core grids. Testing all \(2^{10}\) fiber-support masks leaves precisely the six ordinary stars of present edges through an abstract point and the five exceptional supports of present edges disjoint from one missing abstract edge. Each exceptional type has population 3. For its missing edge \(e\), there is one pair of disjoint present indices complementary to \(e\); only this type meets both. The six nonrung site pairs of that prism consume twelve common-neighbor slots in its own fibers, while the three rung slots require exactly three outside witnesses, one per rung. Each ordinary class has population 9: count contacts on present edge \(ab\) to get \(p_a+p_b=18\) after accounting for the exceptional threes; the present index graph is connected and nonbipartite. This totals \(6\cdot9+5\cdot3=69\) exterior sites.

Let \(A_C\) be the \(30\times30\) core adjacency matrix. Try every literal ternary choice \(w\) of sites on each allowed support. It must satisfy \(w+wA_C\le2\) coordinatewise, and may not use a site pair with zero residual common-neighbor quota. For the selected words, the matrix of total outer incidences, counting a diagonal entry for each contact and an off-diagonal entry for each simultaneous pair, is
\[
 B=12I+2J-A_C-A_C^2.
\]
No two selected words may share three sites. In particular each possible literal word is binary (selected once or absent): every allowed support has at least three contacts.

**Exceptional catalogs.** Each exceptional word meets four fibers. Its three words are identified one per rung of its complementary present prism; try all triples with these distinct rung labels. This covers at most \(9^3=729\) tables per exceptional class because each word has two further ternary coordinates. Retain pair/triple quota compatibility. No restriction is imposed on edges between the three exterior sites themselves.

**The five noncentral ordinary layers.** A noncentral ordinary star has three present incident fibers. In any pair of these fibers, it is the only ordinary type that can contact both. Once the exceptional tables are fixed, its exact pair margins are therefore obtained by subtracting their contributions from \(B\). Number the exceptional classes as the five missing edges in the order above. The sets contributing to the pair margins of ordinary types 0,1,2,3,4 are respectively
\[
       (1,3),\ (2,4),\ (0,3),\ (1,4),\ (0,2).
\]
An exceptional class intersects a noncentral ordinary support in at most two fibers, so a triple conflict between those two classes is impossible. Thus two exceptional triples with the same contributing pair projection can be grouped when computing local compatibility; their distinct global choices are retained.

For any of these five ordinary stars there is a specified balancing anchor at which each of the three sites meets exactly three members of the class. For the central ordinary star 5, each site's allowed count at its anchor is in \(1,2,3,4\). These are verified by the core-site two-walk equations from [the eleven-fiber proof](partial-k6-11.md#3-the-exceptional-twist-exhaust-all-tables-without-presuming-symmetry): enumerate the five exceptional neighbor counts in \(0,\ldots,3\), recover ordinary pair sums and use three present edges at the chosen abstract point to recover twice its count. All remaining equalities, the total degree, and the zero-incidence pattern are checked. A separate verification is made for each anchor; the 69 exterior vertices are not presumed equitable.

For ordinary type \(i\) partition its nine words by the site of the anchor fiber. At every anchor site enumerate all subsets of available words of the allowed size(s), with the pair and triple caps. The exact margins involving the anchor select the available slices. Join the first two chosen slices to a lookup of the third on all remaining pair margins, checking three-common-site conflicts across slices. The five local compatibility relations of the noncentral stars form a cycle on the exceptional catalog indices, so all compatible five-tuples can be listed by following that cycle. Their total across 185 cores before imposing the central layer is **175,776,281**. The dynamic count of these cycles uses signed 64-bit integers, safely since \(729^5<2^{63}\) and every count is nonnegative and bounded by that product.

**Central layer and final checks.** The remaining ordinary star meets five fibers, so may depend on all five exceptional tables. Its slice join permits all four anchor sizes, and excludes each ordinary word sharing three sites with any selected exceptional word. Partial sums above pair quota are safely rejected: all other contributions are nonnegative. The pair-margin lookup uses base 32 (a nine-word contribution to a digit is at most 9, the five triples together at most 15). For every surviving five-tuple and each central solution, try the full Cartesian product of the five noncentral solution lists. The final code of 69 distinct words is retested directly on \(B\), the eleven class populations, and every three-common-site restriction. There are exactly **27,861** distinct literal contact tables across the 185 representatives, with no assumption of any table symmetry.

| Zero-based dihedral core | Full tables | Fail an individual integral exterior row | Reach reciprocal-row test |
|---:|---:|---:|---:|
| 14 | 153 | 153 | 0 |
| 32 | 64 | 64 | 0 |
| 49 | 207 | 207 | 0 |
| 53 | 27,395 | 27,385 | 10 |
| 109 | 2 | 2 | 0 |
| 112 | 3 | 3 | 0 |
| 116 | 2 | 2 | 0 |
| 118 | 34 | 34 | 0 |
| 149 | 1 | 1 | 0 |
| Other 176 cores | 0 | 0 | 0 |

## Exterior rows

Fix any selected word \(w_i\). If \(S_i\) is its subset of exterior neighbors, necessarily
\[
 |S_i|=14-|w_i|,\qquad \sum_{j\in S_i} w_j=2\mathbf1-w_i-w_i A_C .
\]
A possible neighbor \(j\ne i\) shares at most one core site with \(i\). If they share \(x\) and either word already has another contact adjacent to \(x\) in the core, they cannot be adjacent: their edge to \(x\) already has its triangle cap. Two members of \(S_i\) cannot share two core sites, since \(i\) would be a third common neighbor. Finally the members of \(S_i\) having no core site in common with \(i\) must admit a perfect matching into pairs with disjoint core contacts. Indeed each such edge from \(i\) needs an exterior triangle cap, and an exterior triangle's three words pairwise have no common core point. This matching test is necessary, not sufficient. (Equivalently the exterior edges include 105 with their cap in the core, and 258 in 86 exterior triangles; these totals are not needed by the search.)

At each root, integer quota propagation forces absent and present candidates; remaining binary choices are explicitly split. The first pass may stop at a single valid row for a given root, but a veto means it exhausts all choices for that root. **27,851** tables fail this test. For each of the ten surviving tables in core 53, explicitly enumerate **every** admissible row at every vertex. There is no cap on row-domain size or branching. Domains have sizes between 1 and 16. For \(i\ne j\) require both reciprocity and the exact exterior pair-common-neighbor quota:
\[
                 [j\in S_i]=[i\in S_j],\qquad
 |S_i\cap S_j|=2-[j\in S_i]-|w_i\cap w_j|.
\]
Choose a smallest remaining row domain and, for each of its members, restrict every other domain to these exact compatible choices. Every one of the ten tables is rejected at the first branching node: a forced row leaves another domain empty. That completes the ten-fiber exclusion. If a full compatible assignment ever appeared the code would reconstruct the 99-vertex adjacency relation and directly test all 4,851 distinct pairs rather than discarding it.

## Replay

[partial-k6-10.py](partial-k6-10.py) needs Python and NumPy only. The reference run used Python 3.12.14 and NumPy 2.3.5. No LP, MILP, SAT solver, floating-point inequality, external certificate database, global graph symmetry, or time/node cutoff is used. Run without Python `-O`; all numeric counters and support assertions are part of the replay. A complete pass takes several minutes on one core, usually dominated by dihedral representatives 49 and 53.

~~~sh
OPENBLAS_NUM_THREADS=1 OMP_NUM_THREADS=1 python partial-k6-10.py
# Independent deterministic slices of the same 185 representatives, if desired:
OPENBLAS_NUM_THREADS=1 OMP_NUM_THREADS=1 python partial-k6-10.py --shards 2 --shard 0
OPENBLAS_NUM_THREADS=1 OMP_NUM_THREADS=1 python partial-k6-10.py --shards 2 --shard 1
# Or the only core reaching the reciprocal-row test:
python partial-k6-10.py --case 53
~~~

The full-run assertions require the entire 185-core cover, 175,776,281 local cycles, 27,861 complete tables, 27,851 individual row vetoes, and ten reciprocal vetoes. These are counts of the specified configurations in the finite proof, **not** counts of candidate 99-vertex graphs.
