# Six layers are necessary to evade all dyadic lengths through 16

**Theorem.** There is an infinite family of connected cubic bipartite regular cyclic covers of \(K_{3,3}\) whose shortest power-of-two cycle has length \(32\). Each has a specified free cyclic action with six vertex orbits. Consequently the largest integer \(k\) for which minimum degree three and some free abelian action with at most \(k\) vertex orbits force a cycle of length \(4,8,\) or \(16\) is **exactly five**, combining this construction with the [five-orbit theorem](FactorErdosGyarfasAbelianFiveOrbits.md).

The result is sharp for this uniform \(16\)-cutoff, not an assertion about all graphs with six orbits, and not a counterexample to the unrestricted Erdős–Gyárfás conjecture (our graphs have a 32-cycle). The new obstruction is that \(K_{3,3}\) admits no edge-neutral cyclically nonbacktracking walk of length \(4,8,\) or \(16\). This is about individual lengths rather than the usual abelian girth. For the standard voltage and neutral-walk method, see [Exoo](https://www.combinatorics.org/ojs/index.php/eljc/article/download/v11i1n2/pdf) on abelian voltage lifts and [the article on cubic graphs with solvable automorphism groups](https://doi.org/10.1016/j.ejc.2014.10.008) on structural questions for abelian covers of \(K_{3,3}\).

## 1. No neutral cyclically nonbacktracking walks of lengths 4, 8, 16

An edge-neutral walk uses each edge equally often in both directions. Let \(W\) be a nonempty cyclically nonbacktracking closed walk. Its connected support has minimum degree at least two: a visit to a degree-one support vertex would force an immediate reversal, including at the cyclic join. If the support is a cycle, \(W\) follows one direction around it, so it is not neutral. If \(W\) is neutral and has length \(2h\), each support edge is used at least twice, so the support has at most \(h\) edges.

At length 4 or 8, this only allows a cycle as support (or no such support). At length 16 write \(e\) for the number of support edges. For \(e\le5\) there is again only a cycle: the support bipartition either has both sides of size two or has a side of size at least three, in which case it has at least six edges. The remaining cases are as follows.

**Six edges.** A six-vertex support is 2-regular, hence a cycle. A five-vertex support with six edges must be \(K_{2,3}\), a theta with three arms of length two. Degree-two vertices force a whole traversal of an arm. Thus \(W\) would consist of eight arm traversals, alternating direction between the two branch vertices. Neutrality means that each arm appears an even number of times, with equal counts in the two parities. At least one arm appears four or more times; cyclic nonbacktracking allows at most four appearances, and four necessarily occupy the four places of one parity. This contradicts balance.

**Seven edges.** All six vertices must be used. The two degree-three vertices are joined by a theta, with all other vertices of degree two: after suppressing degree-two vertices the only other connected possibility is an edge connecting two loops, which would require two vertex-disjoint cycles of length at least four. Neutrality gives each support edge once in each direction and exactly one additional pair of opposite traversals, on a single edge. Since traversal is constant along an arm, the edge with the extra pair is an arm of length one. The other arms traverse once each way. The total is now eight arm letters (four from the short arm, two from each other arm), and the short arm again cannot occupy both parities.

**Eight edges.** Each support edge is used exactly once each way. Every layer has degree at least two, with two vertices of degree two and four of degree three. Write \(\tau\) for reversal on the 16 directed edges. The walk induces, at each vertex, a permutation from its outgoing arrows (view them first as reversed arrivals) to the outgoing arrows that the walk follows. With no immediate reversal these are derangements: at degree two a transposition, and at degree three a 3-cycle. The successor permutation of the walk on all directed edges is their product after \(\tau\). Its sign is \(+1\), since \(\tau\) and the product of the local derangements are both even. But a single 16-step walk using each directed edge once would make this permutation a 16-cycle, of sign \(-1\). This is impossible.

Thus no \(W\) of length \(4,8,\) or \(16\) is edge-neutral.

## 2. The infinite cyclic covers

Label the base parts \(0,1,2\) and \(3,4,5\). Give the edges \(03,04,05,13,23\) shift zero, and give \(14,15,24,25\) the four independent standard basis vectors in \(\mathbb Z^4\), oriented from the first part to the second. Reverse the signs in the opposite direction. This is a spanning-tree normalization. A closed walk has formal total shift zero precisely when it is edge-neutral: the four cotree nets must then be zero, and the remaining net flow on a tree is identically zero by conservation at each vertex.

Any simple cycle of a lift projects to a cyclically nonbacktracking closed walk, since a reversed matching immediately revisits the preceding lifted vertex. Hence there are no 4-, 8- or 16-cycles in the formal cover. To get a formal 32-cycle, restrict to the three two-edge paths from 0 to 1 through \(3,4,5\). Their shifts are \(0,-e_1,-e_2\), where \(e_1,e_2\) are the first two standard generators. Suppressing the middle layers in this subgraph gives the two-layer three-matching graph. The word
\[
                         0101012010201212
\]
on the three paths, starting at 0 and alternating direction, lifts to the simple 16-cycle from the [two-orbit theorem](FactorErdosGyarfasAbelianTwoOrbits.md) with its independent formal labels. Restoring the distinct middle vertices doubles the length to 32. The companion verifier also checks this 32-step word directly.

For finite cyclic examples choose any positive integer
\[
               M>32(1+65+65^2+65^3)
\]
and evaluate the four shifts at \(1,65,65^2,65^3\) in \(\mathbb Z/M\). A vector tested for any walk of length at most 32, or for collisions of its partial shifts, has all coefficients in \([-32,32]\). If such a vector is nonzero, its highest nonzero digit dominates the lower ones in base 65; its nonzero integer value has absolute value smaller than \(M\). Thus the nonclosure of all projected walks at lengths \(4,8,16\) and the formal simple 32-cycle both persist. The first cotree generator gives a loop of shift 1 based at layer 0, so the lift is connected. Each layer has degree three, and the translation action is free with precisely these six layers as its orbits.

For a much smaller explicit example (abelian rather than cyclic deck group), evaluate the standard basis in \((\mathbb Z/5)^4\). The checker verifies the required short-walk and 32-cycle nonvanishing directly in this group, yielding a connected graph with 3750 vertices.

Run [the companion verifier](verify_factor_erdos_gyarfas_six_orbit_barrier.py) with standard-library Python. In addition to checking the 32-cycle, it independently visits all \(72,648,133128\) rooted directed cyclically nonbacktracking base walks of lengths \(4,8,16\), and verifies the formal and mod-5 exclusions; the no-neutral-walk proof above does not rely on that enumeration.
