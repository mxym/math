# Eleven fibers from a pentagon cannot occur

**Theorem.** In an \(\operatorname{SRG}(99,14,1,2)\), there is no collection of eleven pairwise disjoint triangles indexed by the edges of \(K_6-P_5\), with no cross edges for intersecting indices and a perfect matching across each disjoint pair of indices. Here the removed edges are \(01,12,23,34\), and 5 is the remaining isolated index of the removed-edge graph. This does **not** assert that every choice of eleven \(K_6\)-edges is impossible.

In the good-prism pentagon construction of [the 13-fiber note](partial-k6.md), the base pentagon supplies ten such fibers. If even one of its five secondary prisms were good, the eleventh fiber leaves precisely a four-edge path removed from the abstract pentagon of prospective completions. The theorem therefore forces **all five secondary prisms of every good Berge pentagon to be bad**. In particular, [the rectangle charging bound](pentagon-rectangle-budget.md) gives \(5N_5\le32B+6R\le 44B\), since \(R\le2H\le2B\). The existence question and all four possible ranks remain open.

## 1. Matchings in the 33-site core

Write \(F=E(K_6)-\{01,12,23,34\}\). A perfect matching of \(K_6\) contained in \(F\) gives three fibers with mutually perfect cross matchings. The nine sites are a rook grid: each of the three sites of the third fiber contacts both other fibers and must use corresponding rung endpoints, as unmatched endpoints already have both common neighbors within the six-site prism. Thus the three cross matchings are compatible identifications of the ternary coordinates. Any outside vertex sees exactly one site of a grid: every pair in it already has its full graph common-neighbor quota internally, and its nine vertices send \(9(14-4)=90\) edges to the other 90 vertices.

There are six such triples among the eleven fibers. Encode each triple by a separate latent three-valued coordinate joined to its three fibers; this represents an identification of each of their coordinates with a shared coordinate. Retain six other disjoint-fiber pairs not in any completed triple as individual matching edges. The resulting connected incidence graph has 17 nodes and 24 edges. Permuting the three local labels at nodes makes the 16 matchings on any chosen spanning tree identity. The other eight matchings may be any of the \(6^8=1,679,616\) permutations. The code uses lexicographic edge order and its first connecting spanning tree. Simultaneous conjugation of all eight permutations is mere relabeling; no automorphism of a putative 99-vertex graph is assumed.

For present \(f,g\) sharing an abstract endpoint, every common disjoint present index \(h\) contributes the site permutation \(f\to h\to g\) to the core two-walk counts. In the ten pairs with three such intermediates the three permutations cannot agree on a site, since that produces three common neighbors. This removes core-infeasible assignments. The exact counts are 117,528 remaining labeled assignments and 20,416 conjugacy representatives. In computing conjugacy the first three generators are taken lexicographically minimal, then the tail is taken lexicographically minimal under the stabilizer of that prefix. The program additionally checks nonnegative residual common-neighbor quotas in each nonterminal core and in the terminal core.

## 2. All possible exterior contact words

A vertex outside the 33 sites meets at most one site of each triangle. Its fiber support must meet each of the six present perfect-matching triples exactly once. An exhaustive \(2^{11}\)-mask check gives exactly ten supports: the six ordinary words of present edges containing \(a\), and the four exceptional words of present edges disjoint from a missing edge \(e\). Each \(e\) has a complementary pair of disjoint present indices \(f,g\). Only the exceptional word for \(e\) sees both fibers. Across their nine site pairs, the three rung pairs have one common neighbor each and the six nonrung pairs have two each, for 15 total. The two fibers themselves consume twelve of these counts, there is no third core fiber disjoint from both, and any outside vertex sees at most one site of each fiber. Thus the corresponding exceptional population is three; its three contacts with either fiber are bijective, one on each rung. If \(f=ab\) is present, every site in it has two neighbors in its own fiber and one in each other present index disjoint from \(f\). Counting contacts from the 66 exterior vertices into the three sites gives \(p_a+p_b=18\), after accounting for the population 3 of each exceptional type disjoint from \(f\). Since the present index graph is connected and nonbipartite, every ordinary population is 9.

For each support, try every ternary choice of one site per fiber. Let \(A_C\) be the \(33\times33\) core adjacency matrix and \(z\) such a binary contact vector. The available common-neighbor quotas at distinct core pairs, and the remaining degree on its diagonal, are given by
\[
 B=12I+2J-A_C-A_C^2 .
\]
Discard a word if two of its sites have zero residual quota, or if \(z+zA_C\) exceeds 2 anywhere (two-walk counts between an exterior and a core site). A complete table of selected exterior words must have the above prescribed ten populations, the exact diagonal and pair totals of \(B\), and must cover each three distinct core sites together at most once. The last assertion is because two exterior vertices cannot have three common neighbors. In particular each literal word can be used at most once: all ten support types have size at least three. Within-fiber off-diagonal quotas are zero, and are satisfied automatically.

The binary requirements can be written \(Ax=b,\ Sx\le d,\ 0\le x\le1\), with \(A,S\) nonnegative zero-one (the letter \(A\) in this finite system is not the 99-vertex graph adjacency matrix). The checker performs unit/forced quota propagation and exhaustive binary splitting. For difficult nodes SciPy is used to **discover**, not certify, a separating inequality. Only if integer vectors \(y,z\) with \(z\le0\) satisfy
\[
    y^Tb+z^Td > \sum_j \max\!\bigl(0,(A^Ty+S^Tz)_j\bigr)
\]
is such a node rejected. These dot products and sums use Python arbitrary-precision integers. The inequality contradicts feasibility directly by substituting any \(x\in[0,1]^n\); the right side is the maximum over the unit cube. If the discovery routine reports a positive separation gap but no integer separator validates, the run aborts rather than claiming an exclusion. At a remaining fractional node, both binary choices are explored. Floating point may choose a branching variable, never a rejection. On the reference run 20,415 of the 20,416 complete orbit representatives have no contact table; exactly the explicitly reserved twist \((3,0,4,4,3,3,3,4)\) goes to the next stage. Permutations here are the zero-based lexicographic permutations of \((0,1,2)\).

## 3. The exceptional twist: exhaust all tables without presuming symmetry

The remaining 33-site core admits simultaneous cyclic rotation of its ternary coordinates. This fact alone says nothing about symmetries of a contact table or graph. We enumerate **all** possible tables on this core, not just invariant ones. The ten classes have respectively \(54,24,24,24,54,99;21,21,21,21\) available literal words.

1. **Exceptional triples.** In each exceptional class, distinguish its three members by the three sites on one specified complementary prism rung fiber. Try all triples, one literal word at each site. Retain the necessary rung-bijectivity at all complementary pairs, no repeated triple of common core sites, and no exceeded pair quota. The four catalogs have sizes \(298,79,79,298\); these are not symmetry quotients.

2. **Balanced anchor in each ordinary class.** At core fiber \(f\), put \(C_{fg}=2[f=g]+[f\cap g=\varnothing]\). This is the number of neighbors in fiber \(g\) of any site in \(f\). If \(h_i\) counts its exterior neighbors of one of the ten types \(i\), and \(W_i(g)\) is the \(0/1\) support function, then
\[
 \sum_i h_i=14-\sum_g C_{fg},\qquad
 \sum_i W_i(g)h_i+(C^2)_{fg}
 =\begin{cases}16,&g=f,\\ 5,&g\cap f=\varnothing,\\6,&\text{otherwise.}\end{cases}
\]
Also \(h_i=0\) if \(W_i(f)=0\). Enumerate the four exceptional counts in \(0,\ldots,3\). Every present edge \(ab\) then yields its ordinary pair sum \(h_a+h_b\); each index belongs to an abstract triangle of present edges, recovering \(2h_a\) from three pair sums. The checker tests all remaining equations. For each ordinary star \(a\) this proves that at each site of the selected anchor fiber exactly three neighbors come from \(a\). The choice of anchor is verified separately for each star; there is no assertion of general equitability.

3. **The ordinary nine-word layers.** In any fixed ordinary star, a pair of different incident fibers can be seen by no other ordinary class. Conditional on the exceptional triples, all pair margins on that star are therefore known: subtract the exceptional contributions from \(B\). An exceptional type meeting at most one of these fibers cannot affect this computation or share three sites with a word in the star. Partition the nine required words into three slices of three by the chosen anchor site. Try all triples of available words in each such slice, retaining those satisfying pair caps and the three-site rule. For a fixed selection of exceptional triples, the margins involving the anchor select the exact list for each slice. The other pair margins must be the sum of those of the three chosen slices; the code joins the first two slice lists against a lookup of the third, enforcing triple conflicts. The packed arithmetic for marginal lookup uses base 32; an ordinary nine-word total contributes at most nine to a digit and the four exceptional triples at most twelve, so valid digit sums never carry. The occurrence of the eight cyclically invariant tables in this join is an *output*, not an enforced constraint.

4. **Couple the six layers.** In the missing-edge order \(01,12,23,34\) numbered \(0,1,2,3\), the exceptional catalog indices affecting pair margins in the six ordinary layers are exactly \((1,2,3),(2),(0,3),(1),(0,1,2),(0,1,2,3)\). Accordingly one can first keep the 71 admissible middle catalog entries on each side and the 11,978 endpoint pairs with a nonempty center layer. For each ordered middle pair search the two other ordinary layers and finally the full star through abstract index 5. Sixty-seven middle pairs have both outer layers nonempty before the endpoint compatibility test. For every surviving combination the checker enumerates the Cartesian product of all six compatible ordinary layer lists, combines it with its four exceptional triples, and directly rechecks all contact populations, every residual diagonal/pair quota, and the triple rule. There are exactly **eight distinct complete contact tables**. As a check all eight happen to be invariant under simultaneous ternary rotation; this was never required.

5. **Exterior row veto.** For a selected exterior word \(w\), possible exterior neighbors must be other selected words \(v\) sharing at most one core site with it. Indeed, two adjacent vertices have only one common neighbor. If \(s_v\) are the binary adjacency choices then necessarily
\[
 \sum s_v=14-|w|,\qquad \sum s_v v=2\mathbf1-w-wA_C.
\]
In each of the eight tables, some \(w\) has no feasible binary row. These finite nonnegative equalities are tested by integer forced-column propagation and exhaustive binary splitting. No assumptions on reciprocity or exterior symmetry are required for this veto.

## Replay

Run [partial-k6-11.py](partial-k6-11.py) with assertions enabled. The common code checks the ten support types and the terminal census; the orbit pass asserts 117,528 valid raw assignments, 20,416 conjugacy representatives, exactly one terminal, and exactly 20,415 other rejections. The terminal pass asserts the catalog, incidence, and eight-row-veto counts above.

~~~sh
OPENBLAS_NUM_THREADS=1 OMP_NUM_THREADS=1 python partial-k6-11.py --stage orbits
OPENBLAS_NUM_THREADS=1 OMP_NUM_THREADS=1 python partial-k6-11.py --stage terminal
~~~

The reference environment is Python 3.12, NumPy 2.3.5, SciPy 1.17.0. The first stage takes about 2.5 minutes on a single thread and the terminal stage about 20 seconds; timing and the auxiliary branch/dual counts can vary. The terminal stage uses only NumPy and Python's standard library. Both stages together run by default. No data file, network fetch, randomness, assumed global automorphism, or external proof database is required.
