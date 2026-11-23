# Five signed norm-sixteen supports, and 466 height-two overlays

On the two eight-element shores P,N of a norm-16 marking let M be the 8-by-8 crossing adjacency, with P indexing rows. Each shore is independent and M is 4-regular. The [zero-star and deficiency theorem](../n16-zero-star-forest.md) shows MM^t=2I+2J−D, where D is a 2-regular multigraph on P; the analogous graph on N has the same cycle deck. Its only possible decks are C8, C6+2, C4+C4, C4+2+2, four doubles (2 denotes a pair joined by two parallel deficiency edges). That prior theorem does not identify the crossing matrix on the first four decks. The [four-cube theorem](norm16-edge-and-cube.md) identifies the last deck and two of its exterior portraits.

**New classification.** Each deck determines exactly one bipartite signed support up to independent relabelings of the two shores, without exchanging them. In a canonical consecutive cyclic order on P, the following are representatives; an integer w is the mask of the P neighbors of one N vertex (bit i corresponds to row i, 0≤i≤7).

| D | eight column masks | labeled row / unlabeled column models | order of shore-preserving group |
|---|---|---:|---:|
|8|53,77,83,106,154,166,169,212|2|8|
|6+2|85,90,102,105,141,147,170,180|4|6|
|4+4|58,86,89,101,149,163,172,202|4|32|
|4+2+2|86,89,101,106,149,154,163,172|4|16|
|four 2|85,90,102,105,150,153,165,170|2|192|

Fix D and expose M one row at a time. At stage i a multiset of i-bit column prefixes, with multiplicities m_w, records all prior information up to column permutation. For the next row choose 0≤k_w≤m_w to receive a one. Impose Σk_w=4 and Σ_{w_j=1}k_w=2−D_{ij} for each earlier row j. Split each prefix into its two children and reject a required column weight >4 or unattainable weight 4. At depth eight discard any two columns with more than two common rows. This lists each possible column multiset exactly once since prefixes can be recovered by truncation. Enumerate the row permutations preserving D and take their genuine action on these multisets. In all five cases there is a single orbit; stabilizers are as above. These are abstract relabelings only. Conversely an induced bipartite 4-regular support on 8+8 in an actual Conway graph always gives a true neutral norm16 field: assigning its signs and extending by zero attains the minimum adjacency Rayleigh quotient −4.

One reason these tables are small: for signed rows a_i=2M_i−1, the row Gram is 4(2I−D). Summing any nonempty proper consecutive interval of a single simple cycle has squared norm 8 (two crossing edges). Its entries sum to zero, and all eight entries have parity the interval length. An even interval therefore equals 2(e_p−e_q) for two distinct column sites, and an odd interval has eight signed-unit entries.

**The eight height-two words.** Let H consist of the eight exterior points of height two. Each such point selects a P pair and an N pair. The resulting P-pair multiset is the edge multiset of D, and the N-pair multiset is the edge multiset of the deficiency graph on N. Accordingly one only needs bijections of two eight-edge lists, identifying duplicates as unordered collections of contact words. Reject (i) a 2-by-2 selected crossing block which is not a partial matching: these four sites lie in a single neighborhood; (ii) a P,N pair already appearing in more than 2−M_pn words; (iii) two words sharing more than two sites. These are necessary even if H has an edge. Write K for the simple graph on H joining two words sharing exactly two signed sites; their Z-neighborhoods are disjoint, since their two common neighbors are exhausted.

In fact K is a linear forest, or is exactly C8. Each of the four signed sites in a word appears in precisely one further word, so K has maximum degree two. K has no triangles since three pairwise disjoint Z-neighborhoods of size at least four cannot fit in |Z|=11. It has no 4-cycle: each z can hit at most two cycle vertices, so sixteen incidences in eleven z sites force at least five double hits, whereas each opposite pair supplies at most two. For any cycle of length r in K, its words share all four contacts with their two cycle neighbors and share no signed contacts with other H. The r positive signed sites they contact therefore constitute whole components of D (both of their incident H occurrences are on the cycle), so r is even. If r=6, the two remaining words would have to share all four of their signed contacts, impossible. Thus any cycle has length eight. In that case let a_i count the positive contacts shared across consecutive cycle vertices. Then a_{i−1}+a_i=2, so either the a_i all equal one and D=C8 on both shores, or a_i alternates zero/two and both shores have four double edges. In either case H is edgeless: if ab were its edge, the [height-two edge theorem](norm16-edge-and-cube.md) allows exactly two of the six other words to meet W_a∪W_b in two sites, none more. The conflict neighbors of a and b are disjoint (a common one would meet their disjoint words in four sites), and supply four such words, a contradiction.

The checker applies K's necessary cycle restriction and takes orbits under the whole shore-preserving group of M. It does not assume an automorphism of the unknown graph extends any core relabeling. Columns are distinct since their weights are 4 and intersect in at most 2, so a row permutation preserving the column multiset induces a unique column permutation. The counts, **before attempting any exterior adjacency on H**:

|D|after (i)–(iii), labeled multisets|after cycle restriction|shore-preserving orbits|among these K=C8|
|---|---:|---:|---:|---:|
|8|1820|1820|243|4|
|6+2|681|681|118|0|
|4+4|2068|1984|77|0|
|4+2+2|326|324|26|0|
|four 2|90|72|2|2|

Thus there are 466 necessary height-two overlays at all ranks, 460 with a linear conflict forest and six with a conflict octagon. The four noncube octagon overlays are fixed by the order-eight shore-preserving stabilizer of their own core. In all six octagon cases the same eleven-site zero-neighborhood incidence rules apply; the known two-star rank36 calculation on *cube* old-site Gram matrices cannot be transferred to the four noncube overlays without a separate proof. Neither the core classification nor a passing overlay constructs a graph. Run the [standard-library checker](n16-five-shore-cores.py) directly with `python3 n16-five-shore-cores.py`.
