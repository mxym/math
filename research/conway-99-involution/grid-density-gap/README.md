# Every nine-vertex induced subgraph other than a rook grid has at most sixteen edges

Let G be a strongly regular graph with parameters (99,14,1,2). If nine vertices span more than sixteen edges, they induce the 3-by-3 rook graph with eighteen edges. In particular exactly seventeen edges cannot occur. This result is independent of the partner-regular-root calculation and requires no search, symmetry or coclique hypothesis.

For a nine-set S with e internal edges put v=(A−3I)1_S−1, where A is adjacency. The identity A²+A=12I+2J implies Av=−4v, hence sum(v)=0. With g=3I−A+J/9, g²=7g and v=−g 1_S, so

    ||v||² = 7(36−2e).

Therefore e≤18. Equality means v=0: every point of S has four neighbors inside, every point outside has one. All common neighbors of pairs in S are consequently inside, giving an SRG(9,4,1,2), uniquely the rook graph. For the uniqueness, use two matched axes at any root and label the four remaining vertices by sign pairs. The triangle rule at each axis neighbor forces the four sign-square edges.

Suppose e=17. Then v is integral, of squared norm 14. Write positive mass equal to negative mass, each at most 7 since ||v||₁≤||v||². An entry of magnitude two or more would require at least eight opposite neighbor mass by Av=−4v; impossible. Thus v has seven +1 entries P and seven −1 entries N. Each point of N has at least four neighbors in P, accounting for at least 7·binom(4,2)=42 shared-neighbor incidences for positive pairs. Since no two points have more than two common neighbors, 42=2·binom(7,2) is also the maximum. The same holds on the other side. Hence each sign side is independent (an adjacent pair would have only one common neighbor), the bipartite graph between signs is 4-regular, and no outside vertex sees two points of the same sign. By Av=−4v an outside vertex either sees one of each sign (call its class Y), or neither (T). Every point of T has all its neighbors in Y: indeed A1_{P∪N} is 4 on P∪N, 2 on Y, 0 on T, while A²1_{P∪N} is 28 on T. Thus there are no edges inside T.

For every vertex x we have

    deg_S(x) = 1 + 3[x∈S] + v(x).

Write r=|S∩N|, s=|S∩P|. Summing v on S gives 2e−36=−2, so s=r−2. No negative vertex outside S has even one neighbor in S. Thus any positive in S sees all four of its negative neighbors inside S. Every Y in S sees its unique negative neighbor inside also. The r marked negatives have three S-neighbors each; 4s of their incidences go to marked positives, all others to marked Y. Hence |S∩Y|=3r−4s=8−r. It follows |S∩T|=3−r, so r≤3. If s were positive its four negative neighbors in S would force r≥4. Therefore S contains exactly two negatives, no positives, six Y and one point t∈T.

Each of the two negatives sees three of the six Y, partitioning them into two triples X and Z by the unique negative neighbor. Since t has four S-neighbors, all Y, and shares at most two neighbors with each of the two negatives, t sees precisely two points of each triple. Induced edges in either triple form a matching because all three have a common negative neighbor, whose own neighborhood is a matching. Every Y in S has degree four inside S, and sees at most two vertices in the other triple by comparison with that triple's negative center. In either triple, its point not joined to t must therefore have an internal neighbor. Number this non-t point 0, its internal mate 1, and the other t-neighbor 2. The degrees across the triples are necessarily (2,1,2) in that order.

The two 0s must be joined: otherwise X₀ sees both t-neighbors of Z as well as its own mate X₁, giving it three common neighbors with t. Each 2 must see the opposite 0: the two cross neighbors of X₂ cannot both be t-neighbors, as the neighborhood of t itself is a matching. Thus three cross edges are X₀Z₀, X₂Z₀, X₀Z₂. The remaining cross deficits force a perfect matching between {X₁,X₂} and {Z₁,Z₂}. If X₂Z₂ is used, X₂ and X₀ share Z₀,Z₂ and their negative center. Otherwise X₁Z₂ is used, and this adjacent pair shares t and X₀. Both options contradict the SRG pair counts. This rules out e=17.

The previous rooted 4-cell gap follows immediately by adjoining the root and the four signed parents: such a 9-set has 14+m edges when m of the six possible edges among its four labels are present. This does not state whether any rook grid occurs.

The analytical proof is complete without computation. [Optional terminal-case audit](unrooted.py): run `python3 unrooted.py`; expected surviving cases: `0`.
