# Power-of-two cycles for abelian actions with at most two orbits

A group action on vertices is **free** (semiregular) if no nonidentity element fixes a vertex. We prove:

**Theorem.** Let \(X\) be a finite simple graph of minimum degree at least 3. If \(X\) has a free action by an abelian group on at most two vertex orbits, then every vertex is in a cycle of length \(4,\ 8\), or \(16\). The bound \(16\) is best possible. This includes arbitrary two-layer abelian bi-Cayley graphs, without assuming vertex transitivity of the full graph, as well as Cayley graphs of groups with an abelian index-two subgroup.

There is no corresponding universal bound for a **prescribed edge**. In a connected family satisfying the theorem, the exact shortest power-of-two cycle containing a designated edge has length \(2^{\lceil\log_2(2m)\rceil}\), for every \(m\ge3\). The graphs in this family have \(4m\) vertices.

These are special graph classes, not a proof of the Erdős–Gyárfás conjecture for all graphs of minimum degree 3.

## 1. Three translation matchings

Let \(A\) be an abelian group, written additively. Consider the bipartite graph on \(A_0\sqcup A_1\) with the three matchings \(z_0\sim(z+s)_1\), for \(s\) in a set \(S=\{a,b,c\}\) of distinct labels. Starting in \(A_0\), a word of even length \(s_1\cdots s_{2r}\) lifts to a closed walk precisely if \(s_1-s_2+\cdots-s_{2r}=0\). It is simple exactly when the partial coordinates before closing are distinct within each vertex layer. Translating all three labels by the same element merely changes the origin in \(A_1\).

The exact short-cycle criteria for this three-matching graph are as follows. A relation in the table can use any permutation of the three labels.

| Cycle | Relations sufficient and necessary |
|:--|:--|
| 4 | \(2(a-b)=0\), or \(2a-b-c=0\) |
| 8, in the absence of a 4-cycle | \(4(a-b)=0,\ 4a-3b-c=0,\ 4a-2b-2c=0,\ 3(a-b)=0,\) or \(3a-2b-c=0\) |

For length 4 the only possible non-backtracking cyclic label multiplicities are \((2,2,0)\) and \((2,1,1)\). Repeated labels occur at equal parity, giving the displayed relations. Conversely alternating the first two labels in the first case, or using \(a b a c\) in the second, gives a simple 4-cycle because the labels are distinct and the relations ensure closure.

For length 8, consider a simple cycle, so adjacent labels including the wrap-around are distinct. A label appears at most four times. If it appears four times, those positions are all of the same parity, giving net signed counts of the form \((4,-4,0), (4,-3,-1)\), or \((4,-2,-2)\) up to sign and permutation. Otherwise the multiplicities are \((3,3,2)\). Two net counts are odd and the third is even; each is no larger in absolute value than its multiplicity. The only possibilities, up to sign and permutation, are \((3,-3,0), (3,-2,-1), (2,-1,-1)\), and \((1,-1,0)\). The last two are excluded by the absence of a 4-cycle and distinctness of labels.

To show sufficiency of every listed 8-relation, normalize \(a=0\), \(b=x\), \(c=y\), and assume no 4-cycle. We specify words in the symbols \(0,1,2\) standing for \(0,x,y\), respectively.
* \(4x=0\): label \(x\) has order 4 (order 2 gives a 4-cycle), so use \(01010101\).
* \(3x+y=0\): use \(01010102\). In each layer the partial coordinates are \(0,-x,-2x,-3x\); they are distinct since \(0,x,-3x\) are distinct and thus the order of \(x\) is at least 4.
* \(2(x+y)=0\): use \(01010202\). In each layer the partial coordinates are \(0,-x,-2x,-2x-y\). The only possible coincidences would force \(x=0,\ y=0,\ 2x=0,\ x+y=0,\) or \(2x+y=0\). The first four are excluded and the last gives \(2x=0\) using \(2(x+y)=0\).
* \(3x=0\): use \(01012102\). The element \(x\) has order 3, and \(y\notin\langle x\rangle\), since otherwise \(y=-x\) and there is a 4-cycle. The two partial-coordinate sets are \(\{0,-x,-2x,y\}\) and \(\{0,-x,y-2x,y\}\), both of size four.
* \(2x+y=0\): use \(02020121\). The partial-coordinate sets, written in multiples of \(x\), are \(\{0,2,4,3\}\) and \(\{0,2,4,1\}\). Distinctness of the labels excludes order 1, 2 or 3; order 4 gives a 4-cycle since \(y=-2x\) then has order 2. Hence both sets have four distinct values.

If the graph has neither a 4- nor an 8-cycle, use the word \(0101012010201212\). Its alternating sum is identically zero. In the formal basis \(x,y\), the two parity lists of partial coordinates are
\[
 \begin{aligned}
 &(0,-x,-2x,-3x,-3x+y,-2x+y,-2x+2y,-x+y),\\
 &(0,-x,-2x,-3x+y,-2x+y,-2x+2y,-x+2y,y).
 \end{aligned}
\]
The possible within-layer differences, up to sign, are exactly the following coefficient pairs:
\[
 (0,1),(0,2),(1,-1),(1,-2),(1,0),(1,1),(1,2),
 (2,-1),(2,-2),(2,0),(2,1),(3,-1),(3,0).
\]
A vanishing difference in this list implies equality of labels, one of the 4-relations, or one of the 8-relations above. Hence the word is a simple 16-cycle. This also proves that the exact shortest power-of-two length in the three-matching graph is determined by the table (and is 16 when neither row applies). For example, for \(A=(\mathbb Z/5)^2\), \(S=\{0,(1,0),(0,1)\}\), none of the tabulated relations holds, so the shortest is 16.

## 2. General two-orbit graphs

Freeness identifies each orbit with a copy of \(A\), whose translations preserve the graph. Thus the cross edges are the union of translation matchings; within each orbit the edges have a symmetric set of nonzero steps.

If there are at least three cross matchings, take any three and apply Section 1. The cycle visits both orbits and its translates cover each vertex. If there are one or two cross matchings, each orbit must have internal edges by minimum degree 3. Choose a cross matching and translate coordinates so it is \(z_0\sim z_1\). Choose one nonzero internal step \(x\) in orbit 0 and one \(y\) in orbit 1. When \(y=\pm x\), the two common step edges and two cross edges form a square. Otherwise the cycle
\[
 0_0,\ x_0,\ x_1,\ (x+y)_1,\ (x+y)_0,\ y_0,\ y_1,\ 0_1,\ 0_0
\]
is simple: the only way that two of \(0,x,y,x+y\) coincide is \(x=0,\ y=0,\) or \(y=\pm x\). Its translates again cover both orbits. Finally, if there is just one orbit or there are no cross edges, the internal degree in each orbit is at least 3. Pick steps \(x,y\) with \(y\ne\pm x\); the commuting square on \(0,x,x+y,y\) covers each orbit under translation. This proves the theorem, including the vertex-wise guarantee.

## 3. The prescribed-edge obstruction

Take \(m\ge3\), \(A=\mathbb Z/m\times\mathbb Z/2\), and the three matchings with labels \(0,\ (1,0),\ (1,1)\). This graph is connected, since the label differences generate \(A\). It is the known split Praeger–Xu graph \(\operatorname{SPX}(m,1)\): the split pairs at each coordinate are the label-0 edges, and the directed complete bipartite connections between consecutive fibers give the other two matchings. The result here is its marked-edge spectrum, not the construction of that graph. All label-0 edges are equivalent by translation; fix one of them. The two other matchings form \(m\) separate copies of \(K_{2,2}\), the \(i\)-th consisting of the two vertices with coordinate \(i\) in layer 0 and the two with coordinate \(i+1\) in layer 1. Regard these copies as blocks on an \(m\)-cycle. The label-0 edges give two linking edges across each neighboring block pair. At each block the links to the two neighboring blocks use opposite layers.

For a simple cycle using the marked edge, if its projection uses only a proper interval of \(r\ge1\) links in the cyclic block arrangement, then each used link is crossed twice, as it is a cut in the interval and only two linking edges are available. At each middle block all four vertices each have one external edge of the cycle, so the cycle uses exactly two internal edges. At each terminal block the two external edges have endpoints in the same layer of its \(K_{2,2}\), and the only possible simple internal connecting path has length two. Thus the cycle has length \(4r+2\), not a power of two. The argument also covers a spanning interval omitting one link. A closed simple cycle using all \(m\) links has at least \(m\) external and \(m\) internal edges, because every visited vertex is incident to at most one external edge. It has length at least \(2m\).

Conversely choose one linking edge per link, including the marked one. Their two endpoints belonging to any given block lie on opposite sides of its \(K_{2,2}\), so one may connect them within that block by a simple path of length 1 or of length 3 independently. The resulting simple cycles through the marked edge attain every even length \(2m,2m+2,\dots,4m\), in particular the first power of two at least \(2m\). Combining the lower and upper establishes the claimed exact minimum. In fact the complete simple cycle-length spectrum through the marked edge is
\[
     \{4r+2:1\le r\le m-1\}\ \cup\ \{2m+2s:0\le s\le m\}.
\]
The first set is realized by choosing an interval of \(r\) links containing the marked one, using both external edges on each link, joining the two rails with length-two paths at the terminal blocks, and matching the two rails inside every middle block. No cycle using all links is outside the second set because the graph is bipartite and has \(4m\) vertices. If \(m\) is not a power of two, the smallest power of two through the marked edge is the largest power of two allowed by the order of the graph. The obstruction is local, not an absence of power-of-two cycles elsewhere.

## Related results and verification

* Ghaffari–Mostaghim, [Erdős–Gyárfás conjecture for some families of Cayley graphs](https://doi.org/10.1007/S00010-017-0518-3), Theorem 2.2, give the \(4/8/16\) guarantee for ordinary dihedral Cayley graphs. The three-label reasoning here is related, with the signed relations interpreted in an arbitrary abelian group and a necessary-and-sufficient short-cycle test. The arbitrary two-orbit graph theorem additionally allows unrelated internal step sets and graphs that are not Cayley graphs.
* Alspach–Muir, [Pancyclicity and Cayley graphs on generalized dihedral groups](https://intlpress.com/site/pub/files/_fulltext/journals/joc/2016/0007/0002/JOC-2016-0007-0002-a007.pdf), Theorem 3.1, give substantially stronger pancyclicity results for generalized dihedral Cayley graphs with internal steps. They separately discuss the all-linking case. The edge result in Section 3 is about the exact minimum at one color of edge, not applicable to their internal-step pancyclicity theorem.
* The split Praeger–Xu model is described in §2.4 of [On the number of fixed edges of automorphisms of vertex-transitive graphs of small valency](https://doi.org/10.1007/s10801-022-01176-5); the marked-edge minimum here follows from the explicit cycle spectrum.
* Burkhart, [Odd-ordered Cayley graphs satisfy Erdős–Gyárfás](https://arxiv.org/abs/2611.05060), concerns odd-order Cayley graphs and lifting through normal 2-subgroups. This note neither uses the odd-order theorem nor treats general Cayley graphs.
* [The companion exact checker](verify_factor_erdos_gyarfas_two_orbits.py) verifies the fixed word, enumerates three-matching short cycles independently of the relation test on small product groups, and tests the marked-edge formula on small members of the family. Finite checks supplement the proofs and are not Lean formalization.
