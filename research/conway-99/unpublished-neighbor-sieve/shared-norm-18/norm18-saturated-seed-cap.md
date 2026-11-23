# Saturated norm-18 root seeds: sharper capacity without norm 16 or unit (1,27)

Work in a hypothetical SRG(99,14,1,2). Assume **no neutral norm-16 field and no signed-unit charge-one cost-27 field**. There is no assumption on the Seidel rank, norm 20, or any other selected type. We count both orientations of neutral norm-eighteen fields.

**Theorem.** At any actual norm-eighteen seed, there are at most seven markings. If any two of the six pair-center labels at that seed are adjacent, there are at most six markings, and at most five when the only such edge joins labels with disjoint parent pairs. If at least three label edges occur, there are at most four markings. Consequently, the graph-wide oriented count satisfies \(N_{18}\le35,298\).

## Actual markings and omission pairs

Fix a positive root \(o\) and its four independent negative parents \(Q\), and let \(m\) be the number of actual oriented norm-eighteen markings at this seed. The six pair-center labels are the far vertices with two neighbours in \(Q\), one per pair of \(Q\). Every marking uses at least four labels as positives. For every marking choose any four of its labels. The chosen quartets are distinct: two markings using the same quartet would give a norm-sixteen difference by the [window theorem](exclusion.md). Their two-element complements form the edges of a simple graph \(L\) on the six labels. By the [star exclusion and nonstar unit transfer](norm18-dot8-nonstar.md), no three markings contain the same three labels under our hypotheses; equivalently \(L\) is triangle-free. Thus \(m\le9\), with equality only for \(K_{3,3}\).

Whenever two omission edges meet, the corresponding markings share at least three positive labels. Their same-root dot product can then be only eight: their initial overlap is at least eight, the [dot-nine panel theorem](panel-heights.md) excludes nine with three common pair labels, and dot ten would give norm sixteen. Their difference is unit, so there are no opposite signs, and they agree exactly in their four parents, root, and the three shared labels. In particular the two markings have **no shared private site**, meaning a support site outside the root, parents, and all six labels.

If a marking actually has just four positive labels, its four other positive sites besides \(o\) and those labels are satellites, each with **one** parent in \(Q\). Indeed its twelve non-root parent incidences include eight from the four centers; each of the four other positives has at most one remaining parent, so each has one. Its five private negative sites are far and have zero parents in \(Q\), because same-sign sites are independent and the only negative neighbours of \(o\) are \(Q\). These facts will be used only where every marking is proved to have exactly four positive labels.

A fixed label \(z\) has exactly two neighbours in \(N(o)\), its parents, and twelve far neighbours. Among those far neighbours there are exactly six incidences with \(Q\), counted with multiplicity: for each of its two parents \(q\), the edge \(zq\) has one common neighbour, and for each of the other two \(Q\)-sites the nonedge \(zq\) has two. All these common neighbours are far, because \(z\)'s two near neighbours are in the independent set \(Q\) and none is a mate of a \(Q\)-site. Therefore with no neighbouring label \(z\) has exactly six satellite neighbours and six zero-parent far neighbours. With exactly one neighbouring label, that label accounts for two incidences, so \(z\) has four satellites and seven zero-parent far neighbours.

## Eliminate eight or nine markings when labels are independent

Assume all six labels are independent and \(m\ge8\). A triangle-free graph on six vertices with at least eight edges is bipartite: a nonbipartite one has a chordless 5-cycle, and the sixth vertex can see at most two of that cycle's vertices without a triangle. Thus \(L\) is \(K_{3,3}\), \(K_{3,3}\) minus one edge, or \(K_{2,4}\). In all three cases every vertex has omission degree at least two. It follows that every marking uses exactly four labels: if it actually uses five, its sole omitted label lies on its chosen omission edge, and a different omission edge at that label supplies another marking's chosen quartet inside the five labels. This is forbidden by the window theorem. Using all six labels is excluded by the same theorem.

Consider any label \(z\) whose omission degree is at least three. A marking omitting \(z\) requires at least two private positive satellite neighbours at \(z\), to balance the two negative parents of \(z\) in its zero eigen-row. Other label vertices are independent from \(z\), so cannot supply any of the positive neighbours. All these \(z\)-omitting markings have pairwise intersecting omission edges; they cannot share a private satellite. Since \(z\) has just six satellite neighbours, omission degree four is impossible, ruling out \(K_{2,4}\). At degree three, all six satellites are used in the three omitting markings.

Fix any \(q\in Q\) that is not one of the two parents of a degree-three label \(z\). Then exactly two of its six satellites have parent \(q\), because the nonadjacent pair \(z,q\) has precisely two common neighbours and all labels are independent. A marking omitting \(z\) and \(l\) must have precisely as many private positive sites at \(q\) as omitted labels incident with \(q\): compare the four positive neighbours of the negative \(q\) with the one root and the selected label centres. Thus each of the two satellites at \(q\) must occur in a distinct marking whose other omitted label \(l\) contains that parent \(q\).

In \(K_{3,3}\) or \(K_{3,3}\) minus one edge, let \(U,V\) be the parts of size three and view their members as pairs on the four parents. Every \(q\) that has incidence degree at least two among the three labels of \(U\) has incidence degree at most one among the three labels of \(V\). Since each degree-three omission vertex \(z\in U\) has all three partners in \(V\) available, the preceding result forces every such \(q\) to be a parent of every degree-three label in \(U\). There are at least two degree-three labels in \(U\), and likewise in \(V\). Any three distinct edges of \(K_4\) form a triangle, a star or a path of three edges. The triangle has three vertices of degree two, too many for any one label. A path has two vertices of degree two, and only its middle edge contains both, not two edges. If \(U\) is a star, \(V\) is a triangle and fails in turn. This rules out the two remaining omission graphs.

## Eliminate seven or eight markings if a label edge exists

Suppose \(m\ge7\), and the labels \(a,b\) are adjacent. Their positive supports are independent, so every omission edge meets \(\{a,b\}\). If \(ab\) itself were in \(L\), triangle-freeness would allow at most one edge from \(a,b\) to each other label, hence at most five edges. Thus \(L\) is contained in \(K_{2,4}\) with \(a,b\) on the two-side. For \(m=7,8\) it is missing one or zero edges. In either case \(\{a,b\}\) is the unique two-vertex cover: any cover must contain each of \(a,b\), each of which is incident to at least three edges. Therefore \(ab\) is the only possible actual label adjacency.

Each marking uses exactly four labels. Indeed, a marking actually using five would have to omit one of \(a,b\) not to use their actual edge, and that single omitted label is incident to at least three omission edges. One of the other edges would provide another marking's chosen quartet in its own labels, forbidden by the window theorem. Six actual labels are immediately incompatible with the actual edge.

For \(m=7\) choose \(a\) to have omission degree three, and for \(m=8\) choose either endpoint (degree four). In either case four markings select \(a\), their omission edges all containing \(b\). They therefore have pairwise disjoint private negative supports. Each needs two distinct private negative neighbours of \(a\), besides its two parents. This would require eight distinct zero-parent far neighbours. But \(a\) has exactly one neighbouring label \(b\), so by the six-incidence count only seven zero-parent far neighbours exist. This contradicts \(m\ge7\).

## Eliminate six markings at the sole disjoint-parent edge

Assume exactly one actual label edge \(a b\), and that the two parent pairs of \(a,b\) are disjoint. Suppose \(m=6\). Every omission edge meets \(\{a,b\}\); as before \(a b\notin L\), so \(L\subset K_{2,4}\). Each of \(a,b\) has omission degree at least two since their degrees sum to six. A marking choosing five or six labels is impossible by the same argument as above: to choose five it must omit one of \(a,b\), and the omission degree of that label is at least two, giving a repeated four-label window. Thus all six are thin at this seed. If the two omission degrees are two and four, then the degree-two label is selected by four markings, whose omissions all contain the other label. Their disjoint private negatives would give eight distinct zero-parent far neighbours of that degree-two label, which has only seven because of its sole actual label adjacency. Therefore both omission degrees are three.

Take the three markings \(t_1,t_2,t_3\) omitting \(a\). Each selects \(b\), and they also all select the single label \(c\) among the four other labels that is never omitted with \(a\). Because \(a,b\)'s parent pairs partition \(Q\), the distinct label \(c\) shares exactly one parent \(p\) with \(b\). The only actual edge on all labels is \(a b\), so in particular \(c\) has no label adjacency. The \(t_i\) have pairwise dot eight and pairwise disjoint private supports, by the intersecting-omission rule.

Use \(d_x=(3I-A)e_x\), \(Y=Q\setminus\{p\}\), and form
\[
 w=t_1+t_2+t_3-d_b-d_c+\sum_{q\in Y}d_q .
\]
It is a true charge-one integral field. For \(z=1_Y-e_b-e_c\), its coordinate sum is 1, its squared norm is 5 and \(z^tAz=-4\) because each of \(b,c\) has exactly one parent in \(Y\), they are nonadjacent, and \(Y\) is independent. Hence \(D=3I-A\) gives \((Dz)^2=7(3\cdot5+4)+2=135\). For each \(i\), \(t_i\cdot Dz=7t_i\cdot z=-35\). Their sum has squared norm \(3\cdot18+6\cdot8=102\), so \(w^2=102+135-210=27\).

We now prove it is unit, contradicting \(U_{1,27}=0\). Its entries on \(o\), \(p\), and each \(q\in Y\) are respectively \(0,-1\), and the number (zero or one) of neighbours of \(q\) in \(\{b,c\}\). At \(b,c\) the entry is \(-1\). At \(a\) it is \(0+1-2=-1\), because \(a\) sees \(b\) and both parents of \(a\) lie in \(Y\). The three other label entries are \(2-|N(x)\cap Y|\), equal to zero or one. A private positive of these three markings is nonadjacent to \(b,c\) and has one \(Q\)-parent, so its final entry is zero or one. A private negative has no \(Q\)-parent, and its signed shift adds zero, one or two, so it remains unit.

Any other site sees at most one member of \(Q\). The only possible nonunit value would be \(+2\) at a site seeing both \(b,c\) and missing \(Y\). Such a site cannot have \(p\) as parent, since it would have two neighbours within the matching induced by \(N(p)\). So it must be a zero-parent far neighbour of \(c\). But \(c\) has exactly six zero-parent far neighbours (no label edge at \(c\)), and each of the three selected markings uses two of them as private negatives, with no overlap. All six therefore already occur among the verified unit positions. This proves the claimed contradiction.

## Three or more label edges allow at most four markings

Any omission pair must be a two-vertex cover of the actual graph on the labels. Take any three actual label edges. The possible three-edge shapes are a three-edge star, a path of length three, a triangle, a two-edge path plus a disjoint edge, and three disjoint edges. In the last four shapes there are respectively three, three, two and zero two-vertex covers (isolated vertices give no further covers). Only the three-edge star can have five covers, and they consist exactly of its center \(a\) plus any other label. If \(m\ge5\), all five must be used. No extra edge avoiding \(a\) can then exist, because it would leave at most two covers. There is also no extra edge at \(a\), since each actual neighbouring label consumes two of the six parent incidences of \(a\) and its actual label degree is at most three.

Every marking must use exactly four labels: a marking actually using five must omit \(a\) to avoid the three actual edges, and would contain someone else's chosen quartet. For any actual leaf \(z\) of the three-edge star, four markings select \(z\). All their omissions contain \(a\), so their private negatives are pairwise disjoint. They require eight distinct zero-parent far neighbours of \(z\). Its sole label adjacency leaves only seven, contradiction.

## Population bound

Let \(j\) count actual edges of labels with a common parent, and \(k\) count actual edges of labels with disjoint parents. The [existing exact all-triples-cap menu](norm18-dot8-nonstar.md#the-resulting-graph-wide-upper-bound) gives conditional maxima for \(m\) at each \((j,k)\). Inserting all the new bounds gives the following necessary upper menus (rows \(j=0,\ldots,4\), columns \(k=0,\ldots,3\)); the entries need not be graph-realizable.
\[
\begin{pmatrix}
7&5&4&0\\
6&5&3&0\\
5&4&2&0\\
3&2&1&0\\
2&1&0&0
\end{pmatrix}.
\]
Each entry obeys \(2m+j+3k\le14\). Over the 55,440 actual seeds, \(\sum m=9N_{18}\). The [prism incidence count](exclusion.md#counting-windows) gives \(\sum j=8(99\cdot84-6P)\) and \(\sum k\ge99\cdot336+6P\), where \(P\le851\) is the actual number of triangular prisms. Summing the pointwise inequality yields
\[
18N_{18}\le14\cdot55440-(166320-30P)
\le635370.
\]
The integer count is even by negation, so \(N_{18}\le35,298\). No new numerical optimization, and no assumption on any unselected shell, is used.
