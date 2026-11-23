# Refined label-edge capacities at a norm-eighteen seed

Work in a hypothetical SRG(99,14,1,2). First assume \(N_{16}=U_{1,27}=0\), with \(U\) counting signed-unit affine fields. Under those two absences, whenever the six labels of a norm-eighteen seed have exactly one actual adjacency, at most five markings occur; with at least two label edges at most four occur, and with at least three edges at most three occur. All these local assertions are rank-free.

Under the two additional actual absences \(U_{2,28}=U_{2,30}=0\), the [six-mark theorem for independent labels](norm18-seven-mark-seed.md) applies. The present refinements then give the **oriented graph-wide bound \(N_{18}\le29,842\)**. These four shell absences hold on the rank-36 twelve-type palette \(\{018,020,024,026\}\).

We use the actual seed \((o,Q)\), six pair-center labels, and chosen four-label positive sets from the [earlier saturated-seed analysis](norm18-saturated-seed-cap.md). Their omitted pairs form the triangle-free graph \(L\). Any actual label adjacency must meet every omission pair, because the chosen four-label sets are independent. If two omission pairs intersect, the corresponding markings have dot eight and all their common sites are the five sites \(o,Q\) and their three common positive labels; no private sites are shared. If two omission pairs are disjoint, the two fields have only two common positive labels. They can share **at most one private negative**, because two such negatives would give dot nine with exactly three common positives, whereas the [dot-nine classification](panel-heights.md) requires four common positives and five common negatives. To apply this last clause below all fields under discussion are proved thin, i.e. they use precisely their four chosen positive labels. The neutral differences at a seed are unit, and dot ten is absent, as proved in the antecedent. Every private negative has zero parents in \(Q\).

Recall the exact literal contact count: a label is far from \(o\), has twelve far neighbours, and the total \(Q\)-parent incidences of these neighbours is six. It has no near neighbours outside its two parents. Every far site with two \(Q\)-parents is itself one of the six labels. Thus a label of actual label degree \(d\) has \(6-2d\) one-parent satellite neighbours, and exactly \(6+d\) zero-parent far neighbours. In particular \(d\le3\).

## A single label edge cannot support six markings

The case of a sole actual edge joining labels with disjoint parents is already ruled out by [the earlier unit \(U_{1,27}\) switch](norm18-saturated-seed-cap.md). Here the sole actual label edge is \(ab\), and \(a,b\) have a common parent. Suppose there are six markings. Every edge of \(L\) meets \(\{a,b\}\). If \(ab\) itself is in \(L\), triangle-freeness permits at most one edge from \(\{a,b\}\) to each other label, giving at most five edges in all. Thus \(L\subset K_{2,4}\) with \(a,b\) the size-two part. Their degrees are at least two. All fields are thin: a five-label field would have to omit \(a\) or \(b\) to avoid the actual adjacency, and since that omitted label has degree at least two, the field would contain the chosen quartet of another marking. This would give a forbidden norm-16 difference by the [window theorem](exclusion.md). Six chosen labels are also impossible.

If the degrees in \(L\) of \(a,b\) are two and four, the degree-two label is selected by four markings, whose omissions all contain the other label. Those four fields have pairwise disjoint private negatives, and each needs two private negatives at the selected center. This is eight distinct zero-parent far neighbours at a label of actual degree one, which has only seven. Thus the degrees in \(L\) of \(a,b\) are three each.

Take the three \(a\)-omitting markings. They select \(b\) and one other common centre \(c\), the unique remaining label never omitted with \(a\). If \(b,c\) share any parent \(p\), apply
\[
 w=t_1+t_2+t_3-d_b-d_c+\sum_{q\in Q\setminus\{p\}}d_q,\qquad d_i=(3I-A)e_i .
\]
This is a genuine charge-one cost-27 field by the calculation in the earlier switch, which needs only that \(b,c\) share exactly \(p\), have no actual edge, and occur in all three fields of dot eight. The only changed core evaluation from that proof is \(w_a=1-|N(a)\cap(Q\setminus\{p\})|\), which is either zero or \(-1\), not an exception. Elsewhere the same unit test applies: \(c\) has no label adjacency, so its six zero-parent far neighbours are exhausted by its two private negatives in each of the three fields; an unmarked possible \(+2\) seeing both \(b,c\) and missing \(Q\setminus\{p\}\) cannot see \(p\) (the matching at \(p\)) and cannot be a zero-parent far neighbour of \(c\). Thus this would be a signed-unit \(U_{1,27}\), absent. The analogous argument applies to the three \(b\)-omitting fields. Consequently the unique label never omitted with \(a\) is \(e=\bar b\), the complement parent pair of \(b\); the unique one never omitted with \(b\) is \(f=\bar a\).

It follows that \(L\) consists of a \(K_{2,2}\) joining \(a,b\) to the two remaining labels other than \(e,f\), with pendant edges \(be,af\). Each pendant label \(e,f\) is selected in five fields. Such a label has no actual edges to labels, so it has six literal zero-parent far neighbours and needs ten private negative incidences in its five fields. No private site occurs in more than two fields, because any repeated private site requires pairwise disjoint omission pairs, and all omissions meet \(\{a,b\}\). Since any pair of fields shares at most one private negative, at least four of the six literal sites at each pendant label must be reused and these require four distinct pairs of disjoint omissions avoiding that label. But \(L-e\) and \(L-f\) are a 4-cycle with a pendant edge; each has exactly four pairs of disjoint edges (two within the cycle, two using the pendant). Thus each of those pairs must occur as a shared private-negative witness at the corresponding label. The two distinct matching pairs of the central \(K_{2,2}\) avoid both pendant labels, so each must give a witness adjacent to both \(e,f\). The witnesses are distinct since a private site cannot be in more than two fields. The parent pairs \(e=\bar b,f=\bar a\) also share one parent, because \(a,b\) share one; thus \(e,f\) have three common neighbours, impossible.

## Two actual edges cannot support five markings

It suffices to take exactly two actual label edges, since the previous saturated-seed proof already gives at most four markings when the total is at least three. If the two edges are disjoint, there are at most four two-vertex covers, all of which select one endpoint from each actual edge, so there are at most four omission pairs.

If the two edges are \(ab,ac\), their covers are the five pairs containing \(a\) and the pair \(bc\). Suppose five covers are used by \(L\). Either all five contain \(a\), or \(bc\) is used and exactly one of \(ab,ac\) is omitted from \(L\) (both cannot accompany \(bc\) in the triangle-free omission graph). In both cases there exists an actual leaf, say \(b\), which is selected by four markings all having their chosen omissions incident to \(a\): in the first case use any leaf, and in the second case use the missing star edge's leaf. Those four markings are pairwise disjoint on private sites. They require eight distinct private negative neighbours at \(b\). Yet \(b\) has actual label degree one and only seven zero-parent far neighbours, contradiction. Here thinness also follows if needed: to choose five actual labels one must omit \(a\), and \(L\) has at least four edges there, so a quartet would repeat.

## Three or more actual edges cannot support four markings

Take any three actual label edges, and consider their two-vertex covers. Among the five three-edge shapes (three-star, length-three path, triangle, two-edge path plus disjoint edge, or three disjoint edges), the maximum number of covers except for the star is three. A three-star's five covers all contain its centre \(a\). If there are four markings, the chosen three edges must therefore be such a star. No further actual edge avoids \(a\) since that would leave at most two covers; no further edge at \(a\) is possible because the actual label degree is at most three. Thus the actual label graph is exactly that star, plus two isolated labels.

Four distinct chosen covers through \(a\) leave one peripheral label \(z\) never omitted, so four markings select it. Their omission pairs share \(a\), hence their private negatives are pairwise disjoint. A selected label needs two private negative neighbours beyond its two parents in each marking. This would be eight sites, but \(z\) has actual degree zero or one and therefore at most seven zero-parent far neighbours. This excludes four.

## Graph-wide cap

Assume additionally \(U_{2,28}=U_{2,30}=0\). Pull in \(m\le6\) on independent labels from the [six-mark theorem](norm18-seven-mark-seed.md). For \(j,k\) counting actual label edges with shared/disjoint parents, respectively, intersect the new bounds with the [old exact at-most-two-per-triple table](norm18-dot8-nonstar.md). The resulting necessary upper table on \(m\), in rows \(j=0,\ldots,4\) and columns \(k=0,\ldots,3\), is
\[
 \begin{pmatrix}
 6&5&4&0\\
 5&4&3&0\\
 4&3&2&0\\
 3&2&1&0\\
 2&1&0&0
 \end{pmatrix}.
\]
Every entry obeys \(m+j+k\le6\) except the permissive \((j,k)=(4,3)\) chart. That chart cannot occur on a real seed. Indeed if \(k=3\), all complementary parent-pair labels are adjacent. Any triangle of labels has a shared-parent edge, because the three complementary pairs themselves form a matching; the shared parent already caps that edge, so such a label triangle is impossible. Also a 4-cycle has opposite label pairs nonadjacent, since there are no triangles. Nonadjacent label pairs must have a common parent when \(k=3\), and sharing that parent and the two cycle common neighbours contradicts \(\mu=2\). The actual label graph therefore has girth at least five. With \(j+k=7\), its six vertex degrees sum to 14, so the number of unordered length-two paths is \(\sum_z\binom{d(z)}2\ge10\) by integer convexity (minimizer \(2,2,2,2,3,3\)). But each such path corresponds to a nonedge of labels and no nonedge has two such paths, by absence of triangles and 4-cycles. There are at most \(15-7=8\) nonedges, contradiction.

Thus pointwise \(m+j+k\le6\). Over all 55,440 actual seeds, \(\sum m=9N_{18}\), \(\sum j=8(99\cdot84-6P)\), and \(\sum k\ge99\cdot336+6P\), with at most \(P=851\) graph prisms, as in [the original local incidence count](exclusion.md#counting-windows). Hence
\[
 9N_{18}\le6\cdot55440-8(99\cdot84-6P)-(99\cdot336+6P)
 =232848+42P\le268590.
\]
The count is even by negation, so \(N_{18}\le29,842\). This imposes only the four stated shell absences.
