# The distance-three graph of the outside Hoffman blocks

Let \(C\) be an actual 22-coclique in a hypothetical Conway graph. Write \(B\) for the graph induced on the other 77 sites and \(D\) for its \(22\times77\) point--block incidence matrix with \(C\). Each \(B\)-site corresponds to its four neighbours in \(C\); each pair of points in \(C\) belongs to exactly two blocks, and distinct blocks meet in at most two points. Define \(Q\) on the 77 actual blocks by joining pairs meeting in two points.

**Theorem.** \(Q\) is the distance-three graph of the induced outside graph \(B\), is 6-regular, and every \(Q\)-edge has exactly fourteen length-three paths in \(B\). A \(K_6\) in \(Q\) consists of six of the seven four-blocks complementary to the lines of a Fano plane on seven actual \(C\)-points. Such a \(K_6\) cannot exist when the ternary Hoffman kernel \(\ker D^\top\) has dimension two. A \(K_7\) in \(Q\) gives an integral norm-fourteen neutral marking and a second 22-coclique. No clique of size six is asserted to be compulsory.

## The distance-three relation

Let \(M=A_B\). The block equations from the original strongly regular identity give \(DM=2J-D\) and \(M^2+M-12I=2J-D^\top D\). Also \(DD^\top=12I+2J\). Consequently \(M\) acts by 10 on the constants, by \(-1\) on the \(21\)-dimensional centered image of \(D^\top\), and has eigenvalues among \(3,-4\) on \(\ker D\). Hence
\[
(M+I)(M-3I)(M+4I)=14J,
\qquad M^3+2M^2-11M-12I=14J.
\]
Two blocks meeting in two points are nonadjacent and have no outside common neighbours, so the polynomial gives exactly fourteen three-walks between them, which must be paths. Every other nonadjacent \(B\)-pair has at least one common neighbour in \(B\), since it shares at most one in \(C\). This proves the distance characterization. The six pairs of points in any block identify six different partners, since a repeated partner would share at least three points, proving the degree.

## Six blocks determine a Fano completion

Fix six blocks forming a clique in \(Q\). For each point used in them write \(j\) for its multiplicity and \(a_j\) for the number of points with that multiplicity. One has \(j\le4\): in any chosen block containing the point, each other block through it must use a distinct second point of the chosen block, by the exact point-pair capacity. The two counts of incidences give \(\sum ja_j=24\) and \(\sum \binom j2 a_j=2\binom62=30\). Subtracting yields
\[
3(a_1+a_3)+4a_2=12.
\]
There are at most three points of multiplicity four: any two omit disjoint pairs of blocks, since their incidence sets of size four among six otherwise meet in at least three blocks. If \(a_2=3\) then the counts give \(a_4=4\), impossible. Otherwise \(a_2=0\), \(a_1+a_3=4\), and \(a_4=5-a_3/2\); the sole allowed profile is \(a_4=3,\ a_3=4,\ a_1=a_2=0\). Denote the three high-multiplicity points by \(H\), the four others by \(Y\).

The three omitted block pairs of the \(H\)-points partition the six blocks. Each block contains two points from \(H\) and two from \(Y\). Every point in \(Y\) appears with every point in \(H\) in exactly two blocks: its three occurrences contribute six \(H\)-incidences, each of the three pairs having capacity two. A point of \(Y\) therefore chooses one block in each of the three omitted-block pairs. This gives four binary words on three coordinates. Blocks attached to different omitted pairs share one \(H\)-point and hence exactly one \(Y\)-point. Thus the four words project bijectively to the binary pairs on any two coordinates. Such a four-word array is a parity class: after taking the first two coordinates freely, the third coordinate alternates along each row and column, and is their xor up to a flip. The words for any two distinct \(Y\)-points thus agree in exactly one coordinate.

It follows that \(Y\) itself, if added as the seventh block, uses precisely the six remaining point-pair slots on \(H\cup Y\); all pairs involving \(H\) are already saturated. The seven four-blocks all meet pairwise in two points, so their complements on \(H\cup Y\) are seven triples meeting pairwise in one point. Their 21 distinct pairs exhaust the pairs of the seven points, the Fano plane. If the added block is an actual outside site, these seven outside sites \(X\) and the seven points \(P=H\cup Y\) are independent shores with 4-regular incidence. The original lower adjacency eigenvalue \(-4\) is attained by the Rayleigh quotient of \(1_P-1_X\), giving an actual neutral norm-fourteen eigenfield. Also \((C\setminus P)\cup X\) is a second 22-coclique. Any \(K_7\) contains a \(K_6\) as above and its extra block must be \(Y\): it must meet the six blocks twice, requiring twelve memberships across its four points; no outside point contributes, any \(H\)-point cannot co-occur with a second point of \(P\) because such pairs are saturated, and therefore only the four \(Y\)-points supply twelve.

## The two-dimensional ternary obstruction

In a basis of the ternary kernel \(K=\ker D^\top\), give each point the column color in \(\mathbb F_3^2\). The four colors in every actual block sum to zero. Fix a pair of the six blocks having the same two \(H\)-points. Their two \(Y\)-pairs complement each other in \(Y\) and their color sums agree. The three omitted-block pairs give the three distinct partitions of \(Y\) into two pairs, by the parity array. All pair sums on \(Y\) thus equal half its total color sum, forcing all four colors on \(Y\) equal to one \(\lambda\). Now the three pair sums on \(H\) all equal \(-2\lambda\), forcing all three colors on \(H\) equal to \(-\lambda\).

By [the exact two-deck theorem](hoffman-ternary-rank-two.md), either the zero color occurs six times and each nonzero twice, or the zero color occurs three times, a single nonzero color \(v\) occurs five times and every other nonzero color occurs twice. In the first deck \(\lambda\) would have to be zero, but seven zero sites are required. In the second it would have to be \(v\), but three sites of color \(-v\) are required. Both contradict the literal multiplicities.

## A complementary affine field from an arbitrary six-block clique

Even when no ternary-kernel hypothesis holds, let \(X\) be the six clique blocks, \(P=H\cup Y\), and \(p=1_P-1_X\) on the original 99 sites. Put \(f=(A+4I)p\). Then
\[
 (A-3I)f=2\mathbf 1,\qquad
 \sum_i f_i=18,\qquad
 f\cdot f=30,\qquad f|_C=1_Y.
\]
Indeed \(\sum p_i=1\), \(p\cdot p=13\), and \(p^\top A p=-48\) from the 24 edges between the independent shores. The identity \((A+4I)^2=7(A+4I)+2J\) gives the squared norm. At \(C\), the degrees into \(X\) are four on \(H\), three on \(Y\), and zero elsewhere, giving the restriction. This is an actual charge-two positive-eigenvalue affine field; its coordinates outside \(C\) need not all be nonnegative. No assumption that a short-shell count forces such a clique is made.
