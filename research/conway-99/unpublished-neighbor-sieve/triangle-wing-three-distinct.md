# Three distinct large-wing triangles at a root without a 24-site component

Use the [split-axis chart](big-triangle-wing.md). At any vertex of a hypothetical Conway graph, either an incident triangle has a wing component of size at least 24, or at least **three distinct** incident triangles have an 18-site wing component. In particular if \(b_{18}\) counts literal triangles whose largest wing component is 18 and \(b_{24}\) counts those having a wing component of size at least 24, then
\[
b_{18}+3b_{24}\ge99.
\]
The result is independent of rank, short-label populations and Fano configurations. It does not show that any 24-site component exists.

## Two local facts used beyond the preceding two-cubic case

The [positive-edge argument excluding the last two-cubic root](triangle-wing-no-two-cubic.md#where-that-positive-edge-would-have-to-lie) applies in any dirty three-edge path with degree-two intermediate split vertices, even when there are other cubic or larger split groups. Indeed its first and last defects agree, hence their cells have disjoint axes and are matching cells; the middle cell has the same squared norm 28 and therefore two edges. If it were a path plus isolate, the exact same affine field \(d_I-p\), edge-count and signed-axis contradiction would apply. No statement about the other split groups enters that proof. Thus every such three-edge path has matching cells and a unit defect. The other [short-path facts](triangle-wing-theta-paths.md#defects-and-short-chains) apply as before: maximal degree-two paths have length at most four, any separate cycle has length four with matching cells, and a path field vanishes on all nonpath cells that touch its internal axes.

The [theta exclusion argument](triangle-wing-theta-paths.md) eliminates the path length lists \(333,444,442\) in any separate theta component, even if other dirty components are present. The corresponding proofs use only the component's own start and end columns, the distinct original axes, and the degree-two zero rule. In contrast, the earlier general \(422\) argument used the absence of other cubic components to deduce a certain clean cell. Here we establish the required clean cell independently before using its final contact-parity argument.

A separate dirty four-cycle has the [outer-cell budget](triangle-wing-theta-no-cycles.md#the-outer-cell-budget-of-any-separate-four-cycle): on the twelve sites of its complementary triple of axes, the induced graph is empty or a single four-cycle and isolated sites. In particular if any one of these three outer cells is a matching cell, its four nonisolated sites would exhaust the budget, forcing its own internal graph to be the four-cycle rather than the matching. Therefore no outer cell can be a matching cell, regardless of which split component contains it.

## If only two original axes had cubic groups

Suppose all split degrees are at most three and only two original axes \(a,b\) have cubic groups. By the [no-two-cubic theorem](triangle-wing-no-two-cubic.md), there are at least four cubic groups; an original axis has at most two since its split group sizes partition six. Hence \(a,b\) each split as \(3+3\). In particular **every** axis pair touching either \(a\) or \(b\) is dirty. Denote their groups by \(A_1,A_2\) and \(B_1,B_2\).

Suppress the degree-two paths in the components containing a cubic group, retaining any separate four-cycles. The resulting cubic multigraph has no loops: a degree-two chain returning to its own cubic group gives two incident columns equal up to sign. Equality would contradict their nonpositive shared-axis Gram, and oppositeness would leave the third column zero. Nor can any path connect distinct groups of the same original axis. Such groups have anticomplete cells, and the equality up to sign of the two end columns would make one identically zero on its own cell, impossible. Thus the cubic multigraph has paths only between the two \(A\)-nodes and the two \(B\)-nodes.

The defect spans of \(A_1\) and \(A_2\) are orthogonal, since all their intergroup cell contacts are zero at the shared original axis, and the shared-axis Gram is minus seven times contact count. If some \(B\)-node received paths from both \(A\)-nodes, its three columns would belong, up to signs along the paths, to both of the two orthogonal spans, with exactly one column from one span. The zero sum would then force that singleton column to be zero. Thus each \(B\)-node receives all its paths from only one \(A\)-node. The cubic core is two separate theta components.

## The odd and even theta components are forced

One theta contains the unique original pair \(ab\). It has odd parity because its direct path has length one, and must have type \(133\). Write \(p,q\) for its two long fields and \(r=v_{ab}=-p-q\) for the direct field. The long paths are entirely matching cells by the universal three-edge lemma above.

Their internal axis pairs cannot be disjoint. If they were, their six used original axes would leave only one unused axis. Outside the seven theta cells both fields vanish at any cell touching \(a,b\) by absence of links between the split groups, and otherwise any cell touches an internal axis of at least one path so has one field zero. The [disjoint overlap identity](triangle-wing-theta-disjoint.md#the-exact-overlap-identity-when-the-internal-axes-are-disjoint) therefore applies without requiring other cells clean: with the middle corrections both zero, it forces \(m+u=0\), where \(m\) is the number of \(ab\)-cell edges and \(u\) its number of isolates. This is impossible for \(m=0,1,2\) on four sites.

The long paths cannot share both internal axes because their middle edges are distinct, and the starts at \(a\) and ends at \(b\) each use distinct axes. Thus with suitable names they are
\[
a-i-j-b,\qquad a-k-i-b,
\]
with \(i,j,k\) distinct and the other two axes denoted \(d,e\). As in the crossed-case calculation, \(p\) vanishes on the \(q\)-end cell meeting one of its own internal axes, so \(p\cdot q=0\). The direct \(ab\) cell is empty since \(r^2=56\).

At \(a\), the *other* theta's three incident cells use the remaining axes \(j,d,e\); at \(b\) they use \(k,d,e\). Its paths cannot be odd: there is no second direct \(ab\) edge and \(333\) is excluded. The even lists \(444\) and \(442\) are already excluded, and \(222\) would require three different short middle axes in the intersection \(\{j,d,e\}\cap\{k,d,e\}=\{d,e\}\). It follows that the list is \(422\), with short middle axes exactly \(d,e\) and the long path
\[
a-j-h-k-b,\qquad h\in\{i,d,e\}.
\]
The choice \(h=i\) would repeat the two original middle edges of the odd theta, so by exchanging \(d,e\) take \(h=d\).

## No separate cycle and the final parity obstruction

A separate pure degree-two four-cycle cannot use \(a\) or \(b\), which have only cubic split groups. Its complementary triple has the form \(\{a,b,c\}\). If \(c\in\{i,j,k\}\), one of the cells \(ac,bc\) is an end matching cell of the odd theta, impossible by the outer budget above. If \(c\in\{d,e\}\), the cells \(ac,bc\) form the entire degree-two split group of one short path. Each of their eight sites has two neighbours in their union (the third wing neighbour is its first-layer parent). These are eight nonisolated outer sites, again impossible. Thus there is no separate cycle.

The cell \(C_{ie}\) is not used by either theta, so it is clean. Let \(w\) be the start field of the even long path \(a-j-d-k-b\). It is unit of norm 28 and its four chain cells use eight sites of each sign. The first end cell at \(a\) is a matching; each of its sites has one first-layer parent and one own-cell mate in the same wing component, and exactly one edge left into either other cell of its cubic group. Thus there are four positive sites of \(w\) among the two short cells at \(a\), by the shared-axis contact formula and the unit bound. At \(b\) there are four negative sites among the corresponding short cells. On every other nonchain cell touching either endpoint \(w=0\) by the different split groups; on every nonchain cell touching one of \(j,d,k\) it vanishes by the degree-two zero rule. The remaining two of each sign must therefore fill \(C_{ie}\), the only cell on axes outside the long path not yet counted.

Finally choose \(x\in C_{ab}\), which belongs to the odd theta, so \(w_x=0\). There are no contacts into the even theta's signed end cells or signed short cells by the different split groups at \(a,b\). Its two long interior cells \(C_{jd}\), \(C_{dk}\) are disjoint in axes from \(ab\) and yield exactly one neighbour each by the zero-value formula, with opposite signs. The grid on \(C_{ie}\) yields exactly one further signed neighbour: each outsider has exactly one grid contact, and a site of \(C_{ab}\) contacts none of its first-layer parents or root because the axes are disjoint. There are no other signed sites of \(w\). Three signed neighbours at a zero site contradict \(Aw=-4w\). This excludes the two-original-axis possibility.

At each root with no size-24-or-larger incident triangle there are consequently at least three distinct incident size-18 triangles. If \(R\) roots do meet a size-24-or-larger incident triangle, \(R\le3b_{24}\), and \(3b_{18}\ge3(99-R)\) by counting distinct triangle incidences. This proves the displayed global inequality.
