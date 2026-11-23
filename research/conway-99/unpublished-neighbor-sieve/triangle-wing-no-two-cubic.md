# No root has exactly two cubic split groups and no larger group

Use the [triangle-wing split chart](big-triangle-wing.md) of a hypothetical SRG \((99,14,1,2)\). At any root with no triangle wing component of size at least 24, there are at least four cubic split groups, counted with multiplicity on an original axis. Equivalently there is no root with exactly two cubic groups and no larger group. The assertion does not assume Fano-freeness, the Seidel rank, or a short-shell tuple.

The [theta-path classification](triangle-wing-theta-paths.md), [separate-cycle exclusion](triangle-wing-theta-no-cycles.md), and [last theta calculation](triangle-wing-theta-disjoint.md) leave just one possibility at a root with exactly two cubic groups and no larger one: a \(1,3,3\) theta with disjoint internal axes on its two long paths, and at least one long middle cell a two-edge path plus an isolate. We give a local contradiction for such a long path below. The other path does not enter this local contradiction.

Let the long path have original axes \(a,i,j,b\), in that order. Let \(p=v_{ai}=-v_{ij}=v_{jb}\) be its neutral defect of squared norm 28. The two end cells \(C_{ai},C_{jb}\) are matching cells with \(p=-1\) at all their sites; the middle cell \(C_{ij}\) is a path plus isolate \(I\) with \(p_I=2\). The only possible entry of magnitude greater than one of \(p\) is this \(+2\): a value at most \(-2\) would have to lie in both distinct own cells of the two equal end columns, and a value at least \(+2\) must lie in the own cell of the reversed middle column. Its displayed own-cell values are \(2,1,1,0\).

## The middle isolate gives a unit affine field without a Fano hypothesis

Put \(d_x=(3I-A)e_x\) and \(u=d_I-p\). Since \(d_I^2=23\) and \(p\cdot d_I=7p_I=14\), the field \(u\) has charge one and squared norm \(23+28-28=23\). Its value at \(I\) is \(1\), and all its other entries are at most \(1\), because \(p\ge-1\) and \(d_I\le0\) away from \(I\).

Any charge-one cost-23 integer field whose entries are at most \(1\) is unit, regardless of the existence of Fano markings. Adding \(d_x\) at an entry at most \(-2\) gives charge two and cost \(23+23+2(7u_x+2)\le22\). At cost smaller than 22 the coordinate sum \(-22\) makes this impossible. Equality forces a field with only \(0,-1\) entries by the integer absolute-sum bound, yet the translated distinguished entry is \(+1\). Thus \(u\) has exactly six positive and seventeen negative sites.

The degree-two point of the middle path has the two true sign-flip neighbours. Label it \(++\) in the \(i,j\) cell; the arms are \(-+\) and \(+-\) and the isolate is \(--\). The two first-layer sites \(i^-,j^-\) are negative in \(u\), as they are the parents of \(I\) and \(p\) vanishes on the first layer. Both arms are negative too, since their \(p\)-value is one and they are not adjacent to \(I\). The parent--arm edges \(i^-\,(-+)\) and \(j^-\,(+-)\) are distinct negative edges. For any unit charge-one cost-23 field, if \(e_+,e_-\) are its same-sign edge counts, its sign equations give \(e_-=e_++1\). The pair quota on the six positive sites gives
\[
30-e_+\ge\sum_{x:\,u_x=-1}\binom{2+d_-(x)}2
\ge17+4e_-,
\]
so \(e_+\le1\). Hence the present field has exactly one positive edge.

## Where that positive edge would have to lie

At either internal axis of the long path, the two consecutive cells form the entire degree-two split group. The isolate \(I\) must have two contacts into that end cell, one of the same sign and one of the opposite sign on the shared internal axis. This is the literal signed-axis contact rule of the [root chart](big-triangle-wing.md#ordinary-local-chart-and-real-defects): the unique triangle cap with its own signed parent is the same-sign exterior contact, and the second common neighbour with the opposite parent is the opposite-sign exterior contact. Both contacts are in the end cell because \(I\) has no own-cell edges and the shared split group has just these two cells.

Consequently each end cell has exactly two \(u\)-positive sites, its two nonneighbours of \(I\), one of each sign on the internal axis. The two end cells are anticomplete: they have disjoint axes and equal defect column, taking value \(-1\) on each own cell, so the contact formula \(p=d-1\) gives zero cross contacts. The positive pivot \(I\) has no positive neighbours, since every other positive is a \(-1\) site of \(p\) nonadjacent to \(I\). The sixth positive, outside both ends and off \(I\), has \(p=-1\). It cannot be a root or first-layer site, and its cell cannot meet either end's axes, where the non-own column would be nonnegative. Thus \(p=d-1\) makes it anticomplete to both ends as well. Hence the unique positive edge must join the two positive sites inside one end cell.

This edge differs in its internal-axis sign. If its other sign agrees, it is a sign flip with triangle cap the common first-layer parent on the endpoint axis \(a\) or \(b\). The \(u\)-value there is zero, since \(I\) has first-layer parents only on \(i,j\). But the triangle cap of a positive edge \(xy\) in this unit cost-23 field must have \(u=-1\): the reflected field \(d_x+d_y-u\) has charge one, squared norm \(36+23-2(9+9)=23\), and no coordinate greater than \(1\); hence it is unit by the preceding absolute-sum argument. At the cap it has value \(-2-u_{\mathrm{cap}}\), forcing the claim. This rules out the flip edge.

The only remaining possibility is a diagonal (differing in both parental signs). The end cell is a perfect matching, so the other edge is its other diagonal. All four end vertices then use their opposite-internal-sign contact inside the end cell. Each has exactly one remaining contact in the degree-two split group, in the middle cell, and that contact must have the same internal sign. This makes it impossible for \(I\) to have its required opposite-sign contact into the end cell. Thus the diagonal is impossible too, contradicting existence of the positive edge.

## Global consequence

Let \(L\) be the number of triangles with a wing component of size at least 24, and \(H\) the number of actual 18-site wing components over triangles (a triangle with two such components contributes two). If \(R\) roots meet one of the \(L\) triangles, then \(R\le3L\). Each root outside this set has at least one cubic split group by the [large-wing theorem](big-triangle-wing.md), and the number of cubic split groups there is even by the handshake identity after deleting clean edges. It cannot be two by this theorem, so it is at least four. Each 18-site wing component is counted at its three triangle vertices, giving
\[
3H\ge4(99-R),\qquad H+4L\ge132.
\]
In particular if no component has size at least 24, there are at least 132 order-18 wing-component occurrences. This is not a count of 132 different triangles and does not establish existence of a component of size 24.
