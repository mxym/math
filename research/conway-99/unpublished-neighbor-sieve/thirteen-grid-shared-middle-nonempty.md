# The shared-midpoint thirteen-grid profile has no empty subdivided path

At a thirteen-grid root with no size-24-or-larger component, the [opposite-subdivision classification](triangle-wing-thirteen-grid-bound.md) and [disjoint \(K_4,K_3\) theorem](clean-k4-k3-cross-edge.md) leave only a simple dirty \(K_4\) on axes \(a,b,c,d\) with subdivisions \(a-x-b\), \(c-x-d\) using the same original axis \(x\), in different split groups. The last two axes \(e,f\) are saturated. Under these hypotheses, neither subdivided path may have defect norm squared 56. Equivalently, each of its two dirty cells has at least one own edge. This is rank-free and does not claim to exclude the 13-grid profile.

All defect notation, the first-layer vanishing, and the cell contact formulas are as in the [split-axis chart](big-triangle-wing.md).

Write \(p,-p\) for the \(ax,bx\) defects, and \(t,-t\) for \(cx,dx\). The direct \(ac,ad,bc,bd\) columns are respectively \(u,v,w,z\). The four cubic sums give
\[
 v=-p-u,\qquad w=-t-u,\qquad z=p+t+u,
\]
and \(p\perp t\) by the different split groups on the common midpoint. The field \(p\) vanishes on \(cx,dx\) by the different-group contact rule on \(x\). On the clean \(ab,cd\) cells all four direct columns vanish by the shared-axis rule, so \(p,t\) vanish there. Other clean cells touching \(a,b,x\) have \(p=0\) by the same rule applied to \(ax,bx\). Thus the only potentially nonzero clean cells of \(p\) are \(ec,ed,fc,fd,ef\).

Suppose \(p^2=56\). The two own cells \(ax,bx\) are empty and have values \(-2,+2\) respectively. Each of the 16 sites in the four direct cells sees exactly one neighbour in \(C_{ax}\cup C_{bx}\). For example at \(ac\) the two contact counts from \(ax,bx\) are \(p,1-p\), since \(ax\) shares \(a\) and \(bx\) is disjoint; the other cells are analogous. The \(ax\) sites have eight total contacts into \(ac,ad\): each has a first-layer parent and no own-cell edge, leaving two more neighbours in its three-cell cubic wing at \(a\). Similarly \(bx\) has eight into \(bc,bd\). Hence \(p=+1\) on all of \(ac,ad\) and \(p=-1\) on all of \(bc,bd\). These 16 sites and the eight own-cell sites contribute \(16+32=48\) to \(p^2\); eight squares of entries must remain among the clean cells.

On \(cd\), the eigen equation \(Ap=-4p=0\) has a single possible nonzero clean contribution, from its unique neighbour in \(ef\). All four direct cells share \(c\) or \(d\) with \(cd\) so are anticomplete to it; the four star cells \(ec,ed,fc,fd\) also share an axis and are anticomplete. The two own \(ax,bx\) cells are disjoint in axes from \(cd\), and have defects \(p,-p\) both zero at each \(cd\) site, giving one contact each with weights \(-2,+2\). These cancel. The \(cd\)-to-\(ef\) adjacency is a perfect matching between disjoint clean cells, so \(p=0\) on \(ef\) as well.

Consider a site \(q\) in \(ec\), writing \(s=p(q)\). Its dirty contribution from \(ax,bx\) is \(-2(1+s)+2(1-s)=-4s\). The two direct cells \(ac,bc\) share \(c\) and are anticomplete to \(ec\). At \(q\) their columns \(u,w\) vanish, hence \(t=0\) and \(v=-p,\ z=p\). The two remaining direct cells \(ad,bd\) therefore give signed sum \((1-s)-(1+s)=-2s\), using their respective uniform values \(+1,-1\). Altogether the dirty contribution is \(-6s\). The same calculation holds on each of \(ec,ed,fc,fd\), exchanging the direct columns as necessary. More explicitly, for axis \(d\) the available direct cells are \(ac,bc\), with values \(+1,-1\) and columns \(-p,p\); \(e\) versus \(f\) does not change the counts.

Of the four potentially signed star squares, \(ec\) meets only its opposite \(fd\), and \(ed\) meets only its opposite \(fc\); each disjoint pair is joined by a perfect matching. Each restriction is centered: the nine-point grid indicator is orthogonal to every \(-4\) eigenfield, and \(p\) vanishes on the grid's root and parents. For one opposite pair let \(g,h\) be its restrictions and \(P\) the permutation matrix of its matching. The \(-4\) eigen equation gives
\[
 (2I-A_4)g=Ph,\qquad (2I-A_4)h=P^\top g
\]
with \(A_4\) the square adjacency in the corresponding order. On centered vectors \(A_4\) has eigenvalues \(0,0,-2\), so \(2I-A_4\) has least singular value 2. Consequently \(\|h\|\ge2\|g\|\) and \(\|g\|\ge2\|h\|\), forcing both zero. The other pair also vanishes. This leaves nowhere for the required eight squared entries, a contradiction. The same argument exchanges the subdivided paths and applies to \(t\).
