# Twelve-grid triangular core: exclusion of a cubic midpoint

This is an addition to [the connected core reduction](triangle-wing-twelve-grid-core.md), under those same hypotheses. It leaves only the all-peripheral midpoint layout, with no saturated axis. It does not prove that layout realizable or exclude twelve grids.

## The triangular subdivision cannot have a cubic original midpoint

Name the un-subdivided cubic center \(a\) and the other cubic axes \(b,c,d\). The three subdivisions have distinct middle axes, since any two subdivided links share an endpoint and would otherwise repeat an original cell. The middle cannot be \(a\), since that also repeats a direct spoke. Finally at most one middle can be the third axis in \(\{b,c,d\}\) opposite its link: two such choices repeat a pair. Thus the layouts are either three distinct peripheral middles or one cubic middle and two peripheral middles. We exclude the latter.

By symmetry write the three short paths \(b-d-c,\ c-y-d,\ d-z-b\), with start fields \(p,q,r\), and let \(x\) be the remaining peripheral axis. (The first appearance of \(d\) as a degree-two middle and the cubic group at \(d\) are different split vertices.) The direct \(ab,ac,ad\) columns are
\[
u=r-p,\qquad v=p-q,\qquad w=q-r.
\]
At \(d\) the \(p\)-path is in a different split group from the \(q,r\) endpoints. The shared-axis Gram gives \(p\perp q,r\). Both \(u^2=p^2+r^2\) and \(v^2=p^2+q^2\) are at most 56, while each summand is at least 28. Hence \(p^2=q^2=r^2=28\), and the spoke cells \(C_{ab},C_{ac}\) are empty.

On \(C_{bd},C_{cd}\) both \(q,r\) vanish by the different group at \(d\). Disjoint-axis evaluation of \(v\) on \(C_{bd}\) and of \(u\) on \(C_{cd}\) gives \(p\ge-1\) and \(p\le1\), respectively; thus both own cells are matchings, with \(p=-1\) on \(bd\) and \(p=+1\) on \(cd\). Outside those two cells both \(p,-p\) are off-cell columns, so \(p\) is unit or zero there. On the empty \(ab\) cell, the columns \(p\) at \(bd\) and \(-r\) at \(bz\) give \(p\ge0,r\le0\), while \(-p\) at \(cd\) and \(r\) at \(dz\), off the common axes, give \(p\le1,r\ge-1\). Since \(u=-2\), all four sites have \(p=1,r=-1\). Reversing the argument on the empty \(ac\) cell gives \(p=-1,q=1\) on all four sites. On the remaining dirty cells, \(p=0\): for those touching \(d\) this follows from its degree-two group, and for \(cy,bz\) it follows from zero shared-axis Gram with \(q,r\) respectively.

A clean cell touching \(b,c\), or \(d\) has zero \(p\), since it shares an axis with one of \(p\)'s columns and has no contacts into it. On a clean cell touching \(a\), all three spoke defects vanish, hence \(p=q=r\). This common value is zero on \(ay,az\), by the degree-two group of \(q,r\) respectively. Therefore only the four clean cells \(ax,xy,xz,yz\) can contain the remaining twelve nonzero entries of \(p\), after its sixteen already identified dirty sites.

Two disjoint clean cells are joined by a perfect matching: every site of one has exactly one neighbour in the other by the disjoint-axis defect formula with zero column. Two clean cells sharing an axis are anticomplete. Among these four cells only \(ax,yz\) are disjoint. Let \(f,g\) be the restrictions of \(p\) to these two squares and let \(P\) be their permutation matrix for the matching. Both restrictions are centered by pairing their zero clean columns with \(p\), as above. At a site of \(ax\) there is no contact into \(ab,ac\), and the signed contribution from \(bd,cd\) is \(-(1+p)+(1-p)=-2p\). At a site of \(yz\) these same two cells again supply \(-2p\), and \(ab,ac\) supply a further \(-2p\): they are disjoint in axes, \(q=r=0\) on \(yz\) by the two midpoint groups, and their column values there are \(-p,p\) while their own \(p\)-values are \(1,-1\). The other two potentially signed clean cells \(xy,xz\) are anticomplete to both. Thus the equation \(Ap=-4p\) reads
\[
(A_4+2I)f+Pg=0,\qquad A_4g+P^\top f=0,
\]
with \(A_4\) the square adjacency in the corresponding order. On centered vectors \(A_4\) is negative semidefinite and \(A_4+2I\) is positive semidefinite, from the eigenvalues \(0,0,-2\). The equations give \(f^\top(A_4+2I)f=g^\top A_4g\), so both sides vanish. Each semidefinite operator annihilates its respective vector, and invertibility of \(P\) forces \(f=g=0\). Only eight clean sites in \(xy,xz\) remain for twelve unit entries. This contradiction leaves exactly the all-peripheral axis layout, which has no saturated axis.
