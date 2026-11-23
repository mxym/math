# No empty short path in the all-peripheral twelve-grid core

This is an analytic refinement of the [twelve-grid core](triangle-wing-twelve-grid-core.md) and [cubic-midpoint exclusion](triangle-wing-twelve-grid-cubic-midpoint.md). Under exactly their joint hypotheses, each of the three short paths has defect of squared norm 28 or 42; the two dirty cells on it therefore both have at least one own edge. No exclusion of the remaining profile or unconditional norm-56 ban is claimed.

Use the all-peripheral axes \(a,b,c,d,x,y,z\) and paths \(b-x-c,\ c-y-d,\ d-z-b\), with orientated fields \(p,q,r\). Write \(u=r-p,\ v=p-q,\ w=q-r\) on the direct spokes \(ab,ac,ad\). Use the same shared-axis, disjoint-axis, and own-cell evaluation rules as in the preceding note. A clean cell can support \(p\) only on \(yz\): on the clean cells touching \(b,c,x\) there is a representative \(p\)-column on that axis, and on \(ay,az\) all three fields agree by the spoke equations, with one zero by its degree-two group. The only clean square for \(q\) or \(r\) is respectively \(xz\) or \(xy\). In particular none of these three fields has any common support with another on a clean cell.

Suppose \(p^2=56\); then \(p=-2\) on \(bx\) and \(p=2\) on \(cx\), their own graphs empty. On \(bx\), the spoke \(v=p-q\) is disjoint in axes, so \(q\le-1\); both \(q,-q\) are off-cell columns and hence \(q=-1\). On \(cx\) the same argument with \(u\) gives \(r=1\). There are no \(bx\)-to-\(cy\) contacts and there are \(2\) per \(bx\) site into \(dy\), from \(q\) and \(-q\) respectively. At a \(cy\) site the value of \(p\) is its \(bx\) contact count minus one, so \(p=-1\) on \(cy\); at \(dy\) the average \(p\)-value is one and every entry is at most one, so \(p=1\) there. The mirrored argument gives \(p=-1\) on \(dz\), \(p=1\) on \(bz\).

For a column \(s\) of a cell \(C\) and centered field \(p\), \(\sum_C p=-p\cdot s/7\), from the projector formula and the zero first-layer values. On \(cy,dz\) we have sums \(-4\), so \(p\cdot q=p\cdot r=28\). The two spoke sums are then \(\sum_{ab}p=4,\sum_{ac}p=-4\), forcing \(p=1,-1\) respectively, since they are off both of \(p\)'s own cells. These eight cells account for its full norm \(8\cdot 4+24=56\). All other sites have \(p=0\).

For clarity, the pointwise equation \(Ap=-4p\) on three cells is tabulated below. The columns are the eight cells known to support \(p\), and entries are the signed contribution from the neighbours in each cell. Their \(p\)-labels are respectively \((-2,2,-1,1,-1,1,1,-1)\).
\[
\begin{array}{c|rrrrrrrr|c}
        & bx&cx&cy&dy&dz&bz&ab&ac & Ap\\\hline
 bx     &0&4&0&2&-(1+r)&-r&2+r&0&7-r\\
 dy     &-4&0&-q&2-q&-r&1-r&r&q-2&-3-q-r\\
 cy     &0&2&-1&1&-1-r&1-r&2+r&0&4-r
\end{array}
\]
In the second row \(q\ge0\) because its own column is \(-q\), and \(r\ge0\) from its same-axis column at \(dz\). The third row uses the conclusion \(q=-1\) on \(cy\) established by the second row. Every entry is obtained by applying the own, shared, or disjoint cell formula to the column of the destination cell. For example at \(dy\), \(p=1\) gives two contacts into \(bx\) and none into \(cx\), the \(ab\) count is \(1+u=r\), and the \(ac\) count is \(1+v=2-q\).

The first row yields \(r=-1\) on \(bx\). The second gives \(q+r=1\) on \(dy\), so \(q\le1\); that dirty own cell has no isolate and is a matching. Thus \(q^2=28\), \(q=1,r=0\) on \(dy\). On \(cy\), the shared-axis spoke \(v=p-q\ge0\) with \(p=-1\) gives \(q\le-1\); since its own norm is also 28, no own internal degree two is possible and that cell too is a matching with \(q=-1\). The third row now gives \(r=0\) on \(cy\). Reversing \(b,c\) and \(y,z\), which sends \((p,q,r)\) to \((-p,-r,-q)\), yields the mirrored facts: \(q=1\) on \(cx\), \(r^2=28\), and \(q=0\) on \(dz,bz\).

The spoke \(u\) has \(u^2=p^2+r^2-2p\cdot r=28\), and at \(ab\) its value \(r-1\le-1\) since \(r\le0\) from the \(-r\) column sharing \(b\). Thus the two-edge own graph of \(ab\) has no degree two, so it is a matching and \(r=0\) there. Similarly \(q=0\) on \(ac\). The product \(q\cdot r\) now consists of eight contributions \(+1\) from \(bx,cx\), and the possible negative contributions from \(ad\), with no common clean support. At \(ad\) both are unit or zero (off both own cells); their shared-axis signs are \(q\le0,r\ge0\). So \(4\le q\cdot r\le8\). The squared norm \(w^2=56-2q\cdot r\) is one of \(28,42,56\), forcing \(q\cdot r=7\), \(w^2=42\). But the one-edge cell of \(w\) has two isolated sites, each with \(q-r=-2\) and hence \(qr=-1\). This gives \(q\cdot r\le6\), a contradiction. The other two short paths are symmetric.
