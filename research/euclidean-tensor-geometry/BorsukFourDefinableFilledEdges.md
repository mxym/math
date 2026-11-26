# Five strict pieces for definable compact subsets of the filled edge locus

**Yongxian Zhang.** AI-assisted proof development and internal checks; no external peer review claimed.

Use the three filled triangle edges in four dimensions of [the full-edge spindle theorem](BorsukFourFullEdgeSpindle.md), with diameter bound \(D=\sqrt3\). A compact subset \(X\) of diameter at most \(D\) has a cover by five sets of diameter strictly below \(D\) if it is semialgebraic, or more generally definable (with parameters) in an o-minimal expansion of the real field. The cover gives a partition by assigning overlaps arbitrarily. No angular or radial bound on its normalized vectors besides membership in the unit disk is needed. This statement does not cover arbitrary compact subsets of the locus or the full four-dimensional Borsuk problem. See [Chalmers](https://arxiv.org/abs/2611.17375) and [Tolmachev](https://arxiv.org/abs/2611.16775) for the general six-piece upper bound.

The underlying sufficient condition makes no reference to definability. On an oriented edge and away from its endpoints, use odds \(z=s/(1-s)\) and the normalized transverse vector \(v=w/\sqrt{3s(1-s)}\). Say a limiting tip vector \(v_0\) (a limit along \(z\to0^+\)) is persistent if for each \(\varepsilon>0\) the set of odds of points of \(X\) on that edge with \(\|v-v_0\|<\varepsilon\) contains \((0,\delta)\) for some \(\delta>0\). For each consecutive pair of edges it is enough that every limiting tip vector on at least one of the two participating edges is persistent (or that one tip has no limiting vectors).

Fix an adjacent interface \(i,i-1\) and limiting vectors \(v_0,w_0\) of both tips. For any specified \(r>0\) one can take points with odds \(r^2t,t\) respectively, with \(t\to0^+\), whose vectors converge to \(v_0,w_0\). Indeed take a sequence on the nonpersistent side, passing to a subsequence in each successively smaller prescribed interval supplied by persistence on the other side; if both sides are persistent either can supply the sequence. The diameter bound and [the exact scaled gap](BorsukFourControlledFilledTips.md#gap-at-a-tip-interface) therefore give, for every \(r>0\),
\[
G_0(r)=(2-x)r^2+2(v_0\cdot w_0)r+1-y\ge0,\qquad
x=\|v_0\|^2,\quad y=\|w_0\|^2.
\]
Any positive root must be double. At such a root,
\[
(2-x)(1-y)=(v_0\cdot w_0)^2\le xy,
\qquad
r^2=(1-y)/(2-x)\le x/[2(2-x)]\le1/2.
\]
In particular there is no root in \([1,2]\), regardless of the individual radii.

Use a common cutoff \(c>0\) on all three edges. A crossing diametric pair with odds \(z_p\ge c\ge z_q>0\) has \(1\le\sqrt{z_p/z_q}\le2\) by the scaled gap. If there were clashes at arbitrarily small \(c\), a sequence at one fixed interface would have \(z_p,z_q\to0\); pass to convergent subsequences of the ratios and the two unit-disk vectors. The exact gap tends to zero, contradicting the strict positivity of \(G_0\) on \([1,2]\). Endpoint cases are covered by the shared-apex argument of the existing routing. Thus every sufficiently small common cutoff meets the [compact five-color routing criterion](BorsukFourControlledFilledTips.md#complete-the-routing).

For a definable set, the map to odds and normalized vectors is definable off the endpoints. For any \(\varepsilon>0\) the set of odds approaching a fixed limiting vector within \(\varepsilon\) is a definable subset of the real line, by projection. It accumulates at zero and is a finite union of intervals and points; hence it contains \((0,\delta)\). This supplies precisely persistence, and includes semialgebraic sets. In contrast, the [sparse cutoff obstruction](BorsukFourFilledTipCutoffBarrier.md) uses terminal odds at separated geometric scales; persistence is a way to exclude that mechanism without pointwise angular restrictions.

## An extension to sufficiently dense multiplicative scales

Full persistence may be replaced by a geometric-scale condition. Fix \(\lambda>(2\sqrt3-3)^2\) with \(\lambda\le1\). For each pair of tips, require on at least one side that for every limiting vector and every \(\varepsilon>0\), every sufficiently small \(a>0\) admits odds in \([\lambda a,a]\) having a vector within \(\varepsilon\) of that limit. Suppose crossings nevertheless approach the tips, with limiting ratio \(R\in[1,2]\) and vectors \(v_0,w_0\). Their quadratic \(Ar^2+2(v_0\cdot w_0)r+B\), \(A=2-x\ge1,\,0\le B=1-y\le1\), vanishes at \(R\). Since \(AR+B/R\ge A+B\) for \(R\ge1\), we get \(3-x-y=A+B\le2\sqrt{xy}\), so \(\sqrt x+\sqrt y\ge\sqrt3\), \(B\le2\sqrt3-3\). Its other root \(R_-=B/(AR)\) satisfies \(R_-/R\le2\sqrt3-3\).

Choose \(0<\mu<1\) with \(\lambda\mu>(2\sqrt3-3)^2\). On the good outgoing side, replace the crossing points with ones whose odds are in \([\lambda\mu z_p,\mu z_p]\), whose vectors approach \(v_0\). On the good incoming side, alternatively use \([z_q/\mu,z_q/(\lambda\mu)]\) and vectors tending to \(w_0\). A diagonal subsequence supplies an arbitrarily small vector error and stays within the stated odds range. In either case the new ratio has a subsequential limit in \([\sqrt{\lambda\mu}R,\sqrt\mu R]\subset(R_-,R)\), where the quadratic is strictly negative. This contradicts the diameter assumption and proves the common cutoff exists. This version permits some sparse, nondefinable sets.
