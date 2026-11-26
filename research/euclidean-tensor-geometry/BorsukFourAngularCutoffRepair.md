# Two-sided angular repair for conflicting cutoffs on filled triangle edges

**Yongxian Zhang.** AI-assisted proof development and internal checks; no external peer review claimed.

Use the filled edge locus, normalized vectors, cyclic orientation, and odds \(z\) of [the preceding routing theorem](BorsukFourControlledFilledTips.md), with \(D=\sqrt3\). Let \(X\) be compact with diameter at most \(D\). Fix a common cut \(0<c<1/4\). A crossing pair means a diametric pair on successive edges \(i,i-1\) with \(z_p\ge c\ge z_q>0\). If the unordered pairs of angular rays arising this way, over all three interfaces together, number at most six, then \(X\) has five pieces of diameter strictly below \(D\). The conclusion also holds when there are at most nine distinct rays involved, even with more than six pairs. A more general criterion only requires that the crossing pairs fail to obstruct some common retained arc. This condition can hold even when no small cutoff avoids *all* crossings, as in the [sparse cutoff obstruction](BorsukFourFilledTipCutoffBarrier.md). It does not solve arbitrary compact filled edges or the general four-dimensional problem, where [Chalmers](https://arxiv.org/abs/2611.17375) and [Tolmachev](https://arxiv.org/abs/2611.16775) give the general six-piece bound.

## Two-sided angular repair

At a diametric crossing pair, the unscaled barycentric gap formula
\[
\|p-q\|^2=D^2-\Delta_p-\Delta_q-3\lambda_p\cdot\lambda_q-2w_p\cdot w_q
\]
and its [normalized version](BorsukFourFullEdgeSpindle.md#gap-and-tip-interaction) yield
\[
1\le r\le2,\qquad v_p\cdot v_q\le-r/2\le-1/2 .
\]
Thus \(c/4\le z_q\le c\le z_p\le4c\), both transverse vectors are nonzero, and their shorter angular separation is at least \(2\pi/3\). Apices cannot enter a diametric crossing pair because the shared barycentric coordinate is positive.

Use the enlarged central band \(c/8\le z\le8/c\) on all edges, so each nonzero barycentric coordinate in this band is at least \(b=c/(8+c)\). Take \(0<\eta<\pi/4\) with \(\sin\eta<2b^2\). Choose a closed retained angular arc \(J\) of width \(\pi-2\eta\) and split the complementary arc into two closed spares of width \(\pi/2+\eta\), allowing endpoint overlaps. Within the central band, send each point with angle in a spare cone to that spare color regardless of whether \(z\) is above or below \(c\). Use closed cones containing the zero vector.

Base color \(i\) receives the incoming edge \(i-1\) points with \(z\le c/8\) or with \(c/8\le z\le c\) and angle in \(J\); it also receives outgoing edge \(i\) points with \(z\ge8/c\) or with \(c\le z\le8/c\) and angle in \(J\). A same-edge incoming pair has both odds below 1 and cannot be diametric. A same-edge outgoing pair in the retained arc cannot be antipodal, and an outer outgoing point with \(z\ge8/c\) cannot have a reciprocal partner of odds \(\ge c\). These use the exact [one-edge equality characterization](BorsukFourFullEdgeSpindle.md#compact-routing). Cross pairs in any base are strict provided every diametric crossing pair has at least one of its nonzero directions outside \(J\): both endpoints of a putative clash must lie in the angular band, not on its outer boundaries. In each spare the squared gap is at least \(3b^2-(3/2)\sin\eta>0\) because all central points share a positive barycentric coordinate and the spare width bounds the transverse angle. All five pieces are compact, hence pointwise strictness yields strict diameters.

For any unordered pair at short angular separation \(\delta\ge2\pi/3\), the starts of closed arcs \(J\) that contain both rays form a set of angular measure at most \(\max(0,\pi-2\eta-\delta)\). Since the arc has width less than \(\pi\), at most one orientation of the shorter connecting arc can be used. When there are at most six pairs the total forbidden measure is strictly less than \(2\pi\), so a suitable start exists. More generally use any \(J\) whose start avoids the full union of forbidden starts; for instance the union can have outer measure below \(2\pi\), even if there are infinitely many pairs.


## Eight rays can suffice even with more than six conflicts

In fact, the criterion always succeeds if the crossing pairs together use at most eight distinct angular rays, no matter how many of the pairs occur. If the ray set has a circular gap of at least \(\pi/3\), take an open semicircle beginning at the first endpoint of this gap in the circular order. Its rays lie in an interval of length at most \(2\pi/3\) with the far endpoint excluded, so no two have separation \(2\pi/3\) or larger. Otherwise all circular successive gaps are strictly less than \(\pi/3\). Draw a diameter through any ray. Its two open semicircles together contain at most seven rays, so one contains at most three. These are consecutive in the circular order and their spread is strictly less than \(2\pi/3\). In either case fit the closed retained arc of width \(\pi-2\eta\) inside the chosen open semicircle.

As an abstract angular claim the number eight is sharp for arcs of width \(>160^\circ\): mark every pair at angle \(120^\circ\) among nine equally spaced rays. Any arc wider than \(160^\circ\) contains four consecutive rays, including a marked pair. This is only an obstruction for an abstract list of angular conflicts; it does not assert that the list can be realized by diameter pairs in the filled-edge locus.


For actual filled-edge conflicts one can include **nine** rays. Suppose the nine-ray set has no good open semicircle. A gap of at least \(60^\circ\) would already give one, so every consecutive gap is \(<60^\circ\). Consequently any open semicircle through a boundary ray that contains at most three rays has no conflicting pair (its rays are consecutive). Each of the two open semicircles determined by a boundary ray therefore contains at least four rays, hence exactly four, with no antipodal boundary ray. In the forward semicircle starting from ray \(i\), the only possible conflicting pair is the first and fourth rays, the pair \(i+1,i+4\) modulo 9, since all shorter consecutive spans use at most two gaps. Thus every span of three consecutive gaps is at least \(120^\circ\). Their sum is \(3\cdot360^\circ\), hence each equals \(120^\circ\), and every step-three pair is a conflict.

At such a pair \(v_p\cdot v_q\le-r/2\) with \(r\ge1\); angle exactly \(120^\circ\) forces equality, \(r=1\), and both transverse vectors of unit norm. Their odds are then both \(c\). Each of the nine rays is thus represented by a unit vector at this same odds on some edge. A step-four pair has smaller angular separation \(120^\circ+g\), where \(0<g<60^\circ\), and so cannot be realized on different edges: the scaled gap at equal odds and unit norms is \(1+2v_p\cdot v_q<0\) across any two different edges. The step-four pairs connect the nine indices, so all such unit representatives must lie on one edge (the assertion applies to every choice of representatives). This contradicts the step-three conflicts, which require different edges. Thus a suitable open semicircle exists for any actual list of at most nine rays.


## No counting hypothesis when all conflicts are exactly \(120^\circ\)

No counting hypothesis is needed if all crossing pairs at the chosen cutoff have separation exactly \(120^\circ\). Their nonzero directions form a compact subset \(R\) of the circle: the crossing odds lie in closed bands away from the apices, and a diametric crossing has normalized dot product \(\le-1/2\), implying both norms are bounded away from zero. In the exact-angle case that same bound forces equal odds \(c\) and unit transverse norms at every participating endpoint.

If \(R\) has an open complementary gap of angular length at least \(60^\circ\), start the open semicircle at the first endpoint of the gap. The participating rays in that semicircle have spread strictly below \(120^\circ\) for every included pair. So any closed retained arc of the required slightly smaller width contained in it works.

Otherwise every complementary gap has length \(<60^\circ\). Form a graph on \(R\) by joining rays at shorter separation \(>120^\circ\). Any two rays of separation \(<60^\circ\) have a common graph neighbor: their two open sets of rays at separation \(>120^\circ\) intersect in an open arc longer than \(60^\circ\), which cannot miss \(R\). The relation of being connected by successive moves of length \(<60^\circ\) connects \(R\): its classes are relatively open and closed and separated by distance at least \(60^\circ\) from one another. If two classes existed, traverse the circle from a ray of one class to the first ray outside it; compactness and that separation would give a complementary gap of length at least \(60^\circ\) after the last ray in the first class along that arc. Hence the \(>120^\circ\) graph is connected.

As in the nine-ray proof, every joined pair must be represented on the same edge, since at equal odds \(c\) the scaled gap for points of unit normalized radii on different edges is \(1+2 v_p\cdot v_q<0\). Connectivity would force all crossing endpoints to lie on a single edge, contradicting the existence of a cross-edge pair. Thus a good semicircle exists for any actual exact-angle conflict set.

For a separate angle-only extension, if all marked separations are at least \(\pi-\alpha\) with \(0<\alpha\le\pi/3\), and there are \(n\) rays satisfying \(\lfloor (n-1)/2\rfloor\alpha\le\pi\), a good open semicircle exists without using the geometry. An angular gap at least \(\alpha\) works as above. Otherwise draw a diameter through a ray and take the open side with at most \(\lfloor(n-1)/2\rfloor\) rays. Their consecutive gaps are \(<\alpha\), so any pair there is separated by less than \(\pi-\alpha\).


## A positive angular tolerance at every positive cutoff

For the same filled-edge problem there is a quantitative open neighborhood of the exact-angle case, with no assumption on the number of conflicts or rays. Write \(b=c/(8+c)\). Assume every diametric crossing at this cutoff has shorter separation at most
\[
2\pi/3+b^2/3
\]
(in radians). Then five compact pieces of diameter strictly below \(D\) suffice. The hypothesis admits angles strictly above \(2\pi/3\): for example two endpoints on different edges at equal odds \(c\), with angle \(\theta>2\pi/3\) and common squared normalized radius \(3/[2(1-\cos\theta)]\), give zero scaled gap.

**Stability from the distance formula.** Put \(s=2b^2/3\) and \(K=5s\); in particular \(s<0.01\). If \(p,q\) is a crossing, its odds ratio parameter \(r=\sqrt{z_p/z_q}\) satisfies \(r\ge1\). Both radial-deficit coefficients in the [scaled gap](BorsukFourControlledFilledTips.md#gap-at-a-tip-interface) are at least 1. With \(\alpha=1-\|v\|^2,\ \beta=1-\|w\|^2\), the Lipschitz bound on cosine and the unit disk bounds give \(2v\cdot w\ge-1-s\). As \(G=0\),
\[
1\le r\le1+s,\qquad
\alpha+\beta\le r(1+s-r)\le (1+s)s.
\]
Every participating point therefore has odds in \([c/(1+s)^2,c(1+s)^2]\), and squared normalized radius at least \(A=1-(1+s)s>0\).

Now compare any two participating endpoints on different physical edges, in the cyclic order of the gap formula; they need not themselves form a crossing. Here \(r\in[1/M,M]\) with \(M=(1+s)^2\). In \(G/r\) each radial-deficit coefficient is a convex combination of \(r\) and \(1/r\): the first uses weights \(1,r^2t\), and the second uses weights \(t,1\), respectively. Since \(G/r\ge0\) and each deficit is at most \((1+s)s\), this gives
\[
2v\cdot w\ge-M(1+2(1+s)s)\ge-1-5s .
\]
The last inequality follows by expansion for \(s\le0.01\). Their radius product is at least \(A\), and \((1+5s)/A\le1+7s\) on the same range, so their cosine is at least \(-(1+7s)/2\). On \([2\pi/3,2\pi/3+5s]\) the sine is at least \(4/5\). Thus the shorter angle is at most \(2\pi/3+K\). In particular, rays of participating points farther apart than this must have all their participating representatives on one and the same physical edge.

**Find the retained arc.** Let \(R\) be the compact set of participating directions; compactness follows by restricting to the positive odds and radius bounds above and projecting the closed diametric-crossing set. If it is empty there is no clash to avoid. Otherwise put \(\eta=2b^2\) and \(g=\pi/3-2\eta\). If a complementary gap is longer than \(g\), start the closed retained arc of width \(\pi-2\eta\) slightly inside the gap, leaving more than \(g\) of gap in front of the start. Its participating directions then have angular spread less than \(2\pi/3\), so it retains no whole crossing.

Suppose no complementary gap is longer than \(g\). Let \(h=g+(2\eta-K)>g\). For any two participating rays of short separation \(d\le h\), the open arcs of test rays farther than \(2\pi/3+K\) from the two rays intersect in an open arc of length at least
\[
2\pi/3-2K-d\ \ge\ g+(2\eta-K)>g .
\]
It meets \(R\). By the different-edge bound, the common ray and both original rays have all their participating representatives on a single edge. The steps of length at most \(h\) connect \(R\): distinct step classes would be relatively open and closed, at mutual separation at least \(h\), and following the circle from one class to its complement would expose a complementary gap at least \(h\). Hence all endpoints would lie on the same physical edge, contrary to nonempty \(R\). This gives the required retained arc. The two spare cones work because \(\sin\eta<\eta=2b^2\), giving squared gap \(3b^2-(3/2)\sin\eta>0\). This proof does not provide a cutoff satisfying the angle hypothesis for arbitrary compact filled-edge sets.

## A sharp forced count at exact equality

When all crossings are exactly \(120^\circ\), there are at most six distinct unordered angular crossing pairs, and six is attainable. Orient each uniquely as \((a,a+2\pi/3)\) in the fixed circular direction. If three starts \(a_1<a_2<a_3\) lie in an arc of length strictly below \(2\pi/3\), then for every \(i<j\) the forward difference from \(a_i\) to \(a_j+2\pi/3\) is in \((2\pi/3,4\pi/3)\), so the shorter separation is strictly above \(2\pi/3\). At equal odds \(c\) and unit radii, this forces all participating representatives of the two compared rays onto the same physical edge. The three equal-edge constraints, for \((i,j)=(1,2),(1,3),(2,3)\), place the start and end of the middle crossing on the same edge, a contradiction. Thus for any finite collection of \(n\ge3\) starts each sum of two consecutive circular gaps is at least \(2\pi/3\). Summing gives \(4\pi\ge n(2\pi/3)\). This applies to any selection of starts and therefore rules out any infinite example as well.

In equality, all two-gap sums equal \(2\pi/3\), so the six starts form two interleaved equilateral triples, with consecutive gaps alternating \(g,2\pi/3-g\) for \(0<g<2\pi/3\). Rays three steps apart must lie on the same edge, since their separation exceeds \(2\pi/3\). Every ray now has a unique participating edge, and step-two pairs must cross, which forces the three physical edges to repeat in a fixed order twice around the circle, up to a permutation. Conversely, take any six rays of this form and place one point on each with odds \(c\), unit normalized radius, and this repeating pattern of edge labels. On different edges the angle is at most \(2\pi/3\), hence \(G=1+2\cos\theta\ge0\), with equality exactly at the six step-two pairs. On the same edge distances are at most \(D\) by the one-edge gap formula, and are strict since the odds are not reciprocal. Thus these realizations attain the bound; the regular hexagon is one example.
