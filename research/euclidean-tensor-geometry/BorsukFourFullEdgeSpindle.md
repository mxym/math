# Five strict pieces on the full equilateral edge locus

**Yongxian Zhang.** AI-assisted proof development and internal checks; no external peer review claimed.

Let \(a_0,a_1,a_2\) be unit vectors at the vertices of a centered regular triangle in a plane \(P\subset\mathbb R^4\), put \(W=P^\perp\), and set \(D=\sqrt3\). Thus \(a_i\cdot a_j=-1/2\) for \(i\ne j\). For the oriented edge \(i\) from \(a_i\) to \(a_{i+1}\), write
\[
u=(1-s)a_{i+1}+s a_i,\qquad 0\le s\le1,\qquad
r(s)=\sqrt{3s(1-s)}.
\]
Here and below indices are modulo three. The **filled edge locus** is the union of the fibers \(u+B_W(0,r(s))\) on the three complete edges. Its spherical part consists of the points \(u+w\) of norm \(1\), equivalently \(\|w\|=r(s)\).

**Theorem.** Let \(X\) be a compact subset of the filled edge locus with \(\operatorname{diam} X\le D\). Assume that for each oriented edge \(i\), its points of \(X\) with sufficiently small positive \(s\) are spherical. Then \(X\) has a cover by five compact sets, each of diameter strictly less than \(D\).

In particular the theorem covers all compact, diameter-\(D\) subsets of the **entire spherical edge locus**, with both halves of every edge and arbitrary accumulation at the three contacts. It also covers all **finite** diameter-\(D\) subsets of the entire filled edge locus: the near-tip condition is then vacuous for sufficiently small neighborhoods. For infinite sets, fibers away from the three terminal tips may be entirely filled, and points on the other branch at each contact can be nonspherical. Changing to the opposite cyclic orientation gives the reflected statement. Individual sets in the variable-neighborhood version have a positive margin. For any fixed terminal cutoff, there is a uniform nonexplicit margin and a full tubular perturbation theorem, stated below. The general regular-triangle spindle, including unconstrained nonspherical points near terminal tips and arbitrary planar interior projections, is not proved.

This extends the [cyclic half-edge routing](https://github.com/mxym/math/blob/a236b148148a706c0fa5e544bd544666830c84dc/research/euclidean-tensor-geometry/BorsukFourMidpointFiberRouting.md) in these regimes, but does not give the earlier theorem's explicit numerical margin or pass to the whole filled locus. The remaining contact-star problem is described in [ProofAtlas route R6](https://www.proofatlas.ai/collaboration/borsuk-problem-r4/); general four-dimensional six-part bounds are given by [Chalmers](https://arxiv.org/abs/2611.17375) and [Tolmachev](https://arxiv.org/abs/2611.16775).

## Gap and tip interaction

For a point \(p=u+w\) write \(\lambda_p\) for its planar barycentric vector and \(\Delta_p=1-\|p\|^2\). In the filled edge locus \(\lambda_p\ge0\) componentwise and \(\Delta_p\ge0\). The scalar product of two planar projections is \(\tfrac32\lambda_p\cdot\lambda_q-\tfrac12\), so
\[
D^2-\|p-q\|^2=\Delta_p+\Delta_q+3\lambda_p\cdot\lambda_q+2w_p\cdot w_q. \tag{1}
\]
In particular the apices are compatible with every point of \(X\), so one may add them to \(X\) when absent.

Set \(z=s/(1-s)\), with values \(0\) and \(\infty\) at the terminal and initial apex, respectively. For nonapex \(p\) on edge \(i\) and \(q\) on edge \(i-1\), the shared barycentric coordinate is at \(a_i\), so \(\lambda_p\cdot\lambda_q=s_p(1-s_q)\). Define \(v_p=w_p/r(s_p)\) and \(v_q=w_q/r(s_q)\), vectors of norm at most one. Then (1) gives
\[
\frac{D^2-\|p-q\|^2}{2r(s_p)r(s_q)}
=\frac{\Delta_p+\Delta_q}{2r(s_p)r(s_q)}
+\frac12\sqrt{z_p/z_q}+v_p\cdot v_q. \tag{2}
\]
Consequently any diametric pair of the indicated types satisfies \(z_p\le4z_q\).

**Uniform directional exclusion near a tip.** For each \(i\), for all sufficiently small positive \(z_p\) on edge \(i\), and for every nonapex spherical \(q\) of \(X\) on edge \(i-1\), one has \(v_p\cdot v_q>-1/2\). Otherwise there are \(p_n\) with \(z_{p_n}\to0\), and spherical \(q_n\), for which the dot product is \(\le-1/2\). After passing to subsequences the vectors converge to \(v,v'\). For each **fixed** nonapex spherical \(q\) of \(X\) on edge \(i-1\), \(\Delta_q=0\), and \(0\le\Delta_{p_n}\le r(s_{p_n})^2\). The diameter hypothesis and (2) then imply \(v\cdot v_q\ge0\) by taking \(n\to\infty\). The same holds for the limit of the \(v_{q_n}\), contradicting \(v\cdot v'\le-1/2\). This argument does not require that \(p_n\) itself be spherical. The assertion is vacuous when there are no such \(q\).

Choose \(0<c<1/4\) so small that the directional exclusion applies for \(0<z_p\le4c\) on each edge, and all nonapex \(q\) on each edge with \(0<z_q\le c\) are spherical. Define main positions on edge \(i\) by \(z_p\ge c\) and tips on edge \(i-1\) by \(z_q\le c\). The following strict interaction is crucial:
\[
p\in\text{main positions of edge }i,\quad q\in\text{tips on edge }i-1
\quad\Longrightarrow\quad \|p-q\|<D. \tag{3}
\]
At an endpoint shared by these sets the assertion follows from (1) (the other point has positive coordinate at \(a_i\)). Otherwise a diametric pair would have \(c\le z_p\le4z_q\le4c\), and (2) would give \(v_p\cdot v_q\le-1/2\), contrary to the directional exclusion. Both endpoints of the \(c\) threshold are allowed in (3).

## Compact routing

A pair on one edge can have distance \(D\) only if its positions have reciprocal odds \(z,z^{-1}\), with both points spherical and nonzero transverse directions antipodal, apart from the pair of the two apices. In fact write \(x=2s-1\), \(y=2s'-1\). The planar separation is \(D|x-y|/2\) and the transverse separation is bounded by the sum of the radii, so
\[
\|p-q\|^2
\le \tfrac34\left((x-y)^2+
(\sqrt{1-x^2}+\sqrt{1-y^2})^2\right)
=\tfrac32\left(1+\cos(\arcsin x+\arcsin y)\right).
\]
Equality at \(D^2\) requires \(y=-x\) and equality in the transverse radius and triangle bounds. In particular all tips on the same edge \(z\le c<1\) are mutually strict.

Use three base colors, one indexed by each \(i\), and two spare colors. The base color \(i\) receives all the tips on edge \(i-1\), including \(a_i\), and main points on its outgoing edge according to the following angular routing. Main points with \(z\ge2/c\) stay in the base; they cannot have a reciprocal partner in the main range \(z\ge c\), even at the shared threshold \(2/c\). These include the initial apex.

In the central band \(c\le z\le2/c\), every positive barycentric coordinate is at least \(b=c/(2+c)\). Choose \(0<\eta<\pi/4\) with \(\sin\eta<2b^2\). Choose any reference ray in \(W\). Send the first closed angular arc \([-\eta,\pi/2]\) on all three central bands to spare color four, and the second \([\pi/2,\pi+\eta]\) to spare color five. Keep the remaining closed arc \([\pi+\eta,2\pi-\eta]\) in the corresponding base. Arc endpoints can overlap in this cover. Points with zero transverse vector in the bands may be put in all three angular choices: formally use closed cones including zero, so the pieces remain compact without assigning a direction to zero.

Two central points share some positive barycentric coordinate, even on different edges, and hence \(\lambda_p\cdot\lambda_q\ge b^2\). In either spare color the angular separation is at most \(\pi/2+\eta\), so \(w_p\cdot w_q\ge-(3/4)\sin\eta\) (also true if one is zero). Equation (1) therefore yields a strict squared gap at least \(3b^2-(3/2)\sin\eta>0\). Within the main points remaining in a base color, central pairs cannot be antipodal because their directions occupy a closed arc of width \(\pi-2\eta\), and outer main positions \(z\ge2/c\) cannot have a reciprocal partner. Tips in that base are mutually strict, and all tip–main pairs are strict by (3). Each of the five pieces is a finite union of compact intersections obtained with closed intervals and cones. Thus pointwise strictness gives strict piece diameters. The five pieces cover \(X\), proving the theorem.

## Optional weakening and scope boundary

The proof actually needs only this directional condition: on each oriented edge, directions of nonzero transverse vectors at sufficiently small positive \(z\) lie in the closure of the directions of **spherical nonapex points of \(X\) on that same edge**. To see this, in the directional exclusion proof use arbitrary such \(q_n\) near the preceding terminal tip. A limit of the \(v_{q_n}\) is either zero or a nonnegative scalar multiple of a direction in that closed set. The argument with fixed spherical witnesses still rules out a limiting dot product \(\le-1/2\). Additionally a diametric pair in (3) requires both transverse vectors nonzero by (2). Thus the same conclusion holds under this weaker assumption.

Without a condition at the tips, a fixed preceding point \(q\) with \(\Delta_q>0\) contributes a term of order \(\Delta_q/r(s_p)\) to (2) as \(p\) approaches its terminal apex. No one-sided angular restriction follows from that argument. The proof therefore does not pass to arbitrary filled compact sets by replacing spherical witnesses with interior points or by taking a limit of finite five-colorings.


## Uniform perturbation for a fixed locus

Fix \(0<\rho\le1\). Let \(\mathcal E_\rho\) be the union over the three edges of the points with either \(s\ge\rho\) or \(\|u+w\|=1\). On each edge this is a closed sublocus, so the union is compact. There exist \(\delta,\varepsilon>0\), depending on \(\rho\) but not on the set, such that each compact \(X\) in the closed \(\delta\)-neighborhood of \(\mathcal E_\rho\) with \(\operatorname{diam}X\le D\) is covered by five sets of diameter at most \(D-\varepsilon\). For \(\rho=1\) the locus is exactly the full spherical edge locus. Closure extends the conclusion to bounded sets in the same neighborhood.

Indeed, if there were no such positive constants, for every positive integer \(n\) one could take a nonempty compact \(X_n\) in the closed \(1/n\)-neighborhood, of diameter at most \(D\), with no five-set cover of diameters at most \(D-1/n\). By compactness of the Hausdorff hyperspace of a compact neighborhood of \(\mathcal E_\rho\), a subsequence converges to a nonempty compact \(K\subset\mathcal E_\rho\), with diameter at most \(D\). The theorem gives five compact pieces covering \(K\), all with diameters at most \(D-\gamma\) for some \(\gamma>0\). Enlarging every piece by the Hausdorff distance \(d_H(K,X_n)\) covers \(X_n\), and increases each diameter by at most \(2d_H(K,X_n)\). For sufficiently large \(n\) in the subsequence this gives a five-set cover of diameters at most \(D-1/n\), a contradiction. This does not prove a uniform margin over \(\rho\downarrow0\).

As a weaker consequence for arbitrary subsets of the filled edge locus with diameter at most \(D\), their graph of pairs at distance exactly \(D\) has a proper five-coloring, by finite graph compactness and the finite case above. This does not give smaller diameters for the color classes of a general infinite set. The [filled-tip cutoff obstruction](BorsukFourFilledTipCutoffBarrier.md) shows why the strict tip–main separation itself cannot simply be asserted without the local condition.
