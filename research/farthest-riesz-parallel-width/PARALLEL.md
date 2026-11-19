# Farthest-point Riesz mass of large outer parallel bodies

Let $B$ be the closed unit Euclidean ball in dimension $n\ge3$, let $m=n-1$, and let $s_m$ be the area of $S^m$; write $d\omega$ for its unnormalized area measure. For compact $L$ with at least two points, put $d_L(x)=\max_{y\in L}|x-y|$ and $\sigma_L=-\Delta d_L^{2-n}/[(n-2)s_m]$, the farthest-point probability measure. The Laugesen–Pritsker conjecture is $\sigma_L(L)\le2^{-m}$, with equality only for a closed ball in dimension $n\ge3$. Its unrestricted form is not proved here.

**Theorem.** For every fixed nonempty compact convex $K\subset\mathbb R^n$, including polytopes and lower-dimensional sets, put $K_t=K+tB$, $t>0$. Write $h(u)=\max_{p\in K}u\cdot p$, $e(u)=[h(u)+h(-u)]/2$, $o(u)=[h(u)-h(-u)]/2$. Then
\[
 2^m\sigma_{K_t}(K_t)=1-\frac{(m+3)\int |\nabla e|^2+
 (m-1)\int(|\nabla o|^2-mo^2)}{2s_m t^2}+o_K(t^{-2}).
 \tag{1}
\]
All integrals here and below without a domain are over $S^m$, and derivatives are spherical. In particular, every non-ball $K$ satisfies the conjectured inequality strictly for all $t$ larger than a threshold depending on $K$. A point also gives a ball after enlargement. There is no claim at $t=0$, no monotonicity assertion, and no uniform lower cutoff over all $K$.

**Boundary flux.** For a full-dimensional convex body $L$, at almost every boundary point $x$, the outer normal $u$ and the tangential derivative of $d_L|_{\partial L}$ exist (Lipschitz charts). If $y$ maximizes the distance, the unit vector $b=(x-y)/d_L(x)$ is a convex subgradient of $d_L$ at $x$. All such vectors have that same tangential component, by taking both signs of a tangent derivative along a boundary chart. Their normal components are nonnegative since $y\in L$; since their norms all equal one, their normal components coincide as well. Thus the farthest point is unique there. Compactness then shows that any choice of farthest vectors at points tending to such an $x$ tends to $b$. The exterior homothetic flux limit in the proof of Kawohl–Nitsch–Sweers, Proposition 2.2 (preprint equations (16)–(18)), now admits dominated convergence: $d_L\ge\mathrm{diam}(L)/2>0$, the outward normals are unchanged by homothety and outward radii can be chosen where the ambient gradients exist surface-a.e. This yields
\[
 s_m\sigma_L(L)=\int_{\partial L} d_L(x)^{-m}(u\cdot b)\,dA(x).\tag{2}
\]
The exterior limit counts the mass of the **closed** set. Alternatively it follows by testing the distribution against a Lipschitz cutoff equal to one on $L$, decreasing linearly across the exterior distance shell of thickness $\epsilon$, and using the coarea formula; for (2) applied to $K_t$ one can use the ordinary exterior parallel parametrizations. Only the upper inequality from KNS is needed for the eventual strict bound.

**Distance expansion.** Each $x\in\partial K_t$ with outer normal $u$ has $x=tu+p$, $p\in F_K(u)=\{p:u\cdot p=h(u)\}$. For $K_t$ the outer normal is unique; boundary area need not push to a given normal one-to-one. Put $w=h(u)+h(-u)$ and $a_t=\max_{z\in K}|tu+p-z|$; then $d_{K_t}(x)=t+a_t$. For every maximizing $z_t$ a farthest vector is $b_t=(tu+p-z_t)/a_t$ (for large $t$, $a_t>0$). Uniformly over all listed choices, with $P=P_{u^\perp}$,
\[
 |tu+p-z|=t+u\cdot(p-z)+|P(p-z)|^2/(2t)+O_K(t^{-2}).
\]
It follows that $a_t=t+w+O_K(t^{-1})$ and $u\cdot b_t=1+O_K(t^{-2})$. At $d\omega$-almost every $u$, both support points $p\in F_K(u)$ and $z\in F_K(-u)$ are unique by differentiability of the support function. All maximizers $z_t\to z$, by the uniform first-order expansion and compactness. Comparing the above display at $z$ and $z_t$, and using $u\cdot(p-z_t)\le w$, gives the squeezed second coefficient $a_t=t+w+|P(p-z)|^2/(2t)+o_u(t^{-1})$. Also $u\cdot b_t=1-|P(p-z)|^2/(2t^2)+o_u(t^{-2})$, e.g. by expanding the cosine using its transverse component. Since $P(p-z)=\nabla w(u)$, we obtain, with a bounded residual $R_t$,
\[
 (2t)^m d_{K_t}(x)^{-m} u\cdot b_t
 =1-\frac{m w}{2t}+\frac{R_t(p,u)}{t^2},
 \qquad
 R_t\longrightarrow R:=\frac{m(m+1)}8 w^2-\frac{m+2}4|\nabla w|^2. \tag{3}
\]
Here $|R_t|\le C_K$ uniformly for all sufficiently large $t$, including all nonunique support or farthest choices. At the full-area set of regular directions the limit is uniform over all choices at that fixed $u$.

**Which surface coefficients are needed.** Let $S_{K_t}$ denote boundary area pushed forward under the outer normal. The Minkowski polynomial for surface area measures gives positive, finite coefficient measures $A_j$ depending only on $K$, with
\[
 t^{-m}S_{K_t}=A_0+t^{-1}A_1+t^{-2}A_2+\cdots+t^{-m}A_m,
 \qquad A_0=d\omega.
 \tag{4}
\]
This normalization **includes** the binomial coefficients; it extends to lower-dimensional summands by continuity. Consequently the total variation distance from $t^{-m}S_{K_t}$ to $d\omega$ is $O_K(t^{-1})$. To integrate the last term of (3), take the upper and lower envelopes of $R_t$ over all contact $p\in F_K(u)$ and farthest choices at $tu+p$. They are measurable by compactness and closed graphs, uniformly bounded, and both converge to $R(u)$ area-a.e. Thus their integrals against $t^{-m} S_{K_t}$ tend to $\int R\,d\omega$, by (4) and dominated convergence. This avoids presuming a single support point at a direction charged by a facet-area atom.

The two further identities used from (4) are
\[
 A_1=\Delta h+mh\quad\text{as a measure},\qquad
 A_2(S^m)=\frac{m-1}{2}\int(mh^2-|\nabla h|^2).\tag{5}
\]
For smooth uniformly convex support functions, (4) is the coefficient expansion of $\det(t I+Q_h)$ where $Q_h=\nabla^2 h+h I$. Thus $A_1=(\mathrm{tr}Q_h)d\omega$ and $A_2=\tfrac12[(\mathrm{tr}Q_h)^2-\mathrm{tr}(Q_h^2)]d\omega$. Integrating the latter and using the sphere's integrated Bochner identity $\int[(\Delta h)^2-|\nabla^2h|^2]=(m-1)\int|\nabla h|^2$ yields (5). The general case follows by smooth rotational convolution of the support function plus a vanishing ball, preserving convexity and giving uniform and $H^1$ convergence. Equivalently, the gradients converge almost everywhere at differentiability points by convexity and are uniformly bounded. For fixed $m+1$ distinct positive $t$'s the area measures of the parallel bodies converge weakly, whence by coefficient interpolation each $A_j$ does as well. This proves the needed weak version. In particular, $\int w\,dA_1=\int(mwh-\nabla w\cdot\nabla h)$: approximate the Lipschitz $w$ by spherical convolution with uniform and $H^1$ convergence before pairing with the finite measure.

**Collect the terms.** From (2)–(4), $s_m 2^m\sigma_{K_t}(K_t)$ has constant $s_m$, first coefficient $A_1(S^m)-(m/2)\int w=0$ since $w=2e$, and second coefficient
\[
 A_2(S^m)-(m/2)\int w\,dA_1+\int R.
\]
Insert (5) and (3); the even and odd cross terms integrate to zero. The coefficient of $\int e^2$ vanishes. The coefficients of $\int|\nabla e|^2,\int o^2,\int|\nabla o|^2$ are respectively $-(m+3)/2,m(m-1)/2,-(m-1)/2$, proving (1).

Finally, the first nonconstant eigenvalue of the negative Laplacian on $S^m$ is $m$, with eigenspace the restrictions of linear functions. The odd $o$ has mean zero, so the asserted nonnegative deficit vanishes only if $e$ is constant and $o$ is linear (here $m>1$). Thus $h$ is the support function of a translated closed ball, allowing radius zero. For a positive-radius ball, (2) directly gives $2^{-m}$. The vanishing odd coefficient at $m=1$ is consistent with the classical planar constant-width equality and is not a new planar theorem. ∎
