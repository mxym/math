# The uniform measure on a simplex is determined by its halfspace depth

Let \(T\) be a full-dimensional simplex in \(\mathbb R^d\), \(d\ge1\), and \(P\) its normalized Lebesgue measure. For a Borel probability \(M\), write
\[
D_M(x)=\inf_{u\in S^{d-1}} M\{y:u\cdot y\ge u\cdot x\}.
\]
These are **closed** halfspaces. Equivalently one can use all closed halfspaces containing \(x\).

**Theorem.** If a Borel probability \(Q\) on \(\mathbb R^d\) satisfies \(D_Q(x)=D_P(x)\) for every \(x\), then \(Q=P\). There is no moment or density assumption on \(Q\).

For \(d=2\) this answers the uniform-triangle subquestion in [Nagy, GeMS Project: Some Open Problems, Problem 1](https://gems.karlin.mff.cuni.cz/pdf/Depth_problems_update.pdf). It is not a characterization theorem for every finite-first-moment law.

## 1. Support and directional quantiles

First \(Q\) is supported in \(T\). Put \(C=\overline{\operatorname{conv}}(\operatorname{supp}Q)\). Outside \(C\) a strictly separating halfspace gives zero depth. Thus \(C\) contains \(\operatorname{int} T\), where \(P\) has positive depth (center a small ball at the given point). At each \(x\in\operatorname{int} C\), every open outward halfspace \(\{u\cdot(y-x)>0\}\) contains a support point and hence has positive \(Q\)-mass. That mass is lower semicontinuous in \(u\), by Fatou's lemma. On the unit sphere it therefore has a strictly positive minimum, so \(D_Q(x)>0\). Outside \(T\), \(D_P=0\). Consequently \(\operatorname{int} C\subset T\); taking closures, since \(C\) is full dimensional, gives \(C\subset T\).

For a probability \(M\) on \(T\) and \(0<\alpha\le1\) define
\[
q_M(u,\alpha)=\max\{t:M(u\cdot Y\ge t)\ge\alpha\}.
\]
The maximum exists by compact support and left continuity of the inclusive tail. The depth region is
\[
K_\alpha(M)=\{D_M\ge\alpha\}=\bigcap_{u\in S^{d-1}}\{x:u\cdot x\le q_M(u,\alpha)\}.
\]
For each \(\alpha\), the quantile is Lipschitz in \(u\) with constant \(\sup_{y\in T}|y|\), since the projected variables differ by at most \(|u-u'|\sup_T|y|\). At each boundary point of a full-dimensional \(K_\alpha(M)\) at least one constraint is active: otherwise the continuous slack has a strictly positive minimum over the sphere and the point is interior. At a boundary point with a unique outward unit normal, that normal must therefore be active. For an affine functional \(L\) with gradient pointing along this normal, the upper \(\alpha\)-quantile of \(L(Y)\) equals \(L(x)\), by positive affine rescaling. This argument does not require zero hyperplane masses.

## 2. A visible patch near each vertex

Fix a vertex \(v_0\). Write the barycentric coordinates as \(a,b_1,\ldots,b_d\), with \(a\) the coordinate of \(v_0\), so \(a=1-\sum b_j\). Put \(h=1/(d+1)\). On the open set \(0<b_j(x)<h\) for every \(j\),
\[
D_P(x)=d^d\prod_{j=1}^d b_j(x).
\tag{1}
\]
Indeed put \(r_j=(d+1)b_j(x)\in(0,1)\). The sub-simplex with vertex \(v_0\) and other vertices \(v_0+r_j(v_j-v_0)\) has centroid \(x\) and volume fraction \(\prod_j r_j\). By [Grünbaum's centroid halfspace inequality](https://doi.org/10.2140/pjm.1960.10.1257), every halfspace containing \(x\) cuts at least \((d/(d+1))^d\) of its volume. Conversely the cap of \(T\) given by \(\sum_j b_j(y)/r_j\le d/(d+1)\) passes through \(x\). Its nonzero intercepts on the vertex edges are \(d b_j(x)<1\); it is precisely the sub-simplex scaled from \(v_0\) by \(d/(d+1)\). Thus the lower bound is attained. No formula for the remaining contour pieces is needed.

Fix \(h<r<1\). For \(s=(s_1,\ldots,s_d)\) define
\[
L_s(y)=a(y)+\sum_j s_j b_j(y)=1-\sum_j(1-s_j)b_j(y).
\]
Choose \(0<\eta<1\) such that \((1-r)/(d(1-\eta))<h\). Uniformly for \(\|s\|_\infty<\eta\) and \(r<t<1\), set
\[
b_j(x)=\frac{1-t}{d(1-s_j)},\qquad
\alpha_s(t)=\frac{(1-t)^d}{\prod_j(1-s_j)}.
\]
This is a point in the patch with \(L_s(x)=t\) and \(D_P(x)=\alpha_s(t)\). The set \(K_{\alpha_s(t)}(P)\) is locally a superlevel of (1) at \(x\), with nonzero gradient, so it is full dimensional and its outward unit normal is unique. It points along \(\nabla L_s\), since \(\nabla\log D_P(x)=\sum_j\nabla b_j/b_j(x)=-d\nabla L_s/(1-t)\).

By equality of the depth regions, Section 1 gives that the upper \(\alpha_s(t)\)-quantile of \(L_s(Y)\) under either law equals \(t\). In particular \(Q(L_s\ge t)\ge\alpha_s(t)\). For \(r<t'<t\), the upper \(\alpha_s(t')\)-quantile is \(t'<t\); hence \(Q(L_s\ge t)<\alpha_s(t')\). Letting \(t'\uparrow t\) gives equality, and likewise for \(P\). The maximum of \(L_s\) on \(T\) is \(1\), and neither law has mass at \(1\), by \(\alpha_s(t)\to0\). Thus the projected signed measure \((L_s)_\#(Q-P)\) vanishes on \((r,\infty)\): equality of the inclusive tails there gives equality on all Borel subsets there.

## 3. Recovering signed mass locally from the visible projections

Put \(\mu=Q-P\). For a multi-index \(\beta\) of order \(k\) and any \(\varphi\in C_c^\infty((r,\infty))\), let \(\psi=\varphi\) if \(k=0\), and otherwise let \(\psi\) be its \(k\)-fold primitive integrated from \(-\infty\), so \(\psi^{(k)}=\varphi\) and \(\psi=0\) on \((-\infty,r]\). Although this primitive need not be compactly supported at its upper end, all projected variables for \(\|s\|_\infty<\eta\) lie in a common compact interval. The vanishing just proved gives
\[
0=\int_T\psi(L_s(y))\,d\mu(y).
\]
Differentiating in \(s\) with multi-index \(\beta\) at \(s=0\) is justified because the variables and the necessary derivatives are uniformly bounded on the compact ranges. It yields
\[
\int_T b(y)^\beta\,\varphi(a(y))\,d\mu(y)=0.
\]
Polynomials in the \(d\) independent barycentric coordinates \(b_j\) are dense in \(C(T)\) by Stone–Weierstrass. Thus the signed measure \(\varphi(a)\mu\) is zero. Choosing cutoffs equal to \(1\) on \([r+\varepsilon,1]\) and taking \(\varepsilon\downarrow0\) gives \(\mu|_{\{a>r\}}=0\). Let \(r\downarrow h\) and repeat for every vertex. Every point of \(T\) has some barycentric coordinate greater than \(h\), except the centroid, where all coordinates equal \(h\). Consequently \(\mu\) is supported at the centroid. Since \(\mu(T)=0\), it vanishes there as well. This proves the theorem.
