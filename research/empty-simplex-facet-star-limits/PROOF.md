# Limit law for the largest common-facet star of empty simplices

Let \(X_n\) be iid uniform in a fixed compact convex body \(K\subset\mathbb R^d\) with interior and volume \(A\). Let \(D_n\) be the largest, over all \(d\)-vertex sample facets, number of sample \(d\)-simplices with that facet and with no further sample point in the simplex. Thus \(0\le D_n\le n-d\). Reitzner–Temesvari already proved \(\mathbb ED_n=\Theta(n)\). We determine the following limiting behavior, not just the order.

**Theorem.** For \(d\ge3\), \(D_n/n\to1\) in probability. In the plane \(D_n/n\) converges in distribution to a nondegenerate variable \(M_K\) supported on \([0,1]\). For \(0<u<1\),
\[
 \Pr(M_K\le u)=\exp\!\left[-\frac1{2A^2}
 \int_K\int_{\mathbb R^2}\mathbf1\{g(x,v)>u\}\,dv\,dx\right],
 \qquad
 g(x,v)=\frac1A\int_K \exp\!\left[-\frac{|\det(v,p-x)|}{2A}\right]dp .
 \tag{1}
\]
All positive moments of the normalized maximum converge in both cases. For the disk or square, in particular,
\[
 0.87 < \lim_{n\to\infty}\frac{\mathbb E D_n}{n} <0.941,
\]
confirming the broader numerical window in Reitzner–Temesvari's Remark 1.2. No deterministic worst-case statement is intended.

## 1. Planar edges at distance of order one over n

Write the endpoints of a designated labeled edge as \(x-v/(2n),x+v/(2n)\), using the increasing order of the labels to orient it. For fixed \(x\in\operatorname{int}K\) and \(v\ne0\), these are in \(K\) eventually. The triangle \(T_n(p)\) with this edge and third vertex \(p\) has area exactly \(w(p)/n\), where \(w(p)=|\det(v,p-x)|/2\). Write \(L_n\) for the degree of the edge. Conditional on these prescribed endpoints,
\[
 \mathbb E[L_n/n]\longrightarrow g(x,v),\qquad
 \mathbb E[(L_n/n)^2]\longrightarrow g(x,v)^2. \tag{2}
\]
For the mean, expand into indicators of the \(n-2\) remaining points and integrate \((1-w(p)/(nA))^{n-3}\) over the uniform law of \(p\). For the second moment the diagonal vanishes after division by \(n^2\). For almost every fixed pair \(p,q\), \(p-x,q-x\) are linearly independent. Eventually neither of the two extra vertices lies inside the other's triangle, since the triangles converge to their respective line segments. Each triangle is inside a strip of half-width \(|v|/(2n)\) about its limiting line (by convexity of the strip). The intersection area is at most a constant depending on the angle times \(n^{-2}\). Thus \(n|T_n(p)\cup T_n(q)|\to w(p)+w(q)\). The joint emptiness probability, using \(n-4\) untouched points, tends to \(\exp[-(w(p)+w(q))/A]\). All integrands are bounded by one, so both integrations use dominated convergence.

For \(R<\infty\), only look at edges with \(|v|\le R\). The expected number of these edges for which \(|L_n/n-g(x,v)|>\eta\) tends to zero for any fixed \(\eta>0\). In fact exchangeability, followed by the change from two endpoint positions to \((x,v)\) with absolute Jacobian \(n^{-2}\), writes the expectation as \(\binom n2/(A^2 n^2)\) times an integral over bounded \(K\times\{|v|\le R\}\). The two endpoints must lie in \(K\); for a.e. \(x\) this eventually holds and (2) gives pointwise convergence to zero for the conditional probability. This step concerns all close sample edges, not a potentially biased conditioning on which one attains the maximum.

Let \(N_n(R,u)\) count these edges with \(g(x,v)>u\). Then
\[
 N_n(R,u)\ \Longrightarrow\ \mathrm{Poisson}\bigg(\frac1{2A^2}\int_K\int_{|v|\le R}\mathbf1\{g(x,v)>u\}\,dv\,dx\bigg).
 \tag{3}
\]
For completeness, in any fixed \(t\)-th falling factorial moment first count ordered tuples of \(t\) distinct unsigned edges whose pairs of labels are disjoint. There are \((n)_{2t}/2^t\), with independent events on the endpoints; the single-edge integral just computed (without the degree error) gives the \(t\)-th power of the claimed mean asymptotically. For an intersecting pattern with \(b\) connected components and \(v'\) distinct labels, use a spanning tree in each component: after fixing one root in each tree, each new endpoint must lie within distance \(R/n\) of its parent. With the label assignments included its total contribution is \(O_{R,t}(n^{v'}n^{-2(v'-b)})=O_{R,t}(n^{2b-v'})\). Every component has at least two vertices; since the edges are distinct, an intersection forces one component with at least three. Thus this is \(O(n^{-1})\); finitely many patterns occur. Poisson factorial moments determine its law. The evenness of \(g\) in \(v\) makes orientation immaterial; the factor \(1/2\) is for unordered edges, not an extra intensity convention.

For fixed \(x\) and unit vector \(e\), \(s\mapsto g(x,se)\) decreases continuously and strictly from one to zero (the line through \(x\) in this direction has area zero). Moreover \(g(x,v)\le C_K/|v|\): the density of the signed orthogonal projection of the uniform \(p-x\) is bounded by \(D/A\), \(D=\operatorname{diam}K\). Thus every positive-level set is uniformly bounded in \(v\), its level boundary has Lebesgue measure zero by radial coordinates, and its intensity is continuous in \(u\in(0,1)\). Statements (2)–(3), using levels \(u\pm\eta\) and letting \(\eta\downarrow0\), prove (1) for the maximum truncated to \(|v|\le R\), with that same truncation on the integral.

## 2. Far edges cannot supply a hidden larger maximum

For a designated pair at distance \(a>0\), the area \(W\) of a completion with one uniform vertex satisfies \(\Pr(W\le w)\le C_K w/a\) by the base-height formula and bounded area of a strip. For any fixed integer \(t\ge1\) the conditional moment of its degree is at most \(C_{K,t}a^{-t}\). Indeed expand in \(t\) ordered completions with \(j\) distinct third vertices. For them all to be empty the other \(n-2-j\) points must miss a union of area at least the sum of their \(j\) triangle areas divided by \(t\). Integrating with independent candidate vertices and applying \(\mathbb E e^{-cnW}\le C/(na)\) gives \(C n^j(na)^{-j}\) after counting labels. For large \(n\) this holds uniformly; summing over \(1\le j\le t\) gives the stated bound as \(a\le D\).

For any fixed \(u>0\), a union bound, conditional Markov and the unconditional distance density bounded by \(C_K a\) now give, for \(t>2\),
\[
 \Pr(\exists\text{ edge of length }>R/n\text{ and degree }>un)
 \le C_t u^{-t} n^2\int_{R/n}^D (na)^{-t}a\,da
 \le C'_t u^{-t}R^{2-t}.
\]
Sending \(R\to\infty\) proves the untruncated convergence. The intensity in (1) tends to infinity as \(u\downarrow0\) by monotone convergence, and to zero as \(u\uparrow1\) by bounded convergence; for each intermediate level it is finite and strictly positive. In particular there are no atoms at zero or one and the law is nondegenerate.

## 3. Consequence for the disk and the square

Equivalently realize \(M_K\) as the supremum of \(g(x,v)\) over a Poisson process on \(K\times\mathbb R^2\) of intensity \(dx\,dv/(2A^2)\); its void probabilities give exactly (1). In this auxiliary process the point minimizing \(|v|\) has radius \(R_0\) with \(\Pr(R_0>r)=e^{-\pi r^2/(2A)}\), an independent uniform direction and independent uniform \(x\). Thus \(\mathbb ER_0=\sqrt{A/2}\), \(\mathbb ER_0^2=2A/\pi\). Evaluating \(g\) at this one mark and using \(e^{-s}\ge1-s\) yields
\[
 \mathbb EM_K\ge 1-\frac{\mathbb E|X-Z|}{\pi\sqrt{2A}}
 \ge 1-\frac{\sqrt{\mathbb E|X-Z|^2}}{\pi\sqrt{2A}},
\]
where \(X,Z\) are independent uniform in \(K\), and the mean absolute sine for a uniform angle is \(2/\pi\). In the unit square that second moment is \(1/3\) and in an area-one disk it is \(1/\pi\), by twice the sum of coordinate variances.

For the upper bound, the density of the absolute orthogonal projection \(T=|\det(e,Z-x)|\) is bounded by \(2D/A\), for every unit \(e\). Consequently \(T\) stochastically dominates a uniform variable on \([0,A/(2D)]\). Hence \(g(x,v)\le\int_0^1\exp[-|v|s/(4D)]\,ds\), decreasing in \(|v|\). Apply this simultaneously to every point of the process, then use the nearest radius and \(e^{-b}\le1-b+b^2/2\):
\[
 \mathbb EM_K\le 1-\frac{\sqrt{A/2}}{8D}+\frac{A}{48\pi D^2}.
\]
For the area-one square \(D=\sqrt2\) and for the area-one disk \(D=2/\sqrt\pi\); substitution gives the displayed common window. Similarities leave normalized degrees invariant.

## 4. Higher dimensions: near-complete stars

Normalize \(A=1\), take \(d\ge3\), fix \(1<\alpha<d/2\), and put \(h=n^{-\alpha}\). Call a sample \(d\)-subset a candidate if its points lie in a fixed ball strictly interior to \(K\), its \((d-1)\)-dimensional simplex volume is \(\le h\), and each \((d-2)\)-face has volume at least a sufficiently small fixed \(b>0\). Uniformly for any fixed \(d-1\) positions, an independent last point completes a candidate with probability at most \(C h^2\): the complementary face must have volume at least \(b\), so the point lies in a tube of radius \(O(h)\) about a \((d-2)\)-flat. Conversely an iid \(d\)-tuple is a candidate with probability at least \(c h^2\): put \(d-1\) points in small fixed neighborhoods of a nondegenerate \((d-2)\)-simplex in the interior ball. For the remaining point take a fixed small tangential disk near their barycenter and a perpendicular two-dimensional disk of radius \(c'h\). All subfaces at the barycentric model have positive volume, so the lower face bound persists after these perturbations.

Let \(N\) count candidates. Then \(\mathbb EN\asymp n^dh^2\to\infty\) and \(\operatorname{Var}N\le \mathbb EN+C n^{2d-1}h^4\). Disjoint candidate label sets are independent. For any two overlapping distinct label sets, condition first on one candidate's positions and then on all but one of the other's fresh labels; the uniform one-label bound makes the joint probability \(O(h^4)\). Hence \(N/\mathbb EN\to1\) in probability.

Sum the number of nonempty completions over every candidate, calling the total \(J\). For a fixed candidate some further point completes it to a full simplex of volume at most \(Dh/d\). Given both the candidate and that third-stage vertex, the other points fall inside with probability at most \(nDh/d\) in total. Summing indicators thus gives \(\mathbb EJ\le n\mathbb EN\cdot nDh/d=o(n\mathbb EN)\). Markov and the concentration of \(N\) show that with probability tending to one some candidate has \(o_p(n)\) nonempty completions (more precisely \(J/(nN)\to0\) in probability on \(N>0\)). Its other completions are empty, so \(D_n/n\to1\). Finally \(0\le D_n/n\le1\) makes all positive moment conclusions in the theorem immediate.
