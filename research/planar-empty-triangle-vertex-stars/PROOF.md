# Planar empty triangles through a common vertex: the logarithm is unnecessary

Let \(X_n\) be iid uniform in a fixed planar compact convex body \(K\) with interior. Let \(D_1(X_n)\) be the maximum, over sample vertices, of the number of sample triangles incident to that vertex and containing no further sample point. Then
\[
 \mathbb E D_1(X_n)=\Theta_K(n).
\]
The lower bound is known (Reitzner–Temesvari, arXiv:1808.08734v2, Theorem 1.5(2)); it also follows by dividing three times the expected total empty-triangle count by \(n\). We prove the upper bound. Normalize \(|K|=1\), fix an anchor \(x\in K\), and write \(F_x(B)\) for its number of empty triangles with two vertices in an independent sample \(B\). All constants below are uniform in \(x\), but may depend on \(K\). Boundaries and degeneracies have probability zero in the applications.

## Geometric estimates for adding a point

Write \(W(p,q)=|[x,p,q]|\), \(a=|x-y|>0\) for a new marked point \(y\), and
\[
 \beta(v)=\begin{cases}v(1+\log(1/v)),&0<v<1,\\1,&v\ge1.\end{cases}
 \qquad H(a)=n\beta(1/(na)).
\]
The function is increasing and \(\beta(bv)\le b\beta(v)\) for \(b\ge1\); \(H\) is bounded below by a positive body-dependent constant since \(a\le\operatorname{diam}K\).

For independent uniform \(p,q\) and any \(s>0\),
\[
 \Pr(W(y,p)\le s)\le C\min(1,s/a),\qquad
 \Pr(W(p,q)\le s)\le Cs .
 \tag{1}
\]
The first bound is the area of a strip of half-width \(2s/a\) inside a fixed bounded disk; integrating the analogous bound \(Cs/|p-x|\) over \(p\) proves the second. If \(y\in[x,p,q]\) and \(W(p,q)\le s\), both \(p,q\) must lie in the strip of half-width \(2s/a\) about line \(xy\), since both smaller triangles with base \(xy\) lie inside the original. For a random pair,
\[
 \Pr(y\in[x,p,q],\ W(p,q)\le s)\le Cs\beta(s/a). \tag{2}
\]
Indeed restrict \(p\) to the strip, then integrate \(Cs/|p-x|\) for the second point. In polar coordinates around \(x\), the strip at radius \(u\) has angular measure at most \(C\min(1,s/(au))\). Integrating this over \(0<u<\operatorname{diam}K\) gives \(C_K\beta(s/a)\), also when the strip covers the disk.

Let \(T\) consist of \(n-O(1)\) iid points (only bounded omissions will be used). Let \(B_y\) count the triangles \([x,y,w]\), \(w\in T\), empty of other points of \(T\); set \(L_y\) equal to the sum of their areas. Let \(C_y\) count the triangles \([x,p,q]\), \(p,q\in T\), empty of other points of \(T\), that contain \(y\). Define \(U_y=B_y+C_y\); adding \(y\) changes the anchor count in absolute value by at most \(U_y\). We will use, for fixed integers \(t\ge1\) and \(0\le j\le t\),
\[
 \mathbb E_T[B_y^{t-j} L_y^j]\le C_t H(a)^t n^{-j},\qquad
 \mathbb E_T[U_y^t]\le C_t H(a)^t . \tag{3}
\]

For the first inequality expand in \(t\) ordered labels, allowing repeats. Given the positions of the used labels, emptiness of all selected triangles requires the untouched \(\ge n/2\) points to avoid their union, hence has probability at most \(\exp(-nW_*/2)\), where \(W_*\) is the largest selected area. Slice \(W_*\in[h/n,(h+1)/n]\) for \(h=0,1,\ldots\), using disjoint half-open intervals. With \(s=(h+1)/n\), the product of the \(j\) area weights is at most \(s^j\). For \(v\le t\) distinct labels the number of choices is at most \(C_t n^v\); the geometric probability of all areas at most \(s\) is at most \([C\min(1,s/a)]^v\) by (1) and independence. Since \(n\min(1,s/a)\le(h+1)H(a)\), the contribution is bounded by \(C_t n^{-j}H(a)^t\) upon summing a polynomial in \(h+1\) times \(e^{-h/2}\). We used the uniform positive lower bound on \(H\) to pass from \(v\) to \(t\).

For \(C_y^t\), an ordered list of \(t\) pairs is a possibly repeated-edge graph on \(v\) used labels without isolated vertices. Fix a matching of \(m\) edges, one from each connected component. Then \(v-m\le t\), since each component with \(v'\) vertices requires at least \(v'-1\) edges. Use (2) independently on the matched pairs and the single-point strip restriction on the remaining \(v-2m\) labels. The same slicing and emptiness estimate apply; for one intersection pattern before the exponential factor the bound is
\[
 C_t n^v (s\beta(s/a))^m\beta(s/a)^{v-2m}
 = C_t(ns)^m [n\beta(s/a)]^{v-m}
 \le C'_t(h+1)^v H(a)^t.
\]
There are finitely many patterns at fixed \(t\); the exponential slice sum yields (3) for \(C_y\), hence for \(U_y\).

For a uniform mark \(Y\), uniformly in \(x\), polar integration now gives
\[
 \mathbb E H(|Y-x|)^4=O(n^2),\qquad
 \mathbb E H(|Y-x|)^2=O(1+\log^3 n). \tag{4}
\]
Indeed substitute \(u=n|Y-x|\) in the radial upper bound \(C|Y-x|\,d|Y-x|\). Beyond \(u=1\) the residual integrals are bounded by \(\int_1^\infty u^{-3}(1+\log u)^4du\) and \(\int_1^{O(n)}u^{-1}(1+\log u)^2du\), respectively.

## Two-mark interactions

Take \(n-1\) nonanchor points. Let \(\Delta_i\) be the anchor count minus its value after deleting label \(i\). Equations (3)–(4) yield \(\mathbb E\Delta_i^4=O(n^2)\). For distinct labels denote their locations by \(y,z\), let \(T\) omit both, and form every \(U,B,L\) below from this common independent \(T\). Set \(E_y\) equal to the number of the \(B_z\) triangles that contain \(y\), and reverse the roles to define \(E_z\). Then
\[
 |\Delta_i|\le U_y+1+E_y,\qquad |\Delta_j|\le U_z+1+E_z. \tag{5}
\]
In fact the presence of \(z\) can only remove empty triangles among those already counted by \(U_y\). New terms have either both marks as vertices (at most one triangle with \(x\)), or \(z\) as vertex and \(y\) inside.

By Cauchy–Schwarz in \(T\) conditional on the two marks, the \(U_y^2U_z^2\) term is bounded in expectation by \(C[\mathbb E H(|Y-x|)^2]^2=O(1+\log^6 n)\). For the mixed term \(U_z^2E_y^2\), condition on \(T,z\). The independent uniform \(y\) lies in each counted triangle with probability its area. Therefore \(\mathbb E_y E_y^q\le B_z^{q-1}L_z\) for \(q\ge1\), using \(0\le E_y\le B_z\). In particular, conditional on \(z\) alone,
\[
 \mathbb E[U_z^2 E_y^2\mid z]\le
 (\mathbb E_T U_z^4)^{1/2}(\mathbb E_T B_z^2 L_z^2)^{1/2}
 \le C H(|z-x|)^4/n.
\]
Likewise \(\mathbb E[E_y^4\mid z]\le \mathbb E_T B_z^3L_z\le C H(|z-x|)^4/n\). Integrate over \(z\) using (4) to obtain \(O(n)\) in both cases, with the same estimates under reversal; Cauchy–Schwarz then bounds \(\mathbb E E_y^2E_z^2=O(n)\). Single factors of squared terms are covered by (3)–(4) or by the fourth-moment bound for \(E_y\). Expanding (5) with \((a+b+c)^2\le3(a^2+b^2+c^2)\) gives
\[
 \mathbb E\Delta_i^2\Delta_j^2=O(n+1+\log^6n)=O(n).
\]
Thus \(V=\sum_i\Delta_i^2\) satisfies \(\mathbb E V^2=O(n^3)\), including the diagonal terms.

## Centering and taking the maximum

Write \(F=F_x(X_{n-1})\) and \(G=F-\mathbb EF\). Variance tensorization gives \(\operatorname{Var}(A)\le\sum_i\mathbb E(A-A_i)^2\) for any \(A_i\) independent of coordinate \(i\) and measurable in the other coordinates. Apply it first to \(F\) using the deletion values, giving \((\mathbb EG^2)^2\le\mathbb EV^2\). Then apply it to \(G^2\) using \((G-\Delta_i)^2\), also measurable in the other coordinates. Since \([G^2-(G-\Delta_i)^2]^2\le 8 G^2\Delta_i^2+2\Delta_i^4\),
\[
 \mathbb E G^4\le 3\mathbb E V^2 +8(\mathbb E G^4\,\mathbb E V^2)^{1/2},
\]
which implies \(\mathbb E G^4=O(n^3)\). All variables are bounded for fixed \(n\), and all constants are independent of the anchor. By the second bound in (1) and emptiness of the remaining sample, an individual pair is counted with probability \(O(1/n)\) (use the same exponential slices, or integrate its Laplace transform). Therefore \(\mathbb EF=O(n)\) uniformly too.

Finally, condition in turn on each random anchor \(X_i=x\). If \(F_i\) is its count and \(m(X_i)=\mathbb E[F_i\mid X_i]\), then
\[
 \mathbb E\max_i F_i\le \sup_{x\in K}m(x)+
 \bigg(\sum_{i=1}^n\mathbb E|F_i-m(X_i)|^4\bigg)^{1/4}=O(n).
\]
No independence of different stars is used.
