# Eventual inclusion for bounded orders of hull-volume moments, and failure for unbounded orders

Let \(H_n(K)\) be the convex hull of \(n\) i.i.d. uniform points in a compact full-dimensional convex body \(K\subset\mathbb R^d\); write \(V_n(K)=|H_n(K)|\). These are unnormalized volumes. For real \(p\) and \(t>0\) put
\[
 F_p(t)=\int_1^t s^{p-1}\,ds=
 \begin{cases}(t^p-1)/p,&p\ne0,\\\log t,&p=0.\end{cases}
\]
**Theorem A.** For each fixed \(d\ge1\) and \(P<\infty,\ P\ge0\), there exist \(c_{d,P}>0,N_{d,P}<\infty\) such that, simultaneously for all \(n\ge N_{d,P},\ K\subset L,\ |p|\le P\),
\[
 E F_p(V_n(L))-E F_p(V_n(K))
 \ \ge\ c_{d,P}\big(F_p(|L|)-F_p(|K|)\big).
 \tag{1}
\]
The expectations exist. Thus nontrivial inclusion eventually strictly increases every fixed positive moment and expected log volume, and strictly *decreases* every fixed negative raw moment. The threshold is uniform over the chosen compact interval of orders.

**Theorem B.** For every \(d\ge2\) and **every specified finite** \(n\ge d+1\), there are full-dimensional polytopes \(K\subsetneq L\) and \(0<a<M\) such that, for all \(a<s<M\),
\[
 0<\Pr(V_n(L)>s)= (|K|/|L|)^n\Pr(V_n(K)>s)<\Pr(V_n(K)>s).
 \tag{2}
\]
The common essential supremum of the two volumes is \(M\). For this same pair,
\[
 \lim_{p\to+\infty}\frac{E V_n(L)^p}{E V_n(K)^p}=(|K|/|L|)^n<1 .
 \tag{3}
\]
The pair may depend on \(n\). No dimension-only threshold works for all positive orders simultaneously or gives stochastic domination for every nested pair. This does not assert that any single fixed pair fails for arbitrarily large sample sizes. Dimension one is excluded from B: interval ranges just scale with interval length.

## 1. Uniform estimates for normalized hulls

Write \(Z_j=V_j(K)/|K|\) and \(u_j=\sup_K E(1-Z_j)\). The probability-one affine independence of \(d+1\) samples gives \(Z_j>0\) almost surely for \(j\ge d+1\). Two elementary estimates from the [earlier first-moment proof](../eventual-inclusion-hull-volume/PROOF.md) are used:

- \(u_j\to0\) uniformly in \(K\). Briefly, affine-normalize a maximal-volume simplex to \(T=\operatorname{conv}(0,e_1,\ldots,e_d)\). Cramer's rule yields \(T\subset K\subset[-1,1]^d\). Cover this box by cells of side \(1/J\). For a representative \(w\in K\) of each occupied cell the body \(w+(K-w)/(2J)\) lies within sup-norm \(1/J\) of \(w\), giving relative mass \((2J)^{-d}\). With probability at least \(1-(2J)^d e^{-j/(2J)^d}\) all representatives have a nearby sample. On that event support functions and the cube of radius \(1/(2d)\) inside \(T\) imply that the hull contains a translate of \((1-4d/J)K\). Take \(J>4d\) large, then \(j\to\infty\).
- There exist \(b_d,\eta_d>0\), with \(b_d\le1\), such that for \(m\ge2d\) and any \(x\notin\operatorname{int}K\), under the iid sample law of \(H_m(K)\),
\[
   \Pr\left\{|\operatorname{conv}(x,H_m)|-|H_m|\ge b_d |K|/m\right\}\ge\eta_d .
   \tag{4}
\]
For clarity, this is a probability bound, not an application of a lower bound on an expectation to a nonlinear transform. Choose an affine height \(h(x)\le0=\min_K h\), cut a lower cap \(C=K\cap\{h\le t\}\) of mass \(1/m\), and let \(D=C\cap\{h\ge t/2\}\). Homothety about a point at height \(t\) shows \(|D|\ge2^{-d}|K|/m\). Exactly \(d\) observations fall in \(D\) and all the others outside \(C\) with probability at least \(2^{-d(d+1)-2}/d!\). Conditional on this event, the \(d\) selected points \(Y_i\) are iid uniform in \(D\). Choose \(z_i\in D\) maximizing \(|\det(z_1-x,\ldots,z_d-x)|\); it is at least \(|D|/2^d\) by the usual maximal-basis coordinate bound. With probability \((4d)^{-d^2}\), all \(Y_i\in z_i+(D-z_i)/(4d)\). In maximizing basis coordinates the column matrix is within row-sum norm \(1/2\) of the identity, so its determinant modulus is at least \(2^{-d}\). The half-scaled simplex about \(x\) on \(x,Y_1,\ldots,Y_d\) has volume at least \(2^{-3d}|D|/d!\) and lies below the old hull (intersection only on a null height slice). This proves (4), e.g. with \(b_d=2^{-4d}/d!\), \(\eta_d=(4d)^{-d^2}2^{-d(d+1)-2}/d!\).

We also need a bound not furnished by mere convergence of \(Z_j\). For each \(A>0\) there are \(b(A,d)<\infty\) and \(j_0(A,d)\) with
\[
 \sup_{K,\, j\ge j_0} E Z_j^{-A}\le b(A,d).
 \tag{5}
\]
Use the same simplex normalization. The conditional probability that a fresh uniform point has distance \(\le t\) to any fixed hyperplane is at most \(C_d t\): some normal component has absolute value \(\ge1/\sqrt d\), the corresponding slab fibers in the cube have length \(\le 2\sqrt d\,t\), and \(|K|\ge1/d!\). For one random simplex on \(d+1\) points its volume is \(1/d!\) times the product of the \(d\) successive distances to earlier affine spans. If its volume is at most \(s|K|\), some distance is at most \((d!2^d s)^{1/d}\). Each earlier span is contained in a hyperplane; conditioning on preceding samples and taking a union bound gives probability \(\le C'_d s^{1/d}\). With \(r\) independent disjoint blocks of \(d+1\) points in the sample, \(Z_j\le s\) implies all \(r\) simplex volumes are small. Thus \(\Pr(Z_j\le s)\le\min(1,C'_d s^{1/d})^r\). Take fixed \(r>dA\) and integrate over \(s\in(0,1)\) against \(A s^{-A-1}\) (plus the constant one) to get (5).

## 2. Ordinary versus exterior gains

Work in units of \(v=|K|\). For \(n=m+1\), \(k=\lfloor n/2\rfloor\), and the first \(k\) labels fixed, the Carathéodory essential-label argument gives
\[
 E[Z_n-Z_m\mid X_1,\ldots,X_k]\le \frac{d+1}{n-k}(1-Z_k).
 \tag{6}
\]
Indeed a test point already in the first hull cannot be newly gained; if present in the full hull it has a representation by at most \(d+1\) points, so at most that many of the last \(n-k\) labels can be individually essential. These labels are conditionally exchangeable. Integrate over test points in \(K\) and divide by \(v\).

For \(|p|\le P\) and \(Z_k\le s\le1\), \(F'_p(s)\le Z_k^{-P-1}\). Using (5), (6), and Cauchy–Schwarz gives, uniformly in \(K,p\),
\[
 0\le E[F_p(Z_n)-F_p(Z_m)]
 \le \frac{2(d+1)}{n}(E Z_k^{-2(P+1)})^{1/2} u_k^{1/2}=o(1/n).
 \tag{7}
\]
Here \((1-Z_k)^2\le1-Z_k\).

For \(x\notin\operatorname{int}K\) let \(Z_x=|\operatorname{conv}(x,H_m)|/v\), which is not required to be at most one. The event in (4) intersects \(Z_m\ge1/2\) with probability at least \(\eta_d-2u_m\ge\eta_d/2\) once \(m\) is large enough. On it, integrate the derivative only over \([Z_m,Z_m+b_d/m]\subset[1/2,2]\), where \(F'_p\ge2^{-P-1}\). Outside the event, the gain is nonnegative. Thus
\[
 E[F_p(Z_x)-F_p(Z_m)]\ge\eta_d b_d2^{-P-2}/m .
 \tag{8}
\]
Combining (7),(8), choose constants \(N=N(d,P)\) and \(e=e(d,P)>0\) so that for all \(n\ge N\) and all exterior \(x\),
\[
 E F_p(Z_x)-E F_p(Z_n)\ge e/n .
 \tag{9}
\]
Increase \(N\) whenever (5) below requires it. All choices are uniform in \(p\), including \(p=0\).

## 3. Inclusion, including rare outside samples

Let \(K\subset L\), \(q=1-v/|L|\le1/2\) and \(\lambda=|L|/v\in[1,2]\). For iid sampling in \(L\) set \(Y=V_n(L)/v\). Membership outside \(K\) has binomial count \(B\sim\mathrm{Bin}(n,q)\). With \(B=0\), \(Y\) has law \(Z_n\) for \(K\). With \(B=1\), conditional on the exterior point its other observations are independent uniforms on \(K\), so (9) applies. There is no uniform deterministic lower bound on \(F_p(Y)\) when \(p\le0\). Instead, **under the unconditional law in \(L\)**,
\[
 \|F_p(Y)\|_4+|E F_p(Z_n)|\le C_{d,P}
 \tag{10}
\]
by (5) with \(A=4(P+1)\). In fact \(Y=\lambda Z_n(L)\), with \(Z_n(L)=V_n(L)/|L|\); for \(0<t\le1\) one has \(|F_p(t)|\le t^{-P-1}\), and on \([1,2]\) the function is uniformly bounded. This proves finiteness too, using \(F_p(vt)=F_p(v)+v^p F_p(t)\).

Hölder's inequality and \(\Pr(B\ge2)\le {n\choose2}q^2\) now give
\[
 E F_p(Y)-E F_p(Z_n)
 \ \ge\ q(1-q)^{n-1} e -C_{d,P}\left[{n\choose2}q^2\right]^{3/4}.
 \tag{11}
\]
For each fixed \(n\ge N\), the right side is at least \(e q/4\) whenever \(q\le q_0(n,d,P)\) for some positive \(q_0\). Since \(F_p(\lambda)\le 2^{P+1}(\lambda-1)\le2^{P+2}q\), multiplying (11) by \(v^p\) gives (1) for these small inclusions with a constant depending only on \(d,P\), not \(n\). For a general pair, the nested interpolation \(K_t=(1-t)K+tL\) has continuous positive volume (nesting follows from its support functions). Subdivide \([0,1]\) so that every successive relative increment obeys the chosen \(q_0\), and sum (1). This proves A.

## 4. Sharp obstruction to a single threshold for all positive orders

Fix \(d\ge2\) and \(n\ge d+1\). Choose any \(d\)-polytope \(S\) having exactly \(n\) vertices \(v_1,\ldots,v_n\), and let \(M=|S|\). For instance the convex hull of \(n\) distinct moment-curve points is full-dimensional by Vandermonde and every point is exposed (use the linear functional on the first two coordinates representing \(2t_i t-t^2\)). Take \(z\) in the relative interior of a facet, with outer unit normal \(\nu\), and let \(y=z+\epsilon\nu\). At \(\epsilon=0\) every \(n\)-tuple from \(\{v_1,\ldots,v_n,z\}\) containing \(z\) misses some extreme vertex of \(S\); the hull is a proper convex subset of \(S\), of strictly smaller volume. Finitely many tuples and continuity therefore allow \(\epsilon>0\) so small that **every** such tuple with \(y\) in place of \(z\) has hull volume \(\le M-2\gamma\), for some \(0<\gamma<M/2\). Put \(L=\operatorname{conv}(S,y)\).

Hull volume of a tuple is convex in each point separately. Fixing the remaining hull \(Q\), in full dimension the volume of \(\operatorname{conv}(Q,x)\) equals \(|Q|\) plus the sum of pyramids on visible facets, i.e. \(\sum_F |F|(\nu_F\cdot x-h_F)_+/d\). If \(\dim Q=d-1\) the volume is \(|Q|_{d-1}\operatorname{dist}(x,\operatorname{aff}Q)/d\), and for smaller dimension it is zero. Hence one can successively replace each unfixed point of a tuple in \(L\) by a generator from \(\{v_i,y\}\) without decreasing volume. The maximum possible volume is \(M\): all-generator tuples containing \(y\) have volume less than \(M\), and without it the hull is in \(S\).

By continuity and finiteness once again, there is a neighborhood \(U\) of \(y\) such that any point \(x\in U\cap L\), together with any \(n-1\) generators, has hull volume at most \(M-\gamma\). The same then holds with **arbitrary** other points in \(L\) by separate convexity. Since \(\nu\cdot y\) strictly exceeds the support height of \(S\), it uniquely maximizes \(\nu\cdot x\) on \(L\). By compactness one can truncate a small cap around \(y\) with a hyperplane normal to \(\nu\), so that the resulting \(K\) contains \(S\), \(|K|<|L|\) and \(L\setminus K\subset U\). For \(a=M-\gamma\) no tuple containing an outside point can have volume greater than \(a\). Conditional on all samples from \(L\) lying in \(K\), the joint law is the iid uniform law on \(K\). This proves the equality in (2). For each \(s<M\) there is positive probability that the \(n\) points fall near the respective vertices of \(S\), giving hull volume greater than \(s\) by continuity. Thus the upper tail is indeed positive.

Finally
\[
 E V_n(L)^p = (|K|/|L|)^n E V_n(K)^p + E[V_n(L)^p;\text{ some sample is outside }K] .
\]
The last term is at most \(a^p\) for \(p>0\). For any fixed \(s\in(a,M)\), the other body's moment is bounded below by \(s^p\Pr(V_n(K)>s)>0\). Taking \(p\to+\infty\) proves (3) and Theorem B.
