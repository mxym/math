# Volume-weighted anchors: a conditioning-free structural inverse theorem

Date: 2026-10-07.

## Result and scope

The determinant-threshold selection and the barycentric condition-number loss in the supplied proof are unnecessary. There is a complete replacement for its integrated-assignment lemma:

**Theorem.** Let \(\nu\) be a centered Borel probability law on \(\mathbb R^d\), with bounded support \(\mathcal S\) that affinely spans \(\mathbb R^d\). Fix any norm and write \(\Lambda=\operatorname{diam}\mathcal S\) in that norm. For independent samples from \(\nu\), let

\[
 A=\mathbb E|\det(X_1,\ldots,X_d)|,\qquad
 B=\mathbb E|\det((X_0,1),\ldots,(X_d,1))|,
 \qquad D=B-A.
\]

Then \(B>0\), \(D\ge0\), and there are affinely independent anchors \(w_0,\ldots,w_d\in\mathcal S\) and a Borel assignment \(I:\mathcal S\to\{0,\ldots,d\}\) such that

\[
 \boxed{\quad
 \mathbb E\|X-w_{I(X)}\|
 \le \Lambda\,\frac{(d+1)(d+2)}2\,\frac{B-A}{B}.
 \quad}                                                    \tag{1}
\]

Consequently, for the cone law in the supplied proof, whose support lies in the Euclidean unit ball,

\[
 \boxed{\quad
 h\le (d+1)(d+2)\frac{D}{B}
 =\frac{(d+1)^2(d+2)e(K)}{1+(d+1)e(K)}
 \le (d+1)^2(d+2)e(K).
 \quad}                                                    \tag{2}
\]

There is no determinant threshold, no probability-loss factor, and no upper bound on barycentric coordinates in this theorem. It applies to arbitrary centered bounded full-dimensional laws, so convex-boundary realizability is not required for this assignment step. The actual cone-law geometry is useful for obtaining polynomial directional dispersion and hence a polynomially controlled enclosing polar simplex; see Section 6.

This report does not use an arbitrary-law example as a convex-body obstruction. No obstruction is needed: the suspected clipping problem has a direct solution.

## 1. The integrated witness, including singular bases

For an ordered base \(\mathbf x=(x_1,\ldots,x_d)\), put

\[
 F_{\mathbf x}(y)=\det((x_1,1),\ldots,(x_d,1),(y,1)),
 \quad P(\mathbf x)=\mathbb E(F_{\mathbf x}(X))_+,
 \quad N(\mathbf x)=\mathbb E(-F_{\mathbf x}(X))_+.
\]

The determinant is affine in its final argument. Since \(\mathbb EX=0\),

\[
 |\mathbb EF_{\mathbf x}(X)|=|\det(x_1,\ldots,x_d)|.
\]

It follows that

\[
 D=2\mathbb E_{\mathbf X}\min(P(\mathbf X),N(\mathbf X))\ge0. \tag{3}
\]

This identity is valid when a base is singular. Define the continuous nonnegative witness

\[
 \psi_{\mathbf x}(y,z)
 =\min((F_{\mathbf x}(y))_+,(-F_{\mathbf x}(z))_+)
 +\min((-F_{\mathbf x}(y))_+,(F_{\mathbf x}(z))_+).
\]

For independent \(Y,Z\), each minimum has expectation at most \(\min(P,N)\). Thus

\[
 \mathbb E_{\mathbf X,Y,Z}\psi_{\mathbf X}(Y,Z)\le D.       \tag{4}
\]

All expectations are finite because the law has bounded support.

## 2. Anchor witness and exact barycentric identities

Let \(W=(W_0,\ldots,W_d)\) have law \(\mu=\nu^{\otimes(d+1)}\), and set

\[
 V(W)=|\det((W_0,1),\ldots,(W_d,1))|.
\]

For a deterministic anchor tuple \(W\), form \(G(W,x)\) by summing:

1. For every \(i\), the witness with the other \(d\) anchors as base and \(w_i,x\) as test points.
2. For every \(i<j\), the witness with \(x\) and the other \(d-1\) anchors as base and \(w_i,w_j\) as test points.

Fix any deterministic ordering of each base. Reversing its orientation does not change \(\psi\). Put

\[
 H(W)=\int G(W,x)\,d\nu(x),\qquad
 N_d=(d+1)+\binom{d+1}{2}=\frac{(d+1)(d+2)}2.
\]

Every summand, before integrating the anchors, uses exactly \(d+2\) independent samples in the configuration of (4). Therefore

\[
 \mathbb E_\mu H\le N_dD.                                \tag{5}
\]

The map \(H\) is measurable; in fact it is continuous on the compact support of \(\mu\), by continuity of determinants and dominated convergence.

Suppose now that \(V(W)>0\), and let \(\alpha_i(x)\) be the barycentric coordinates of \(x\) in this anchor simplex. For the first kind of witness, determinant affinity gives exactly

\[
 \psi=V(W)\min(1,(-\alpha_i(x))_+).                       \tag{6}
\]

For the pair \(i<j\), determinant expansion gives the two tested determinants, up to one common orientation sign, as

\[
 V(W)\alpha_j(x),\qquad -V(W)\alpha_i(x).
\]

Hence this pair witness is exactly

\[
 V(W)\bigl[
 \min((\alpha_i)_+,(\alpha_j)_+)
 +\min((-\alpha_i)_+,(-\alpha_j)_+)
 \bigr].                                                \tag{7}
\]

In particular, with

\[
 \phi_W(x)=
 \sum_i\min(1,(-\alpha_i(x))_+)
 +\sum_{i<j}\min((\alpha_i(x))_+,(\alpha_j(x))_+),
\]

we have

\[
 V(W)\phi_W(x)\le G(W,x).                               \tag{8}
\]

The extra negative-negative contribution in (7) is nonnegative and can be discarded.

## 3. The clipping issue disappears after capping the metric distance

Choose \(r=r(x)\) to maximize \(\alpha_i(x)\), resolving ties by the least index. Since \(\sum_i\alpha_i=1\), its maximum is positive. This selection is Borel.

Let

\[
 N_x=\sum_i(-\alpha_i(x))_+,\qquad
 U_x=\sum_{i\ne r}(\alpha_i(x))_+.
\]

Because \(\alpha_r>0\), the affine decomposition gives

\[
 x-w_r=\sum_{i\ne r}\alpha_i(x)(w_i-w_r),
 \qquad
 \|x-w_r\|\le\Lambda(N_x+U_x).                           \tag{9}
\]

There is also the independent bound \(\|x-w_r\|\le\Lambda\), since both points lie in \(\mathcal S\). Combining them,

\[
 \|x-w_r\|\le\Lambda\min(1,N_x+U_x).                     \tag{10}
\]

For arbitrary nonnegative \(n_i\),

\[
 \min\bigl(1,\sum_i n_i\bigr)\le\sum_i\min(1,n_i).
\]

Also, because \(r\) is a largest positive coefficient, the pairs containing \(r\) already give

\[
 U_x=\sum_{i\ne r}\min((\alpha_r)_+,(\alpha_i)_+)
 \le\sum_{i<j}\min((\alpha_i)_+,(\alpha_j)_+).
\]

Therefore

\[
 \min(1,N_x+U_x)
 \le\min(1,N_x)+U_x
 \le\phi_W(x).
\]

Together with (8) and (10), this proves the pointwise estimate

\[
 \boxed{\quad
 \|x-w_{r(x)}\|\le\Lambda\phi_W(x)
 \le\Lambda\frac{G(W,x)}{V(W)}.
 \quad}                                                  \tag{11}
\]

Equivalently: if a negative coefficient has magnitude at least one, its clipped witness already pays for the entire diameter-bounded distance. If none does, clipping is inactive and the usual barycentric estimate applies. A potentially enormous negative barycentric coefficient cannot cause a loss.

Integrating (11), for every nonsingular anchor tuple,

\[
 h(W):=\int\|x-w_{r(x)}\|\,d\nu(x)
 \le\Lambda\frac{H(W)}{V(W)}.                            \tag{12}
\]

No conditioning property of \(W\) was used.

## 4. Volume-weighted selection: existence, nonatomic laws, and zero defect

The full-dimensional support contains an affinely independent tuple. Continuity of \(V\), together with the definition of support, gives a positive-product-measure neighborhood on which \(V>0\). Thus

\[
 B=\mathbb E_\mu V>0.
\]

Introduce the probability measure

\[
 d\widehat\mu(W)=\frac{V(W)}{B}\,d\mu(W).
\]

It is concentrated on support tuples with \(V(W)>0\). Define \(R(W)=H(W)/V(W)\) there; its arbitrary value on \(V=0\) does not affect \(\widehat\mu\). Then

\[
 \mathbb E_{\widehat\mu}R
 =\frac{\mathbb E_\mu[H\mathbf1_{\{V>0\}}]}{B}
 \le\frac{\mathbb E_\mu H}{B}
 \le N_d\frac{D}{B}.                                    \tag{13}
\]

The restriction indicator in this equality is important. One need not and should not assume that \(H=0\) on every singular anchor tuple.

Any integrable real random variable has at least one point in its probability-one domain where its value is at most its expectation: otherwise the nonnegative difference from that expectation would be strictly positive almost surely and have positive integral. Applying this fact to (13), there exists a tuple \(W\in\mathcal S^{d+1}\) with

\[
 V(W)>0,\qquad \frac{H(W)}{V(W)}\le N_d\frac{D}{B}.
\]

Combining with (12) proves (1). This is an existence argument under a finite probability measure, not a compact-minimum claim for a ratio near singular tuples. It works without atoms and requires no quantitative lower bound on the selected determinant.

**The case \(D=0\).** Equation (5), nonnegativity, and \(\widehat\mu\ll\mu\) imply \(H=0\) for \(\widehat\mu\)-almost every tuple. Such tuples automatically have \(V>0\). Select any one. Equation (12) gives \(h=0\), so the law is supported on its \(d+1\) anchors. Since they belong to the support and are affinely independent, all their probabilities are positive. Their centered weighted sum is zero, so zero lies in the interior of their simplex. This also proves equality rigidity directly.

## 5. Quantitative origin-in-hull guarantee

Now use the Euclidean norm and define the one-sided directional first-moment dispersion

\[
 \delta=\inf_{\|u\|_2=1}\int(u\cdot x)_+\,d\nu(x).
\]

For a centered full-dimensional bounded law, \(\delta>0\): a vanishing directional expectation would, by centering, force the support into a hyperplane; continuity in \(u\) and compactness of the unit sphere make the infimum positive.

Let the assignment from (1) have cost \(h\), and let \(T=\operatorname{conv}(w_0,\ldots,w_d)\). The positive-part function is one-Lipschitz, so for every unit \(u\),

\[
 \mathbb E(u\cdot w_{I(X)})_+\ge\delta-h.
\]

If \(h<\delta\), the right side is positive. At least one anchor then satisfies \(u\cdot w_i\ge\delta-h\). The support-function characterization of containment yields

\[
 \boxed{\quad (\delta-h)B_2^d\subset T.\quad}             \tag{14}
\]

In particular, when \(h\le\delta/2\), the selected anchors contain \((\delta/2)B_2^d\). The geometric conditioning is a consequence of small assignment error and dispersion. It need not be imposed while selecting anchors.

For an arbitrary centered law, dispersion can be very poor. Claiming polynomial Euclidean conditioning for all such laws would be false because linear compressions preserve \(D/B\) while making Euclidean directional dispersion arbitrarily small. This observation is only about arbitrary-law geometry. It is not a convex-body obstruction under the normalization of the supplied proof.

## 6. Actual cone laws have polynomial dispersion in the available normalization

For the body in the supplied proof, use

\[
 B_2^d\subset K\subset R_0 B_2^d,
 \qquad R_0=d(d+1).
\]

Its cone law is centered, supported on \(\partial K^\circ\subset B_2^d\), and satisfies Cauchy's formula

\[
 \mathbb E(u\cdot X)_+
 =\frac{|K\mid u^\perp|_{d-1}}{d|K|}.
\]

By integration along lines parallel to \(u\),

\[
 |K|\le \operatorname{width}_u(K)\,|K\mid u^\perp|_{d-1}
 \le 2R_0\,|K\mid u^\perp|_{d-1}.
\]

Therefore

\[
 \delta\ge\frac1{2dR_0}.                                 \tag{15}
\]

Set

\[
 b_*:=\frac1{4dR_0},\qquad M_*:=4dR_0,
 \qquad Q_*:=(d+1)^2(d+2).
\]

Equations (2), (14), and (15) give the complete replacement statement:

\[
 h\le Q_*e(K),\qquad
 Q_*e(K)\le b_*\ \Longrightarrow\
 b_*B_2^d\subset T\subset B_2^d.
\]

Consequently \(P=T^\circ\) is an enclosing simplex satisfying

\[
 B_2^d\subset K\subset P\subset M_*B_2^d.
\]

Because each anchor lies in \(\partial K^\circ\), it obeys \(h_K(w_i)=1\), exactly as required by the subsequent first-variation and projection arguments in the supplied proof. Its barycentric coordinates of zero are strictly positive, so the formula for the cone law of \(P\) applies unchanged.

The denominator \(B\) must be preserved until using

\[
 \frac{D}{B}
 =\frac{(d+1)e(K)}{1+(d+1)e(K)}.
\]

Replacing \(D\) by \((d+1)e(K)\) too early would discard the scale-free information on which the improved selection depends.

The main proof, [POLYNOMIAL_REFINEMENT.md](POLYNOMIAL_REFINEMENT.md), assembles the remaining endpoint conversion and its explicit polynomial global constant. This report establishes the new assignment/inradius input in full and does not duplicate that assembly.

## 7. Additional interpretations and verification

- Let \(p_i=\mathbb P(I(X)=i)\). The theorem provides a coupling between \(\nu\) and a law supported on \(d+1\) affinely independent points with Wasserstein-1 cost at most the right side of (1).
- Since nearest-anchor assignment can only decrease the cost, for any \(t>0\), the mass at distance greater than \(t\Lambda\) from all anchors is at most \(N_d(D/B)/t\).
- The defect ratio \(D/B\) is invariant under invertible linear changes of coordinates of a centered law. For an uncentered bounded law, the same statement applies after subtracting its mean in the definition of \(A\); the affine determinant \(B\) is translation invariant.
- The theorem works in any norm, with that norm's support diameter. Euclidean structure enters only the convenient ball formulation of (14).
- An exact rational check covered 37,448 barycentric vectors in dimensions 1 through 5 and verified \(\min(1,N+U)\le\phi\), including large negative coefficients. This is a regression check only. The analytic inequalities above establish the unrestricted statement.

## 8. Exact stress tests: rare mass, thin directions, and singular tuples

These are **arbitrary centered probability-law regressions**. No claim is made that the laws containing an atom at zero are cone laws of full-dimensional convex bodies; they cannot be, since a cone law is supported on a polar boundary away from zero. The examples test the stronger probabilistic theorem, not convex-body realizability or an obstruction to the convex-body result.

A companion exact-arithmetic checker, `check_weighted_anchors.py`, enumerates all ordered anchor triples and test points for the following two-dimensional laws. It verifies \(A,B,D,\mathbb EV^2\), the pointwise clipped inequality, \(h(W)\le\Lambda H(W)/V(W)\) on every nonsingular tuple, the genuine volume-weighted expectation, and existence of a qualifying tuple. It passed all ten listed parameter cases.

### 8.1 A centered simplex with arbitrarily rare essential directions

Let \(0<t\le1/4\), and put

\[
 a=e_1,\quad b=e_2,\quad c=-t(e_1+e_2),
 \qquad
 p_a=p_b=\frac{t}{1+2t},\quad p_c=\frac1{1+2t}.
\]

This law is centered. Its essential positive-coordinate atoms have probabilities tending to zero. For a nonsingular ordered triple the three sampled points must be distinct, and its determinant is \(1+2t\). Direct enumeration gives

\[
 A=B=\frac{6t^2}{(1+2t)^2},\qquad D=0,
 \qquad
 \mathbb P(V>0)=\frac{6t^2}{(1+2t)^3},
 \qquad
 \mathbb EV^2=\frac{6t^2}{1+2t}.
\]

Thus ordinary nonsingular sampling has probability tending to zero quadratically, while the volume-weighted law gives probability one to exact copies of the supporting triangle. The selected assignment has \(h=0\). No fixed nonsingular-sampling probability and no positive lower bound on \(B\) is required.

The checker used \(t=1/4,1/100,1/10000\). For example, at \(t=1/10000\), \(B=1/16673334\), whereas \(\mathbb EV^2=1/16670000\). These are distinct moments, both explicitly computed.

### 8.2 Positive defect, rare mass, and genuinely huge negative barycentric coordinates

Mix the preceding law with an atom of mass \(\eta\) at zero, multiplying its original probabilities by \(1-\eta\), where \(0<\eta<1/2\). Write

\[
 A_0=\frac{6t^2}{(1+2t)^2}.
\]

Because the original law is centered, the new law remains centered. Expanding by the number of zero samples gives exactly

\[
 A=(1-\eta)^2A_0,
 \qquad
 B=(1-\eta)^2(1+2\eta)A_0,
 \qquad
 D=2\eta(1-\eta)^2A_0,
 \qquad
 \frac DB=\frac{2\eta}{1+2\eta},
\]

and independently

\[
 \mathbb EV^2=\frac{6t^2(1-\eta)^2}{1+2t}.
\]

There are four unordered nonsingular anchor types. Under the volume-weighted law, the probability of the original triangle \(\{a,b,c\}\) is

\[
 \frac{1-\eta}{1+2\eta},
\]

while each of \(\{0,a,b\},\{0,a,c\},\{0,b,c\}\) has probability

\[
 \frac{\eta}{1+2\eta}.
\]

These are computed using \(V\), not \(V^2\). For comparison, the \(V^2\)-weighted probabilities would instead be \(1-\eta\), \(\eta/(1+2t)\), \(\eta t/(1+2t)\), and \(\eta t/(1+2t)\), respectively. Substituting the second-moment weighting would change the argument.

Use the infinity norm, so the support diameter is \(\Lambda=1+t\). For the original triangle,

\[
 \frac HV=\frac{3\eta t}{1+2t},\qquad h=\eta t.
\]

For each of the other three unordered anchor types,

\[
 \frac HV=\frac{3(1-\eta)t}{1+2t}.
\]

In particular, relative to the anchors \((0,a,c)\), the omitted point \(b\) has barycentric coordinates

\[
 (2+1/t,-1,-1/t).
\]

The negative coefficient \(-1/t\) diverges as \(t\downarrow0\). Nevertheless its distance from the assigned anchor zero is exactly one, its full normalized witness is three, and the assignment cost for this tuple is

\[
 h=\frac{(1-\eta)t}{1+2t}.
\]

This explicitly tests the former clipping failure mode and shows why the diameter cap fixes it. The actual weighted expectation is

\[
 \mathbb E_{\widehat\mu}\frac HV
 =\frac{12\eta(1-\eta)t}{(1+2\eta)(1+2t)}
 \le 6\frac DB.
\]

The checker used \(\eta=1/100\) and the same three values of \(t\). At \(t=1/10000\), its selected triangle has \(H/V=1/333400\) and \(h=1/1000000\), while \(6D/B=2/17\). The small absolute first moments and the large barycentric coefficients create no selection loss.

### 8.3 Near-degenerate nonzero-defect laws

Give each corner of the rectangle \(\{(\pm1,\pm s)\}\) mass \(1/4\), with \(0<s\le1\). Direct enumeration gives

\[
 A=s,\qquad B=\frac32s,\qquad D=\frac12s,
 \qquad \frac DB=\frac13,
 \qquad \mathbb EV^2=6s^2.
\]

Every nonsingular triple has \(V=4s\) and \(H/V=1/2\), even as its determinant tends to zero. The fourth corner has barycentric coefficients \((1,-1,1)\) in a suitable anchor ordering. With the ordering whose largest-positive tie selects the nearer vertical neighbor, the infinity-norm assignment cost is \(h=s/2\). Other orderings can have larger cost, and the checker verifies the bound for all of them.

The selected-triple estimate remains \(H/V=1/2\le6D/B=2\) independently of \(s\). The exact tests used \(s=1,1/100,1/10000\). This also makes the moment distinction conspicuous: \(B\) scales linearly with \(s\), while \(\mathbb EV^2\) scales quadratically.

### 8.4 A singular tuple with strictly positive witness cost

Give each point of \(\{0,\pm e_1,\pm e_2\}\) mass \(1/5\). Then

\[
 A=\frac8{25},\qquad B=\frac{72}{125},\qquad
 D=\frac{32}{125},\qquad \mathbb EV^2=\frac{24}{25}.
\]

The anchor tuple \((-e_1,0,e_1)\) has \(V=0\), but \(H=2/5\): for either test point \(\pm e_2\), the pair witness using the two endpoints and the middle anchor is one. This proves that replacing the restricted expectation in (13) by an asserted equality with \(\mathbb EH/B\) would be incorrect.

Exact enumeration yields

\[
 \mathbb E[H\mathbf1_{\{V=0\}}]=\frac{24}{625},\qquad
 \mathbb E[H\mathbf1_{\{V>0\}}]=\frac{168}{625},\qquad
 \mathbb EH=\frac{192}{625}.
\]

Accordingly,

\[
 \mathbb E_{\widehat\mu}(H/V)
 =\frac{\mathbb E[H\mathbf1_{\{V>0\}}]}{B}
 =\frac7{15}
 \le 6D/B=\frac83.
\]

The volume-weighted law gives the singular, positive-cost tuples zero mass, exactly as the proof requires.

### 8.5 Why an integrated conclusion does not imply support concentration

In any dimension, let \(\nu_0\) give equal mass to the \(d+1\) vertices of a regular simplex centered at zero, with each vertex of norm one. Then \(B_0=A_0>0\). For

\[
 \nu_\varepsilon=(1-\varepsilon)\nu_0+\varepsilon\delta_0,
 \qquad 0<\varepsilon<1,
\]

expansion by the number of zero samples yields

\[
 A_\varepsilon=(1-\varepsilon)^dA_0,
 \qquad
 B_\varepsilon=(1-\varepsilon)^d(1+d\varepsilon)A_0,
 \qquad
 \frac{D_\varepsilon}{B_\varepsilon}
 =\frac{d\varepsilon}{1+d\varepsilon}\longrightarrow0.
\]

Yet its support always consists of the same \(d+2\) points, with every pair at distance at least one. Any choice of \(d+1\) support anchors omits a point at distance at least one from all its anchors. Even \(d+1\) arbitrary centers cannot cover these \(d+2\) points with balls of radius strictly less than \(1/2\). Thus vanishing defect does not force the full support to lie near \(d+1\) points in Hausdorff distance. The valid conclusion is integrated concentration, as in (1).

For \(0<\varepsilon\le1/(d+2)\), the original simplex anchors achieve \(h=\varepsilon\), by assigning zero to any vertex. Any other support-anchor choice omits a vertex of mass \((1-\varepsilon)/(d+1)\ge\varepsilon\), at distance at least one from every remaining anchor. Thus the optimal assignment cost among \(d+1\) support anchors is exactly \(\varepsilon\). In particular, the general theorem's linear order in \(D/B\) cannot be improved to a higher power, even with constants depending on fixed dimension.

This is an **arbitrary-law limitation only**. The atom at zero precludes cone-law realization for a full-dimensional convex body. It does not obstruct the actual cone-law theorem, and it does not say that the convex hull is far from a simplex: the convex hull here is exactly the original simplex for every \(\varepsilon\).

## Source and changes

Inspected source: [sources/sharp-simplex-proof.tex](../sources/sharp-simplex-proof.tex), pinned in [SOURCE_PINS.json](../SOURCE_PINS.json), especially its integrated-assignment section.

The determinant cancellation identity and integrated witness are retained. The new points are the diameter-capped pointwise estimate (11), volume-weighted selection (13), and their combination (1). The actual cone-law dispersion bound (15) uses only the displayed Cauchy identity and elementary fiber integration. No external stability theorem is used in this argument.
