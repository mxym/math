# A finite rational-duality obstruction to sharp positive-power Bellman envelopes

**Research note, 8 October 2026.** AI-assisted independent continuation of entry 005. The affine projection-body product calculus and the certified binary \(T_5\) rate are inherited from previously published 005 results. The new all-degree no-go theorem and the infinite-series obstruction below are proved with standard-library exact arithmetic. This note makes no journal-priority, human-refereeing, or complete Lean-formalization claim.

## Abstract

The unrestricted projection-body growth problem for the point-generated Cartesian-product/affine-join class remains open. A leading method is to certify a dimension-homogeneous convex Bellman potential by **separate closure under every possible join and product**, with nonnegative even-power coefficients. We prove a **strict, all-degree obstruction** to this proof architecture: for *any* finite or countably summable sequence of nonnegative coefficients, the nominal logarithmic rate must be **strictly larger than \(486139/10^7=0.0486139\)** if the potential is product-closed even merely at self-products of three explicit, actually attainable polytopes. This barrier is strictly above the previously certified binary \(T_5\) orbit rate. The proof uses three rational self-product constraints and positive rational dual weights; six even-degree columns are checked individually, **all infinitely many remaining powers** are controlled by elementary rational geometric tails, and the decisive weighted logarithms are enclosed by a separate exact atanh checker. Stronger still, we determine the **exact minimum for the infinite linear programme defined by these three necessary inequalities**: it has a uniquely supported primal solution in degrees **2, 4, 8** and an exact rational dual, yielding the stronger certified floor. No finite extrapolation is involved. Furthermore, a Bertrand-prime argument proves that **no finite polynomial or finite-knot polynomial spline**, with **arbitrary signed real coefficients**, can satisfy a sharp independent join/product Bellman induction. An all-orders Stirling–Bernoulli argument strengthens this to **every real-analytic germ**, including infinite convergent power series: the orbit multipliers have infinitely many rationally linearly independent logarithms, forcing infinitely many independent profile parameters.

Moreover we prove a **Stirling–Bernoulli nonanalyticity theorem**: no real-analytic homogeneous scalar profile at zero, even with infinitely many convergent signed coefficients, can be an exactly sharp separately inductive Bellman potential. For a smooth hypothetical profile we uniquely determine its **entire divergent formal even Taylor jet**, with exact rational recurrences and the first six nonzero coefficients certified.

We also derive the **exact scalar binary-orbit continuation functional**. Its naturally associated upper-potential candidate, which would be sharp at every point of the \(T_5\) orbit, is **not** superadditive under joins: a join of two copies of the attainable polytope \(T_1\times T_2\) yields a rigorously certified defect below \(-3/10\). This is a failure of two particular **inductive proof mechanisms**, not a counterexample to global optimality of the \(T_5\) orbit. The observations identify why simply adding many positive higher-power terms or reusing the exact binary continuation value cannot close the unrestricted problem without additional state information or a different convex potential.

## 1. Exact state rules and the Bellman induction being tested

For a \(d\)-dimensional convex polytope \(K\), let \(R(K)=|\Pi K|/|K|^{d-1}\), where \(\Pi K\) denotes its projection body. Set \(g(d)=d^d/d!\) and use the inherited affine cone invariant \(a(K)\) from [005 version 2](../../preprints/005-simplex-product-optimum/v2/paper.md). Write
\[
 D=d+1,\qquad H=1/a(K),\qquad Q=a(K)R(K)/g(d).
 \tag{1.1}
\]
Every positive-dimensional point-generated body has \(2\le H\le D\); the formal point has \((D,H,Q)=(1,1,1)\). The exact formulas imported from 005 v2 are
\[
 (D,H,Q)(A*B)=(D_A+D_B,H_A+H_B,Q_AQ_B)
 \tag{1.2}
\]
for joins, and, for Cartesian products with positive factor dimensions \(r,s\), \(n=r+s\), factor states \((H,Q)=(h,u)\), \((j,v)\),
\[
 H'=\frac{n}{r/h+s/j},\qquad
 Q'=uv\,\frac{g(r)g(s)}{g(n)}\frac{sh+rj}{n}.
 \tag{1.3}
\]
Only invertible affine maps on affine hulls are included in the construction class.

Consider **any** finite or infinite nonnegative coefficient family
\[
 a_k\ge0\quad(k\ge1),\qquad
 T:=\sum_{k\ge1}a_k<\infty,
\]
and the potential
\[
 \boxed{\Phi_a(D,H)=\sum_{k\ge1} a_k
 \left(D-\frac{H^{2k}}{D^{2k-1}}\right).}
 \tag{1.4}
\]
The series converges absolutely for every reachable state, since \(0\le H/D\le1\). It vanishes at the formal point, is nonnegative and obeys \(\Phi_a(D,H)\le TD\). Because \(t\mapsto t^{2k}\) is convex, (1.4) is automatically **join-superadditive** by weighted Jensen:
\[
 \Phi_a(D_A+D_B,H_A+H_B)\ge
 \Phi_a(D_A,H_A)+\Phi_a(D_B,H_B).
\]
If one further proves the **one-step product condition**
\[
 \boxed{\Phi_a(n+1,H')-\Phi_a(r+1,h)-\Phi_a(s+1,j)
 \ge\log\left(\frac{g(r)g(s)}{g(n)}\frac{sh+rj}{n}\right)}
 \tag{1.5}
\]
for all realizable operand states, induction from the point gives \(\log Q(K)\le\Phi_a(D(K),H(K))\le TD(K)\). The inherited spectral reduction then gives the growth upper bound \(\Gamma_{\mathcal C}\le e^{1+T}\).

The theorem below restricts only the **standard separate product-closure proof obligation** (1.5), *not* all possible ways of bounding \(Q\). In particular, a proof that uses slack depending on the actual factor \(Q\)-values may be immune to this obstruction.

## 2. Three geometrically attained operand states

The following three positive-dimensional states are actual point-generated polytopes; none is a fabricated value in a continuous relaxation:

| \(r\) | \(h=H(K)\) | An explicit construction |
|---|---|---|
| \(5\) | \(6\) | \(K_1=T_5\) |
| \(13\) | \(10\) | \(K_2=(T_4\times T_4)*T_4\) |
| \(36\) | \(133/8\) | \(K_3=\text{point}*(T_5\times T_5)*[T_6\times(\text{point}*(T_4\times T_4)*(T_4\times T_4))]\) |

These identities follow by direct substitution in (1.2)–(1.3). For example, inside \(K_3\), the join of the point and two \(T_4\times T_4\) blocks has dimension \(18\) and \(H=1+5+5=11\). Its product with \(T_6\) has dimension \(24\) and \(H=24/(6/7+18/11)=77/8\). Adding the outer point and \(T_5\times T_5\) block gives \(D=1+11+25=37\), i.e. dimension 36, and \(H=1+6+77/8=133/8\). Their attainability is also cross-checked against the older fully certified 48-dimensional Pareto source file, pinned by SHA-256 in the checker.

Apply (1.5) to the Cartesian square of each \(K_i\). When \(r=s\), \(h=j\), the output state has \(H'=h\) and its exact product multiplier is
\[
 M(r,h)=h\frac{g(r)^2}{g(2r)}
 =h\frac{\binom{2r}{r}}{4^r}.
 \tag{2.1}
\]
The contribution of a single coefficient \(a_k\) to the product-side difference is the rational number
\[
 b_{r,h}(k):=
 h^{2k}\left(\frac{2}{(r+1)^{2k-1}}-
 \frac{1}{(2r+1)^{2k-1}}\right)-1.
 \tag{2.2}
\]
Therefore three **necessary** conditions for any potential satisfying (1.5) are
\[
 \boxed{\sum_{k\ge1}a_k b_{r_i,h_i}(k)
 \ge\log M(r_i,h_i),\quad i=1,2,3.}
 \tag{2.3}
\]
The right sides are logarithms of explicit rational numbers, not floating-point solver inputs.

## 3. An all-degree rational dual certificate

**Theorem 1 (positive-even-power Bellman obstruction).** Let \((a_k)_{k\ge1}\) be any finite or countably infinite family of nonnegative real coefficients with finite sum \(T\), and suppose the Bellman potential (1.4) satisfies the product closure condition (1.5) for every *actually attainable* pair of operands. Then
\[
 \boxed{T>\frac{48613}{10^6}=0.048613.}
 \tag{3.1}
\]
Consequently this proof architecture **cannot certify** a projection-body growth ceiling below \(e^{1+48613/10^6}\). This threshold lies **strictly above** the certified upper endpoint of the binary \(T_5\) construction, so adding arbitrary positive even powers to the existing full-state product Bellman potential cannot prove that construction globally optimal.

**Proof.** Use the following explicitly positive rational dual weights:
\[
 \boxed{(w_1,w_2,w_3)=\frac1{10^6}(93264,3651,24062).}
 \tag{3.2}
\]
For an even exponent \(p=2k\), set
\[
 B_p=\sum_{i=1}^3w_i b_{r_i,h_i}(k).
\]
We claim
\[
 \boxed{B_p<1\quad\text{for every even }p\ge2.}
 \tag{3.3}
\]
For \(p=2,4,6,8,10,12\), the accompanying checker evaluates the rational expressions (2.2) and proves (3.3) by exact integer/Fraction arithmetic. There are no unverified intermediate exponents.

For every even \(p\ge14\), the equal-factor expressions yield the elementary strict bounds
\[
\begin{aligned}
 b_{5,6}(p)&=11-6(6/11)^{p-1}\le11,\\
 b_{13,10}(p)&=20(5/7)^{p-1}-10(10/27)^{p-1}-1
 \le20(5/7)^{p-1}-1,\\
 b_{36,133/8}(p)&=\frac{133}{4}(133/296)^{p-1}
 -\frac{133}{8}(133/584)^{p-1}-1
 \le\frac{133}{4}(133/296)^{p-1}-1.
\end{aligned}
\]
Because \(0<5/7,133/296<1\), it suffices to bound these at \(p=14\). The checker establishes the single exact rational inequality
\[
 \boxed{11w_1-w_2-w_3+
 20w_2(5/7)^{13}+
 \frac{133}{4}w_3(133/296)^{13}<1,}
 \tag{3.4}
\]
proving (3.3) **uniformly for all remaining degrees**. Thus (3.3) is an infinite-degree theorem, not a finite-degree extrapolation.

Multiply the three necessary inequalities (2.3) by \(w_i\), sum them, and interchange the absolutely convergent sums. We get
\[
 \sum_iw_i\log M(r_i,h_i)
 \le\sum_{k\ge1}a_k B_{2k}
 \le\sum_{k\ge1}a_k=T.
 \tag{3.5}
\]
The remaining real-number comparison is proven with independently replayable rational logarithm intervals:
\[
 \boxed{\sum_iw_i\log\left(h_i\binom{2r_i}{r_i}4^{-r_i}\right)
 >\frac{48613}{10^6}.}
 \tag{3.6}
\]
The checker uses the positive atanh series \(\log y=2\sum_{j\ge0} z^{2j+1}/(2j+1)\), \(z=(y-1)/(y+1)\), with an **exact** tail bound and exact power-of-two normalization, so (3.6) does not rely on floating-point evaluation. Equations (3.5)–(3.6) prove (3.1). \(\square\)

The earlier 005 v5/sharpened-lower replay certifies \(\Gamma_{T_5}<2.853465550704\). To compare without numerical logarithms, the new checker also verifies
\[
 \boxed{\sum_{j=0}^{17}\frac{(1+48613/10^6)^j}{j!}
 >2.853465550704.}
 \tag{3.7}
\]
The left side is a rational *strict lower bound* for \(e^{1+48613/10^6}\), showing that the obstruction is separated from the binary orbit by a genuine provable gap. This **does not show** the binary orbit is optimal or that the true full-class value exceeds it; it shows the specified *method family* cannot decide equality at its sharp predicted value.

### Theorem 1.1 (exactly solved three-state infinite-power relaxation)

The three inequalities (2.3), considered **by themselves** as an optimization problem over all finite or summable nonnegative even-degree coefficients, have an exactly solvable optimum. Let
\[
 p_1=2,\quad p_2=4,\quad p_3=8,\qquad
 M_{ij}=b_{r_i,h_i}(p_j/2),
\]
where the columns are the exact rational coefficients in (2.2), and put
\[
 L_i=\log M(r_i,h_i),\qquad
 w^*=(M^T)^{-1}\begin{pmatrix}1\\1\\1\end{pmatrix}.
\]
The matrix \(M\) is invertible over \(\mathbb Q\), all three entries of \(w^*\) are **strictly positive rational numbers**, and the exact optimal value of the restricted three-state problem is
\[
 \boxed{T_{\mathrm{three}}=\sum_{i=1}^3 w_i^*L_i
 >\frac{486139}{10^7}=0.0486139.}
 \tag{3.8}
\]
Its **unique nonnegative optimizing coefficient sequence** has support exactly in degrees \(2,4,8\), with corresponding three coefficients
\[
 \begin{pmatrix}a_1\\a_2\\a_4\end{pmatrix}=M^{-1}
 \begin{pmatrix}L_1\\L_2\\L_3\end{pmatrix}>0,
 \qquad a_k=0\quad(k\notin\{1,2,4\}).
 \tag{3.9}
\]

**Proof.** The separate exact checker [`check_sharp_dual.py`](code/check_sharp_dual.py) uses rational Cramer's rule to compute \(w^*\) from the 3-by-3 matrix. It verifies the three equalities
\[
 \sum_i w_i^* b_{r_i,h_i}(k)=1\qquad(k=1,2,4)
\]
and the **strict inequalities**
\[
 \sum_iw_i^*b_{r_i,h_i}(k)<1
 \qquad(k=3,5,6,7,8,9,\ldots).
\]
The cases \(k=1,2,3,4,5,6\) are exact rational checks; for every \(k\ge7\), the same monotone geometric estimate as (3.4), now evaluated with \(w^*\), proves the strict bound. Thus the dual vector \(w^*\) is feasible against **infinitely many** columns and yields the lower value \(w^*\cdot L\) for every feasible nonnegative coefficient sequence.

The matrix inverse applied to the logarithm vector \(L\) gives the primal sequence (3.9). Its three entries are shown **strictly positive** by explicitly enclosing each rational logarithm in a positive-term atanh interval, multiplying by the exact rational inverse, and checking the resulting rational lower bounds. This finite sequence meets all three original constraints (2.3) **with equality**, proving that its objective \(T\) attains the dual lower value \(w^*\cdot L\). Any optimum with positive coefficient outside \(k\in\{1,2,4\}\) would be strictly larger than its dual lower value, by the strict dual inequalities. Hence every optimizer is supported on those three powers, and invertibility of \(M\) proves uniqueness. Finally the checker certifies (3.8) by a strict rational logarithm lower bound. \(\square\)

**Interpretation.** The exact optimal value \(T_{\mathrm{three}}\) belongs to the *relaxation using only the three explicit necessary product tests*. Full Bellman product closure imposes **many more inequalities**, so this is a rigorous **lower bound** on the true infimum of Bellman coefficients, *not* a proof that the three-degree polynomial in (3.9) closes the global Bellman induction. In particular, Theorem 1 can be strengthened to the strict floor \(T>0.0486139\) in its stated full-product-closure setting. The two exact checkers independently report a simpler coarse dual and the exact three-test primal-dual optimum; both remain useful adversarial regression certificates.

## 4. The exact binary-tail functional and a second obstruction

A natural attempt to escape polynomial coefficient optimization is to use the **exact value** of continuing any initial body forever with the binary \((K\times K)*(K\times K)\) operation. For a seed with state \((d,H,Q)\), define
\[
 d_j=\frac{(3d+1)4^j-1}{3},\qquad
 G(d)=\frac29\log2+
 2\sum_{j\ge0}4^{-j-1}\log\frac{g(d_j)^2}{g(2d_j)}.
 \tag{4.1}
\]
Robbins's factorial estimates imply absolute convergence because the summands grow at most linearly in \(j\) while the weights decay as \(4^{-j}\). From (1.2)–(1.3), direct iteration gives the exact binary-orbit limit
\[
 \boxed{q_\infty(d,H,Q)=
 \frac{\log Q+(2/3)\log H+G(d)}{d+1/3}.}
 \tag{4.2}
\]
Here \(q_\infty\) is the limit of \(\log Q_j/(d_j+1)\), equivalently the logarithm of the limiting normalized spectral root. Let \(c_*:=q_\infty(5,6,1)\), the certified binary \(T_5\) orbit rate. The tempting **exact binary-tail upper potential** is
\[
 \boxed{\mathcal B(d,H)=c_*(d+1/3)-\frac23\log H-G(d).}
 \tag{4.3}
\]
The inequality \(\log Q(K)\le\mathcal B(d,H)\) is *equivalent* to saying that continuing from \(K\) by the binary recursion has limiting spectral rate no larger than that of the \(T_5\) binary recursion. If this inequality were established for every point-generated \(K\), the full-class optimum would follow by applying it to arbitrarily large self-joins of \(K\) and taking their limit. It is therefore a natural sharper alternative to (1.4).

**Theorem 2 (naive join induction fails for the exact binary-tail functional).** Even on realizable states, \(\mathcal B\) is **not** join-superadditive. Set \(A=T_1\times T_2\). The exact inherited product formulas give
\[
 (d,H,Q)(A)=(3,18/7,28/27),
 \qquad(d,H)(A*A)=(7,36/7).
\]
Then
\[
 \boxed{\mathcal B(7,36/7)-2\mathcal B(3,18/7)<-\frac3{10}.}
 \tag{4.4}
\]

**Proof.** The definition (4.3) gives the exact simplification
\[
 \mathcal B(7,36/7)-2\mathcal B(3,18/7)
 =\frac23c_*+\frac23\log(9/7)+2G(3)-G(7).
 \tag{4.5}
\]
The separate exact checker [`check_binary_tail.py`](code/check_binary_tail.py) proves (4.4) using \(12\) explicitly enclosed terms of each series in (4.1), Robbins's *rational* two-sided factorial remainder inequalities, and a closed-form geometric bound for the entire omitted infinite tail. It also verifies the required rational pi bracket using Machin's formula and positive/remainder-controlled logarithm intervals. No floating point enters the decision. The computed strict upper interval lies below \(-3/10\), proving the theorem. \(\square\)

Failure of join-superadditivity means one **cannot simply substitute** (4.3) into the ordinary join/product induction and declare an upper theorem. It does **not** establish any body with \(q_\infty>c_*\): an upper potential may have significant slack at an operand even when its bare algebraic join inequality fails. A sharper argument would have to retain those realizable-state slacks or use another invariant.

### Theorem 3 (exact orbit interpolation and forced quadratic curvature)

The negative result of Theorem 2 also exposes **positive structural information** about any potential sharp proof. Suppose \(\psi:[0,1]\to\mathbb R\) is convex and continuous, \(\psi(0)=0\), \(\psi(1)=c_*\), and
\[
 \boxed{\Phi_\psi(D,H)=D\left(c_*-\psi(H/D)\right)}
 \tag{4.6}
\]
is join-superadditive and satisfies the separate exact product-closure condition (1.5) at all actually attainable operands. Such a potential, if it exists, would imply the conjectured global rate ceiling \(e^{1+c_*}\). It is subject to an **infinite list of forced equalities** and a uniquely determined near-zero quadratic curvature.

Let \(K_0=T_5\), \(K_{j+1}=(K_j\times K_j)*(K_j\times K_j)\), and write its exact state as \((d_j,H_j,Q_j)\), \(D_j=d_j+1\), \(t_j=H_j/D_j\). Then
\[
 \boxed{\psi(t_j)=c_*-\frac{\log Q_j}{D_j}
 \quad\text{for every integer }j\ge0.}
 \tag{4.7}
\]
If moreover \(\psi(t)=\alpha t^2+o(t^2)\) as \(t\downarrow0\), necessarily
\[
 \boxed{\alpha=\frac8{81}\left(c_*+
 \frac12\log\frac{27}{4\pi}\right),\qquad
 \frac{4256}{100000}<\alpha<\frac{4257}{100000}.}
 \tag{4.8}
\]
The rational interval (4.8) is independently certified by `check_binary_tail.py` using the same explicit infinite-series tail estimates, the pi bracket and rational logarithm intervals.

**Proof.** Define the nonnegative induction slack along the orbit by
\[
 E_j=\Phi_\psi(D_j,H_j)-\log Q_j.
\]
The initial simplex \(K_0=T_5\) is a join of six points and \(\Phi_\psi(6,6)=6(c_*-\psi(1))=0=\log Q_0\), so \(E_0=0\). For every binary step, the exact product \(Q\)-formula and the assumed product and join closures give
\[
 \boxed{E_{j+1}\ge4E_j\ge0.}
\]
However, \(D_j=(16\cdot4^j+2)/3\), \(H_j=6\cdot2^j\), and by the definition of \(c_*\) we have \(\log Q_j/D_j\to c_*\). Since \(t_j\to0\), the continuity condition yields
\[
 \frac{E_j}{D_j}=c_*-\psi(t_j)-\frac{\log Q_j}{D_j}\longrightarrow0.
\]
If any \(E_j>0\), iteration gives \(E_{j+m}\ge4^mE_j\), whereas \(D_{j+m}/4^m\) converges to a positive finite constant; this contradicts \(E_{j+m}/D_{j+m}\to0\). Hence every \(E_j=0\), proving the interpolation identities (4.7) *exactly*, not just in the limit.

For the curvature, define the orbit's scalar deficit \(F_j=c_*D_j-\log Q_j\). The recursion from (1.2)–(1.3) gives
\[
 F_{j+1}=4F_j-2c_*-2\left(\log H_j+\log\frac{g(d_j)^2}{g(2d_j)}\right).
\]
The term in parentheses tends, by Robbins, to \(\log((3\sqrt3/2)/\sqrt\pi)=\frac12\log(27/(4\pi))\). The exact tail representation (4.1) shows that \((F_j)\) is bounded; the bounded solution of this affine fourfold recursion therefore converges to
\[
 \lim_{j\to\infty}F_j=\frac23\left(c_*+\frac12\log\frac{27}{4\pi}\right).
\]
By (4.7), \(F_j=D_j\psi(t_j)\). If \(\psi(t)\sim\alpha t^2\), then
\(F_j\to\alpha\lim H_j^2/D_j=(27/4)\alpha\), proving the exact expression (4.8). The strict rational interval is verified by the source checker. \(\square\)

This theorem does **not** assert that a convex sharp potential exists. Instead it converts that existence problem into a constrained **convex interpolation / product-closure problem** with infinitely many exact orbit anchors and a pinned quadratic germ. It explains why a finite perturbation of arbitrary polynomial coefficients can easily disrupt sharpness: along an extremal infinite orbit, *every intermediate induction slack must vanish*.

### Theorem 4 (prime-rank rigidity: no finite polynomial or finite-knot sharp Bellman profile)

The interpolation equations in Theorem 3 impose a stronger **infinite-rank** constraint, independent of any positivity, even-power or convexity assumption. Let
\[
 d_j=\frac{16\cdot4^j-1}{3},\qquad H_j=6\cdot2^j,
 \qquad D_j=d_j+1,\quad t_j=\frac{H_j}{D_j},
\]
and define the exact positive **rational multipliers**
\[
 \boxed{M_j=H_j\frac{g(d_j)^2}{g(2d_j)}
 =6\cdot2^j\frac{\binom{2d_j}{d_j}}{4^{d_j}}\in\mathbb Q_{>0}.}
 \tag{4.11}
\]

**Lemma 4.1 (infinite rational linear independence).** The sequence
\[
 \boxed{\{\log M_j:j=0,1,2,\ldots\}}
\]
is **linearly independent over \(\mathbb Q\)**. Equivalently, the countably infinite set of rational numbers \(M_j\) is multiplicatively independent: every finitely supported integer product \(\prod_jM_j^{n_j}=1\) has all \(n_j=0\).

**Proof.** By the classical **Bertrand postulate**, for every \(j\ge0\) there exists a prime \(p_j\) satisfying
\[
 d_j<p_j<2d_j.
\]
Since \(d_j=4d_{j-1}+1\), for every \(i<j\) we have \(2d_i<d_j<p_j\). Also \(p_j\ge7\), so \(p_j\) divides neither \(H_i=6\cdot2^i\) nor any denominator \(4^{d_i}\). Consequently \(v_{p_j}(M_i)=0\) whenever \(i<j\). On the other hand \(d_j<p_j<2d_j<2p_j\) implies
\[
 v_{p_j}\binom{2d_j}{d_j}=1,
 \qquad\boxed{v_{p_j}(M_j)=1.}
\]
In a nontrivial finite multiplicative relation let \(J\) be the *largest* index with nonzero exponent. Applying \(v_{p_J}\) gives \(n_J=0\), a contradiction. Taking logarithms gives the asserted \(\mathbb Q\)-linear independence. \(\square\)

**Theorem 4.2 (sharp profile requires infinitely many independent parameters).** Suppose \(\psi:[0,1]\to\mathbb R\) satisfies only the following hypotheses:

1. \(\psi\) is continuous at zero, with \(\psi(0)=0\) and \(\psi(1)=c_*\);
2. the homogeneous potential \(\Phi_\psi(D,H)=D(c_*-\psi(H/D))\) satisfies the **separate join and product closure inequalities** from (1.2)–(1.5), at least along the actual \(T_5\) orbit and its intermediate Cartesian squares.

Then **there is no** \(\varepsilon>0\) and no finite-degree polynomial \(P\in\mathbb R[t]\) such that \(\psi(t)=P(t)\) for all \(0<t<\varepsilon\). This excludes **all finite-degree homogeneous polynomial profiles, even with signed coefficients**, and **all convex (or nonconvex) splines with only finitely many polynomial pieces**, from being sharp using that ordinary independent join/product induction. Neither convexity nor differentiability of \(\psi\) is needed for this obstruction.

More generally, for any finite list of functions \(f_1,\ldots,f_m\) defined near zero with \(f_\ell(t_j)\in\mathbb Q\) for all sufficiently large \(j\), no such sharp \(\psi\) can satisfy \(\psi(t)=\sum_{\ell=1}^m a_\ell f_\ell(t)\) for real coefficients \(a_\ell\) near zero.

**Proof.** By the proof of Theorem 3, the nonnegative induction slack \(E_j=\Phi_\psi(D_j,H_j)-\log Q_j\) obeys \(E_{j+1}\ge4E_j\) and \(E_j/D_j\to0\). Hence \(E_j=0\) **for every** \(j\), so the exact interpolation identities (4.7) hold:
\[
 \log Q_j=D_j(c_*-\psi(t_j)).
\]
The exact binary operation is the join of two equal Cartesian squares; its \(Q\)-recurrence is
\[
 \log Q_{j+1}=4\log Q_j+2\log M_j.
\]
Substitute the interpolation identities and use \(D_{j+1}=4D_j-2\), obtaining
\[
 \boxed{\log M_j=-c_*+2D_j\psi(t_j)
 -\frac{D_{j+1}}2\psi(t_{j+1}).}
 \tag{4.12}
\]
All \(D_j\) and \(t_j\) are rational. If \(\psi=P\) is a real polynomial of degree at most \(m\) on an interval near zero, then for every sufficiently large \(j\), the right side of (4.12) lies in the fixed finite-dimensional \(\mathbb Q\)-vector space spanned by \(c_*\) and the \(m+1\) real coefficients of \(P\). This contradicts Lemma 4.1, since infinitely many \(\log M_j\) cannot all lie in a fixed finite-dimensional \(\mathbb Q\)-space. The identical argument applies to any finite list of functions with rational values on the eventual orbit points \(t_j\). Every function with finitely many polynomial spline pieces agrees with **one** polynomial on some interval immediately to the right of zero, so the stated spline exclusion follows. \(\square\)

**Significance and exact scope.** This is an *unconditional analytical no-go* for **all finite-degree polynomial and finite-knot piecewise-polynomial potentials**, not merely for the nonnegative even-power cone in Theorem 1. It does **not** exclude a genuinely infinite series, a non-polynomial germ or infinitely many knots accumulating at zero; nor does it exclude global proofs that retain attainable-state slack instead of demanding separate Bellman closure. The theorem also says nothing about the actual value of \(\lambda_*\): it proves that if the binary \(T_5\) orbit is globally optimal, its sharp induction cannot be realized by any finite polynomial/spline architecture of the stated kind.

The independent companion [`check_prime_independence.py`](code/check_prime_independence.py) replays exact \(p\)-adic valuation witnesses for thirteen consecutive orbit levels, using only integer trial-division primality and Legendre valuations. **The infinite theorem uses Bertrand's postulate**, not a finite computation; all other ingredients are the inherited exact product/join identities and the interpolation argument above.

**Corollary 4.3 (a strictly positive gap at each bounded polynomial degree).** Fix a finite integer \(m\ge1\). Among all **nondecreasing** real polynomial functions \(\psi:[0,1]\to\mathbb R\) of degree at most \(m\), normalized by \(\psi(0)=0\), \(\psi(1)=c\ge0\), whose homogeneous Bellman potential \(D(c-\psi(H/D))\) obeys ordinary separate join/product closure for every point-generated construction, there exists a constant \(\varepsilon_m>0\) such that
\[
 \boxed{c\ge c_*+\varepsilon_m.}
 \tag{4.13}
\]
This holds **without assuming the coefficients of the polynomial are nonnegative** and gives a *uniform obstruction at each fixed degree*, not merely an impossibility of equality.

**Proof.** Assume otherwise. By the inherited binary lower construction every such upper coefficient satisfies \(c\ge c_*\), so there would be admissible degree-\(m\) polynomial profiles \(\psi_n\) with endpoint values \(c_n=\psi_n(1)\downarrow c_*\). Nondecreasingness and \(\psi_n(0)=0\) imply
\(0\le\psi_n(t)\le c_n\) for every \(t\in[0,1]\). Choose \(m\) fixed distinct positive rational interpolation nodes \(t_i\in(0,1]\). The coefficient vector of \(\psi_n\), whose constant term is zero, is the inverse of a fixed, nonsingular Vandermonde-type matrix applied to the bounded vector \((\psi_n(t_i))_{i=1}^m\). Hence the coefficients are uniformly bounded. Passing to a subsequence, they converge to those of another degree-\(m\) polynomial \(\psi\), uniformly on \([0,1]\), with \(\psi(0)=0\), \(\psi(1)=c_*\).

Every individual join/product closure comparison is a continuous linear inequality in the coefficients of \(\psi_n\) and \(c_n\), with a fixed real logarithmic multiplier on the right. Therefore it survives coefficientwise limits, and \(\psi\) is a sharp separately closed polynomial Bellman potential. This contradicts Theorem 4.2. Thus the infimum of all admissible \(c\) at fixed degree is strictly greater than \(c_*\), proving (4.13). \(\square\)

No numerical value of \(\varepsilon_m\) is asserted: the corollary is a compactness theorem. It does **not** supply a uniform gap independent of degree \(m\), which would require substantially stronger control and is not claimed.

### Theorem 5 (no real-analytic sharp homogeneous Bellman germ)

The polynomial restriction in Theorem 4 can be dropped **entirely** at the cost of one additional classical analytic input: the full Euler–Maclaurin Stirling asymptotic expansion and the exact Euler formula for Bernoulli numbers. The resulting obstruction applies to **every convergent power series near the origin**, even of infinite degree.

**Theorem 5.1 (nonanalyticity is necessary for exact sharp induction).** Under the hypotheses of Theorem 4.2—namely, the exact binary \(T_5\) candidate rate \(c_*\), continuity \(\psi(0)=0\), normalization \(\psi(1)=c_*\), and ordinary separate product/join Bellman closure on the actual orbit—there is **no** \(\varepsilon>0\) for which \(\psi\) is **real analytic** on \((-\varepsilon,\varepsilon)\) about zero.

Thus a sharp one-state homogeneous Bellman potential, *if it exists*, must possess a **nonanalytic germ at \(H/D=0\)**. This excludes finite polynomials, real-analytic nonpolynomial profiles, and infinite power series with positive radius of convergence. It does **not** exclude a smooth but nonanalytic function, a divergent asymptotic series with exponentially small corrections, a function with infinitely many knots accumulating at zero, or a dimension-dependent/reachability-sensitive potential.

**Proof.** Let \(C(x)=\Gamma(2x+1)/(4^x\Gamma(x+1)^2)\), defined for positive real \(x\). For integer \(d\), \(C(d)=\binom{2d}{d}/4^d=g(d)^2/g(2d)\). The all-orders Stirling expansion (obtained by Euler–Maclaurin summation of \(\log\Gamma\)) gives as real \(v\downarrow0\):
\[
 \boxed{F(v):=\log C(1/v)+\frac12\log\frac{\pi}{v}
 \sim\sum_{k=1}^\infty \beta_k v^{2k-1},\qquad
 \beta_k=-\left(2-2^{1-2k}\right)\frac{B_{2k}}{2k(2k-1)}.}
 \tag{4.14}
\]
Here \(B_{2k}\) are the classical Bernoulli numbers. This is an **asymptotic** series, with a valid remainder estimate at each fixed truncation order; it is not asserted to converge. Euler's identity
\[
 |B_{2k}|=\frac{2(2k)!}{(2\pi)^{2k}}\zeta(2k)
\]
shows \(\lvert\beta_k\rvert>2(2k-2)!/(2\pi)^{2k}\). Consequently the formal series in (4.14) has **radius of convergence zero**. Its first four coefficients, independently replayed with rational Bernoulli arithmetic, are
\[
 \beta_1=-\frac18,\quad\beta_2=\frac1{192},\quad
 \beta_3=-\frac1{640},\quad\beta_4=\frac{17}{14336}.
\]

Put \(u_j=2^{-j}\), \(w_j=u_j^2=4^{-j}\), and recall the exact binary orbit identities
\[
 d_j=\frac{16-w_j}{3w_j},\qquad
 H_j=\frac6{u_j},\qquad
 D_j=\frac{16+2u_j^2}{3u_j^2},\qquad
 t_j=\frac{H_j}{D_j}=\frac{9u_j}{8+u_j^2}.
 \tag{4.15}
\]
Define for real \(w>0\) near zero
\[
 f(w)=\log\left[\frac6{\sqrt w}
 C\left(\frac{16-w}{3w}\right)\right].
\]
Then exactly \(f(w_j)=\log M_j\). Let \(v(w)=3w/(16-w)\), an analytic local change of variable with analytic inverse \(w(v)=16v/(3+v)\). Formula (4.14) yields the all-orders positive-axis asymptotic expansion
\[
 \boxed{f(w)\sim\log\frac{3\sqrt3}{2\sqrt\pi}
 -\frac12\log(1-w/16)
 +\sum_{k\ge1}\beta_k\left(\frac{3w}{16-w}\right)^{2k-1}.}
 \tag{4.16}
\]
The formal power series on the right has **zero radius of convergence**. Indeed its first two terms form an analytic germ, while the remaining formal composition cannot converge: otherwise composing with the analytic inverse \(w(v)\) would make the factorially divergent series \(\sum_k\beta_kv^{2k-1}\) convergent, a contradiction.

Now assume, toward a contradiction, that \(\psi\) is real analytic about zero. The orbit interpolation relation (4.12) gives, for all sufficiently large \(j\),
\[
 f(u_j^2)=\mathcal R(u_j),
\]
where
\[
 \boxed{\mathcal R(u)=-c_*+2\,\frac{16+2u^2}{3u^2}
 \psi\left(\frac{9u}{8+u^2}\right)
 -\frac12\frac{16+2(u/2)^2}{3(u/2)^2}
 \psi\left(\frac{9(u/2)}{8+(u/2)^2}\right).}
 \tag{4.17}
\]
Because \(\psi\) is real analytic at zero, \(\mathcal R(u)\) has a **convergent Laurent expansion with at most a second-order pole** at \(u=0\). But \(f(u_j^2)\) tends to the finite constant \(\log(3\sqrt3/(2\sqrt\pi))\); since \(u_j\to0\), equality on the sequence forces the Laurent principal part to vanish. Hence \(\mathcal R\) is actually **analytic** at \(u=0\).

The all-orders expansion (4.16) contains **integer powers of \(w=u^2\) only**, whereas the Taylor series of the analytic function \(\mathcal R(u)\) a priori contains arbitrary integer powers of \(u\). Equality \(\mathcal R(u_j)=f(u_j^2)\) on the sequence \(u_j\downarrow0\), combined with uniqueness of asymptotic coefficients, forces all the **odd** Taylor coefficients of \(\mathcal R\) to vanish. (Inductively subtract the first \(n-1\) terms and divide by \(u_j^n\), using the Poincaré remainder estimate at every order.) Thus \(\mathcal R(u)=G(u^2)\) for some **convergent analytic** power series \(G(w)\) near \(w=0\). The same uniqueness argument then forces the Taylor coefficients of \(G(w)\) to coincide, term for term, with the formal asymptotic coefficients in (4.16). This is impossible because the latter series diverges with radius zero. The contradiction proves the theorem. \(\square\)

**Corollary 5.2 (a uniquely forced, divergent all-orders Taylor jet).** Suppose instead that a sharp separately inductive profile \(\psi\) is merely **smooth to every order at zero**, without assuming analyticity. Then **every odd Taylor coefficient of \(\psi\) vanishes**, and the even Taylor coefficients are uniquely determined by \(c_*\), the classical Bernoulli numbers, and rational arithmetic. More precisely, write
\[
 L=c_*+\log\frac{3\sqrt3}{2\sqrt\pi},
 \qquad f_0=\log\frac{3\sqrt3}{2\sqrt\pi},
\]
and for every \(m\ge1\) define the rational coefficient
\[
 \boxed{f_m=\frac1{16^m}\left[\frac1{2m}+
 \sum_{k=1}^{\lfloor(m+1)/2\rfloor}
 \beta_k3^{2k-1}\binom{m-1}{2k-2}\right].}
 \tag{4.18}
\]
Define a *formal* power series \(A(w)=\sum_{m\ge0}A_mw^m\) by
\[
 \boxed{A_0=\frac23L,\qquad
 A_m=\frac{f_m}{2-\tfrac12\,4^{-m}}\quad(m\ge1).}
 \tag{4.19}
\]
Let \(w(x)\) denote the **unique formal rational power series**, vanishing at \(x=0\), solving
\[
 \boxed{w(x)=\frac{x}{81}(8+w(x))^2,\qquad x=t^2.}
 \tag{4.20}
\]
Then the complete Taylor jet of any smooth sharp \(\psi\) is exactly
\[
 \boxed{\psi(t)\ \widehat{=}\
 \frac{x(8+w(x))}{54}\,A(w(x)),\qquad x=t^2,}
 \tag{4.21}
\]
where \(\widehat{=}\) denotes **equality of formal Taylor series** (not equality of functions, and not convergence). The first three forced terms are
\[
 \boxed{\begin{aligned}
 \psi(t)\ \widehat{=}\;&\frac{8L}{81}t^2
 +\left(\frac{64L}{6561}+\frac{16}{32805}\right)t^4\\
 &+\left(\frac{1024L}{531441}
       +\frac{6784}{55801305}\right)t^6+\cdots.
 \end{aligned}}
 \tag{4.22}
\]
This uniquely forced formal Taylor series has **radius of convergence zero**, so smoothness of a hypothetical sharp profile could only occur through a genuinely **nonanalytic**, all-orders asymptotic germ.

**Proof.** Let \(F_j=c_*D_j-\log Q_j=D_j\psi(t_j)\), as established by exact orbit interpolation. The binary recurrence is
\[
 F_{j+1}=4F_j-2c_*-2\log M_j.
\]
The function \(f(w)\) from the proof of Theorem 5.1 has the complete Poincaré expansion \(f(w)\sim f_0+\sum_{m\ge1}f_mw^m\); the coefficient formula (4.18) follows directly by expanding \(-\tfrac12\log(1-w/16)\) and \(\beta_k(3w/(16-w))^{2k-1}\). If \(\psi\) is smooth at zero, its Taylor expansion to every fixed order exists. Set \(u=\sqrt w\), so \(D(u)\psi(t(u))\) has at worst a finite-order Laurent asymptotic series in \(u\). The recurrence along the geometric sequence \(u_j=2^{-j}\) forces, successively, its leading negative and every odd power coefficient to vanish, since \(c_*+f(u^2)\) has only even nonnegative powers. Thus it has a formal expansion \(A(w)=\sum A_mw^m\), obeying
\[
 2A(w)-\tfrac12A(w/4)\ \widehat{=}\ c_*+f(w).
\]
Matching coefficients gives (4.19), because every multiplier \(2-\tfrac12 4^{-m}\) is nonzero. The state identity \(t=9\sqrt w/(8+w)\) implies \(w=x(8+w)^2/81\); also \(D=(16+2w)/(3w)\), so \(\psi(t)=A(w)/D=x(8+w)A(w)/54\). This proves the formal identity (4.21), its uniqueness, and the initial coefficients (4.22). The exact coefficient prefix through \(t^{12}\) is independently replayed by `check_formal_germ.py`.

Finally the formal series \(f(w)\) has radius zero by Theorem 5.1. If \(A(w)\) converged, the linear combination \(2A(w)-\tfrac12A(w/4)\) would converge, contradicting the divergent \(f(w)\). The substitutions \(w=w(x)\) and \(x=t^2\) are invertible analytic local changes of variables (in \(w,x\)), and the prefactor \(x(8+w(x))/54\) has a simple nonzero leading term; hence convergence of the Taylor series of \(\psi(t)\) would imply convergence of \(A(w)\). This is impossible, proving the stated divergence. \(\square\)

The independent [`check_stirling_germ.py`](code/check_stirling_germ.py) verifies the initial rational Bernoulli coefficients, sign alternation, sixteen strict rational factorial lower bounds, the exact invertible coordinate transformation and thirteen orbit substitutions. The **infinite** divergence and asymptotic-series existence are analytical consequences of the classical Euler identities displayed above, not statements inferred from sixteen checked coefficients.

**Combined meaning of Theorems 3–5.** Any sharp, scalar, separately inductive homogeneous potential must interpolate **infinitely many exact orbit values**, must have the uniquely determined **quadratic asymptotic coefficient** from Theorem 3 when such an expansion exists, and must be **nonanalytic at zero**. This narrows the realistic sharp candidates to genuinely non-polynomial, nonanalytic or dimension/reachability-sensitive constructions. It does not establish that any such construction exists.

### A rigorously certified escape from the three-test power barrier

The rational dual obstruction of Theorem 1 is **specific to the positive-even-power cone**, not an obstruction to *every* convex homogeneous Bellman profile. To make this limitation precise, define the convex nondecreasing piecewise-linear function
\[
 \psi_0(t)=\frac3{100}(t-1/5)_+
 +\frac1{25}(t-1/2)_+
 +\frac3{200}(t-3/4)_+,
 \qquad (u)_+=\max\{u,0\}.
 \tag{4.9}
\]
It has \(\psi_0(0)=0\) and \(\psi_0(1)=191/4000=0.04775\), a smaller nominal coefficient than even the binary orbit rate. Let \(c_0=191/4000\). For the three explicitly attained states of Section 2, the product-closure inequalities
\[
 -c_0+2(r+1)\psi_0\!\left(\frac h{r+1}\right)
 -(2r+1)\psi_0\!\left(\frac h{2r+1}\right)
 >\log M(r,h)
 \tag{4.10}
\]
**all hold strictly**, as certified in exact fractions and rational log intervals by `check.py`. But the same inequality **fails strictly** at \((r,h)=(85,24)\), the genuine second-level \(T_5\) binary-recursion body. Thus (4.9) is **not a global supersolution**. It proves that the mere three-test obstruction cannot be generalized to all convex profiles, while the failure at a deeper reachable state demonstrates why finite data do not suffice to solve the unrestricted problem.

## 5. What the barrier rules out — and what it leaves open

Theorems 1 and 1.1 concern exactly the cone of **nonnegative even-power homogeneous profiles** \(\Phi_a(D,H)\) in (1.4), *provided they are verified through separate product closure for all attainable factor states*. It does not exclude convex profiles based on different functions of \(H/D\), signed coefficients that nevertheless retain convexity, piecewise-defined convex profiles, dimension-dependent corrections, or a proof based on direct attainable-state deficits. Indeed, finite-dimensional numerical exploration with convex piecewise-linear profiles respecting the binary \(T_5\) orbit's first several exact states suggests those more flexible families can evade the **three isolated necessary constraints** in Theorem 1; this is explicitly *discovery evidence only* and **not** a global supersolution or validated all-parameter result.

Theorem 2 shows that the second apparently natural attempt — using the exact binary continuation value as a scalar inductive potential — also cannot be proved through the unmodified join-superadditivity step, even on simple realizable bodies. Theorem 3 supplies exact orbit anchors and a forced curvature condition for any future sharp continuous convex potential. However the two obstructions leave the direct inequality \(q_\infty(K)\le c_*\) open, and in particular does not falsify the conjectural exact full-class spectral optimum. The combined conclusions direct work toward a **reachability-sensitive, dimension-dependent, or more flexible convex Bellman envelope**, instead of further numerical coefficient retuning in a method class that now has a strict certified floor.

## 6. Reproduction and dependency scope

The proof code is self-contained except for Python 3.10+ standard-library arbitrary-precision integers and `fractions.Fraction`:

```sh
python3 notes/projection-bellman-power-obstruction/code/check.py
python3 -O notes/projection-bellman-power-obstruction/code/check.py
python3 notes/projection-bellman-power-obstruction/code/check_formal_germ.py
python3 notes/projection-bellman-power-obstruction/code/check_stirling_germ.py
python3 notes/projection-bellman-power-obstruction/code/check_prime_independence.py
python3 notes/projection-bellman-power-obstruction/code/check_sharp_dual.py
python3 -O notes/projection-bellman-power-obstruction/code/check_sharp_dual.py
python3 notes/projection-bellman-power-obstruction/code/check_binary_tail.py
python3 -O notes/projection-bellman-power-obstruction/code/check_binary_tail.py
python3 notes/projection-bellman-power-obstruction/code/negative_controls.py
(cd notes/projection-bellman-power-obstruction && sha256sum -c SHA256SUMS)
```

The first checker also verifies the three attained source states against the independently certified exact 48-dimensional Pareto-frontier source (pinned SHA-256). The second includes its **own** pi and infinite-series bounds, importing only the elementary exact rational logarithm helper from the first. All three use explicit exception-based comparisons that remain active under Python optimization. The [proof audit](AUDIT.md) pinpoints the imported affine geometry, inherited binary orbit endpoint, mathematical tail reductions, and what the checkers do not verify. The result is restricted to one Bellman proof architecture and two precise method barriers; the unrestricted optimal growth rate \(\Gamma_{\mathcal C}\) remains unknown.
