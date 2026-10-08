# A finite rational-duality obstruction to sharp positive-power Bellman envelopes

**Research note, 8 October 2026.** AI-assisted independent continuation of entry 005. The affine projection-body product calculus and the certified binary \(T_5\) rate are inherited from previously published 005 results. The new all-degree no-go theorem and the infinite-series obstruction below are proved with standard-library exact arithmetic. This note makes no journal-priority, human-refereeing, or complete Lean-formalization claim.

## Abstract

The unrestricted projection-body growth problem for the point-generated Cartesian-product/affine-join class remains open. A leading method is to certify a dimension-homogeneous convex Bellman potential by **separate closure under every possible join and product**, with nonnegative even-power coefficients. We prove a **strict, all-degree obstruction** to this proof architecture: for *any* finite or countably summable sequence of nonnegative coefficients, the nominal logarithmic rate must be **strictly larger than \(486139/10^7=0.0486139\)** if the potential is product-closed even merely at self-products of three explicit, actually attainable polytopes. This barrier is strictly above the previously certified binary \(T_5\) orbit rate. The proof uses three rational self-product constraints and positive rational dual weights; six even-degree columns are checked individually, **all infinitely many remaining powers** are controlled by elementary rational geometric tails, and the decisive weighted logarithms are enclosed by a separate exact atanh checker. Stronger still, we determine the **exact minimum for the infinite linear programme defined by these three necessary inequalities**: it has a uniquely supported primal solution in degrees **2, 4, 8** and an exact rational dual, yielding the stronger certified floor. No finite extrapolation is involved.

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
python3 notes/projection-bellman-power-obstruction/code/check_sharp_dual.py
python3 -O notes/projection-bellman-power-obstruction/code/check_sharp_dual.py
python3 notes/projection-bellman-power-obstruction/code/check_binary_tail.py
python3 -O notes/projection-bellman-power-obstruction/code/check_binary_tail.py
python3 notes/projection-bellman-power-obstruction/code/negative_controls.py
(cd notes/projection-bellman-power-obstruction && sha256sum -c SHA256SUMS)
```

The first checker also verifies the three attained source states against the independently certified exact 48-dimensional Pareto-frontier source (pinned SHA-256). The second includes its **own** pi and infinite-series bounds, importing only the elementary exact rational logarithm helper from the first. All three use explicit exception-based comparisons that remain active under Python optimization. The [proof audit](AUDIT.md) pinpoints the imported affine geometry, inherited binary orbit endpoint, mathematical tail reductions, and what the checkers do not verify. The result is restricted to one Bellman proof architecture and two precise method barriers; the unrestricted optimal growth rate \(\Gamma_{\mathcal C}\) remains unknown.
