# Simultaneous integer-degree failures of harmonic dimension comparison

## 1. Setup

Let \((M,g)\) be a connected complete smooth Riemannian manifold without
boundary and fix a base point \(o\). For \(d\ge 0\), let
\(\mathcal H_d(M,g)\) be the real vector space of smooth harmonic functions
\(u\) for which
\[
 |u(x)|\le C_u(1+d_g(o,x))^d
\]
for all \(x\), with \(C_u<\infty\) depending on \(u\). Write
\[
 h_d(M,g)=\dim_{\mathbb R}\mathcal H_d(M,g).
\]
For Euclidean three-space and an integer \(d\ge0\),
\[
 h_d(\mathbb R^3,g_{\mathrm E})=(d+1)^2.
\]

We use the near-Euclidean three-dimensional counterexample theorem from
OpenAI/math family 361, pinned in [SOURCE_MAP.md](SOURCE_MAP.md). In the
form needed here, it says:

> **Imported input.** Given \(\varepsilon>0\) and \(1<c<9/4\), there is
> \(k_0=k_0(\varepsilon,c)\) such that for every integer \(k\ge k_0\)
> there exists a complete smooth metric \(g_k\) on \(\mathbb R^3\),
> Euclidean near the origin, with \(\operatorname{Ric}_{g_k}\ge0\),
> positive Ricci curvature outside a compact set, and
> \[
> (1+\varepsilon)^{-2}g_{\mathrm E}
> \le g_k\le
> (1+\varepsilon)^2g_{\mathrm E},
> \]
> for which
> \[
> h_k(\mathbb R^3,g_k)\ge c(k+1)^2.
> \]
> Its asymptotic volume ratio can be chosen arbitrarily close to one.

Only this stated consequence of the upstream construction is imported below.

## 2. Degree monotonicity

**Lemma 2.1.** If \(0\le s\le t\), then
\[
 \mathcal H_s(M,g)\subseteq\mathcal H_t(M,g),
 \qquad
 h_s(M,g)\le h_t(M,g).
\]

**Proof.**
If \(u\in\mathcal H_s(M,g)\), then for some \(C_u<\infty\),
\[
 |u(x)|\le C_u(1+d_g(o,x))^s.
\]
Since \(1+d_g(o,x)\ge1\) and \(s\le t\),
\[
 (1+d_g(o,x))^s\le(1+d_g(o,x))^t.
\]
Thus the same constant \(C_u\) proves \(u\in\mathcal H_t(M,g)\).
The dimension inequality follows from the linear inclusion. \(\square\)

## 3. A simultaneous block theorem

**Theorem 3.1 (quantitative simultaneous block).**
Let
\[
 \varepsilon>0,\qquad \beta>1,\qquad A>1,
 \qquad A\beta^2<\frac94.
\]
Then there is an integer \(k_0\) such that for every integer
\(k\ge k_0\) there exists a single complete smooth metric \(g_k\) on
\(\mathbb R^3\) with all the geometric conclusions of the imported input
and such that, simultaneously for every integer
\[
 k\le d\le \lfloor\beta(k+1)\rfloor-1,
\]
one has
\[
 h_d(\mathbb R^3,g_k)
 >
 A(d+1)^2
 =
 A\,h_d(\mathbb R^3,g_{\mathrm E}).
\]
In particular, the Euclidean integer-degree comparison fails at every
degree in that entire consecutive block for the same metric.

**Proof.**
Choose a real number \(c\) with
\[
 A\beta^2<c<\frac94.
\]
Apply the imported near-Euclidean result with this \(c\) and the prescribed
\(\varepsilon\). For every sufficiently large integer \(k\), it gives one
metric \(g_k\) satisfying
\[
 h_k(\mathbb R^3,g_k)\ge c(k+1)^2.
\]
Fix any integer \(d\) in the displayed block. Lemma 2.1 gives
\[
 h_d(\mathbb R^3,g_k)\ge h_k(\mathbb R^3,g_k).
\]
Also
\[
 d+1\le\lfloor\beta(k+1)\rfloor\le\beta(k+1).
\]
Consequently,
\[
 \begin{aligned}
 h_d(\mathbb R^3,g_k)
 &\ge c(k+1)^2\\
 &>A\beta^2(k+1)^2\\
 &\ge A(d+1)^2.
 \end{aligned}
\]
The metric is not changed as \(d\) varies, so all inequalities hold
simultaneously. The remaining geometric assertions are exactly those of
the imported input. \(\square\)

## 4. Consequences

**Corollary 4.1 (any block ratio below \(3/2\)).**
Fix \(\varepsilon>0\) and \(1<\beta<3/2\). For all sufficiently large
integers \(k\), there is one complete smooth metric \(g_k\) on
\(\mathbb R^3\), globally \((1+\varepsilon)\)-bi-Lipschitz to Euclidean
space via the identity map, for which
\[
 h_d(\mathbb R^3,g_k)>(d+1)^2
\]
for every integer
\[
 k\le d\le\lfloor\beta(k+1)\rfloor-1.
\]

**Proof.**
Because \(\beta^2<9/4\), choose \(A>1\) sufficiently close to \(1\) that
\(A\beta^2<9/4\), then apply Theorem 3.1. \(\square\)

**Corollary 4.2 (arbitrarily long consecutive runs).**
For every \(\varepsilon>0\) and every positive integer \(N\), there is a
complete smooth metric \(g\) on \(\mathbb R^3\), globally
\((1+\varepsilon)\)-bi-Lipschitz to Euclidean space, with
\(\operatorname{Ric}_g\ge0\), such that the Euclidean harmonic-dimension
comparison fails at at least \(N\) consecutive positive integer degrees.

**Proof.**
Fix any \(\beta\in(1,3/2)\). The number of integers in the block of
Corollary 4.1 is
\[
 \lfloor\beta(k+1)\rfloor-k,
\]
which tends to infinity linearly in \(k\). \(\square\)

**Corollary 4.3 (block excess phase diagram).**
For a fixed block ratio \(\beta\in(1,3/2)\), every multiplicative excess
\[
 1<A<\frac{9}{4\beta^2}
\]
is simultaneously attainable throughout the block in Theorem 3.1, while
retaining arbitrary prescribed global bi-Lipschitz closeness to Euclidean
space.

This is the exact region delivered by the imported \(9/4\) one-degree
constant together with degree monotonicity. No assertion is made that the
boundary \(A\beta^2=9/4\), the ratio \(3/2\), or either constant is
geometrically optimal.

## 5. Quantifiers and the remaining problem

The result changes the quantifiers in one useful but limited way. The
upstream statement has the form
\[
 \forall k\gg1\;\exists g_k:\quad
 \text{comparison fails at degree }k.
\]
Theorem 3.1 strengthens this to
\[
 \forall k\gg1\;\exists g_k:\quad
 \text{comparison fails simultaneously for all }
 d\in[k,\beta k+O(1)].
\]
It does **not** establish
\[
 \exists g\;\forall^\infty d
\quad\text{or even}\quad
 \exists g\;\exists d_j\to\infty
\]
with comparison failure. The upstream analytic construction cycles a
finite spectral band chosen after \(k\); turning those finitely many
programs into one asymptotic metric is a genuinely additional problem and
is not hidden in the monotonicity argument above.

## 6. Verification status

The new deduction consists of Lemma 2.1 plus the three displayed
inequalities in Theorem 3.1. It uses no floating-point computation and no
solver output. The optional [checker.py](checker.py) uses Python
\`fractions.Fraction\` only to replay the finite rational inequality for
sample or user-supplied rational parameters. The analytic existence input
is not reproved by that checker; it is pinned explicitly in
[SOURCE_MAP.md](SOURCE_MAP.md).
