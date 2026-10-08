# No quadratic germ: a quantitative second-order oscillation theorem for sharp projection-body Bellman potentials

**Research note — 8 October 2026.** An entry-005 continuation, prepared with AI assistance. Geometry and the exact binary \(T_5\) orbit come from the existing public manuscripts; the method obstruction and the oscillation inequality below are additional deductions. All nontrivial numerical inequalities are independently verified by exact rational intervals. No mathematical-priority, human-refereeing or Lean-completeness claim is made.

## Abstract

Let \(\mathcal C\) be the class of convex polytopes generated from a point by arbitrary Cartesian products and affine joins. The sharp asymptotic spectral value of \(\mathcal C\) remains unknown; the balanced binary recursion starting from a 5-simplex is a leading candidate. We investigate a standard way of proving its optimality: a **dimension-homogeneous scalar Bellman potential** depending only on the ratio \(t=H/D\), with separate one-step closure under products and joins. We prove a considerably stronger obstruction than the previously established exclusion of finite polynomials or analytic potentials: **no such exactly sharp potential can have even a second-order asymptotic expansion at zero**. In fact, the original \(T_5\) orbit determines a unique quadratic coefficient \(\alpha\), but any continuous-at-zero, normalized, separately closed sharp profile must have a **quantitatively nonvanishing second-order oscillation**, bounded below by a universal rational constant:
\[
 \boxed{\liminf_{t\downarrow0}\frac{|\psi(t)-\alpha t^2|}{t^2}=0,
 \qquad \limsup_{t\downarrow0}\frac{|\psi(t)-\alpha t^2|}{t^2}>\frac1{4000}.}
\]
The proof uses two infinite families of **actually realizable** polytopes: the original orbit and its perturbations by precisely \(2^{j-1}\) additional point joins. The resulting self-product inequalities have a strict negative asymptotic quadratic slack. The sign and the rational oscillation coefficient are checked with an independent standard-library exact checker. No numerical search, finite extrapolation or floating calculation enters the final theorem. The result constrains the **sharp induction architecture**, not the as-yet unknown global optimal spectral rate.

## 1. Setup and the exact product–join calculus

For a full-dimensional \(d\)-polytope \(K\), write \(\Pi K\) for its projection body and
\[
 R(K)=\frac{|\Pi K|}{|K|^{d-1}},\qquad g(d)=\frac{d^d}{d!}.
\]
Use the existing affine-invariant state \(a(K)>0\) of [entry 005 v2](../../preprints/005-simplex-product-optimum/v2/paper.md), with
\[
 D(K)=d+1,\quad H(K)=1/a(K),\quad Q(K)=\frac{a(K)R(K)}{g(d)}.
 \tag{1.1}
\]
For the formal point, \((D,H,Q)=(1,1,1)\). The exact join rule is
\[
 (D,H,Q)(A*B)=(D_A+D_B,H_A+H_B,Q_AQ_B).
 \tag{1.2}
\]
For positive-dimensional factor dimensions \(r,s\), \(n=r+s\), and factor states \((h,u)=(H,Q)(A)\), \((j,v)=(H,Q)(B)\), the exact Cartesian-product rule is
\[
 H(A\times B)=\frac n{r/h+s/j},\qquad
 Q(A\times B)=uv\frac{g(r)g(s)}{g(n)}\frac{sh+rj}{n}.
 \tag{1.3}
\]
All affine changes of coordinates in our class are invertible on affine hulls. These geometric identities and the positivity of \(H,Q\) are inherited from 005 v2, not reproved by the arithmetic checker.

Let \(K_0=T_5\), and for \(j\ge0\) recursively let
\[
 K_{j+1}=(K_j\times K_j)*(K_j\times K_j).
 \tag{1.4}
\]
Write its exact state as \((d_j,D_j,H_j,Q_j)\). The inherited formulas give
\[
 d_j=\frac{16\cdot4^j-1}{3},\qquad
 D_j=\frac{16\cdot4^j+2}{3},\qquad
 H_j=6\cdot2^j.
 \tag{1.5}
\]
Put \(C(d)=g(d)^2/g(2d)=\binom{2d}{d}/4^d\) for positive integer \(d\). Then
\[
 Q_{j+1}=Q_j^4\bigl[H_j C(d_j)\bigr]^2,
 \qquad Q_0=1.
 \tag{1.6}
\]
The [independently certified binary-orbit analysis](../../preprints/005-simplex-product-optimum/v5/paper.md) establishes that the following real limit exists:
\[
 c_*:=\lim_{j\to\infty}\frac{\log Q_j}{D_j}>0,
 \qquad \exp(1+c_*)\approx2.8534655507015.
 \tag{1.7}
\]
The displayed decimal is for orientation only. Our certificate bounds \(c_*\) directly with rational logarithmic intervals and a provable infinite tail, and **all proof decisions are rational**.

### The sharp scalar Bellman proof architecture

Let \(\psi:[0,1]\to\mathbb R\) be any function with \(\psi(0)=0\), \(\psi(1)=c_*\), and \(\psi(t)\to0\) as \(t\downarrow0\). **No convexity, monotonicity or differentiability is assumed.** Consider the homogeneous potential
\[
 \boxed{\Phi_\psi(D,H)=D\bigl(c_*-\psi(H/D)\bigr).}
 \tag{1.8}
\]
Assume that it satisfies the usual **separate local closure** under joins and nontrivial products of all actually attainable states:
\[
 \Phi_\psi(D_A+D_B,H_A+H_B)\ge
 \Phi_\psi(D_A,H_A)+\Phi_\psi(D_B,H_B),
 \tag{1.9}
\]
\[
 \Phi_\psi(n+1,H(A\times B))\ge
 \Phi_\psi(r+1,H_A)+\Phi_\psi(s+1,H_B)
 +\log\!\left(\frac{g(r)g(s)}{g(n)}\frac{sH_A+rH_B}{n}\right).
 \tag{1.10}
\]
The point has potential zero because \(\psi(1)=c_*\). Together these conditions imply \(\log Q(K)\le\Phi_\psi(D(K),H(K))\) for all point-generated polytopes, via induction. Were \(c_*\) the true global optimum, such a potential would provide one kind of sharp global certificate. We establish a rigorous obstruction to **this precise proof mechanism**, without asserting or denying the equality itself.

## 2. Main theorem: strictly positive second-order oscillation

Define the exact constant
\[
 \boxed{L=c_*+\frac12\log\frac{27}{4\pi},\qquad
 \alpha_*=\frac8{81}L.}
 \tag{2.1}
\]
Both are positive. The independent rational checker verifies the strict analytic bound
\[
 \boxed{0<L<\frac{54}{125}=0.432.}
 \tag{2.2}
\]
It needs only Robbins factorial bounds, the elementary pi enclosure \(333/106<\pi<355/113\), and rational atanh enclosures for natural logarithms.

**Theorem 2.1 (no quadratic germ for a sharp scalar Bellman supersolution).** Any function \(\psi\) satisfying the endpoint/continuity conditions following (1.8) and the separate closure conditions (1.9)–(1.10) must obey
\[
 \boxed{\liminf_{t\downarrow0}\frac{|\psi(t)-\alpha_*t^2|}{t^2}=0,
 \qquad \limsup_{t\downarrow0}\frac{|\psi(t)-\alpha_*t^2|}{t^2}
 >\frac1{4000}.}
 \tag{2.3}
\]
In particular, \(\lim_{t\downarrow0}\psi(t)/t^2\) **does not exist**, and \(\psi\) cannot be **twice differentiable at the origin**. This excludes *even nonanalytic* \(C^2\) sharp scalar Bellman profiles. It is strictly stronger, under the same closure architecture, than the earlier nonanalyticity and finite-polynomial exclusions.

The theorem concerns the ratio variable \(t=H/D\). It does **not** exclude sharp potentials depending additionally on dimension, the actual \(Q\)-deficit, a multidimensional reachability invariant, or proofs that do not establish (1.9)–(1.10) individually.

## 3. The original orbit forces one unique quadratic coefficient

**Lemma 3.1 (exact orbit interpolation).** Under the hypotheses of Theorem 2.1,
\[
 \boxed{\Phi_\psi(D_j,H_j)=\log Q_j\qquad(j\ge0).}
 \tag{3.1}
\]

**Proof.** Define the ordinary induction slack \(E_j=\Phi_\psi(D_j,H_j)-\log Q_j\). The simplex \(K_0=T_5\) is the join of six points, and \(\Phi_\psi(1,1)=0\). Thus (1.9) gives \(E_0=\Phi_\psi(6,6)-\log 1=6(c_*-\psi(1))=0\). Each binary product–join step contains two equal products, so (1.9)–(1.10), together with the exact \(Q\) recurrence, give \(E_{j+1}\ge4E_j\ge0\).

Yet \(H_j/D_j\to0\), \(\psi(t)\to0\) as \(t\downarrow0\), and \(\log Q_j/D_j\to c_*\). Hence \(E_j/D_j\to0\). If any \(E_j>0\), then \(E_{j+m}\ge4^m E_j\) while \(D_{j+m}/4^m\) approaches a finite positive number (for fixed \(j\)), contradicting \(E_{j+m}/D_{j+m}\to0\). Therefore every slack vanishes. \(\square\)

Define the actual deficit \(F_j=D_j\psi(H_j/D_j)=c_*D_j-\log Q_j\), using Lemma 3.1, and the exact step multiplier \(M_j=H_j C(d_j)\). Equation (1.6) yields
\[
 \boxed{F_{j+1}=4F_j-2(c_*+\log M_j).}
 \tag{3.2}
\]
By the central binomial Stirling estimate,
\[
 C(d)=\frac1{\sqrt{\pi d}}\bigl(1+O(d^{-1})\bigr).
\]
Since \(H_j/\sqrt{d_j}\to z_0=3\sqrt3/2\), it follows that
\[
 \log M_j\to\ell_0:=\log\frac{z_0}{\sqrt\pi}
 =\frac12\log\frac{27}{4\pi}.
 \tag{3.3}
\]
Iterate (3.2) **backwards** from index \(j+m\):
\[
 F_j=4^{-m}F_{j+m}
 +\sum_{i=0}^{m-1}2\cdot4^{-i-1}(c_*+\log M_{j+i}).
\]
As \(F_{j+m}/D_{j+m}\to0\) and \(D_{j+m}=O(4^{j+m})\), the first term tends to zero. Therefore
\[
 \boxed{F_j=2\sum_{i\ge0}4^{-i-1}(c_*+\log M_{j+i})
 \longrightarrow\frac23(c_*+\ell_0)=\frac23L.}
 \tag{3.4}
\]
Finally \(D_j(H_j/D_j)^2=H_j^2/D_j\to27/4\), so (3.4) proves
\[
 \boxed{\lim_{j\to\infty}
 \frac{\psi(H_j/D_j)}{(H_j/D_j)^2}
 =\frac{(2/3)L}{27/4}=\alpha_*.}
 \tag{3.5}
\]
This is an **unconditional forced subsequence limit** for any candidate scalar supersolution, not an assumption that a quadratic germ exists. In particular the first part of (2.3) follows immediately.

## 4. Point-join perturbations violate the forced quadratic approximation

The crucial second family consists of **actually attained polytopes**
\[
 \boxed{A_j=K_j*(\underbrace{\text{point}*\cdots*\text{point}}_{m_j\ \mathrm{factors}}),
 \qquad m_j=2^{j-1}\quad(j\ge1).}
 \tag{4.1}
\]
By the exact join state rule (1.2), with \(r_j=\dim A_j\), \(h_j=H(A_j)\),
\[
 \boxed{r_j=\frac{16\cdot4^j-1}{3}+2^{j-1},\qquad
 h_j=6\cdot2^j+2^{j-1}=13\cdot2^{j-1}.}
 \tag{4.2}
\]
Thus
\[
 \boxed{\frac{h_j^2}{r_j}\longrightarrow z^2=\frac{507}{64},\qquad
 \frac{z}{z_0}=\frac{13}{12}.}
 \tag{4.3}
\]
Both arguments \(h_j/(r_j+1)\) and \(h_j/(2r_j+1)\) tend to zero, so they probe the **local germ** of \(\psi\), despite the bodies' globally complicated construction.

Apply the required product-closure inequality (1.10) to \(A_j\times A_j\). Its output \(H\) equals \(h_j\), and the exact multiplicative \(Q\)-factor is \(h_jC(r_j)\). Set
\[
 \boxed{S_j(\psi)=-c_*+2(r_j+1)\psi\!\left(\frac{h_j}{r_j+1}\right)
 -(2r_j+1)\psi\!\left(\frac{h_j}{2r_j+1}\right)
 -\log[h_jC(r_j)].}
 \tag{4.4}
\]
Then product closure forces \(S_j(\psi)\ge0\) for **every** integer \(j\ge1\).

Consider the *formal quadratic approximation* \(\psi_0(t)=\alpha_*t^2\); it is not asserted to satisfy product/join closure. The central-binomial asymptotic and (4.3) give the **exact limit**
\[
 \begin{aligned}
 \lim_{j\to\infty}S_j(\psi_0)
 &=-c_*+\frac32\alpha_*z^2-\log\frac z{\sqrt\pi}\\
 &=\left[\left(\frac{13}{12}\right)^2-1\right]L
 -\log\frac{13}{12}\\
 &=\boxed{\frac{25}{144}L-\log\frac{13}{12}.}
 \end{aligned}
 \tag{4.5}
\]
**Lemma 4.1 (strict rational asymptotic obstruction).** The limit in (4.5) is strictly less than \(-1/200\).

**Proof.** The exact checker independently verifies \(L<54/125\); Section 6 describes its rational certification. The elementary atanh expansion, with \((13/12-1)/(13/12+1)=1/25\), gives
\[
 \log\frac{13}{12}=2\sum_{k\ge0}\frac{(1/25)^{2k+1}}{2k+1}
 >\frac2{25}.
\]
Consequently
\[
 \frac{25}{144}L-\log\frac{13}{12}
 <\frac{25}{144}\frac{54}{125}-\frac2{25}
 =\frac3{40}-\frac2{25}=\boxed{-\frac1{200}}.
\]
This inequality is strict and contains **no numerical optimization**. \(\square\)

## 5. A universal nonzero oscillation amplitude

Define the second-order residual \(\delta(t)=\psi(t)-\alpha_*t^2\) and its extended nonnegative limsup
\[
 \eta:=\limsup_{t\downarrow0}\frac{|\delta(t)|}{t^2}\in[0,+\infty].
\]
If \(\eta=+\infty\), the second inequality of Theorem 2.1 is automatic. Otherwise, by the definition of limsup, for every \(\varepsilon>0\) the values of \(|\delta(t)|/t^2\) at both of the arguments in (4.4) are eventually no greater than \(\eta+\varepsilon\). Therefore
\[
 \begin{aligned}
 0\le S_j(\psi)
 &\le S_j(\psi_0)+(\eta+\varepsilon)h_j^2
 \left(\frac2{r_j+1}+\frac1{2r_j+1}\right).
 \end{aligned}
\]
By (4.3), the correction coefficient tends to
\[
 \boxed{\frac52 z^2=\frac{2535}{128}.}
\]
Pass to the limit and then let \(\varepsilon\downarrow0\). Combining this with Lemma 4.1 yields
\[
 \eta\ge\frac{-\lim S_j(\psi_0)}{2535/128}
 >\frac{1/200}{2535/128}
 =\frac{16}{63375}
 >\boxed{\frac1{4000}}.
 \tag{5.1}
\]
Meanwhile (3.5) states that the same normalized residual tends to zero **along the original orbit** \(t_j=H_j/D_j\). Therefore its liminf is zero but its limsup exceeds \(1/4000\), proving (2.3) in full. \(\square\)

If \(\psi\) possessed any quadratic expansion \(\psi(t)=a t^2+o(t^2)\), the orbit limit (3.5) would force \(a=\alpha_*\), contradicting (5.1). In particular, if \(\psi\) were twice differentiable at zero, its finite orbit limit would force \(\psi'(0)=0\) and \(\psi''(0)/2=\alpha_*\), again contradicting (5.1). Thus the sharp scalar induction must have a **genuinely oscillatory second-order germ**, irrespective of whether it is a polynomial, analytic, smooth, convex or otherwise.

### Corollary 5.2 (the exact differentiability threshold for convex sharp profiles)

If \(\psi\) also happens to be **convex**, then it must have a **right first derivative** at the origin, and that derivative equals zero:
\[
 \boxed{\psi'_+(0)=0.}
\]
Nevertheless it admits **no finite right second derivative** at zero, and the normalized right derivative \(\psi'_+(t)/t\) cannot have a finite limit as \(t\downarrow0\). Thus the obstruction occurs at **second order**, not necessarily at the first derivative.

**Proof.** For a convex function with \(\psi(0)=0\), the secant slope \(t\mapsto\psi(t)/t\) is nondecreasing for positive \(t\). Along the original orbit (3.5), \(\psi(t_j)/t_j=\alpha_*t_j+o(t_j)\to0\). For each fixed \(t>0\), choose \(j\) so large that \(t_j<t\); monotonicity gives \(\psi(t)/t\ge\psi(t_j)/t_j\), whose right side tends to zero, so \(\psi(t)/t\ge0\). For arbitrary small \(t\), choose the orbit index with \(t_{j+1}<t\le t_j\); then
\[
 0\le\frac{\psi(t)}t\le\frac{\psi(t_j)}{t_j}\longrightarrow0.
\]
This proves the right derivative exists and vanishes. A finite right second derivative would give a second-order asymptotic expansion and contradict Theorem 2.1. Finally, if the right convex derivative \(\psi'_+(t)/t\) had a finite limit \(a\), integration of the monotone derivative on \([0,t]\) would give \(\psi(t)/t^2\to a/2\), again contradicting (2.3). \(\square\)

## 6. Independent exact checker and dependencies

The proof only requires two strict scalar estimates, one inherited from the binary orbit and one elementary:
\[
 c_*<\frac{49}{1000},\qquad
 \frac12\log\frac{27}{4\pi}<\frac{383}{1000}.
\]
These imply \(L<49/1000+383/1000=54/125\). The [standalone checker](code/check.py) proves the first estimate directly from the **exact** binary-orbit limit series
\[
 c_*=\frac{(2/3)\log6+G(5)}{16/3},\qquad
 G(5)=\frac29\log2+
 2\sum_{j\ge0}\frac1{4^{j+1}}\log\frac{g(d_j)^2}{g(2d_j)},
\]
with the first thirteen summands bracketed by two-sided Robbins factorial inequalities and the entire infinite tail bounded by a closed geometric/logarithmic remainder. It certifies \(333/106<\pi<355/113\) from the Machin arctangent identity, brackets all logarithms using finite rational atanh series with exact remainders, and checks \(27/(4\cdot333/106)=159/74\). The second estimate then follows from an exact interval for \(\tfrac12\log(159/74)\). The checker also verifies the explicit point-join formulas and all purely rational constants (4.3), (4.5) and (5.1).

The **infinite-index** claims are not inferred from checking sixteen sample dimensions: they follow analytically from the exact state recursion, Stirling's central binomial limit, backward summation in Section 3, and the limiting product inequalities in Sections 4–5. The checker is independent of the previously published Python sources; it uses only `int`, `fractions.Fraction` and the Python standard library. No floats, random search, optimizer or non-replayable solver output contribute to mathematical decisions.

Replay from repository root:

```sh
python3 notes/projection-bellman-quadratic-oscillation/code/check.py
python3 -O notes/projection-bellman-quadratic-oscillation/code/check.py
python3 notes/projection-bellman-quadratic-oscillation/code/negative_controls.py
(cd notes/projection-bellman-quadratic-oscillation && sha256sum -c SHA256SUMS)
```

The prior [Bellman methodological obstruction note](../projection-bellman-power-obstruction/paper.md) proved that positive-even-power, finite-polynomial and real-analytic scalar sharp Bellman attempts fail under separate closure; this note **subsumes all those regularity exclusions** by ruling out a quadratic germ without even assuming convexity. It does **not** show \(c_*\) fails to be the true full-class optimum, does not construct a correct sharp Bellman supersolution, and does not rule out **non-scalar** or reachability-sensitive proof methods. The next central task is to construct a potential with the required second-order oscillations (or abandon scalar state compression), prove global product/join closure and attain equality with the binary orbit.

## 7. A canonical nonanalytic orbit interpolant also fails the Bellman product inequality

Theorem 2.1 proves that any sharp separately closed scalar profile needs a nontrivial second-order oscillation; it does not assert that **all** such profiles fail. We now test a natural explicit nonanalytic interpolation of the entire binary \(T_5\) orbit, and prove that this particular candidate also fails at a small, actually attainable body. Unlike the universal oscillation theorem, this example gives a **finite concrete product-closure counterexample** with an explicitly replayable rational interval.

For every real \(x>0\), define the positive continuous gamma ratio
\[
 C(x)=\frac{\Gamma(2x+1)}{4^x\Gamma(x+1)^2}
 =\frac{\Gamma(x+1/2)}{\sqrt\pi\,\Gamma(x+1)}.
 \tag{7.1}
\]
Its value at integers \(x=d\) is the central-binomial ratio \(\binom{2d}{d}/4^d\). Define the smooth real-dimension extension
\[
 \boxed{G(x)=\frac29\log2+
 2\sum_{k=0}^\infty 4^{-k-1}
 \log C\!\left(\frac{(3x+1)4^k-1}{3}\right).}
 \tag{7.2}
\]
The series is absolutely convergent for every \(x>0\), because each logarithmic summand is \(O(k+\log(x+1))\) by Gamma-ratio inequalities, while the weight is \(O(4^{-k})\).

For \(0<t\le1\), define auxiliary real variables
\[
 \boxed{\begin{aligned}
 u(t)&=\frac{16t}{9+\sqrt{81-32t^2}},\qquad w(t)=u(t)^2,\\
 d(t)&=\frac{16-w(t)}{3w(t)},\qquad
 h(t)=\frac6{u(t)},\qquad D(t)=d(t)+1,
 \end{aligned}}
 \tag{7.3}
\]
so \(h(t)/D(t)=t\) exactly. The **canonical orbit interpolation profile** is
\[
 \boxed{\psi_{\mathrm{can}}(t)=\frac1{D(t)}
 \left[\frac23(c_*+\log h(t))+G(d(t))\right],
 \quad \psi_{\mathrm{can}}(0)=0.}
 \tag{7.4}
\]
The positivity of \(d(t)\ge5\), the Gamma ratio bound and the cancellation of the large logarithmic terms in (7.4) show \(\psi_{\mathrm{can}}(t)=O(t^2)\), so this extension is continuous at zero. At the original orbit points \(t_j=H_j/D_j\), the auxiliary variables satisfy \(u(t_j)=2^{-j}\), \(d(t_j)=d_j\), \(h(t_j)=H_j\). The exact binary-continuation series therefore gives
\[
 \boxed{\psi_{\mathrm{can}}(t_j)=c_*-\frac{\log Q_j}{D_j}}
 \qquad\text{for every }j\ge0.
 \tag{7.5}
\]
Thus \(\psi_{\mathrm{can}}\) satisfies **every forced orbit interpolation equality** (3.1), not just the leading curvature. The Stirling–Bernoulli divergence analysis in the [preceding 005 Bellman note](../projection-bellman-power-obstruction/paper.md) also proves this exact Gamma continuation is **not real analytic at zero**, even though it admits a full formal even-power asymptotic expansion. It is the most immediate attempt to turn the exact binary-tail value function of the preceding 005 work into a *one-variable homogeneous* Bellman potential.

**Theorem 7.1 (explicit failure at dimension eight).** Let
\[
 A=(T_1\times T_2)*\underbrace{\mathrm{point}*\cdots*\mathrm{point}}_{5\ \mathrm{points}}.
\]
Then \((\dim A,H(A),Q(A))=(8,53/7,28/27)\), and the self-product condition (1.10) fails **strictly** for the canonical profile. More precisely,
\[
 \boxed{\begin{aligned}
 &-c_*+18\psi_{\mathrm{can}}(53/63)
 -17\psi_{\mathrm{can}}(53/119)\\
 &\hspace{25mm}-\log\left(\frac{53}{7}\frac{\binom{16}{8}}{4^8}\right)
 <-\frac1{20000}.
 \end{aligned}}
 \tag{7.6}
\]
Consequently \(\psi_{\mathrm{can}}\) is **not** an independently product-closed sharp Bellman profile, even though it matches the entire binary \(T_5\) orbit exactly.

**Proof.** The state of \(T_1\times T_2\), computed directly from (1.3), is \((d,H,Q)=(3,18/7,28/27)\). Joining five points adds five to both \(d,H\) and leaves \(Q\) unchanged. For its Cartesian square, the product output retains \(H=53/7\) and has augmented dimension \(D=17\); the input augmented dimension is nine. Therefore (1.10) is precisely the assertion that the expression in (7.6) is nonnegative.

The [independent pure-rational checker](code/check_canonical_rational.py) evaluates the expression with **outward-rounded 136-bit dyadic rational intervals**, not floating-point values. It encloses \(\log C(x)\) for every positive real argument needed in (7.2) by the first four Bernoulli terms of the Stirling expansion and the **signed next-term remainder** obtained from Binet's positive-kernel formula:
\[
 \begin{aligned}
 \log C(x)&=-\tfrac12\log(\pi x)
  +\sum_{k=1}^4\frac{\beta_k}{x^{2k-1}}+\mathcal E_4(x),\\
 -\frac{2B_{10}}{90x^9}&<\mathcal E_4(x)
 <\frac{B_{10}}{90(2x)^9},\qquad B_{10}=\frac5{66}.
 \end{aligned}
 \tag{7.7}
\]
The alternating remainder statement follows by inserting the positive-kernel identity
\[
 \log\Gamma(x+1)=\left(x+\tfrac12\right)\log x-x
 +\tfrac12\log(2\pi)
 +2\int_0^\infty\frac{\arctan(v/x)}{e^{2\pi v}-1}\,dv
\]
into the exact finite alternating expansion of \(\arctan(v/x)\), whose error has the sign of and is bounded by its next term for \(v/x>0\). Taking the difference of the expansions at \(2x\) and \(x\) gives (7.7). This bounds **all real arguments**, not just integer factorials.

For the omitted part of (7.2), Gamma log-convexity gives the elementary strict bounds
\[
 \frac1{\sqrt{\pi(x+1/2)}}<C(x)<\frac1{\sqrt{\pi x}}
 \qquad(x>0).
 \tag{7.8}
\]
To see this, apply log-convexity to \(\Gamma(x+1/2)^2\le\Gamma(x)\Gamma(x+1)\) and to \(\Gamma(x+1)^2\le\Gamma(x+1/2)\Gamma(x+3/2)\), then use Gamma's functional equation. Since each recursive argument in (7.2) lies between \(x4^k\) and \((x+1/2)4^k\) after adding \(1/2\), the weighted logarithmic tails sum to **closed exact geometric quantities**. The checker uses twenty finite Gamma terms and encloses **every remaining term for all \(k\ge20\)** in this way.

Every remaining logarithm and square root is enclosed using rational atanh series and dyadic integer-square-root bounds; \(\pi\) is bounded by exact rational Machin arctangent intervals. The final inequality test is the **strict rational comparison** of the computed upper endpoint to \(-1/20000\); the program throws an explicit exception if it fails. An entirely separate [192-bit SageMath/Arb checker](code/check_canonical_arb.py) reconstructs the same expression from Arb `log_gamma`, using only the analytic infinite-tail bounds (7.8), and independently verifies the same strict sign. The pure-rational checker needs **no** Sage, Arb or third-party libraries to replay (7.6), and its ordinary/optimized Python modes agree byte-for-byte. \(\square\)

**Corollary 7.2 (forced quantitative correction to the canonical profile).** Any scalar \(\psi\) satisfying the sharp product-closure hypothesis of Theorem 2.1 must satisfy
\[
 \boxed{18\delta(53/63)-17\delta(53/119)>\frac1{20000},
 \quad \delta=\psi-\psi_{\mathrm{can}}.}
 \tag{7.9}
\]
In particular
\[
 \boxed{\max\{|\delta(53/63)|,|\delta(53/119)|\}>
 \frac1{700000}.}
 \tag{7.10}
\]

**Proof.** Subtract the strictly failing product inequality (7.6) from the required nonnegative product inequality (1.10) for \(A\times A\). The normalization \(\psi(1)=\psi_{\mathrm{can}}(1)=c_*\) cancels the common constant. The absolute-value estimate follows because the left side of (7.9) has magnitude at most \(35\max\{|\delta(53/63)|,|\delta(53/119)|\}\). \(\square\)

This result is distinct from the asymptotic oscillation theorem: (7.9) forces a **definite finite-state correction**, while (2.3) forces a **nonvanishing relative second-order correction arbitrarily close to zero**. Together they show that matching the entire attractive binary orbit is not sufficient for product closure: both its finite off-orbit state geometry and its infinitesimal variations impose additional constraints. The existence of an alternative sharp potential remains unresolved.
