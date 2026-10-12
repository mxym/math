# Exact two-layer projection-volume spectrum and a strict product–join depth separation

**Research note, 8 October 2026.** Supplement to entry 005. Prepared with AI assistance, using the published product/join calculus of 005 v2. The analytic tail bounds and explicit rational comparisons are reproduced below, together with a small independent-execution arithmetic certificate. No priority or human-peer-review claim is made.

## Abstract

We determine the exact projection-body growth rate for the class obtained by joining arbitrary finite collections of Cartesian products of two simplices and points. The unique highest per-block logarithmic spectral rate is achieved by \(T_5\times T_5\), whereas a second independent sharp affine-defect inequality has its unique equality block at \(T_4\times T_4\). Combining these two universal bounds proves a strict **operation-depth separation already in dimension 85**: a concrete body formed by a product of two joins, followed by a join, beats every body constructed using only joins of simplex products. The depth gap persists asymptotically. Every finite comparison uses rational powers or proved rational logarithm intervals; the unbounded parameter tails are treated analytically, not by extrapolating a search grid. This concerns the point-generated product/join class, not all convex bodies.

## 1. Geometry and the two-layer subgrammar

For a \(d\)-dimensional convex body \(K\), let \(\Pi K\) denote its projection body and set
\[
 R(K)=\frac{|\Pi K|}{|K|^{d-1}},\qquad
 g(d)=\frac{d^d}{d!},\qquad c_d=(d+1)g(d).
\]
Use the 005 v2 invariants
\[
 D=d+1,\qquad H(K)=1/a(K),\qquad
 Q(K)=\frac{a(K)R(K)}{g(d)},
 \qquad \frac{R(K)}{c_d}=\frac{H(K)Q(K)}D.
 \tag{1.1}
\]
The formal point has \((D,H,Q)=(1,1,1)\). Under affine joins these three coordinates become \((D_1+D_2,H_1+H_2,Q_1Q_2)\), as proved in [005 v2](../../preprints/005-simplex-product-optimum/v2/paper.md). All affine changes of coordinates here are isomorphisms of affine hulls.

Write \(T_p\) for a \(p\)-simplex. Define \(B_{p,q}=T_p\times T_q\) for any positive integers \(p,q\). The **two-layer class \(\mathcal B\)** consists of finite affine joins of points and such \(B_{p,q}\), up to invertible affine equivalence. Thus each product block has two simplex factors; no product is permitted *above* a join node. In contrast, the full point-generated class \(\mathcal C\) permits arbitrary nested products and joins and contains \(\mathcal B\).

Put \(n=p+q\). The product identity in 005 v2 yields
\[
 \boxed{
 H_{p,q}=\frac{n}{p/(p+1)+q/(q+1)},\qquad
 Q_{p,q}=\binom np\frac{p^p q^q}{n^n}
 \left(1+\frac{2pq}n\right).}
 \tag{1.2}
\]
Equivalently, \(Q_{p,q}=\binom np p^p q^q(n+2pq)/n^{n+1}\), a strictly positive rational number. The normalization is such that \(D(B_{p,q})=n+1\); each point has \(Q=1,D=H=1\).

Define
\[
 A=\frac1{11}\log\frac{189}{128},\qquad
 B=\frac14\log\frac{175}{128}.
 \tag{1.3}
\]

**Theorem 1 (two different sharp universal block constants).** For every \(p,q\ge1\),
\[
 \boxed{\log Q_{p,q}\le A(p+q+1)}
 \quad\text{with equality iff }\{p,q\}=\{5,5\},
 \tag{1.4}
\]
\[
 \boxed{\log Q_{p,q}\le B(p+q+1-H_{p,q})}
 \quad\text{with equality iff }\{p,q\}=\{4,4\}.
 \tag{1.5}
\]
The equality values are \(Q_{5,5}=189/128\), \(D_{5,5}=11\), and \(Q_{4,4}=175/128\), \(D_{4,4}-H_{4,4}=4\).

These inequalities pass unchanged to any \(K\in\mathcal B\), because \(D,H,\log Q\) are additive under joins, and points contribute \(D=H=1,\log Q=0\):
\[
 \boxed{\log Q(K)\le\min\{A D(K),\ B(D(K)-H(K))\}.}
 \tag{1.6}
\]

**Theorem 2 (exact two-layer asymptotic rate).** With \(\mathcal B_d=\{K\in\mathcal B:\dim K=d\}\),
\[
 \boxed{\lim_{d\to\infty}\sup_{K\in\mathcal B_d}R(K)^{1/d}
 = e\left(\frac{189}{128}\right)^{1/11}.}
 \tag{1.7}
\]
The corresponding single-body quantity \(Q(K)^{1/D(K)}\) attains its maximum exactly on joins of copies of \(B_{5,5}\) without extra point summands (up to the operation-grammar identification and affine equivalence). No claim of geometric uniqueness beyond this specified representation is needed.

**Theorem 3 (explicit and asymptotic depth separation).** Let
\[
 K_0=T_5,\quad K_1=(K_0\times K_0)^{*2},\quad
 K_2=(K_1\times K_1)^{*2}.
 \tag{1.8}
\]
Then \(\dim K_2=85\) and
\[
 \boxed{R(K_2)>\sup_{K\in\mathcal B_{85}}R(K).}
 \tag{1.9}
\]
Furthermore, the full point-generated class \(\mathcal C\) satisfies
\[
 \liminf_{d\to\infty}\sup_{K\in\mathcal C_d} R(K)^{1/d}
 \ge e\,Q(K_2)^{1/86}
 >e(189/128)^{1/11}.
 \tag{1.10}
\]
Thus, for all sufficiently large dimensions, an optimizer over the full recursive class **cannot** be a two-layer join of simplex products. Theorems 2–3 do not determine the optimal constant over \(\mathcal C\), nor the first dimension where the strict separation occurs.

## 2. A single analytic bound for every two-simplex product

The following inequality closes both infinite parameter tails. Let \(n=p+q\ge2\), set \(t=pq/n\). Then
\[
 \frac{n-1}{n}\le t\le\frac n4,\qquad t\ge\frac12.
\]
Using the upper Robbins bound for \(n!\) and the lower bound for \(p!,q!\), and dropping their favorable strictly positive remainder corrections, gives
\[
 \binom np\frac{p^pq^q}{n^n}
 <e^{1/(12n)}\sqrt{\frac n{2\pi pq}}.
\]
The function \(f(t)=(1+2t)/\sqrt t\) is increasing on \([1/2,\infty)\), since
\(f'(t)=(2t-1)/(2t^{3/2})\ge0\). Multiplying by the factor in (1.2) therefore gives
\[
 Q_{p,q}
 <e^{1/(12n)}\left(1+\frac n2\right)\sqrt{\frac2{\pi n}}.
 \tag{2.1}
\]
For \(0<x<1\), \(e^x<1/(1-x)\), by comparison of power series. With the certified rational bound \(\pi>\pi_0:=333/106\), define for real \(x\ge2\)
\[
 U(x)=\frac{1+x/2}{1-1/(12x)}
 \sqrt{\frac2{\pi_0 x}},\qquad \ell(x)=\log U(x).
 \tag{2.2}
\]
Then for all integers \(n=p+q\ge2\),
\[
 \boxed{Q_{p,q}<U(n).}
 \tag{2.3}
\]
The checker certifies \(333/106<\pi<355/113\) by Machin's arctangent identity and alternating Taylor series; only the lower inequality is needed for (2.2).

A direct derivative calculation gives
\[
 \ell'(x)=\frac1{x+2}-\frac1{2x}-\frac1{x(12x-1)}.
 \tag{2.4}
\]
For \(x\ge16\), \(\ell'(x)>0\), because \((x-2)(12x-1)>2(x+2)\), a quadratic inequality holding and increasing on that interval. Also \(\ell'(x)<1/(2x)\).

## 3. Proof of the sharp spectral block constant

When \(2\le n=p+q\le15\), a finite exact check compares
\[
 \boxed{Q_{p,q}^{11}\le(189/128)^{n+1}.}
 \tag{3.1}
\]
All \(56\) unordered positive pairs in this range are compared using integers and rational powers. Equality occurs only at \(p=q=5\), where the exact binomial expression is \(Q_{5,5}=189/128\). This is a valid finite part because the rest of the infinite range is handled analytically below.

For \(x\ge16\), we claim \(\ell(x)/(x+1)\) is decreasing. From (2.4),
\[
 (x+1)\ell'(x)<\frac{x+1}{2x}\le\frac{17}{32}.
 \tag{3.2}
\]
On the other hand, \(U(16)>7/4\): indeed, \(\pi_0<22/7\), and
\[
 U(16)^2>9^2\frac{2}{(22/7)16}
 =\frac{567}{176}>\left(\frac74\right)^2.
\]
Writing \(z=(7/4-1)/(7/4+1)=3/11\), the positive logarithm series yields
\[
 \ell(16)>\log(7/4)>2(z+z^3/3)>17/32.
 \tag{3.3}
\]
Because \(\ell\) increases on \([16,\infty)\), equations (3.2)–(3.3) imply
\((x+1)\ell'(x)-\ell(x)<0\), proving the claimed monotonicity. The exact rational comparison
\[
 \boxed{U(16)^{22}<(189/128)^{34}}
 \tag{3.4}
\]
is checked after replacing \(U(16)^2\) by its rational expression from (2.2). Hence, for every integer \(n\ge16\),
\[
 \frac{\log Q_{p,q}}{n+1}
 <\frac{\ell(n)}{n+1}
 \le\frac{\ell(16)}{17}
 <\frac1{11}\log(189/128)=A.
\]
Together with (3.1), this proves the first inequality of Theorem 1, including uniqueness. \(\square\)

## 4. Proof of the sharp affine-defect block constant

We first establish a uniform geometric lower bound for \(D-H\). The concave function \(s\mapsto s/(s+1)\) has, at fixed \(p+q=n\) with \(p,q\ge1\), a sum minimized at \(p=1,q=n-1\). Thus
\[
 \frac p{p+1}+\frac q{q+1}
 \ge\frac12+\frac{n-1}n=\frac{3n-2}{2n}.
\]
By (1.2),
\[
 \boxed{D-H\ge n+1-\frac{2n^2}{3n-2}
 =\frac{(n-1)(n+2)}{3n-2}\ge\frac n3.}
 \tag{4.1}
\]
The final comparison is equivalent to \(5n-6\ge0\).

For \(2\le n\le39\), the checker evaluates the exact rationals \(Q_{p,q}\) and \(D-H\), then verifies
\[
 \boxed{4\log Q_{p,q}\le(D-H)\log(175/128)}
 \tag{4.2}
\]
for all \(380\) unordered positive pairs, strictly except \(p=q=4\). Logarithms are enclosed by a finite rational `atanh` series with a proved geometric-tail bound; no floating point is used. At \((4,4)\), the equality is established directly from \(Q=175/128\) and \(D-H=4\).

For real \(x\ge40\), put \(F(x)=Bx/3-\ell(x)\), with \(B=\frac14\log(175/128)\). The positive logarithm series gives
\[
 \log(175/128)>2\frac{47}{303}=\frac{94}{303}>\frac3{10},
 \qquad B>\frac3{40}.
\]
Together with (2.4), for \(x\ge40\),
\[
 F'(x)=\frac B3-\ell'(x)
 >\frac1{40}-\frac1{2x}\ge\frac1{80}>0.
 \tag{4.3}
\]
At \(x=40\), the strict rational comparison
\[
 \boxed{U(40)^6<(175/128)^{20}}
 \tag{4.4}
\]
proves \(F(40)>0\). Therefore for every integer \(n\ge40\),
\[
 \log Q_{p,q}<\ell(n)<\frac B3n\le B(D-H).
\]
Combining with (4.2) proves the second inequality of Theorem 1, including its unique equality pair. \(\square\)

## 5. Exact asymptotics for the two-layer class

Let \(K\in\mathcal B_d\), \(D=d+1\). Join additivity, together with Theorem 1, gives (1.6) and in particular \(Q(K)\le(189/128)^{D/11}\). For every point or block \(B_{p,q}\), \(H\le D\) (for blocks this follows from \(p/(p+1)+q/(q+1)\ge1>n/(n+1)\)), so the join also satisfies \(H(K)\le D\). Hence
\[
 R(K)=g(d)H(K)Q(K)
 \le g(d)(d+1)(189/128)^{(d+1)/11}.
\]
Stirling's formula gives \(g(d)^{1/d}\to e\), and thus the limsup in (1.7) is no larger than \(e(189/128)^{1/11}\).

For the reverse inequality, given \(D=d+1\), write \(D=11k+r\), \(0\le r<11\). Join \(k\) copies of \(B_{5,5}\) and \(r\) point factors. Then \(D=11k+r\), \(H=6k+r\), \(Q=(189/128)^k\). For large \(d\), \(k\to\infty\), so \(H^{1/d}\to1\), \(k/d\to1/11\), and the resulting \(R^{1/d}\) tends to the asserted constant. This proves (1.7). It also proves the single-body spectral maximizer statement because \(\log Q/D\) is a \(D\)-weighted average of individual block rates, and the unique maximal block rate is \(A>0\); any positive point component or different block strictly lowers that average. \(\square\)

## 6. Exact dimension-85 separation

The construction (1.8) has \(K_1=B_{5,5}*B_{5,5}\). Hence \(d_1=21\), \(H_1=12\), \(Q_1=(189/128)^2\). Form the Cartesian square of \(K_1\); applying the equal-factor case of the exact product identity gives
\[
 Q(K_1\times K_1)=Q_1^2 H_1\frac{g(21)^2}{g(42)},
 \qquad H(K_1\times K_1)=H_1=12.
\]
Joining two copies of this product yields \(K_2\) with
\[
 \boxed{D_2=86,\quad H_2=24,\quad
 Q_2=\left[12\left(\frac{189}{128}\right)^4
 \frac{g(21)^2}{g(42)}\right]^2.}
 \tag{6.1}
\]
It follows from (1.1) that its normalized projection-volume ratio is the exact rational
\[
 r_2:=\frac{R(K_2)}{c_{85}}=\frac{24}{86}Q_2>13.
 \tag{6.2}
\]

Now take *any* \(K\in\mathcal B_{85}\) and set \(t=H(K)/86\in(0,1]\). By (1.6),
\[
 \frac{R(K)}{c_{85}}
 =tQ(K)\le t\min\{e^{86A},e^{86B(1-t)}\}.
 \tag{6.3}
\]
For \(t\le3/5\), this is bounded by
\[
 \frac35 e^{86A}=rac35\left(\frac{189}{128}\right)^{86/11}.
 \tag{6.4}
\]
For \(t\ge3/5\), the function \(t\mapsto t e^{86B(1-t)}\) is strictly decreasing, since its logarithmic derivative \(1/t-86B\) is negative: \(1/t\le5/3\) and \(86B>86(3/40)>5/3\). Its largest value is therefore at \(t=3/5\), giving
\[
 \frac35\left(\frac{175}{128}\right)^{43/5}.
 \tag{6.5}
\]
The checker verifies the two **integer/rational-power** inequalities
\[
 \boxed{
 \left(\frac53 r_2\right)^{11}>
 \left(\frac{189}{128}\right)^{86},\qquad
 \left(\frac53 r_2\right)^5>
 \left(\frac{175}{128}\right)^{43}.}
 \tag{6.6}
\]
These comparisons have no logarithm-interval uncertainty at all. They prove \(r_2\) exceeds both (6.4) and (6.5), yielding (1.9).

Finally the checker also verifies \(Q_2^{11}>(189/128)^{86}\), so \(Q_2^{1/86}>(189/128)^{1/11}\). Joining arbitrarily many copies of \(K_2\) and at most 85 extra points reaches every sufficiently large dimension and gives an asymptotic root rate \(e Q_2^{1/86}\) by the same Stirling argument as in Section 5. This proves (1.10) and the eventual strict depth separation. \(\square\)

## 7. Replay, certification and scope

Run

```sh
python3 notes/two-layer-projection-depth-separation/code/check.py
python3 -O notes/two-layer-projection-depth-separation/code/check.py
```

The [checker](code/check.py) independently evaluates \(Q_{p,q}\), \(H_{p,q}\), the 56 sharp-spectral finite cases, the 380 sharp-defect finite cases, the two unbounded-tail rational base inequalities, and all explicit 85-dimensional separations. Every logarithm on the finite defect core is bounded by twenty rational terms of \(\log y=2\operatorname{artanh}((y-1)/(y+1))\) after exact power-of-two normalization. The remainder is bounded by \(2z^{41}/(41(1-z^2))\) with \(0\le z\le1/3\). Machin's identity \(\pi=16\arctan(1/5)-4\arctan(1/239)\), checked via alternating rational Taylor series, certifies the \(\pi\) bounds. Exact fractional comparisons, not decimal estimates, decide every certificate branch. The full infinite-dimensional statements also depend on the **explicit elementary derivative and Stirling arguments** displayed above; they are not inferred from finite enumeration.

This is a new sharp classification of the **specified two-layer class**, not a proof of the optimum over the unrestricted product/join class \(\mathcal C\) or all convex bodies. Historical 005 v2/v5 proofs and the separate sharp dimension-48 note remain unchanged; the latter's finite optima are compatible with a strict depth separation first established here at dimension 85. The actual earliest strict crossover dimension is not asserted. Neither full proof-assistant formalization nor external peer review has been performed.
