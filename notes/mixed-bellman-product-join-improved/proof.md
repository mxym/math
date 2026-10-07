# Improved mixed quadratic/quartic Bellman bound

## 1. Statement and inherited calculus

Let \(\mathcal C\) be the class generated from a formal point by finitely
many Cartesian products and joins, modulo invertible affine maps on affine
hulls. For positive-dimensional \(K\), put
\[
d=\dim K,\quad D=d+1,\quad H=1/a(K),\quad
Q=\frac{a(K)R(K)}{g(d)},\qquad g(d)=\frac{d^d}{d!}.
\]
For the formal point set \((D,H,Q)=(1,1,1)\).

The exact calculus established in entry 005 v2 is
\[
(D,H,Q)(A*B)=(D_A+D_B,H_A+H_B,Q_AQ_B),
\]
and, for a product of dimensions \(r,s\),
\[
H'=\frac{r+s}{r/H_1+s/H_2},
\]
\[
Q'=Q_1Q_2\frac{g(r)g(s)}{g(r+s)}
\frac{sH_1+rH_2}{r+s}.
\]
Every positive-dimensional state in this class satisfies
\[
2\le H\le d+1.
\]
The upper bound is the inherited inequality \(a\ge1/(d+1)\); the lower
bound follows because the interval has \(H=2\), joins add \(H\), and
products average \(a=1/H\), preserving \(a\le1/2\).

Define
\[
\alpha=\frac{271}{6250},\qquad
\beta=\frac{5453}{10^6},\qquad
T=\alpha+\beta=\frac{48813}{10^6}.
\]
We prove
\[
\boxed{\log Q(K)\le
\alpha\left(D-\frac{H^2}{D}\right)
+\beta\left(D-\frac{H^4}{D^3}\right).}\tag{1}
\]

For joins, the perspective inequalities
\[
\frac{(H_1+H_2)^p}{(D_1+D_2)^{p-1}}
\le \frac{H_1^p}{D_1^{p-1}}+\frac{H_2^p}{D_2^{p-1}},
\qquad p=2,4,
\]
make (1) automatic. The point has equality. It remains to check products.

## 2. Product reduction

Let \(n=r+s\), \(h=H_1\), \(j=H_2\),
\[
C=\frac{g(r)g(s)}{g(n)},\qquad
x=\frac{s h+r j}{n}.
\]
As in the published mixed-Bellman proof, weighted harmonic mean is bounded
by the corresponding arithmetic and fourth-power means. Hence product
closure follows from strict negativity of
\[
f_{r,s}(h,j)=\log(Cx)-\alpha G_2(h,j)-\beta G_4(h,j)+T,\tag{2}
\]
where
\[
G_2=\frac{h^2}{r+1}+\frac{j^2}{s+1}
-\frac{(rh+sj)^2}{n^2(n+1)},
\]
and
\[
G_4=A_4h^4+B_4j^4,
\]
\[
A_4=\frac1{(r+1)^3}-\frac r{n(n+1)^3},\qquad
B_4=\frac1{(s+1)^3}-\frac s{n(n+1)^3}.
\]
Both quartic coefficients are positive. The quadratic form \(G_2\) is
positive definite, with determinant
\[
\frac{rs(3n+2)}{(r+1)n^2(s+1)(n+1)}>0.
\]
Therefore (2) is strictly concave on the positive quadrant. A supporting
plane at one rational point bounds an entire state rectangle.

We split all dimension pairs into three exhaustive regions.

## 3. Finite rectangles: \(1\le r\le s\le199\)

The certificate `mixed_finite_points.json` contains one rational supporting
point in each of the 19,900 rectangles
\[
[2,r+1]\times[2,s+1].
\]
`check_finite.py` recomputes the exact rational gradient and an outward
rational interval for the logarithm, then maximizes the supporting plane on
the whole rectangle by choosing the appropriate endpoints. Strict
concavity makes this a global upper bound, not a sampled-grid test.

All rectangles pass with strict negative upper bound. The closest rectangle
is \((r,s)=(5,5)\), whose certificate uses \((h,j)=(6,6)\). Its exact
upper margin is stored in `finite_report.json`; it is approximately
\(-1.12\times10^{-5}\).

The logarithm checker uses the convergent atanh series with an explicit
geometric remainder and outward dyadic rounding. No floating-point value is
used in a proof decision.

## 4. Imbalanced tail: \(1\le r<200\le s\)

Put
\[
z=1/s\in(0,1/200],\qquad h=H_1,\qquad u=H_2/(s+1)\in[0,1].
\]
The published mixed-Bellman argument gives exact regular formulas on the
compact box \([2,r+1]\times[0,1]\):
\[
G_2=a h^2+bhu+c u^2,
\qquad
G_4=a_4h^4+d_4u^4,
\]
with rational functions of \((r,z)\) whose denominators stay positive on
the closed interval. The factorial ratio obeys
\[
C\le g(r)e^{-r}\sqrt{1+rz}.
\]
Thus the product violation is bounded by a strictly concave function with a
uniform negative quadratic remainder. Young's inequality turns interval
bounds for the quadratic coefficients into two separated scalar parabolas;
each is maximized exactly at a clipped rational vertex.

`mixed_tail_certificate.json` contains 22,311 dyadic cells, of maximum depth
8, covering every \(r=1,\dots,199\) and the entire interval
\([0,1/200]\). `check_mixed_tail.py` recomputes the interval bounds and
requires exact adjacency of all cells, so gaps and overlaps are rejected.
Every cell has certified upper bound less than \(-10^{-8}\). The worst cell
and SHA-256 are recorded in `tail_report.json`.

The endpoint \(z=0\) is only a regular limiting parameter used to close the
compact interval; it is not an infinite-dimensional body.

## 5. Both dimensions at least 200

Let
\[
\delta=4rs+3n+2,\qquad k=\frac{3n+2}{\delta}.
\]
Direct expansion gives the nonnegative-square identity
\[
G_2-kx^2=
\frac{rs}{(r+1)n^2(s+1)(n+1)\delta}
\big[(s+1)(3r+s+2)h-(r+1)(r+3s+2)j\big]^2\ge0.
\]
Dropping the nonnegative quartic contribution increases (2), hence
\[
f_{r,s}\le \log(Cx)-\alpha kx^2+T.
\]
Maximizing in \(x>0\) shows it is enough to prove
\[
\frac{C^2}{k}<2\alpha e^{1-2T}.\tag{3}
\]
The normalized factorial sequence argument in the predecessor proof gives
\[
C^2<\frac{n}{2\pi rs}.
\]
For \(r,s\ge200\),
\[
\frac{C^2}{k}
<\frac2\pi\left(\frac{n}{3n+2}+\frac{n}{4rs}\right)
<\frac{2/3+1/200}{\pi}.\tag{4}
\]

`check_large_200.py` certifies (3)--(4) without floating point. A Machin
alternating-series estimate supplies a rational lower bound for \(\pi\),
and the positive degree-7 Taylor polynomial gives a rational lower bound for
\[
\exp(1-2T)=\exp(451187/500000).
\]
The resulting strict rational margin is printed by the checker. The script
also replays the nonnegative-square identity at representative exact inputs.

This proves (1) for every finite product/join tree.

## 6. Asymptotic consequence

The spectral reduction already established for entry 005 says
\[
\Gamma_{\mathcal C}=e\sup_{K\in\mathcal C}Q(K)^{1/(d+1)}.
\]
From (1),
\[
Q(K)^{1/D}\le e^T,
\]
so
\[
\Gamma_{\mathcal C}\le e^{1+T}=e^{1.048813}.
\]
`check_large_200.py` gives an exact positive-series/geometric-tail upper
bound proving
\[
\boxed{e^{1.048813}<2.854262.}
\]
Together with the inherited certified construction,
\[
\boxed{2.8534<\Gamma_{\mathcal C}<2.854262.}
\]
The theorem does not identify the optimum and does not apply to arbitrary
convex bodies outside the point-generated product/join class.
