# Exact finite tangent certificate for the mixed quadratic/quartic envelope

This note proves the finite part of a proposed stronger Bellman envelope for entry 005. It supersedes the weaker linear envelope as the active research direction. The current public quadratic Bellman bound \(\Gamma_{\mathcal C}<2.8589\) is acknowledged as completed work. The finite result below is not by itself a global growth bound: the infinite dimension tails must be proved separately before making that claim.

## Proposition

Set
\[
\alpha=\frac{87}{2000},\qquad
\beta=\frac{11}{2000},\qquad
T=\frac{49}{1000}=\alpha+\beta.
\]
For every integer pair \(1\le r\le s\le199\), put \(n=r+s\), and define on the rectangle
\[
\mathcal B_{r,s}=[2,r+1]\times[2,s+1]
\]
the following functions:
\[
C=\frac{g(r)g(s)}{g(n)},\qquad
x=\frac{rJ+sH}{n},\qquad
v=rH+sJ,
\]
\[
G_2=\frac{H^2}{r+1}+\frac{J^2}{s+1}
-\frac{v^2}{n^2(n+1)},
\]
\[
A=\frac1{(r+1)^3}-\frac r{n(n+1)^3},\qquad
B=\frac1{(s+1)^3}-\frac s{n(n+1)^3},\qquad
G_4=AH^4+BJ^4.
\]
Then, for every real \((H,J)\in\mathcal B_{r,s}\),
\[
\boxed{
 f_{r,s}(H,J):=\log(Cx)-\alpha G_2-\beta G_4+T
 <-\frac3{2000}<0.
}
\tag{1}
\]
The statement includes every real auxiliary state in all 19,900 rectangles, not just the finitely stored tangent points.

## 1. Relevance to the invariant calculus

The intended global potential is
\[
P(D,H)=TD-\alpha\frac{H^2}{D}-\beta\frac{H^4}{D^3}.
\tag{2}
\]
It vanishes at the formal point \((D,H)=(1,1)\), because \(T=\alpha+\beta\). The perspective functions \(H^2/D\) and \(H^4/D^3\) are subadditive under simultaneous addition of positive \((D,H)\): this follows by weighted Jensen's inequality for the convex functions \(u^2,u^4\). Consequently \(P\) is superadditive under joins, and the region \(\log Q\le P(D,H)\) is preserved by joins.

For a product of factors of dimensions \(r,s\), the exact entry-005 calculus gives
\[
D'=r+s+1,
\quad H'=\frac n{r/H+s/J},
\quad Q'=Q_AQ_BCx.
\]
The actual product gain available in (2) is
\[
P(D',H')-P(r+1,H)-P(s+1,J)
=-T+\alpha\widehat G_2+\beta\widehat G_4,
\]
where
\[
\widehat G_2=\frac{H^2}{r+1}+\frac{J^2}{s+1}-\frac{(H')^2}{n+1},
\]
\[
\widehat G_4=\frac{H^4}{(r+1)^3}+\frac{J^4}{(s+1)^3}-\frac{(H')^4}{(n+1)^3}.
\]
Weighted harmonic mean is at most weighted arithmetic mean, so
\(H'\le v/n\), and hence \(\widehat G_2\ge G_2\). By the fourth-power mean inequality,
\[
(H')^4\le\frac{rH^4+sJ^4}{n},
\]
so \(\widehat G_4\ge G_4\). Thus (1) proves the needed product inequality on the entire finite region.

The box lower bound \(H,J\ge2\) is valid in the point-generated recursive class: positive-dimensional generators begin with an interval, joins add \(H\), and products take dimension-weighted arithmetic means of \(a=1/H\). The upper bounds \(H\le r+1,J\le s+1\) are inherited from \(a\ge1/(d+1)\).

## 2. Global concavity makes one tangent point sufficient

The matrix of \(G_2\) is positive definite. Indeed, by weighted Cauchy's inequality,
\[
(rH+sJ)^2\le
\bigl(r^2(r+1)+s^2(s+1)\bigr)
\left(\frac{H^2}{r+1}+\frac{J^2}{s+1}\right).
\]
The coefficient
\[
q=\frac{r^2(r+1)+s^2(s+1)}{n^2(n+1)}<1,
\]
because
\[
n^2(n+1)-r^2(r+1)-s^2(s+1)=rs(3n+2)>0.
\]
Therefore \(G_2\) is bounded below by the positive definite quadratic
\((1-q)(H^2/(r+1)+J^2/(s+1))\). Also \(A,B>0\), directly from \(n>r,s\), so \(G_4\) is convex. The logarithm of the positive affine function \(x\) is concave. Since \(\alpha>0\), the function \(f_{r,s}\) is strictly concave on the positive quadrant.

For any rational point \(p=(h,j)\) inside the rectangle, differentiable concavity gives
\[
f_{r,s}(H,J)\le
f_{r,s}(p)+\partial_Hf(p)(H-h)+\partial_Jf(p)(J-j).
\tag{3}
\]
The derivatives are entirely rational at rational \(p\):
\[
\partial_H f=
\frac{s}{nx}
-\alpha\left(\frac{2H}{r+1}-\frac{2rv}{n^2(n+1)}\right)
-4\beta AH^3,
\tag{4}
\]
\[
\partial_J f=
\frac{r}{nx}
-\alpha\left(\frac{2J}{s+1}-\frac{2sv}{n^2(n+1)}\right)
-4\beta BJ^3.
\tag{5}
\]
Write these derivatives as \(u,w\). The maximum of the right-hand linear part in (3) over the rectangle is exactly
\[
S_p=
 u\bigl(e_r(u)-h\bigr)+w\bigl(e_s(w)-j\bigr),
\quad
 e_d(t)=\begin{cases}d+1,&t\ge0,\\2,&t<0.\end{cases}
\tag{6}
\]
This formula also works for the degenerate interval \([2,2]\) when a dimension equals one.

It is therefore sufficient to enclose \(f(p)\) rigorously from above and check
\[
\overline{f(p)}+S_p<-3/2000.
\tag{7}
\]
No condition on the quality or optimality of the point is needed. Numerical optimization is allowed to propose a point, but only (7) is a proof decision.

## 3. Rational point certificate and exact logarithms

The certificate `mixed_finite_points.json` contains exactly one point for every integer pair \(1\le r\le s\le199\), with common denominator \(10^9\). Its rows are
\[
[r,s,h_{r,s}^{\rm num},j_{r,s}^{\rm num}],
\quad
p_{r,s}=\left(\frac{h_{r,s}^{\rm num}}{10^9},
\frac{j_{r,s}^{\rm num}}{10^9}\right).
\]
`check_finite.py` verifies the constants, row order, complete coverage, integer types, and membership of each point in its rectangle. Thus no claimed coverage is inferred from the producer's behavior.

Only \(\log C\) and \(\log x\) need interval arithmetic. For any positive rational \(y\), write \(y=2^k a\) with \(1\le a<2\), and put \(z=(a-1)/(a+1)\in[0,1/3)\). For \(N=20\),
\[
\log a=2\sum_{i=0}^{N-1}\frac{z^{2i+1}}{2i+1}+\mathcal R_N,
\qquad
0\le\mathcal R_N\le
\frac{2z^{2N+1}}{(2N+1)(1-z^2)}.
\tag{8}
\]
This follows by integrating the geometric series for \(1/(1-u^2)\), or by bounding each omitted denominator below by \(2N+1\). The same formula at \(z=1/3\) encloses \(\log2\). When \(k<0\), interval endpoints are swapped before multiplication by \(k\).

For efficient exact arithmetic, each proved logarithm interval is widened outward to denominator \(2^{96}\): the lower endpoint is rounded down and the upper endpoint is rounded up by integer division. This rounding preserves containment and is an explicit rational operation. It prevents factorial-log sums from acquiring unnecessarily large common denominators.

The checker caches intervals for all integer logarithms through 398 and sums them to enclose \(\log m!\). It uses the exact identity
\[
\log C=r\log r+s\log s-n\log n
+\log(n!)-\log(r!)-\log(s!).
\tag{9}
\]
All negative coefficients swap the interval endpoints. The logarithm of rational \(x\) uses (8) directly. Every other term in (4)–(7) is computed exactly with Python's arbitrary-precision integers and `Fraction`.

## 4. Exact replay result

All 19,900 rectangles pass the strict tangent inequality. The checker independently verifies the stronger uniform statement that the greatest upper bound is below \(-3/2000\).

The greatest certified upper bound occurs at \((r,s)=(5,5)\), at the stored rational point
\[
p=\left(\frac{5995534181}{10^9},\frac{5995534181}{10^9}\right),
\]
and is exactly
\[
-\frac{
4413660883391528808456775345099078038506643341751217747172653805929
}{
2822843300471492517091967238144000000000000000000000000000000000000000
}
<-\frac3{2000}.
\tag{10}
\]
The approximation \(-0.00156355\) is useful for scale but is not used in any proof decision.

Combining (3), (6), and the exact comparison (7) proves (1) at every real point of every rectangle. This completes the finite proposition.

Run:

```sh
python3 check_finite.py mixed_finite_points.json --quiet --report finite_report.json
python3 -O check_finite.py mixed_finite_points.json --quiet --report finite_report_optimized.json
```

The verifier imports neither SciPy nor the point generator and uses no floating-point arithmetic in a mathematical comparison. Explicit exceptions retain all checks with `python -O`. The report contains the exact worst interval, point, gradients, support correction, and uniform strict margin. Both ordinary Python and `python -O` completed successfully, and their JSON reports are byte-identical.

`generate_finite_points.py` is supplied only to reproduce the discovery process. Its numerical convergence is not an assumption: arbitrary proposed points are accepted only after the exact independent tangent check.

## Remaining global obligation

The assembled proof in `proof.md` also certifies the product inequality when \(s\ge200\) and \(r\le199\), and when both dimensions are sufficiently large. Those regions are handled separately by the team's analytic/interval tail proofs. All three regions have now passed exact replay and separate mathematical audit; the all-dimensional theorem is stated in `proof.md`.
