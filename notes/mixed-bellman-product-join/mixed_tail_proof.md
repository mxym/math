# Exact proof of the imbalanced dimension tails for the mixed Bellman envelope

This note certifies the product step with constants
\[
 \alpha=87/2000,\qquad \beta=11/2000,\qquad T=\alpha+\beta=49/1000.
\]
It covers every pair of integer dimensions
\[
 1\le r<200,\qquad s\ge200,
\]
and every real auxiliary state
\[
 2\le H\le r+1,\qquad 2\le J\le s+1.
\]
The proposed invariant is
\[
 \log Q\le T D-\alpha H^2/D-\beta H^4/D^3.
\]
Only the product closure is at issue here; convexity of the homogeneous
perspectives \(H^2/D\) and \(H^4/D^3\) gives join closure directly.

## 1. A concave relaxation of the exact product violation

Put \(n=r+s\), \(C=g(r)g(s)/g(n)\), and
\[
 x=\frac{sH+rJ}{n},\qquad
 H'=\frac{nHJ}{rJ+sH}.
\]
The exact product closure condition is
\[
 \log(Cx)-\alpha G_2-\beta G_4+T\le0,
\]
where
\[
 G_p=\frac{H^p}{(r+1)^{p-1}}+
       \frac{J^p}{(s+1)^{p-1}}-
       \frac{(H')^p}{(n+1)^{p-1}}.
\]
Weighted harmonic mean is at most weighted arithmetic mean and at most the
weighted fourth power mean. Consequently
\[
 G_2\ge q_2:=\frac{H^2}{r+1}+\frac{J^2}{s+1}
                 -\frac{(rH+sJ)^2}{n^2(n+1)},
\]
\[
 G_4\ge q_4:=A H^4+B J^4,
\]
\[
 A=\frac1{(r+1)^3}-\frac{r}{n(n+1)^3}>0,
 \qquad
 B=\frac1{(s+1)^3}-\frac{s}{n(n+1)^3}>0.
\]
Thus it suffices to bound
\[
 f=\log(Cx)-\alpha q_2-\beta q_4+T.
\]
The form \(q_2\) is positive definite: weighted Cauchy gives
\[
 (rH+sJ)^2\le
 \left(\frac{H^2}{r+1}+\frac{J^2}{s+1}\right)
 \bigl(r^2(r+1)+s^2(s+1)\bigr),
\]
and
\[
 n^2(n+1)-r^2(r+1)-s^2(s+1)=rs(3n+2)>0.
\]
Therefore \(f\) is strictly concave on its state rectangle.

## 2. Replace an infinite dimension by a compact real interval

Set \(z=1/s\), \(h=H\), and \(j=J/(s+1)\). The actual states belong to
the larger fixed box
\[
 \mathcal B_r=[2,r+1]\times[0,1].
\]
Robbins' bounds write
\[
 g(k)=\frac{e^k}{\sqrt{2\pi k}}e^{-\delta_k},
 \qquad \frac1{12k+1}<\delta_k<\frac1{12k}.
\]
Since \(n\ge s+1\), we have \(\delta_n-\delta_s<0\), so
\[
 C<g(r)e^{-r}\sqrt{1+rz}.
\]
Hence the logarithmic term is bounded above by
\[
 \log g(r)-r+\log\bigl(h+r(1+z)j\bigr)
                   -\tfrac12\log(1+rz).
\]
There is no singularity at \(z=0\) in the following exact rational
cancellation formulas. Define
\[
 P_2=(1+rz)^2(1+(r+1)z),\qquad
 S_2=3+(3r+2)z+r(r+1)z^2,
\]
\[
 P_4=(1+rz)(1+(r+1)z)^3,
\]
\[
 S_4=4+(6r+9)z+(4r^2+9r+6)z^2+(r+1)^3z^3.
\]
Direct expansion gives
\[
 q_2=a h^2+b h j+c j^2,
\]
\[
 a=\frac1{r+1}-\frac{r^2z^3}{P_2},\qquad
 b=-\frac{2rz(1+z)}{P_2},\qquad
 c=\frac{r(1+z)S_2}{P_2},
\]
and
\[
 q_4=a_4h^4+d_4j^4,
\]
\[
 a_4=\frac1{(r+1)^3}-\frac{rz^4}{P_4},\qquad
 d_4=\frac{r(1+z)S_4}{P_4}.
\]
The resulting function
\[
 F_{r,z}(h,j)=\log g(r)-r+\log\bigl(h+r(1+z)j\bigr)
 -\tfrac12\log(1+rz)-\alpha q_2-\beta q_4+T
\]
dominates the exact product violation. It remains to prove
\[
 F_{r,z}<0\quad
 (1\le r<200,\quad 0\le z\le1/200,\quad(h,j)\in\mathcal B_r).
\]
At \(z=0\), these formulas mean their continuous algebraic extensions;
including that endpoint strengthens the required finite-dimensional claim.

## 3. Rigorous supporting bounds on each real interval

Fix a rational interval \(I=[z_0,z_1]\) and a rational point
\(p=(h_0,j_0)\in\mathcal B_r\). Rational interval arithmetic encloses all
five coefficient functions on \(I\). Write their enclosures as
\(a\in[a_-,a_+]\), \(b\in[b_-,b_+]\), and \(c\in[c_-,c_+]\), and put
\[
 m_h=a_-/2,\qquad
 m_j=c_- -\frac{\max(b_-^2,b_+^2)}{2a_-}.
\]
The checker requires both \(m_h,m_j>0\). Young's inequality then gives,
uniformly for \(z\in I\),
\[
 q_2(\Delta h,\Delta j)\ge
 m_h(\Delta h)^2+m_j(\Delta j)^2.
\]
The logarithm is concave and \(q_4\) is convex. The exact quadratic
expansion of \(q_2\) therefore gives the stronger supporting inequality
\[
 F_{r,z}(y)\le F_{r,z}(p)+\nabla F_{r,z}(p)\cdot(y-p)
 -\alpha\left(m_h(\Delta h)^2+m_j(\Delta j)^2\right).
\]
The gradient components are rational functions:
\[
 F_h=\frac1{h+r(1+z)j}
 -\alpha(2ah+bj)-4\beta a_4h^3,
\]
\[
 F_j=\frac{r(1+z)}{h+r(1+z)j}
 -\alpha(bh+2cj)-4\beta d_4j^3.
\]
Each is enclosed on \(I\) using rational interval arithmetic.

For an enclosed gradient \(g\in[g_-,g_+]\) and displacement interval
\([L,U]\) with \(L\le0\le U\), the maximum of
\(g\Delta-\alpha m\Delta^2\) is bounded exactly by maximizing
\(g_-\Delta-\alpha m\Delta^2\) on \([L,0]\) and
\(g_+\Delta-\alpha m\Delta^2\) on \([0,U]\). Each maximizer is the
rational point \(g_\pm/(2\alpha m)\) clipped to its interval. The checker
adds these two coordinate bounds to the interval upper bound for
\(F_{r,z}(p)\).

## 4. Exact evidence and completeness

`mixed_tail_certificate.json` gives rational supporting points on dyadic
subintervals of \([0,1/200]\), separately for each integer \(1\le r<200\).
`check_mixed_tail.py` checks every cell using the preceding formulas, then
sorts each dimension's intervals and verifies that they meet exactly from
zero to \(1/200\), with neither a gap nor an overlap. Thus no real \(z\)
or auxiliary state is omitted.

All proof decisions use Python integers and `Fraction`; the checker imports
no numerical optimization package and uses no floating-point comparisons.
Logarithm bounds use the rational identity
\[
 \log x=2\sum_{k\ge0}\frac{w^{2k+1}}{2k+1},
 \qquad w=\frac{x-1}{x+1},
\]
after power-of-two range reduction to \(1\le x\le2\). Twenty-eight terms
give a lower bound, and the omitted tail is at most
\[
 \frac{2w^{57}}{57(1-w^2)}.
\]
Each logarithm interval is rounded outward to denominator \(10^{24}\).
This rounding is itself integer arithmetic and preserves the enclosure.

The separate generator uses numerical optimization only to propose
supporting points. It accepts a cell only after the same exact supporting
bound passes. Those numerical proposals are unnecessary to the proof:
the saved certificate is replayed by the exact checker and separately audited.

Run the exact verifier from any directory:

```text
python check_mixed_tail.py
python -O check_mixed_tail.py
```

The output records the cell count, maximum subdivision depth, certificate
SHA-256, and a uniform exact negative endpoint. Together with the finite
dimension certificate and the analytic large-dimension lemma, this proves
the mixed invariant for the complete point-generated product/join class.
