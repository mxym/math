# A certified two-sided interval for the binary T5 recursion

Entry 005 continuation — 7 October 2026.

This note strengthens the existing lower-endpoint certificate for the binary
self-similar family
\[
K_0=T_5,\qquad K_{j+1}=(K_j\times K_j)*(K_j\times K_j).
\]
It does not introduce a new construction.  Its purpose is to remove essentially
all numerical uncertainty in the limiting rate of this particular orbit.

The inherited exact calculus gives
\[
d_j=\frac{16\cdot4^j-1}{3},\qquad
a_j=\frac1{6\cdot2^j},\qquad
R_{j+1}=R_j^4D_j,
\]
with \(R_0=625/4\), and
\[
D_j=2a_j\frac{g(4d_j+1)}{g(2d_j)^2},\qquad
g(n)=\frac{n^n}{n!}.
\]
Write
\[
\Lambda_{2,5}=\lim_{j\to\infty}R_j^{1/d_j}.
\]

## Theorem

\[
\boxed{
2.853465550695797
<
\Lambda_{2,5}
<
2.853465550704.
}
\]

Thus the certified interval has width less than \(8.3\times10^{-12}\).
In particular, the earlier strict lower endpoint
\(2.85346555052\) remains correct but is no longer the sharpest certified
statement for this orbit.

This theorem concerns only the displayed T5 recursion.  It does **not** prove
that this orbit is optimal in the full point-generated product/join class
\(\mathcal C\), whose global Bellman upper bound remains separate.

## 1. Exact step-factor form

Put
\[
q_j=2d_j=\frac{32\cdot4^j-2}{3}.
\]
The identity already used in the preceding certificate is
\[
D_j=
2a_j\,
\frac{4^{q_j}}{\binom{2q_j}{q_j}}
\left(1+\frac1{2q_j}\right)^{2q_j}.
\tag{1}
\]

We use Robbins' strict Stirling inequalities
\[
\sqrt{2\pi}\,m^{m+1/2}e^{-m+1/(12m+1)}
<
m!
<
\sqrt{2\pi}\,m^{m+1/2}e^{-m+1/(12m)}.
\]
They imply
\[
\binom{2q}{q}
<
\frac{4^q}{\sqrt{\pi q}}
\exp\!\left(\frac1{24q}-\frac2{12q+1}\right)
\tag{2}
\]
and
\[
\binom{2q}{q}
>
\frac{4^q}{\sqrt{\pi q}}
\exp\!\left(\frac1{24q+1}-\frac1{6q}\right).
\tag{3}
\]

For \(n>1\), the alternating logarithm series gives
\[
1-\frac1{2n}
<
n\log\left(1+\frac1n\right)
<
1-\frac1{2n}+\frac1{3n^2}.
\tag{4}
\]
We apply this with \(n=2q\).

## 2. A uniform lower tail from j=7

Combining (1), (2), and the lower half of (4) gives
\[
D_j>
\frac13
\sqrt{\frac\pi3\left(32-\frac2{4^j}\right)}
\exp(y_-(q_j)),
\]
where
\[
y_-(q)=1+\frac2{12q+1}-\frac7{24q}.
\tag{5}
\]
The square-root factor increases with \(j\).  Also
\[
y_-'(q)=
-\frac{24}{(12q+1)^2}+\frac7{24q^2}>0,
\]
because
\(7(12q+1)^2>576q^2\).  Hence the right side of (5) is minimized
at \(j=7\).

Machin's identity
\[
\pi=16\arctan(1/5)-4\arctan(1/239)
\]
with alternating rational truncations, followed by the positive degree-14
Taylor polynomial for \(e^{y_-(q_7)}\), gives the exact rational
comparison
\[
D_j>5.24519195\qquad(j\ge7).
\tag{6}
\]
The checker performs the comparison after squaring, so no numerical square
root is trusted.

## 3. Upper factors

Using (3) and the upper half of (4) gives the specific estimate
\[
D_7<
\frac13
\sqrt{\frac\pi3\left(32-\frac2{4^7}\right)}
\exp\!\left(
1+\frac1{6q_7}-\frac1{24q_7+1}
-\frac1{4q_7}+\frac1{12q_7^2}
\right).
\]
Exact rational upper bounds for \(\pi\) and the exponential prove
\[
D_7<5.245192.
\tag{7}
\]

For every \(j\ge8\), use only
\[
\left(1+\frac1{2q}\right)^{2q}<e,
\qquad
32-\frac2{4^j}<32.
\]
The correction
\[
u(q)=\frac1{6q}-\frac1{24q+1}
\]
is strictly decreasing for \(q>0\).  Therefore (1) and (3) imply
\[
D_j<
\frac13\sqrt{\frac{32\pi}{3}}
\exp(1+u(q_8))
<5.245207
\qquad(j\ge8),
\tag{8}
\]
where the last comparison is again an exact rational Machin/Taylor check.

## 4. Restarted limit formula

For every fixed \(J\), the exact recurrence gives
\[
\log\Lambda_{2,5}
=
\frac{
\log R_J+
\sum_{t\ge0}4^{-t-1}\log D_{J+t}}
{d_J+1/3}.
\tag{9}
\]
Let \(E_J=3d_J+1\).  Multiplying (9) by \(E_J\), the tail weights become
\(3\cdot4^{-t-1}\), whose sum is one.

At \(J=7\), (6) therefore yields
\[
\Lambda_{2,5}^{E_7}
>
R_7^3(5.24519195),
\qquad
E_7=262144.
\tag{10}
\]
The checker reconstructs \(R_7\) exactly and proves by a single integer
comparison that
\[
(2.853465550695797)^{262144}
<
R_7^3(5.24519195).
\tag{11}
\]

For the upper bound, \(d_8=4d_7+1\), hence
\[
E_8=4E_7=1048576,
\qquad
R_8=R_7^4D_7.
\]
Equations (7)--(9) give
\[
\Lambda_{2,5}^{E_8}
<
R_7^{12}(5.245192)^3(5.245207).
\tag{12}
\]
A second exact integer comparison proves
\[
R_7^{12}(5.245192)^3(5.245207)
<
(2.853465550704)^{1048576}.
\tag{13}
\]
Equations (10)--(13) prove the theorem.

## 5. Verification

Run from this directory:

```sh
python3 check_limit_interval.py
python3 -O check_limit_interval.py
```

The checker uses only Python's standard library, integers, and
`fractions.Fraction`.  Every proof decision is exact.  It verifies:

- rational lower and upper Machin bounds for \(\pi\);
- the lower factor (6);
- the specific upper factor (7);
- the uniform upper tail (8);
- the exact T5 recurrence through \(R_7\);
- the integer endpoint comparisons (11) and (13).

The analytic monotonicity statements reducing the infinite tails to the
checked rational endpoints are written above; the finite arithmetic checker
does not replace them.

## Scope

This is an additive refinement of
`notes/mixed-bellman-product-join/sharpened-binary-lower/`.
No old certificate is modified or invalidated.  There is no claim of
optimality of the T5 recursion, no new unrestricted convex-body bound, no
priority claim, and no assertion of proof-assistant or human-referee
verification.
