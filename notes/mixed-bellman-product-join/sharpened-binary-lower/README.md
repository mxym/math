# Sharpened lower endpoint for the binary T5 recursion

Entry 005 continuation — 7 October 2026.

This note sharpens the certified lower endpoint for the binary self-similar
family
\[
K_0=T_5,\qquad K_{j+1}=(K_j\times K_j)*(K_j\times K_j).
\]
No new construction is introduced. The previously used tail estimate
\(D_j>3\) is very wasteful: the exact step factors are already larger than
5 and converge to about 5.2452057.

Write
\[
d_j=\dim K_j,\qquad a_j=a(K_j),\qquad R_j=R(K_j).
\]
The inherited exact calculus gives
\[
d_j=\frac{16\cdot4^j-1}{3},\qquad
a_j=\frac1{6\cdot2^j},
\]
and
\[
R_{j+1}=R_j^4D_j,\qquad
D_j=2a_j\frac{g(4d_j+1)}{g(2d_j)^2},
\qquad g(n)=\frac{n^n}{n!}.
\]

The original result of this file is
\[
\Lambda_{2,5}>2.85346555052,
\qquad
\Lambda_{2,5}=\lim_{j\to\infty}R_j^{1/d_j}.
\]
It remains a valid short certificate.

A stronger additive companion now proves the two-sided interval
\[
\boxed{
2.853465550695797<\Lambda_{2,5}<2.853465550704.
}
\]
See [LIMIT_INTERVAL.md](LIMIT_INTERVAL.md) and
[check_limit_interval.py](check_limit_interval.py).  Consequently the full
point-generated product/join class satisfies
\[
\boxed{
2.853465550695797<\Gamma_{\mathcal C}<2.85386,
}
\]
using the separately certified positive-sextic Bellman upper theorem.

## 1. A uniform tail factor D_j > 5.245

Put
\[
q=2d_j.
\]
The exact identity used already in entry 005 v2 is
\[
\frac{g(2q+1)}{g(q)^2}
=
\frac{4^q}{\binom{2q}{q}}
\left(1+\frac1{2q}\right)^{2q}.
\]
Hence
\[
D_j=
2a_j\frac{4^q}{\binom{2q}{q}}
\left(1+\frac1{2q}\right)^{2q}.
\tag{1}
\]

Robbins' Stirling inequalities imply
\[
\binom{2q}{q}
<
\frac{4^q}{\sqrt{\pi q}}.
\tag{2}
\]
Indeed, use the upper Robbins bound for \((2q)!\) and the lower bound for
both factors \(q!\). The extra exponential factor is
\[
\exp\!\left(\frac1{24q}-\frac2{12q+1}\right)<1.
\]

Let
\[
n=2q=4d_j=\frac{64\cdot4^j-4}{3}.
\]
For every \(n\ge1\),
\[
\log\left(1+\frac1n\right)>\frac1n-\frac1{2n^2},
\]
so
\[
\left(1+\frac1n\right)^n
>
\exp\left(1-\frac1{2n}\right).
\tag{3}
\]

For \(j\ge7\),
\[
n\ge n_7=349524
\]
and
\[
2a_j\sqrt{\pi q}
=
\frac13
\sqrt{\frac{\pi}{3}\left(32-\frac2{4^j}\right)}.
\]
Using the classical rational lower bound
\[
\pi>\frac{333}{106},
\]
equations (1)--(3) imply
\[
D_j>
\frac13
\sqrt{
\frac{333}{106}\,
\frac{32-2/4^7}{3}
}
\exp\left(1-\frac1{2n_7}\right).
\tag{4}
\]

To make (4) completely rational, put
\[
y=1-\frac1{2n_7}
\]
and use the positive Taylor polynomial
\[
E_8(y)=\sum_{k=0}^8\frac{y^k}{k!}<e^y.
\]
Exact rational arithmetic verifies
\[
\frac19\frac{333}{106}
\frac{32\cdot4^7-2}{3\cdot4^7}
E_8(y)^2
>
\left(\frac{524511}{100000}\right)^2.
\tag{5}
\]
All quantities are positive, so (4)--(5) prove
\[
\boxed{D_j>\frac{524511}{100000}=5.24511\qquad(j\ge7).}
\tag{6}
\]

For completeness, the checker also verifies
\(\pi>333/106\) directly from Machin's formula using alternating rational
arctangent bounds.

## 2. Restarted lower-tail formula

The exact logarithmic recurrence gives, for every fixed \(J\),
\[
\log\Lambda_{2,5}
=
\frac{
\log R_J+
\sum_{t=0}^{\infty}4^{-t-1}\log D_{J+t}
}{
d_J+1/3
}.
\tag{7}
\]
With \(J=7\), equation (6) and
\[
\sum_{t=0}^{\infty}4^{-t-1}=\frac13
\]
give
\[
\Lambda_{2,5}>
\left(
\frac{524511}{100000}R_7^3
\right)^{1/(3d_7+1)}.
\tag{8}
\]

Here
\[
d_7=87381,\qquad 3d_7+1=262144.
\]
The supplied checker reconstructs the exact rational \(R_7\) from the
recurrence, without floating point, and verifies the integer inequality
\[
\left(\frac{71336638763}{25000000000}\right)^{262144}
<
\frac{524511}{100000}R_7^3.
\tag{9}
\]
The rational number on the left base is exactly
\[
\frac{71336638763}{25000000000}=2.85346555052.
\]
Combining (8) and (9) proves the stated lower endpoint.

## 3. Verification

Run

~~~sh
python3 check_sharpened_lower.py
python3 -O check_sharpened_lower.py
~~~

The checker uses only Python's standard library, integers, and
fractions.Fraction. It verifies:

- the Machin lower bound for pi;
- the rational Taylor inequality (5);
- all exact recurrence states through level 7;
- the dimension and exponent \(d_7=87381\), \(3d_7+1=262144\);
- the final large-integer inequality (9).

No floating-point value is used in a proof decision.

## 4. Stronger two-sided companion

The additive [limit-interval note](LIMIT_INTERVAL.md) retains the Robbins
exponential corrections on both sides and uses two exact restart levels.  Its
standard-library checker passes in ordinary and optimized Python and certifies
\[
2.853465550695797<\Lambda_{2,5}<2.853465550704.
\]
The older one-sided proof above and its checker are preserved unchanged.

## 5. Scope

This is a sharper certificate for the existing binary \(T_5\) family.
It does not prove that this family is optimal in the full product/join
class. The current upper bound remains the positive-sextic Bellman
envelope. Thus the main unresolved problem is still to close the gap
between the finite construction and the global Bellman upper envelope.
