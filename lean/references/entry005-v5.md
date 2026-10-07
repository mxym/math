# The unique balanced homogeneous simplex recursion

**mxym — AI-assisted research manuscript. Entry 005, version 5, 7 October 2026.**

This note continues the product/join calculus of [version 2](../v2/paper.md) and the spectral reduction in [version 2's supplement](../v2/ASYMPTOTIC_SPECTRAL_REDUCTION.md). It proves an infinite-parameter optimality theorem for the natural homogeneous recursion containing the previously certified \(T_5\) orbit.

No claim is made here about the full product/join closure. In particular, arbitrary nonhomogeneous operation trees and the more general recursions \((K^m)^{*k}\) with \(m\ne k\) are not classified by this theorem.

## 1. The balanced homogeneous family

For a positive-dimensional body \(K\), let \(K^t\) denote the Cartesian product of \(t\) copies and \(K^{*t}\) the join of \(t\) copies.

Fix integers
\[
t\ge2,\qquad p\ge1.
\]
Let \(T_p\) be a \(p\)-dimensional simplex and define
\[
K_0^{(t,p)}=T_p,\qquad
K_{j+1}^{(t,p)}=
\left(\left(K_j^{(t,p)}\right)^t\right)^{*t}.
\tag{1.1}
\]
Write
\[
d_j=\dim K_j^{(t,p)},\qquad
R_j=R(K_j^{(t,p)}),\qquad
a_j=a(K_j^{(t,p)}).
\]

The exact identities from version 2 imply that the limit
\[
\Lambda_{t,p}:=\lim_{j\to\infty}R_j^{1/d_j}
\tag{1.2}
\]
exists. The main result identifies the unique best pair \((t,p)\) in the entire two-parameter family.

### Theorem 1.1. Unique optimum

Among all integers \(t\ge2\) and \(p\ge1\),
\[
\boxed{\Lambda_{t,p}}
\]
has a unique maximum at
\[
\boxed{(t,p)=(2,5).}
\]

More quantitatively, for every \((t,p)\ne(2,5)\),
\[
\boxed{
\Lambda_{t,p}<e^{131/125}
<\frac{14267}{5000}
<\Lambda_{2,5}.
}
\tag{1.3}
\]
Thus every competing balanced homogeneous simplex recursion is separated from the \(T_5\) binary orbit by a strict certified gap.

The final lower inequality is the \(2.8534\) endpoint already certified in version 2. We rederive the relevant tail estimate and independently replay the exact integer comparison in this version.

## 2. Exact recurrence

Put
\[
T=t^2,\qquad c=\frac1{t+1}.
\]
For one step of (1.1), first form the \(t\)-fold product. It has dimension \(td_j\), invariant \(a_j\), and projection ratio \(R_j^t\). Joining \(t\) copies then gives
\[
d_{j+1}=T d_j+t-1,
\qquad
a_{j+1}=\frac{a_j}{t}.
\tag{2.1}
\]
Since \(a(T_p)=1/(p+1)\),
\[
\boxed{
d_j+c=(p+c)T^j,\qquad
a_j=\frac1{(p+1)t^j}.
}
\tag{2.2}
\]

The self-join formula from version 2 gives
\[
R_{j+1}=R_j^T D_j,
\tag{2.3}
\]
where
\[
\boxed{
D_j=
t\,a_j^{\,t-1}
\frac{g(d_{j+1})}{g(td_j)^t},
\qquad
g(n)=\frac{n^n}{n!}.
}
\tag{2.4}
\]
Indeed, if \(P=(K_j)^t\), then \(a(P)=a_j\), \(R(P)=R_j^t\), and
\[
Q(P)=\frac{a_jR_j^t}{g(td_j)}.
\]
For the join of \(t\) copies of \(P\),
\[
R(P^{*t})
=
g(d_{j+1})\frac{t}{a_j}Q(P)^t,
\]
which is exactly (2.3)--(2.4).

## 3. The logarithmic limit formula

The two-sided Stirling bounds used below imply that, for fixed \(t,p\),
\[
\log D_j=O_{t,p}(1).
\]
Iterating (2.3) therefore gives an absolutely convergent series:
\[
\boxed{
\log\Lambda_{t,p}
=
\frac{
\log R_0+
\sum_{j=0}^{\infty}T^{-j-1}\log D_j
}{
p+c
}.
}
\tag{3.1}
\]
To see this directly,
\[
\frac{\log R_J}{T^J}
=
\log R_0+\sum_{j=0}^{J-1}T^{-j-1}\log D_j,
\]
while
\[
\frac{d_J}{T^J}\longrightarrow p+c
\]
by (2.2).

The rest of the proof consists of a dimension-uniform upper estimate for \(D_j\), followed by a finite exact screening.

## 4. A uniform Robbins--Stirling envelope

We use the classical Robbins form of Stirling's bounds: for every integer \(n\ge1\),
\[
\sqrt{2\pi n}\left(\frac ne\right)^n
e^{1/(12n+1)}
<
n!
<
\sqrt{2\pi n}\left(\frac ne\right)^n
e^{1/(12n)}.
\tag{4.1}
\]
Consequently,
\[
\frac{e^n}{\sqrt{2\pi n}}e^{-1/(12n)}
<
g(n)
<
\frac{e^n}{\sqrt{2\pi n}}.
\tag{4.2}
\]

### Lemma 4.1. Uniform tail factor

For every \(j\ge0\),
\[
\boxed{D_j<C_{t,p},}
\tag{4.3}
\]
where
\[
\boxed{
C_{t,p}
=
t^{t/2}
e^{\,t-1+1/(12p)}
\frac{\bigl(2\pi(p+c)\bigr)^{(t-1)/2}}
{(p+1)^{t-1}}.
}
\tag{4.4}
\]

**Proof.**
Put
\[
d=d_j,\qquad q=td,\qquad n=d_{j+1}=tq+t-1.
\]
Using the upper estimate for \(g(n)\) and the lower estimate for \(g(q)\) in (4.2),
\[
\frac{g(n)}{g(q)^t}
<
e^{t-1}
(2\pi)^{(t-1)/2}
\frac{q^{t/2}}{\sqrt n}
e^{1/(12d)}.
\]
Since
\[
n>t^2d,\qquad q=td,
\]
we have
\[
\frac{q^{t/2}}{\sqrt n}
<
t^{t/2-1}d^{(t-1)/2}.
\]
Multiplying by \(t a_j^{t-1}\) gives
\[
D_j
<
t^{t/2}e^{t-1+1/(12d)}
(2\pi)^{(t-1)/2}
\bigl(a_j\sqrt d\bigr)^{t-1}.
\]
By (2.2),
\[
d_j<(p+c)t^{2j},
\]
hence
\[
a_j\sqrt{d_j}
<
\frac{\sqrt{p+c}}{p+1}.
\]
Also \(d_j\ge p\). Substitution gives (4.4). \(\square\)

### Corollary 4.2. Global and restarted upper bounds

For every \(t,p\),
\[
\boxed{
\log\Lambda_{t,p}
<
U_{t,p}:=
\frac{
\log c_p+\frac1{T-1}\log C_{t,p}
}{
p+c
},
}
\tag{4.5}
\]
where
\[
c_p=(p+1)g(p)=R(T_p).
\]

More generally, after any exact level \(J\),
\[
\boxed{
\log\Lambda_{t,p}
<
\frac{
\log R_J+\frac1{T-1}\log C_{t,p}
}{
d_J+c
}.
}
\tag{4.6}
\]

**Proof.**
The geometric series satisfies
\[
\sum_{j=0}^{\infty}T^{-j-1}=\frac1{T-1}.
\]
Insert (4.3) into (3.1). Restarting the same argument at level \(J\) gives (4.6). \(\square\)

## 5. A simpler large-\(p\) envelope

For the infinite parameter tails it is convenient to eliminate \(c_p\). From (4.2),
\[
c_p
<
\frac{(p+1)e^p}{\sqrt{2\pi p}}.
\tag{5.1}
\]
Let
\[
A_t=1-\frac{c}{2},
\qquad
\alpha_t=\frac{t}{2(T-1)}.
\]
Combining (4.4), (4.5), and
\[
p+c<p+1
\]
inside the positive logarithmic term gives
\[
\boxed{
\log\Lambda_{t,p}
<
1+\frac{B_t(p)}{p+c},
}
\tag{5.2}
\]
with
\[
\boxed{
B_t(p)
=
A_t\log(p+1)
-\frac12\log p
-\frac{1-c}{2}\log(2\pi)
+\alpha_t\log t
+\frac1{12p(T-1)}.
}
\tag{5.3}
\]

This estimate is deliberately slightly weaker than (4.5), but it is simple enough to control the two infinite tails analytically.

## 6. The tail \(2\le t\le19,\ p\ge20\)

For fixed \(t\), differentiate (5.3):
\[
B_t''(p)
=
-\frac{A_t}{(p+1)^2}
+\frac1{2p^2}
+\frac1{6(T-1)p^3}.
\tag{6.1}
\]
Because
\[
A_t\ge\frac56,\qquad T-1\ge3,
\]
we have
\[
B_t''(p)
\le
-\frac{5}{6(p+1)^2}
+\frac1{2p^2}
+\frac1{18p^3}.
\tag{6.2}
\]
The right side is negative for \(p\ge4\). Clearing positive denominators reduces this to
\[
6p^3-19p^2-11p-1>0,
\]
which holds at \(p=4\) and then increases, since its derivative is already positive there and remains increasing.

Define
\[
H_t(p)=B_t(p)-(p+c)B_t'(p).
\]
Then
\[
H_t'(p)=-(p+c)B_t''(p)>0
\qquad(p\ge4).
\tag{6.3}
\]
The exact checker verifies, for each of the eighteen integers
\[
2\le t\le19,
\]
that
\[
H_t(20)>0,
\qquad
\frac{B_t(20)}{20+c}<\frac1{25}.
\tag{6.4}
\]
Therefore \(B_t(p)/(p+c)\) is decreasing for all real \(p\ge20\), and
\[
\boxed{
\log\Lambda_{t,p}<1+\frac1{25}=1.04
}
\tag{6.5}
\]
for every integer \(2\le t\le19\) and \(p\ge20\).

The finite checks in (6.4) use rigorous rational logarithm intervals, not floating point.

## 7. The tail \(t\ge20\)

For \(t\ge20\),
\[
c\le\frac1{21},\qquad
A_t\le1,\qquad
\frac{1-c}{2}\ge\frac{10}{21}.
\]
Moreover,
\[
\alpha_t\log t
=
\frac{t}{t+1}\frac{\log t}{2(t-1)}
<
\frac{\log t}{2(t-1)}
\le
\frac{\log20}{38},
\tag{7.1}
\]
because \(\log t/(t-1)\) is decreasing for \(t>1\). Finally,
\[
\frac1{12p(T-1)}
\le
\frac1{4788p},
\]
and \(2\pi>6\). Hence
\[
B_t(p)\le F(p),
\tag{7.2}
\]
where
\[
F(p)=
\log(p+1)-\frac12\log p
-\frac{10}{21}\log6
+\frac1{38}\log20
+\frac1{4788p}.
\tag{7.3}
\]

We claim
\[
\boxed{\frac{F(p)}p<\frac6{125}}
\tag{7.4}
\]
for every positive integer \(p\) for which \(F(p)\ge0\); when \(F(p)<0\), the desired spectral bound is immediate.

As in Section 6,
\[
F''(p)
=
-\frac1{(p+1)^2}
+\frac1{2p^2}
+\frac1{2394p^3}
<0
\qquad(p\ge4),
\]
because this is bounded above by the already negative right side of (6.2). Put
\[
H_F(p)=F(p)-pF'(p).
\]
Then \(H_F'(p)=-pF''(p)>0\) for \(p\ge4\). The exact checker verifies
\[
H_F(9)>0
\tag{7.5}
\]
and verifies (7.4) directly for \(1\le p\le9\). Therefore \(F(p)/p\) decreases for \(p\ge9\), proving (7.4) for all positive integers.

Equations (5.2), (7.2), and (7.4) give
\[
\boxed{
\log\Lambda_{t,p}<1+\frac6{125}=\frac{131}{125}
}
\tag{7.6}
\]
for every \(t\ge20\) and every \(p\ge1\).

## 8. The finite core

It remains to treat
\[
2\le t\le19,\qquad 1\le p\le19.
\]
There are \(18\cdot19=342\) pairs.

The exact checker evaluates the rigorous logarithmic upper bound (4.5). It proves
\[
U_{t,p}<\frac{131}{125}
\tag{8.1}
\]
for 335 of the 342 pairs. The only pairs not eliminated by the first envelope are
\[
(t,p)=(2,p),\qquad 1\le p\le7.
\tag{8.2}
\]

For
\[
p\in\{1,2,3,4,6,7\},
\]
the checker evaluates the first three recurrences (2.1)--(2.4) in exact rational arithmetic and then applies the restarted tail bound (4.6). In every case it certifies
\[
\log\Lambda_{2,p}<\frac{131}{125}.
\tag{8.3}
\]
Thus the sole surviving pair is
\[
(2,5).
\]

This is a finite proof certificate, not a numerical search: the arithmetic states \(R_J,a_J,d_J\) are exact fractions and integers, while every logarithm is enclosed by a rational interval with a proved remainder.

## 9. The winning orbit

For \((t,p)=(2,5)\), the recursion is exactly the version-2 family
\[
K_0=T_5,\qquad
K_{j+1}=(K_j\times K_j)*(K_j\times K_j).
\]
Here
\[
d_j=\frac{16\cdot4^j-1}{3},
\qquad
a_j=\frac1{6\cdot2^j}.
\tag{9.1}
\]

For this orbit, write
\[
R_{j+1}=R_j^4D_j.
\]
Version 2 proved
\[
D_j>3.
\tag{9.2}
\]
For completeness, its short proof is as follows. Put \(q=2d_j\). The exact ratio is
\[
\frac{g(2q+1)}{g(q)^2}
=
\frac{4^q}{\binom{2q}{q}}
\left(1+\frac1{2q}\right)^{2q}.
\]
The elementary estimates
\[
\binom{2q}{q}\le\frac{4^q}{\sqrt{3q+1}},
\qquad
\left(1+\frac1{2q}\right)^{2q}>2
\]
give
\[
D_j>4a_j\sqrt{6d_j+1}
=
\frac23\sqrt{32-4^{-j}}
>3.
\]

Restarting the limit series at level \(j\) therefore gives
\[
\Lambda_{2,5}
>
(3R_j^3)^{1/(3d_j+1)}.
\tag{9.3}
\]
At \(j=6\),
\[
d_6=21845,\qquad 3d_6+1=65536.
\]
The checker reconstructs the complete rational \(R_6\) from the recurrence and verifies the integer inequality
\[
\boxed{
\left(\frac{14267}{5000}\right)^{65536}
<
3R_6^3.
}
\tag{9.4}
\]
Hence
\[
\boxed{
\Lambda_{2,5}>\frac{14267}{5000}=2.8534.
}
\tag{9.5}
\]

The upper endpoint \(\Lambda_{2,5}<2.8535\) remains available from version 2 but is not needed for uniqueness here.

## 10. Exact logarithm certificate

The finite comparisons in Sections 6--8 are independently replayable with [code/check_balanced.py](code/check_balanced.py). No floating-point logarithm is used.

For a positive rational \(x\), first write
\[
x=2^k y,\qquad 1\le y<2.
\]
Set
\[
z=\frac{y-1}{y+1},
\qquad 0\le z<\frac13.
\]
Then
\[
\log y
=
2\sum_{n=0}^{N-1}\frac{z^{2n+1}}{2n+1}
+\mathcal R_N,
\]
with the exact remainder bound
\[
0<\mathcal R_N
\le
\frac{2z^{2N+1}}{(2N+1)(1-z^2)}.
\tag{10.1}
\]
The same expansion at \(z=1/3\) encloses \(\log2\). The checker uses \(N=48\), all arithmetic is Fraction, and
\[
\frac{333}{106}<\pi<\frac{355}{113}
\]
supplies rational bounds for \(\log(2\pi)\).

The checker also certifies
\[
\log\left(\frac{14267}{5000}\right)
>
\frac{131}{125}.
\tag{10.2}
\]
Thus
\[
e^{131/125}<\frac{14267}{5000}.
\tag{10.3}
\]

Ordinary Python and python -O must produce byte-identical reports. The script uses explicit exceptions for every correctness condition.

## 11. Scope and next obstruction

Theorem 1.1 is an infinite-family classification: it rules out every other arity \(t\) and every other simplex seed dimension \(p\) in the balanced homogeneous recursion (1.1).

It does **not** prove that the \(T_5\) binary orbit is optimal in the full point-generated product/join class. Version 3 already shows that no finite-dimensional body can attain the global spectral supremum, so full optimality requires a dimension-uniform envelope over arbitrary operation trees.

A natural next enlargement is
\[
K_{j+1}=(K_j^m)^{*k}
\]
with independent product and join arities \(m,k\), followed by genuinely nonhomogeneous periodic or variable operation trees. Preliminary floating-point exploration is discovery-only and is not part of this theorem.

## 12. Provenance

The exact product/join identities, the invariant \(a\), and the \(T_5\) self-similar construction are inherited from entry 005 version 2. Version 3 supplies the spectral nonattainment theorem but is not needed for the arithmetic classification above.

The upstream projection-body product identity and simplex values ultimately trace to OpenAI family 088, pinned at commit adc7f1241b42e322a6451854ab7e4b4c146bf78a, as recorded in versions 1--4.

A focused comparison with Brannen, Saroglou, and the upstream family is recorded in [the version-5 prior-work note](../../../comparisons/2026-10-07-balanced-recursion.md). No first-discovery claim is made for Theorem 1.1 before a broader literature comparison. The public record establishes only what this repository proves and when it disclosed it.
