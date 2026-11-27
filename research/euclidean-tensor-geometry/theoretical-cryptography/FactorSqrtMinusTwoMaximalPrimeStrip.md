# The unique 197-point prime candidate shape in \(\mathbb Z[\sqrt{-2}]\), and its exclusion from an infinite strip

Let \(R=\mathbb Z[\sqrt{-2}]\) and identify \(a+b\sqrt{-2}\) with
\((a,b)\), of norm \(a^2+2b^2\). We study components of all irreducible
elements, not associate classes, at Euclidean edge radius
\(\sqrt6\le D<\sqrt8\). The step set is
\[
 F=\big(\{-2,-1,0,1,2\}\times\{-1,0,1\}\big)\setminus\{(0,0)\}.
\]
The [previous exact sieve result](https://github.com/mxym/math/blob/main/notes/sqrt-minus-two-exact-sieve-optimum/paper.md)
gives \(90\le B_D\le197\), and the [previous conditional result](https://github.com/mxym/math/blob/main/notes/sqrt-minus-two-conditional-prime-197/paper.md)
gives \(B_D=197\) under one instance of Schinzel's Hypothesis H.
We do not change that global unconditional interval.

**Theorem.** Put \(Q=742840526010\). In the graph on lattice points with
norm coprime to \(Q\), the size-197 components have exactly four translation
classes modulo \(Q\mathbb Z^2\). They all have one shape up to translation
and reflection. That shape is the only universally norm-admissible
connected 197-point shape up to these equivalences. Every size-197
component of actual irreducibles is one of the four candidate classes.

More precisely, no component of 197 actual irreducibles can meet the
**infinite vertical strip**
\[
                  |a|<377085620510840247 .
\]
The bound is on entire graph components intersecting the strip.
Assuming the classical Hypothesis H, this strip boundary is sharp:
infinitely many size-197 components have a point at its boundary.
The same method determines exactly which horizontal anchor coordinates
can support a 197-point component under that hypothesis.

## 1. Complete enumeration of maximal sieve components

Use the same norm sieve as the previous bound:
\[
 Q=1122\cdot19\cdot5\cdot41\cdot43\cdot59\cdot67,\qquad
 1122=2\cdot3\cdot11\cdot17 .
\]
A representative of a component is always anchored at its least point
in lexicographic order, first comparing \(a\), then \(b\). The coordinates
of its anchor class are taken in \([0,Q)^2\).

The [exact companion](verify_factor_sqrt_minus_two_maximal_strip.js)
reconstructs the period-1122 components from scratch. First it marks
every allowed residue, and runs breadth-first exploration with each
discovered vertex stored as a lift in \(\mathbb Z^2\). Every edge
returning to a marked residue is checked to return to that same lift.
Thus no quotient component has nonzero translation around a walk.
These finite lifted components and their \(1122\mathbb Z^2\)-translates
give the exact full infinite-lattice partition. There are 204,800 allowed
residues, 6,688 components, and maximum component size 2,283.

At a refinement stage, suppose \(C\) is one full-lattice component at
period \(q\). To add a new norm prime \(p\nmid q\), inspect each
\(C+q(u,v)\) for \(0\le u,v<p\), delete the norm multiples of \(p\),
and take the connected components within what remains.
The \(p^2\) shifts exhaust its translates modulo \(pq\). Deleting
vertices never merges components; any component below 197 can be
discarded permanently when finding maximal components.
This yields the following exact counts; a branch that is kept at one
stage is processed at every one of its shifts at the next stage.

| Added prime | Shift configurations | Retained components of size at least 197 | Largest size |
|---:|---:|---:|---:|
| 19 | 74,366 | 140 | 298 |
| 5 | 3,500 | 12 | 241 |
| 41 | 20,172 | 44 | 217 |
| 43 | 81,356 | 20 | 205 |
| 59 | 69,620 | 12 | 201 |
| 67 | 53,868 | 4 | 197 |

Unlike the previous upper-bound computation, the threshold here is
\(\ge197\), not \(>197\): equal-size branches must be preserved.
The exact \(Q\)-anchor classes are

| \(a\bmod Q\) | \(b\bmod Q\) |
|---:|---:|
| 287186037979 | 371420262993 |
| 287186037979 | 742840525998 |
| 455654487987 | 371420262976 |
| 455654487987 | 742840525981 |

Let \(S\) be the shape obtained by subtracting the anchor of the
second row. Its horizontal coordinates range from 0 to 44.
The first row is the same shape translated vertically by \(Q/2\).
The last two are horizontal reflections of the first two, with the
anchor renormalized. The companion checks these exact set identities,
as well as all four shape boundaries against the norm rule.
The vertical half-period is possible because the prime-2 rule
depends only on \(a\), but the table uses the stated square period \(Q\).

If \(S'\) is any universally norm-admissible connected 197-point
shape, use the Chinese remainder theorem to choose a single translate
of \(S'\) that is allowed for all primes dividing \(Q\).
It lies in one of the enumerated components of size at most 197, hence
is exactly that component. Conversely the shape \(S\) is universally
norm-admissible (also verified by §3 below). This proves the shape
classification. It identifies the already known admissible 197-point
shape as unique; it is not a new existence proof of simultaneous prime
values.

## 2. From the lattice sieve to actual irreducibles

The ring \(R\) is norm-Euclidean: rounding both real coefficients to
nearest integers gives an error of norm at most \(1/4+2/4<1\).
Consequently it is a UFD with units \(\pm1\). Every irreducible
\(\pi\) divides its rational integer norm, so it divides a rational
prime \(p\), and its norm is \(p\) or \(p^2\).
The latter case is exactly the rational prime \(p\) up to a unit,
when \(p\) remains irreducible. A rational prime is reducible in \(R\)
if and only if there is an element of norm \(p\): one direction uses
\(z\bar z=p\), and in the other both nonunit factor norms must be \(p\).
An element of rational prime norm is always irreducible.

All irreducibles whose norms have a prime divisor in \(Q\) lie in
the previously known 90-vertex component. To recheck this independently,
the companion enumerates norm-\(p\) representations for each \(p\mid Q\)
and the two rational associates in the cases with none. It builds the
actual irreducible closure of \((0,1)\) using the norm characterization,
rechecks that it has size 90, and checks inclusion of each exceptional
irreducible. Thus any other actual component lies in a \(Q\)-sieve
component. If its size is 197, equality of the vertex sets follows.
In particular, up to changing the sign of \(a\), its shape is \(S\)
and its horizontal anchor is
\[
               A_k=a_0+Qk,\qquad a_0=287186037979,\qquad k\in\mathbb Z.
\]
The vertical anchor is one of the first two rows modulo \(Q\).
These two rows have the same possible horizontal positions when adding
other primes, since they are translates of exactly the same shape
and \(Q\) is invertible modulo any added prime.

## 3. Projection to the horizontal coordinate

The first sieve already implies that every vertex in a candidate has
\(|a|\ge a_0\): for the displayed orientation, \(a\) ranges from \(A_k\)
to \(A_k+44\), and \(0<a_0+44<Q/2\).
In particular no irreducible of norm \(p\) or rational associates
\(\pm p\) for \(p\le394\) can be an exceptional vertex of a candidate.
For each prime \(p\le394\) not dividing \(Q\), define
\[
 E_p=\left\{x\in\mathbb F_p:\exists\,y\in\mathbb F_p,\ \
 (x+u)^2+2(y+v)^2\ne0\text{ for all }(u,v)\in S\right\}.
\]
Every 197-irreducible candidate must have \(A_k\bmod p\in E_p\).
The only \(p\) with \(E_p\ne\mathbb F_p\), and their cardinalities,
are the following:
\[
\begin{array}{c|rrrrrrrrrrr}
p&7&73&83&89&97&107&113&131&137&139&179\\ \hline
|E_p|&1&1&6&24&36&39&75&113&120&125&178
\end{array}
\]
The companion computes each \(E_p\) twice: once by literal norm tests
for every potential row and a search for an allowed vertical residue;
and again by computing the forbidden vertical residues from the
factorization of \(x^2+2y^2\) for split primes, or its single zero
\((0,0)\) for inert primes. It checks complete equality of the results.
By CRT the allowed integers \(k\) form a set of residue classes of
relative density \(\prod_{p:\,E_p\ne\mathbb F_p}|E_p|/p\), in this
normalized orientation. This is a statement about congruence
candidates, not actual primes.

At \(p>394=2|S|\), every \(x\) has a permitted \(y\): the product of
the 197 norm polynomials in \(y\) has a nonzero leading coefficient
modulo \(p\) and degree 394. Thus the indicated small-prime tests are
exactly the local obstructions for the horizontal projection; there
is no approximation by ignoring larger primes.

The distance of a proposed component from the axis \(a=0\) is
\[
 d(k)=
 \begin{cases}
 A_k,& A_k>0,\\
 -A_k-44,&A_k<0.
 \end{cases}
\]
The order \(0,-1,1,-2,2,\ldots\) is the strictly increasing order
of these distances, since \(2a_0+44<Q\). The first \(k\) satisfying
all the displayed row tests is \(-507627\), with
\[
                A_{-507627}=-377085620510840291,\qquad
                d(-507627)=377085620510840247.
\]
The companion checks all 1,015,254 tested indices in this order,
using modular multiplication before constructing a large coordinate.
It separately checks the nearest permissible index by first
combining the two singleton tests modulo \(7\cdot73=511\), then
testing that reduced progression with arbitrary-precision residues.
All large coordinates and the final distance are exact integers.
Reflection preserves the distances. This proves the unconditional
strip exclusion for the full prime graph.

## 4. Conditional sharpness and the admissible horizontal positions

Fix any \(k\) passing the projected small-prime tests, and put \(A=A_k\).
For each \(p\le394\) not dividing \(Q\), choose a permitted vertical
residue for this \(A\bmod p\); choose the second row's vertical anchor
modulo \(Q\) for the remaining primes.
CRT produces a progression \(b=b_*+M t\), with
\(M=Q\prod_{p\le394,p\nmid Q}p\), on which every small prime
is avoided at every vertex. The companion constructs and verifies
one such progression at the nearest allowed value \(k=-507627\).
Together with the large-prime degree argument this also verifies
that \(S\) really is universally norm-admissible.

On this vertical progression the 197 norms are the polynomials
\[
              f_{u,v}(t)=(A+u)^2+2(b_*+Mt+v)^2,\quad (u,v)\in S .
\]
They have positive leading coefficient and strictly negative
discriminant since \(A+u\ne0\). They are pairwise distinct:
different \(v\)'s give different linear coefficients, while the same
\(v\) and different \(u\)'s give different squares \((A+u)^2\)
(all the \(A+u\)'s have the same sign). The product has no fixed
prime divisor: CRT handles \(p\le394\), and for \(p>394\)
the leading coefficient is nonzero and degree 394 is less than \(p\).
In particular the polynomials are primitive as well as irreducible.
Classical [Schinzel–Sierpiński Hypothesis H](https://doi.org/10.4064/aa-4-3-185-208),
if true, supplies infinitely many simultaneous rational-prime
specializations for each such \(A\). Each gives a 197-point
connected set of irreducibles, necessarily a full component by
the upper bound. Distinct sufficiently separated vertical anchors
give distinct components.

Therefore the row congruences are unconditional necessary conditions
and, under H, sufficient at every eligible horizontal anchor.
The nearest allowed anchor attains the displayed strip boundary
under the same hypothesis. No simultaneous-primality existence,
global improvement to \([90,197]\), or resolution of Hypothesis H
is asserted unconditionally.
