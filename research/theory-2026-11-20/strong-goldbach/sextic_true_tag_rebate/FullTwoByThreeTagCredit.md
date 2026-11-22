# The whole two-by-three tagged chamber, with the actual correction retained

Keep the fixed even \(N\), central \(J\),
\(L=\log N\), \(M=|J|N\mathfrak S(N)\), original
target-unit pairing \(x+y=N,\ x\in NJ,\ (x,N)=1\),
and **identical** sharp compensated \(S=G_b+W,\ b=.003\),
of [the earlier two-by-three theorem](TwoByThreeTagCredit.md).

Now use all squarefree rows with exactly two distinct prime
factors in \((N^{.003},N^{.080}]\) on the left and exactly
three on the right. Every other prime factor on both arms
must be \(>N^{.080}\). There are **no tag-sum, sign, or
quotient-rank exclusions**. Let \(\mathcal V\) denote this
full chamber and \(\mathcal V^{\rm op}\) its reflection.

**Proposition.** The original signed sum over
\(\mathcal V\cup\mathcal V^{\rm op}\) exceeds \(.0883M+o(M)\).
This **replaces**, not adds to, the earlier \(.0395M\)
credit on the smaller two-by-three support. All other
physical chambers remain disjoint. Thus the \(1.3068M\)
comparison (including the unchanged-score
[.003 tiny improvement](ImprovedTinyCovariance.md)
and the [three-by-three credit](ThreeByThreeTagCredit.md))
increases to \(1.3556M\) before the new smaller signed
exterior. If separately using the disjoint
[medium semiprime adverse charge](MediumSemiprimeAdverse.md),
the corresponding coefficient is \(.9706M\).
These are comparisons with changed literal exterior sums,
not a lower on either exterior or a proof of Goldbach.

## 1. The real score and a sharp upper on the retained correction

The .003 gate passes on both sides and \(Q=0\).
On the right \(W=0\) without a tag-sum condition: after
the first two tags the third actual prime is \(\le N^{.080}\),
whereas \(W\) would require that quotient to be rough above
\(N^{(.555-.065)/3}\). Thus \(S=H\) there.
On the left \(S=H+W\) with **the original actual \(W\)**.
It clips a negative score to zero exactly on its genuine
selected rows. In particular
\[
                |S|\le |H|,\qquad S_+=H_+.                       \tag{1}
\]
The squarefree restriction discards only zero scores.
The counts \(2,3\) at the fixed .080 cutoff determine the
orientation and exclude both one-by-two and three-by-three.
Both arms have less than .1251 least factor, so none of
the .1251-rough or mixed Q-boundary chambers occurs.
The three-tag arm cannot have the .110-rough quotient
of the older complete two-tag chamber. The medium
adverse chamber needs zero .080 tags on one arm, so
is also disjoint. The old smaller two-by-three support
is contained in \(\mathcal V\) and its old credit is replaced.

Write \(\mathsf m_a\) for the ordinary one-arm moment at
the fixed tag list with remaining actual factors \(>N^a\).
On the two-tag arm, normalize all scores by \(Luv\),
where \(u,v\) are the actual tag angles, and let \(A_H\)
be the normalized original \(H\). Put \(a=.080\).
On a cell where \(W\) can occur, we use the upper
\[
 \mathsf m_a\!\left(\frac{W}{Luv}\right)
             \ \le\ -\mathsf m_{.163}(A_H).                      \tag{2}
\]
Indeed every actual \(W\) row in the cell has quotient
roughness \(>(.555-.065)/3>.163\) in angular units.
Every score on this larger ordinary one-arm region
is nonpositive. To see the last assertion, the total
rank is between 3 and 8, since seven quotient factors
above .163 already exceed total one. Rank three has
one giant quotient prime, so its normalized value
is the two-tag divided difference \(g_2(0)\).
This is negative for all \(0<u,v\le .080\).
In fact \(F'''(s)>0\) on \(0\le s\le .160\), and the
double uniform average of \(F''(\alpha u+\beta v)\)
is largest at \(u=v=.080\), where it is \(-14.65306624\).
Rank four is negative because the sum of squared angles
is at least \((1-u-v)^2/2\ge .3528>11/35\).
Ranks five, six, seven are nonpositive by the exact
[sextic slice formulas](Proof.md#2-the-whole-rough-negative-arm-comparison),
and rank eight is zero. These conclusions have uniform
strict room where a strict sign was used, so the
\(O_J(1/L)\) change to own-log angles is harmless.
Thus (2) is an upper on the ordinary mass of a subset of
a true nonnegative \(-A_H\) measure, not a change to \(W\).
On a cell where \(W\) is impossible, use zero in (2).
It suffices for that distinction that the first-two
actual sum in \(W\) is \(\le .065\) and both actual
tag angles exceed .005.

The left ordinary positive moment \(\mathsf m_a((A_H)_+)\)
receives only possible ranks 9, 11, 13.
The same rank-three/four signs above apply for \(a=.080\),
without any extra conditions on other primes; ranks
five through seven and the high even ranks are as before.
For quotient rank \(k=r-2\in\{7,9,11\}\), with total
\(T=1-u-v\), the high odd envelope after dividing the
actual two least factors out is bounded by
\[
       1056\,2^{k-3}(T/k)^2+80640\,2^{k-5}(T/k)^4 .
\]
Indeed the extra least-two and least-four products
in the original envelope have geometric means at most
\(T/k\). Multiply by the genuine rank-\(k\) ordinary
density and sum. There are no ranks above 14 since
\(13\cdot .080>1\). This is the same positive finite-rank
recurrence as in the three-by-three proof.

## 2. Actual signed transfer on every cell pair

Partition \((.003,.080]\) into eleven half-open .007 bins.
Use nondecreasing cell lists, including coincident cells,
while the actual primes remain distinct and ordered.
An \(r\)-tag arm gives true ordered harmonic volume
\(.007^r/\prod_j n_j!\), where \(n_j\) are its cell
multiplicities, exactly as in the two previous theorems.
Fix a paired cell and use the actual physical measure
weighted by all five tag angles, divided by the product
of these two volumes and \(M/L^2\).

Genuine nonnegative source transfers apply also to the
actual \(W\) gate and the weighted \(S\): its bounded
finite-rank angular weights are piecewise continuous in
the genuine product factors, with the same true-box
approximation and reduced residue as before.
For a receiver cell of upper tag sum \(\tau\), use the
real linear level exponent
\[
                   D=\min(.320,.498-\tau).
\]
The **actual** marked modulus times sieve divisor is
at most \(N^{.498}\); on the three-tag arm the relative
ratio is between 3.225 and 4, and on the two-tag arm
it is exactly 4. Use the exact lower \(k\) and upper \(U\)
bounds and ordinary local masks of the three-by-three
transfer. Actual shared prime labels are forbidden by
target units; actual tag squares or other repeated
quotient primes in a lower model are removed by the same
power-small \(p^2\) floor at \(p>N^{.003}\).
These are bounds on one common physical squarefree
measure. No quotient independence is used.

Let \(A=S(x)/(Luv)\) on the two-tag arm and \(B\)
be the normalized right \(H\) on the three-tag arm.
The same signed Cauchy inequality as in the earlier
two-by-three theorem gives the cell lower
\[
  d\{-k_{\rm R}\mathsf m_{\rm L}(A)
                  -(U_{\rm R}-k_{\rm R})\mathsf m_{\rm L}(A_+)\}
   -\sqrt{U_{\rm L}U_{\rm R}
              \mathsf m_{\rm L}(A^2)\mathsf m_{\rm R}((B+d)^2)} .
                                                                    \tag{3}
\]
Here \(d>0\) is fixed before \(N\to\infty\). Insert the
true upper of the signed ordinary first moment from
(2), the unchanged positive moment by (1), and the
upper of the square via (1). The right shifted square
keeps its inclusive atom and all zero-score ranks.
All numerical inputs are thus ordinary **one-arm**
moments, while (3) is a lower for the **true coupled**
weighted covariance in that same full physical cell.

## 3. Exact all-cell replay

Run:

    python3 -OB check_full_two_by_three_tag_credit.py

The [checker](check_full_two_by_three_tag_credit.py) verifies
the exact previous checker bytes, then reuses the outward
one-arm convolution, four occupied classes, third finite
difference, true sieve coefficient bounds, and nonnegative
rank-density recursion of the previous theorems. It uses
160 ordered-separator bins and evaluates the additional
ordinary left first moment at floor .163 where required.
The shift is \(d=\lfloor1000-2000s_0\rfloor\), where
\(s_0\) is the center sum on the three-tag arm.
Every angular bound encloses the whole interval product
before enforcing the actual ordering.

The certified sum uses all \(66\times286=18876\) cell
pairs and both reflected orientations. In particular the
7150 cells whose computed lower is negative are **included**
with their full signed lower; their summed bilateral
lower contribution is about \(-.06932831\). It does not
assert that those individual actual covariances are
negative. The exact outward bilateral sum is
\(>.0883959\). The total per-orientation tag volume
is \(.077^5/12\), about \(2.2556534\cdot 10^{-7}\),
so no region of the specified chamber is left out.
Both real orientations use central intervals of
the same length, without assuming \(J=1-J\).

Replace only the old \(.0395M\) credit by the safe
\(.0883M\), and remove the whole new physical pair
of chambers from the signed exterior. This is the
claimed gain of \(.0488M\) with the smaller support.
