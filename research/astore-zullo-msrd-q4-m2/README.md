# Exactly three full blocks in the \(q=4,\ m=2\) case of Astore–Zullo

**Result.** Over \(K=\mathbb F_{16}\), with base field \(F=\mathbb F_4\),
there is a three-dimensional maximum sum-rank distance (MSRD) system
of three full blocks of \(F\)-rank two, but none of four full blocks.
Thus the maximum number of full blocks of length two for dimension
three is three. In particular, [Astore–Zullo, Problem 6.16](https://arxiv.org/html/2610.23633v1)
has a negative answer for \((q,m)=(4,2)\).
This is a fixed-parameter result, not a resolution for all \(q,m\)
or of Conjecture 6.21.

The exclusion below is analytic. The two scripts are independent
finite regression checks: projective incidence in a polynomial
model and direct sum-rank checks in a tower-field model.

## 1. From sum-rank to Baer sublines

For \(t\) full blocks let \(U_i\) be the \(F\)-span in \(K^3\) of
the two columns in block \(i\) of a generator matrix. A
three-dimensional MSRD code of length \(2t\) has minimum
sum-rank distance \(2t-2\). Each block must have rank two as
an \(F\)-span. Equivalently, this is part of the definition of
a nondegenerate system in the source paper. It also follows for a
full-dimensional code attaining this distance: a dependence in
a block can be removed by an invertible \(F\)-linear change of its
columns followed by deletion of a zero column, which preserves
all weights and contradicts the Singleton bound for the shorter
profile.

For a nonzero message \(\alpha\in K^3\), the rank of its \(i\)th
block is \(2-\dim_F(U_i\cap H_\alpha)\), where \(H_\alpha\)
is the \(K\)-hyperplane \(\ker(\alpha\cdot -)\). This follows
by applying rank-nullity over \(F\) to the linear functional on
\(U_i\). Thus the MSRD condition is that
\[
 \sum_i\dim_F(U_i\cap H)\le 2
 \qquad\text{for every \(K\)-hyperplane \(H\) of \(K^3\)}. \tag{1}
\]
Conversely, (1) for \(t\ge2\) forces the spans of all the \(U_i\)
together to be all of \(K^3\), since otherwise a hyperplane
containing them all would have sum \(2t>2\). Each block in an
MSRD code of at least two blocks must \(K\)-span a two-dimensional
space: otherwise a hyperplane containing its one-dimensional
\(K\)-span and a nonzero vector from another block would violate
(1). Consequently the projective support \(\ell_i\) is a line,
and the five projective points of \(U_i\setminus\{0\}\) form
a *Baer subline* \(B_i\subset\ell_i\), meaning the projective
image of \(\mathrm{PG}(1,F)\) in \(\mathrm{PG}(1,K)\). Conversely
every Baer subline is the projective image of such a subspace,
by choosing two \(K\)-independent vectors as an \(F\)-basis
after a projectivity of the line.

Condition (1) translates exactly to:

* the supporting lines are distinct; no point chosen for one
  block lies on the supporting line of another;
* no line contains chosen points from three different blocks.

Necessity follows by summing the intersection ranks. For
sufficiency a supporting line contributes two from its own
block and zero elsewhere. Any other line contributes at most
one from each block, and at most two in total by the second
condition. Thus the conditions are also sufficient for (1).
Singleton then gives equality in the distance assertion.

## 2. Normalize any two blocks

Write \(\bar a=a^4\), \(N(a)=a\bar a=a^5\), and
\(U=\{a\in K:N(a)=1\}\). Norm on \(K^\times\) is onto
\(F^\times\) with kernel of order five, by the multiplicative
group of a finite field or by the explicit primitive element
in §3.

We first show that all Baer sublines of
\(\mathrm{PG}(1,K)\) avoiding \(\infty\) are the affine circles
\[
 \{z\in K: N(z-c)=r\},\qquad c\in K,\ r\in F^\times. \tag{2}
\]
The norm-one circle is a Baer subline: for
\(\theta\in K\setminus F\) the projectivity
\(x\mapsto (x-\theta)/(x-\bar\theta)\) on
\(\mathrm{PG}(1,K)\) sends \(F\cup\{\infty\}\) into \(U\), since
conjugation inverts each image; its five images are distinct.
Scaling and translating gives (2). Two different circles have
at most two common points. With the same center different
radii give none; with different centers subtracting the norm
equations gives a nontrivial affine \(F\)-linear trace equation
in \(z\). The trace pairing in this quadratic extension is
nonzero: a nonzero multiplier is invertible, and
\(w+\bar w=0\) holds exactly for \(w\in F\). Thus the trace
equation cuts out an affine \(F\)-line in the two-dimensional
\(F\)-space \(K\). Substitution \(z=z_0+a s\), \(s\in F\),
\(a\ne0\), into a norm equation yields a quadratic with
leading coefficient \(N(a)\ne0\), so at most two solutions.

There are \(16\cdot3=48\) distinct circles (2). Every three
distinct points of \(\mathrm{PG}(1,K)\) lie on exactly one
Baer subline: send them to \(\infty,0,1\), and use the
three-point projectivity property of \(\mathrm{PGL}(2,F)\)
on their preimages to see that the uniquely normalized
subline is \(\mathrm{PG}(1,F)\). Hence there are
\(\binom{17}{3}/\binom{5}{3}=68\) Baer sublines in total,
and \(\binom{16}{2}/\binom 42=20\) through \(\infty\).
This proves (2) exhausts the other 48.

For any pair of blocks, their supporting lines are distinct,
and their common point is not chosen in either. A projectivity
of \(\mathrm{PG}(2,K)\) sends the lines to \(Y=0\), \(X=0\)
and their common point to \((0:0:1)\), using a basis chosen
on the two lines. Their chosen sets are now circles (2) in
coordinates \(Z/X\), \(Z/Y\), respectively. A single shear
\(Z\mapsto Z-c_1 X-c_2 Y\) removes both centers.
Scaling \(X\) and \(Y\) independently by norm preimages
of the two radii normalizes both to radius one. Therefore
every candidate family with at least two blocks is equivalent,
by a common projectivity, to one containing the normalized pair
\[
 A=\{(1:0:s):s\in U\},\qquad B=\{(0:1:u):u\in U\},
 \tag{3}
\]
on \(Y=0\), \(X=0\). Projectivities preserve all incidence and
send Baer sublines to Baer sublines, so this reduction loses
no possible extension.

## 3. Allowed points after fixing the pair

Every point of a new block must avoid both old supporting
lines, so it can be written \((1:t:z)\) with \(t\ne0\).
It must not be collinear with a point of each of \(A,B\).
The line through \((1:0:s)\), \((0:1:u)\) has equation
\(Z=sX+uY\). Thus the allowed points in the chart are those
with \(z\notin U+tU\).

The sum of the five elements of \(U\) is zero (they are the
roots of \(X^5-1\)). Its ten sums of distinct unordered pairs
are all distinct: if the pairs share a point, cancellation
forces equality of the pairs; if disjoint, equality forces
the unused fifth element to be zero, impossible. No such
sum is in \(U\): if it were one of the summands, the other
would be zero, and if distinct from both, the other two
elements of \(U\) would sum to zero in characteristic two.
So \(U+U=\{0\}\cup(K^\times\setminus U)\).

For \(t\notin U\), instead \(U+tU=K^\times\). Here is a
short direct field certificate. Take
\(K=\mathbb F_2[a]/(a^4+a+1)\); the polynomial is irreducible
(no roots in \(\mathbb F_2\) and not divisible by the only
irreducible quadratic \(X^2+X+1\)). Its root \(a\) has
order fifteen: powers \(a^3\), \(a^5=a^2+a\) are not 1.
Then \(U=\langle a^3\rangle\).
The sumset \(U+a U\) contains
\[
  1=a^9+a\,a^6,\qquad
  a=1+a\,a^3,\qquad
  a^2=a^{12}+a\,a^6 .
\]
Each identity follows by \(a^4=a+1\); these elements represent
the three cosets of \(U\) in \(K^\times\). Since \(U+aU\)
is invariant under multiplication by \(U\) and excludes zero,
it is all \(K^\times\). Replacing \(a\) by \(a^{-1}\) does
not change the conclusion, since
\(U+a^{-1}U=a^{-1}(U+aU)\). Those two ratios up to \(U\)
cover \(K^\times\setminus U\).

The resulting allowed set is exactly
\[
 \{(1:t:z):t,z\in U\}
 \ \cup\
 \{(1:t:0):t\in K^\times\setminus U\}. \tag{4}
\]
There are \(25+10=35\) points in (4).

## 4. Additional block lines and incompatibility

A new supporting line must not contain any selected point
of \(A\) or \(B\). The line \(X=0\) is already excluded.
In the chart \(X=1\), every other line is vertical \(t=c\)
or \(z=\alpha t+\beta\). In the vertical case \(c=0\) is an
old supporting line. For \(c\ne0\), (4) supplies exactly
five points if \(c\in U\), and only one if \(c\notin U\).
Thus the only possible vertical block \(V_c\) is
\[
 V_c=\{(1:c:z):z\in U\},\qquad c\in U .
\]
These five-point sets are Baer sublines by §2.

For a nonvertical line the intersections with the base lines
are \((1:0:\beta)\) and \((0:1:\alpha)\). To avoid selected
base points both \(\alpha,\beta\) must be outside \(U\).
In particular, the five lines \(z=s\), \(s\in U\), meet \(A\),
and the five lines \(z=st\), \(s\in U\), meet \(B\).
Though each of those ten lines contains five points of (4),
none can support an additional block.
If \(\alpha=\beta=0\), the line is \(Z=0\). If exactly
one is zero, the conditions \(\alpha,\beta\notin U\)
and \(t\ne0\) give no points of (4): in the constant case
the value is neither zero nor in \(U\), and in the other
case \(t\in U\) implies \(\alpha t\notin U\) while the
value never vanishes. If \(\alpha,\beta\ne0\), at most
two points come from \(t,z\in U\). Indeed, substitute \(t^4=t^{-1}\)
into \((\alpha t+\beta)^5=1\) and multiply by \(t\) to obtain
\[
 \alpha\beta^4t^2+(\alpha^5+\beta^5+1)t+\alpha^4\beta=0.
\]
The leading coefficient is nonzero, so at most two \(t\)'s occur. The possible zero value of \(z\)
adds at most one further point. So no five-point Baer subline
of (4) lies on any such line other than \(Z=0\).

Two distinct vertical candidates \(V_c,V_d\) cannot coexist:
for any \(s\in U\) the two selected points with \(z=s\)
lie on the horizontal line through \((1:0:s)\in A\).
Two candidates on \(Z=0\) likewise cannot coexist because
their supporting lines would coincide. It remains to rule
out a Baer subline on \(Z=0\) together with \(V_c\).
For a selected zero-line point at \(t\in K^\times\setminus U\),
the line joining it to \((1:c:s)\in V_c\), \(s\in U\),
has slope \(s/(t+c)\) and intercept \(st/(t+c)\).
It therefore hits a selected point of \(B\) if \(t+c\in U\)
and of \(A\) if \(t/(t+c)\in U\). Put \(v=t/c\).
The resulting exclusion tests are \(v+1\in U\) and
\(v/(v+1)\in U\); they are independent of the choice of
\(s\in U\). The first forbids the four values
\(v=1+u\), \(u\in U\setminus\{1\}\), outside \(U\) by §3.
The second forbids the four values
\(v=u/(1+u)\), \(u\in U\setminus\{1\}\), also outside \(U\)
since \(1+u\notin U\). These two sets are disjoint,
because if both tests hold their product \(v\) belongs
to \(U\). Thus 8 of the 10 allowed zero-line parameters
are forbidden by a vertical block. At most two can coexist
with \(V_c\), not the five needed for a Baer subline.

This proves at most one further block can be added to (3);
there are at most three altogether. The bound is attained
by (3) and \(V_1\): its line meets the base lines only at
their unchosen common point, and (4) guarantees no
three-block collinear triple. All equivalences of §1 apply.

## 5. Literature and replay

Astore and Zullo, [*On the Length of Maximum Sum-Rank Distance Codes*,
arXiv:2610.23633v1](https://arxiv.org/abs/2610.23633v1), 16 October
2026, Problem 6.16 (PDF p. 24) asks about full \(m\)-blocks with \(t=q\) and
\(k=m+1\). Theorem 6.18 (p. 25) answers yes for \((q,m)=(3,2)\), not
for \(q=4\); their Remark 6.19 has a three-block construction
for other \(q\) with certain norms and specifically does not
give a full \(q\)-block answer at \(q=4\). Our result also
does not contradict their separate Conjecture 6.21,
whose hypothesis \(\min(k,N-k)\ge4\) fails in dimension 3.

On 27 November 2026 searches for the paper and its Problem 6.16
with \(q=4\), \(\mathbb F_{16}\), *Baer sublines*, *full blocks*
and *semiovals* found no source deciding this precise
case. This is not a priority guarantee. We make no claim to
novelty of three-block attainability alone, of linearized
Reed–Solomon codes, or of the standard correspondence of §1.

Run independently using Python 3 and its standard library:

    python3 verify_geometry.py
    python3 verify_rank.py

The first uses the polynomial model of §3 and checks projective
incidences directly: 273 points, 35 eligible points after (3),
7 individual candidate sublines on 6 supports, 0 compatible
pairs. The second uses the tower \(F_4[b]/(b^2+b+\omega)\) for
\(K\), generates sublines from rank-two column pairs and checks
all normalized nonzero messages via their sum-rank weights. It
independently recovers 7 single extensions and no pair. Both
check attainment and deliberate failing examples.
