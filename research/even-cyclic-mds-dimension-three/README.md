# Even-length cyclic MDS codes in dimension and codimension three

**Scope.** The even-length, dimension-three and codimension-three
slices of [Liu–Li–Huang, Open Problem 1.1](https://arxiv.org/html/2611.32165v1#S1.ThmThm1).
Let \(n\ge5\) be even, \(q=p^f\) a prime power, \(p\nmid n\), and
\(n\nmid q-1,\ n\nmid q+1\). Thus \(p\) is odd. No claims are made
for other dimensions, repeated roots, or constacyclic codes.

Write \(n=2m\) and
\[
 B_m(T)=\sum_{j=0}^{m/2}\binom{m}{2j}T^j,\qquad
 D_m=\operatorname{Res}_T(T^{m/2}+1,B_m(T)),
\]
where these polynomials are used only for \(4\mid m\).
An \([n,3]_q\) cyclic MDS code (equivalently, an
\([n,n-3]_q\) cyclic MDS code) exists **if and only if**
\[
  4\mid m,\qquad q\equiv m-1\pmod {2m},\qquad p\nmid D_m .
\]
In the allowed residue, \(n\mid q^2-1\) follows automatically
and \(D_m\ne0\) as an integer. Thus the two polynomials of degree
\(n/4\) give exactly the excluded characteristics among the
allowed fields, not merely a sufficient lower bound on \(p\).
When a code exists there is one base-field monomial-equivalence
class. Its representative has Fourier support
\(\{0,1,m-1\}\). See [PROOF.md](PROOF.md) for the base-field
trace realization and the exact count of singular three-column
minors, also when the candidate fails to be MDS.

With \(h=(q+1)/m\) (necessarily odd), the determinant test is
equivalent to the absence of rational points on a genus
\((h-1)^2\) curve. A symmetry pairs every point corresponding to a
repeated label with one giving an actual bad triple. Consequently
\(q+1>2(h-1)^2\sqrt q\) is sufficient for nonexistence, without
subtracting the repeated-label points in the Hasse–Weil test.
For \(h=1\) no code exists. For \(h=3\) the entire list is
\([8,3]_{11}\), \([16,3]_{23}\), and their respective duals.
These positive examples were already known geometrically.

The underlying planar two-ellipse orbit, general Fourier-minor
method, and the \(q^{3/4}\) order of the related chord-covering
bound are not new. In particular Shokrollahi's odd-characteristic
RS result is explicitly for length \(q-1\), not these lengths.
The focused addendum is the exact small-degree arithmetic test,
the singular-minor/curve-point counts and the fixed-index
nonexistence conclusion. For orientation, the proof records a
separately credited odd-length Singer-type test; we do not claim
that odd case as a new resolution. See [SOURCES.md](SOURCES.md)
for the precise comparison and limits of the source check.

## Replay

Run `sh replay.sh` with Python 3.8+ (standard library only).
One program uses exact integer norms, prime-field polynomial
gcds and enumeration of the stable support sieve. The other
forms literal three-column determinants and counts the torus
points and the involution in independently represented quadratic
fields. Neither finite check is used in place of the general
proof; they certify the small-index table and boundary examples.
