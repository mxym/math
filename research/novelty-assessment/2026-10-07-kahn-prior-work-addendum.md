# Kahn 1994: prior work for the near-linear cover programme

Added 7 October 2026 after reading the primary manuscript. This corrects
the earlier limited literature screens; it is not a proof correction.
Previously frozen proof packages and their checksums are preserved.

Jeff Kahn, *On a Problem of Erdős and Lovász. II: n(r)=O(r)*,
Journal of the American Mathematical Society **7** (1994), 125–143,
DOI [10.1090/S0894-0347-1994-1224593-5](https://doi.org/10.1090/S0894-0347-1994-1224593-5),
[primary manuscript](https://www.ams.org/journals/jams/1994-07-01/S0894-0347-1994-1224593-5/S0894-0347-1994-1224593-5.pdf),
Section 5, Corollary 5.4 (printed page 140), establishes:

For fixed c, an intersecting r-uniform hypergraph with at most cr edges
and maximum intersection of two distinct edges o(r) satisfies
tau(H) <= (c/(c+1)+o(1))r, as r tends to infinity.

This already gives superlinear edge necessity when tau/r tends to one
in the linear subclass. It applies without a partite assumption.

The corresponding conclusion under I(H)=o(r²) is a simple consequence,
which we spell out. Put epsilon=I/r² and
delta=sqrt(epsilon)+r^(-1/2). Then delta tends to zero and delta*r tends
to infinity. A pair with intersection at least delta*r contributes at
least delta*r-1 to I. The number of such pairs is at most
I/(delta*r-1)=o(r). Delete one edge from each bad pair. At most s=o(r)
distinct edges are removed; the remaining family has maximum pair
intersection o(r). Adding removed edges back increases its minimum
cover number by at most s, by choosing one vertex from each removed
edge. Kahn's corollary therefore gives the harmonic bound for the
original sequence as well. When I=0 the bad-pair count is zero and
the same choice of delta works.

For m/r tending to c, apply the corollary with any fixed upper budget
c+eta, then let eta decrease to zero. For bounded but nonconvergent
m/r, pass to subsequences. Consequently tau/r tending to one and
I=o(r²) imply m/r tending to infinity. This includes the partite
tau>=r-1 setting. Kahn's result also implies all weaker constant-slope
edge lower bounds in this restricted asymptotic class.

These consequences of Kahn's corollary are **prior results**, not an
original breakthrough of this repository. The independent deductions
in the frozen notes remain valid. This correction does not concern
the unrestricted partite inequalities 13r/4-O(1) or (10/3-o(1))r,
whose hypotheses allow uncontrolled intersections.

The newer cover-law package proves the smaller piecewise linear bound
h(c), a finite inequality with an explicit I/r coefficient, an explicit
strict gap at noninteger c>1, and integer equality degree rigidity.
At positive integers h(c)=c/(c+1); between integers h(c) is strictly
smaller. These distinctions survive the comparison with Corollary 5.4.
The present limited screen has not established their historical novelty.
The affine-space endpoint examples are standard design duals.

Kahn's Conjecture 5.5 in the same section asks whether the harmonic
bound remains valid with only maximum *triple* intersection o(r).
Its current literature status is being checked. No solution of that
conjecture is claimed here.
