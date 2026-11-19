# The six-point Sylvester probability: the triangle minimum

Let six independent points be uniform in a compact planar convex body of positive area. The probability that all six are vertices of their convex hull is **at least 91/900**, with equality exactly for triangles. This is the lower extremum at six points, not the disk/ellipse maximum, a statement for all sample sizes, or a new formula for the triangle value.

The proof conditions on the six horizontal coordinates. It represents the upper and lower slice heights by endpoint widths and nonnegative slope jumps, then applies the established convex-comb recursion. Moving every chord parallel to itself until it rests on one line cannot increase the probability: this is where the exact coefficient calculation is used. For polygons, a shake along a diagonal removes at least one vertex. Approximation, and a separate strict-shaking argument, give the assertion and equality characterization for general bodies.

- [Proof](LOWER.md) and [primary sources / prior-work scope](SOURCES.md)
- [Exact verifier](lower_exact.py) and [expected output](CHECKS.txt)
- [Independent internal mathematical review](REVIEW.md)

Run `python3 -B -O lower_exact.py` with Python 3.9+ and NumPy. It derives the coefficients directly from the recursion, uses Python arbitrary-precision integers, checks every exact division and runs with assertions disabled. The 3,876 abscissa nodes form a unisolvent interpolation set, not a sample used to infer a sign. The verifier requires no downloaded certificate or network access.

Status: AI-assisted, internally reviewed and replayed, not externally peer-reviewed or formally verified in a proof assistant. The literature search is bounded and does not guarantee priority.
