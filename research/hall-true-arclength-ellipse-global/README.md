# The circle uniquely maximizes the acute-triangle probability for true ellipse perimeter samples

Pick three independent uniform **arc-length** points on any Euclidean ellipse. The probability they form an acute triangle is at most \(1/4\), with equality **if and only if the ellipse is a circle**. This concerns every semiaxis ratio, not only small departures from a circle.

The [proof](PROOF.md) splits the aspect-ratio range in two. For thin ellipses, a comparison with uniform angular sampling reduces the upper bound to ten terms of a positive series. Elsewhere, the exact orthogonal-chord integral becomes a finite Fourier-polynomial lower bound on the excess obtuse probability, with both truncation errors controlled. After removing the quartic zero at the circle and a positive denominator, all 267 Bernstein coefficients on one interval are strictly positive. This is an exact, rational, computer-assisted sign proof, not simulation.

This extends the [previous local comparison](../hall-true-area-ellipsoid-local/README.md), which already derived the moving-domain triangle integral and its first nonzero term. The [December 2024 question about probability at given semiaxes, with Christophe Boilley's January 2025 arc-integral answer](https://math.stackexchange.com/questions/5014676/probability-that-triangle-on-ellipse-is-acute), is a direct precedent. See [sources and corpus comparison](SOURCES.md). We do not claim monotonicity between different noncircular ellipses, a global theorem for higher-dimensional ellipsoids or general boundary curves, or a solution of Hall's volume-sampling conjecture.

**Reproduce** (standard-library Python 3):
```sh
sha256sum -c SHA256SUMS
python3 -B -O verify_poly.py
python3 -B -O check_primitive.py
```
The second check tests all 4,913 Fourier triples against residues of an independently derived simplex Laplace transform. The [internal mathematical review](REVIEW.md) records the scope and analytical checks. This AI-assisted result has not received external peer review; bibliographic searches cannot certify priority.
