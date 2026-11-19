# Which crossing tubes overlap least in the hyperbolic plane?

**Yongxian Zhang.** AI-assisted mathematical research note. Independently reviewed internally, not externally peer reviewed. Worldwide priority is not asserted.

Take any finite set of distinct complete geodesics in the curvature −1 hyperbolic plane, every two crossing at an interior point. Thicken every geodesic by the same positive distance. For **every** positive power of the pairwise intersection areas, their sum has one minimizing arrangement, up to isometry and labels: all the lines pass through one point and make equal successive angles there. The [proof](PROOF.md) gives the exact minimum at any width and all three leading constants when the half-width is 1/n.

The central step is geometric. Moving all crossings onto each possible anchor line's chosen point converts the family to a set of concurrent lines. Averaging this operation and using the hyperbolic triangle angle defect strictly improves the energy unless the lines were already concurrent. Strict log convexity of the exact two-tube area handles powers smaller than one as well. Once the family is concurrent, optimization of its directions on a circle uses a classical result.

This answers one precise finite-family version of Steinerberger's broad negative-curvature question; it makes no claim about noncrossing lines, closed geodesics on quotient surfaces, or general Kakeya estimates. See [sources and comparison](SOURCES.md) and [independent internal review](REVIEW.md). Reproduce the finite arithmetic checks with `sha256sum -c SHA256SUMS` and `python3 -O verify.py`, comparing [CHECKS.txt](CHECKS.txt).
