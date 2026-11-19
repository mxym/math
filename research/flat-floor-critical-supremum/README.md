# The sharp fixed-floor convex-position supremum at the critical sample size

Fix a convex floor of positive relative volume in a supporting hyperplane of a convex body in dimension $d\ge2$. The body may overhang its floor. What is the largest possible probability that all $d+1$ independent uniform samples are on the hull they form with that floor?

The [theorem and proof](SUPREMUM.md) give the supremum, which is never attained. For three samples in the plane it is $1-8/(3\pi^2)$; for four in space it is $485/512$. For $2\le n\le d$ the supremum is one and is not attained; the two-sample statement was already proved by Marckert and Morin. The proof bounds the event by replacing the whole floor with a point, applies the **classical** measurable-set Busemann random simplex inequality, and constructs bodies approaching its bound without changing the prescribed floor or volume.

This answers the maximum-value question at critical sample size in the unrestricted fixed-floor class. It does not determine the supremum within a vertical prism or at larger sample sizes. The distinct [planar all-$n$ minimum and square counterexample](../flat-floor-convex-position/) do not give this value.

See [sources and scope](SOURCES.md) and the [independent internal mathematical review](REVIEW.md). AI-assisted research; not externally peer-reviewed; priority is not established. The argument is analytic. The optional Python check compares the displayed constant with an independent radial-integral calculation and is not a proof by dimension enumeration.

    python3 -B -O check.py
    sha256sum -c SHA256SUMS
