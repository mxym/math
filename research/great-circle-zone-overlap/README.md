# Sharp asymptotics for overlap of great-circle zones

**Yongxian Zhang.** AI-assisted mathematical note. Independently reviewed internally, not externally peer reviewed. Priority is not asserted.

How much must $n$ great-circle neighborhoods of half-width $1/n$ overlap on the unit sphere? For the sum of powers of the pairwise intersection areas, Steinerberger proved the sharp *orders* in all three regimes and connected shrinking zones around fixed circles to a projective Riesz kernel. Here the number of circles and the width vary **together**, and we optimize the true, bounded intersection area rather than substituting the bare singular kernel.

The [proof](PROOF.md) shows that the two optimized energies, properly scaled, have ratio tending to one, with relative error bounds for $s>1$. With ordered pairs and ordinary sphere area, the minimum total pair-overlap tends to $4\pi$ at $s=1$; the critical $s=2$ minimum is asymptotic to $32 n^{-2}\log n$. At $s>2$ the leading coefficient is expressed in terms of the established planar hypersingular Riesz constant, not evaluated here. Optimizing poles equidistribute as **unoriented lines**.

This gives macroscopic information, not identical finite minimizers, their microscopic arrangement, a discrepancy rate, or an $L^\infty$ multiplicity bound. See [prior work and scope](SOURCES.md), and the [independent internal review](REVIEW.md). Reproduce the supporting exact consistency checks with `sha256sum -c SHA256SUMS` and `python3 -O verify.py` (compare [CHECKS.txt](CHECKS.txt)). The limiting theorem is proved analytically.
