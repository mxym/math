# The sharp star Steiner ratio for weighted concyclic sites

For **each** integer $n\ge2$, the largest ratio between the least cost of a star rooted at one of $n$ **concyclic** sites and the least cost of a star centered anywhere in the plane is

$$
\frac2n\cot\frac{\pi}{2n}.
$$

The bound permits arbitrary positive demand weights, and the circle center need not be the geometric median. A regular $n$-gon with equal masses attains the bound. In particular the sharp supremum over all such finite circular configurations is $4/\pi$. These are the circular-input cases of the planar predictions of Dumitrescu–Tóth–Xu and Fekete–Meijer. **No assertion is made for unrestricted planar configurations.**

- [Finite-cardinality proof](FINITE.md): inversion and positive quadrature reduce the result to a lower bound for a weighted sum of distances on a circle. A telescoping identity and a gap-convexity estimate handle the near-regular regime; a complementary integral inequality handles the rest. There is a direct argument for three sites.
- [Shorter proof of the cardinality-free constant](CONCYCLIC.md): this also gives a detailed derivation of the shared quadrature identity.
- [Source and repository comparisons](SOURCES.md) distinguish previous results for a circle centered at the Weber point, for evenly spaced rays, and for dimensions three and up.
- [Internal mathematical review](reviews/FINITE-REVIEW.md) and [companion review](reviews/REVIEW.md). These are AI-assisted internal checks, not external peer review, and this draft does not establish priority. The reviewed Markdown source fingerprints refer to the mathematically identical pre-formatting copies; this edition updates display-math delimiters and draft labels.

From this directory, run `python3 -B -O finite_check.py` and compare to [FINITE-CHECKS.txt](FINITE-CHECKS.txt). The replay bounds entire intervals with integer fractions. On systems with GNU coreutils, `sha256sum -c SHA256SUMS` checks the package files.

For a shorter alternate verification of the three residual scalar bounds, run `python3 -B -O bernstein_check.py`. After clearing the positive denominators in (5) and (6), the respective degrees are 5, 4, and 3. The program subdivides their domains into 8, 1, and 4 intervals and expands in the nonnegative Bernstein basis on each interval; [the exact smallest coefficients](BERNSTEIN-CHECKS.txt) are all positive. This is a second arithmetic route, not an additional external review.
