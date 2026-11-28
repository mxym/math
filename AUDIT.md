# Verification record

Two author-external checks were made on fixed research snapshots. This is an internal independent audit, not journal peer review.

1. On [47e5951e](https://github.com/mxym/math/commit/47e5951edb92f801e7eea8b02ddfc81bcf275bc1), the reviewer independently checked the pair-support count without a triple; the single-triple 36° phase bound and obstruction to joining two occupied axes; and why any E₆ completion containing one triple must contain its negatives and all 18 axial difference roots, even when the completion is not assumed to preserve the marked planes.
2. On [4b782c9c](https://github.com/mxym/math/commit/4b782c9cb9f76b74fbb231d9fce0c91e7523a83d), the reviewer independently recalculated the single-triple obstruction at 60. The upper envelope quadratic on the triangle has vertex values 2/3−√3/2 and 25/24−5√3/8. Both are negative. The forced radii and phases at the zero-triple 60-point equality case and the remaining coordinate conjugations were also checked.

The independently written standard-Python program checks the root set in a different coordinate scaling, including all 5,184 ordered root reflections and the 18 completion directions. It checks all 1,770 pairs of the non-root witness, including inner product 1/3, and all 1,596 pairs of the 57-point witness using four-basis arithmetic in Q(√2,√3). Both programs were re-run in normal Python on the fixed material. The author program separately verifies a simple-root diagram and its 72-point Weyl orbit.

The three witnesses are not an upper-bound certificate on their own. The interval-free, analytic phase and counting proof is the part of the manuscript that applies to arbitrary continuous radii and phases.
