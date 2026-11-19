# Farthest-point Riesz mass: large outer parallels and a width criterion

Laugesen and Pritsker asked whether the Newtonian measure associated with the farthest distance to a compact set can put more mass back on that set than it does on a ball. In dimension $n\ge3$ the proposed upper bound is $2^{1-n}$. This note proves two partial results:

1. **Large outer parallel bodies, with an explicit second-order term.** For each fixed compact convex $K$, the normalized mass of $K+tB$ approaches one as $t$ tends to infinity. The first correction is of order $t^{-2}$, with an explicit deficit depending on the even and odd parts of the support function of $K$. Its coefficient is strictly positive unless $K$ is a translated ball or point. No regularity of $K$ is needed. See [the expansion and its proof](PARALLEL.md).
2. **A criterion using only the directional widths.** A condition on the support function of the central symmetral yields the sharp mass inequality for the original body. In particular it holds, with equality only for balls, if the half-width, normalized by a constant, is sufficiently close to one in $C^3$; the allowed distance is given explicitly. No separate smallness assumption is imposed on the odd part of the support function. See [the criterion and its proof](WIDTH.md).

Neither result settles the general conjecture. The first gives no uniform enlargement threshold and says nothing about monotonicity in $t$. The second is a smooth *width* condition, not an unrestricted neighborhood in the Hausdorff metric. The planar conjecture, the centrally symmetric and the constant-width cases, and the main flux comparison are prior results, not claims of this note.

[References, prior results and search limits](SOURCES.md) · [Internal review of the expansion](reviews/PARALLEL_REVIEW.md) · [Internal review of the criterion](reviews/WIDTH_REVIEW.md). These are AI-assisted proofs and AI internal reviews; they have not received external peer review and no priority is claimed.

## Reproduce the checks

From this directory, run `sha256sum -c SHA256SUMS` and `python3 -B -O verify.py`. [Expected output](CHECKS.txt). The standard-library test uses exact rational arithmetic to check a nonsmooth capsule, a translation and an odd degree-three harmonic, and to check coefficient algebra and curvature margins in selected dimensions. The analytic proofs, not these finite tests, establish the general statements.
