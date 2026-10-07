# 010 — Finite multiscale harmonic-dimension counterexamples

This directory contains a finite quantifier strengthening of OpenAI/math
family 361.

For every finite number m of scales, every beta > 1, and every A >= 1
satisfying A beta^2 < 9/4, the v1 theorem constructs one complete smooth
Ricci-nonnegative metric on R^3 with the A-factor Euclidean
harmonic-dimension comparison violated simultaneously on m widely separated
consecutive blocks

    k_r <= d <= floor(beta (k_r+1)) - 1.

More precisely, h_d > A(d+1)^2 throughout every block. Thus the finite
multiscale construction retains the full one-scale excess tradeoff
A beta^2 < 9/4. The same metric can be globally arbitrarily close to
Euclidean in the bi-Lipschitz sense, with asymptotic volume ratio
arbitrarily close to one.

The new argument is finite-dimensional. It promotes all designated spectral
doubles to one common largest cutoff, concatenates disjoint band cycles,
and proves an exact rank-average identity for each band despite the presence
of all the others. The long Ricci/transfer/matching construction is imported
from a pinned public OpenAI/math commit and audited for the precise
finite-program hypotheses used here.

This result does not claim one fixed metric with violations at infinitely
many unbounded degrees.

See v1/ for the manuscript, dependency map, proof audit, and exact
arithmetic verification.

No novelty or priority claim is made pending systematic literature review.
