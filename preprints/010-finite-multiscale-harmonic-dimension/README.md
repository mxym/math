# 010 — Finite multiscale harmonic-dimension counterexamples

This directory contains a finite quantifier strengthening of OpenAI/math
family 361.

For every finite number m of scales and every block ratio beta < 3/2, the
v1 theorem constructs one complete smooth Ricci-nonnegative metric on R^3
that violates the Euclidean integer-degree harmonic-dimension comparison
simultaneously on m widely separated consecutive blocks

    k_r <= d <= floor(beta (k_r+1)) - 1.

The same metric can be globally arbitrarily close to Euclidean in the
bi-Lipschitz sense, with asymptotic volume ratio arbitrarily close to one.

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
