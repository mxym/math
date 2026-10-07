# Proof audit: tail-sensitive interpolation and transport

## Independent theorem

1. On a one-dimensional interval, monotone convex derivatives give the finite-difference estimate for every h, including h greater than interval length.
2. On each superlevel component of a BV density slice, the set where both derivative magnitudes are at most L is an interval up to null sets. Restriction therefore introduces at most one good interval, not an uncontrolled fragmentation.
3. On the bad set the large derivative dominates any bounded derivative, giving the pointwise factor-four tail estimate. Summing component tails is bounded by the vector-gradient tail without a dimension factor.
4. One-dimensional coarea counts superlevel components by half the full slice variation. Endpoint jumps are included. Tonelli applies to nonnegative terms; the potentials need only be finite convex on the open source domain.
5. The h optimization and the p-moment balance give exponent (p-2)/(3p-2). A normalized boundary ramp proves that exponent sharp for general potential-to-gradient interpolation, including failure of a moment-only interpolation modulus at p=2.

## Transport dependencies and limits

The source-specific application imports the centered-potential Lipschitz estimate from manuscript 001 v2. This pass inspected its conditional-cell transport, normalized-barycenter cancellation, moving-site variance, bounded-gradient interpolation, P2 completion and Gaussian sharpness mechanisms. It did not independently formalize or re-prove every finite-cell regularity hypothesis or the compact companion engine. The new theorem is separated as an independent interpolation statement and a transport implication under explicit assumption (P).

The bounded-target compact-source potential estimate is completed to all P2 targets in this manuscript. No naive truncation of a convex gradient is assumed to remain a Brenier map. Gradient pushforwards identify tails with actual target tails. The stretched-exponential estimate balances the tail against the one-third term.

The Wasserstein map exponent is NOT proved optimal. The p=2 ramp is NOT a counterexample to uniform Brenier-map continuity in Wasserstein distance. Constants may depend on dimension and the source; only the moment threshold p>2 is dimension-independent.

## Exact checks

6000 inequalities for rational piecewise-affine convex potentials and piecewise-constant densities, including zero-density gaps and non-log-concave profiles; 15 exact sharp-ramp cases; six exact exponent cases. Checks remain active with Python -O. They are finite regression evidence, not a formal proof of the general interpolation or the imported transport input.

## Provenance

Audited 001 source blob: d6896f8ac49e3a945324d5d57c54e1797775b1e5, in commit 5c6c088aa5abf1c1a4bdca6a8ce5beaa27faaef3. Earlier sources and the coarea theorem are cited. No prior manuscript was overwritten; no external peer review or priority certification is asserted.
