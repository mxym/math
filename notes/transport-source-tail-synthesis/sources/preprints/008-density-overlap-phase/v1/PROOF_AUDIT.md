# Proof audit: density overlap and the boundary phase diagram

## Independent interpolation argument

1. The overlap weight min(r(x),r(x+h)) controls both difference-quotient endpoints and both translated signed-square terms. All signed changes of variables involve absolutely integrable functions. Convexity is required of the potentials and their domain, not of the density.
2. The exact translated-weight identity is expressed as the difference of two bounded relative losses at the SAME point. Replacing it by an untruncated density ratio would impose a stronger and unnecessary condition. The two losses yield coefficient fourteen in the final inequality.
3. The pointwise root inequality is integrated with Lebesgue measure, while the losses use the density-weighted probability measure. The distinction is explicit. Negative and positive root translations have equal norms.
4. The Sobolev root condition is global after zero extension. The Fisher criterion does not silently ignore support-boundary jumps. Chain-rule truncations and Holder prove the implication for every p>=4.

## Complete boundary family

5. The chosen source is fixed for each beta and strongly log-concave on its convex domain. The transverse bump has all root Sobolev orders, so no transverse hard jump changes the phase boundary.
6. The first root translation has power, critical logarithmic, and Sobolev regimes according to beta compared with p/(p-2)-1. The upper transport estimates invoke the pinned centered-potential theorem from 001 v3, not a new proof of that theorem.
7. The rare-cell lower bound uses unit-length rare directions and exactly unit pth target moments. Its hinge potentials and two-atom costs are explicit. The interior three-atom lower bound uses the actual source marginals, including symmetry only in the transverse coordinate.

## Critical logarithm: nontrivial proof obligations

8. Each scale solves TWO cumulative distribution equations, preserving both neighboring outer masses as well as the central mass. Matching only central masses would not justify the small target-coupling cost.
9. Symmetry of the bounded transverse marginal and a uniform first-derivative estimate for the longitudinal density give inverse-CDF errors O(h^2/t_n), uniformly in the number of scales. Choosing h below a fixed small multiple of the smallest t_n keeps every strip disjoint and overlapping its partner.
10. The local strips are realized by two GLOBAL finite convex maxima. The changed cusp positions preserve all outer slopes; supporting-line inequalities exclude interference from nonlocal planes. No arbitrary patched vector field is declared optimal.
11. Directly integrating the gradients yields an exact common-source map-cost identity. The same-label target coupling is used only as an upper bound, not incorrectly declared optimal.
12. The critical identity beta*p/2=beta+1 yields a logarithmic moment integral. One common scale factor places BOTH targets inside the unit moment class. Constants in the cost and moment bounds are uniform in K and h.
13. Choosing K comparable to log(1/w) and h explicitly from w proves a lower bound for EVERY sufficiently small w. The resulting logarithmic exponent is both necessary and sufficient, not an endpoint conjecture or a sequence-only statement.

## Dependency status

The independent interpolation and all lower-bound constructions stand without assumption (P). The transport upper bounds and hence the matched two-sided phase diagram use (P), supplied for the displayed sources by 001 v3, pinned source blob 0007edf5e28e4b4b0d34b2043cffd6e13e9f5aed. This pass reread the all-P2 statement and the finite-cell, conditional covariance, and moving-site variance mechanisms. It did not externally certify or formally reprove the entire 001 manuscript. That dependency is disclosed prominently and bundled at its fixed snapshot.

## Actual finite checks and layout review

Local standard-library exact arithmetic passed 1920 root/loss inequalities, 960 signed-square identities and 320 interpolation inequalities. Six separately built 2D finite affine-max examples had every target label mass matched and every source cell-pair integrated (454 intersections total). The checker recomputed the full map cost independently of the local strip formula. Its rational auxiliary density is explicitly not the smooth theorem density. Python -O also passed a smaller complete replay.

The 11-page LaTeX PDF was compiled twice, with no unresolved references or overfull boxes reported, rendered, and all pages visually inspected. Uploaded source and checker blob hashes match the tested local files. Finite tests and visual review are not a proof-assistant formalization or independent peer review. Bibliographic novelty and journal significance have not been certified.
