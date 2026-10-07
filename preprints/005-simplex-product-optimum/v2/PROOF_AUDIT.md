# Proof audit and replay scope — 005 v2

## Analytic self-review

The following checks concern the written argument. They are not independent referee review.

**Normalization and covariance.** Projection-body segments use full facet area-normal vectors as generator lengths, not a doubled or halved determinant sum. Horizontal and lifted determinants scale respectively as $|\det L|^{d-1}$ and $|\det L|^d$. Translations act by a shear on the lifted zonotope. Both invariants are affine invariant, including under orientation reversal.

**Degenerate minor cases and equality.** The lower bound for a accounts for horizontally dependent d-tuples instead of dividing by a zero determinant. Such tuples can still give positive lifted minors. This is essential to the equality classification: a short positive dependence forces a strictly positive error term; a full-dimensional positive dependence yields a simplex containing K whose vertices equality places back inside K. The equality theorem is stated for polytopes only. Approximation by strict inequalities is not misused to claim the same equality theorem for all convex bodies.

**Product and join dimensions.** The only nonzero determinant patterns are (r,s) for a product horizontal determinant, (r+1,s) or (r,s+1) for its lift and for a join horizontal determinant, and (r+1,s+1) for a join lift. The join's extra coordinate and the two support numerators are included. A direct facet-integration argument fixes the beta-integral coefficients. Interval factors work with endpoint facet volume one. Point factors occur only formally in the join grammar; a point join is a pyramid, and a pair of points yields an interval.

**Continuity.** The general-body definition of a uses an actual pyramid. Common interior balls give multiplicative Hausdorff sandwiches for bodies and projection bodies. This establishes continuity and preserves positivity via a >= 1/(d+1). It avoids assuming a polytope facet formula for a nonsmooth body.

**Amplification.** The pyramid iff includes its equality boundary. Universal join amplification uses an explicit central-binomial induction and gives a finite sufficient m. This is not a limiting heuristic. Its conclusion is failure of finite-dimensional attainment across dimensions, not failure of fixed-dimensional existence.

**Finite closure.** Coordinates are (R,aR), not (R,a). Product/join maps are positive bilinear. Downward convex hulls therefore permit pruning, with a proved inductive certificate interface. Every retained vertex is attained by a recipe; every ordered pair image is checked. No assumption that a single R-maximizing child also maximizes the parent's result is made.

**Infinite family.** The dimension and a recurrences are solved exactly. Bounds 3 < D_j < 6 apply for all levels, not just those computed. They prove existence, strict increase, and an explicit analytic tail bracket. Exact inequalities at level 6, with exponent 65536, certify the decimal rational endpoints. Finitely many recurrence evaluations alone would not certify a limit.

**All dimensions and comparison.** A block dimension at most sqrt(n) leaves a residual of negligible relative dimension. The comparison with v1.1 uses convergence of both root sequences and a strictly separated rational factor. No explicit starting dimension is claimed. No comparison with the unrestricted best known bound is inferred.

## Independent algorithmic verification actually run

The checker was run successfully on the VPS with standard Python and again with `python3 -O`. Both generated reports agree. Its independence consists of different checking algorithms without importing the producer; this is not a claim that a second human or a second proof assistant reviewed the research.

- The finite certificate contains 46 upper-hull vertices in dimensions zero through fourteen. Its closure checks cover every ordered product and join split.
- Fourteen direct tests evaluate rational facet data for products, joins and pyramids, including nonsimplex square and octahedron inputs.
- All 136 maximal horizontal/lifted minors of the fourteen-dimensional witness are evaluated with exact division checks.
- The recursive family is recomputed by central-binomial coefficients rather than the producer's g-ratios. The endpoint and old-class comparisons are integer inequalities after clearing denominators.
- Four corrupted certificates are rejected.

The manifest and replay reports give the exact sizes and hashes. No numerical optimization or external solver is a proof dependency.

## Adjacent manuscript review

This pass read the complete 004 v1.1, 005 v1.1, 006 v1, and 007 v1 source arguments, including endpoint and scope sections. No material error was identified in those reviewed arguments. This is a bounded-scope mathematical review, not certification of the entire shared repository.

004: checked density flattening, predecessor-grid stability, conditional terminal-bit independence, separate parameter-boundary representatives, repair of every exceptional center, and the countable tail/scale union. Its finite toy is correctly not claimed to witness the small-density theorem.

005 v1.1: replayed its exact verifier through dimension 300, including seven rational comparisons, 80 finite no-tie certificates, and exhaustive partition dynamic programming. No prior file was modified.

006: checked the tail-independent order of parameter choices, the finest-grid buffer cost, the two-buffer treatment of closed error bounds, countable indexing of remainder classes, distinctness of output hits, and the separate C1/flat-smooth endpoint constructions. The argument correctly avoids claiming all-modulus or all-smooth nonuniversality.

007: checked the one-dimensional good-interval truncation, BV layer-cake counting with endpoint jumps, vector-tail summation without an extra tail dimension factor, the sharp ramp exponent, and the explicit separation of interpolation from the imported potential bound (P). The 001 transport engine underlying (P) was not fully re-audited in this pass. Therefore the source-specific transport application retains that dependency; only its local interpolation proof was reviewed independently of that engine.

No changes to 004, 006, or 007 were made merely to register an audit. Their authorship and first-disclosure records remain intact.

The adjacent finite checkers were also replayed under optimized Python: six 004 cases, nine 006 robust-cover cases, and 6000 007 interpolation inequalities, plus its 15 ramp and six exponent checks. Exact reports and source-script hashes are stored in `results/adjacent-*`. These regression passes do not replace the written infinite arguments or revalidate the imported 001 transport engine.
