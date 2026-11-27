# Thirty retained D5 roots suffice for a forty-point ceiling

**Theorem.** A five-dimensional kissing configuration containing at least 30 of the 40 signed roots of a rotated D5 has at most 40 points. The [nine-omission theorem](KissingFiveNineOmissions.md) leaves only ten omissions. We make no claim about all five-dimensional configurations.

For a hypothetical code of 41 points let U be its ten missing roots and let its eleven outsiders be distinct nonroots. Use the real chamber enclosures and capacity-one signed blocker masks of the [initial certificate](KissingFiveNearD5.md); all eight additional size-ten ideals pass the capacity-one test. In fact no larger mask ever occurs by the [all-rank D_n bound](RootDnCapMultiplicities.md). As before the 20-line projective upper bound implies that some two outsiders have product <−1. They cannot have a common blocker.

**First pass.** Enumerate the 171,637 signed ten-omission classes containing a candidate mask. In addition to the previous hull comparisons, precompute strict open angular caps: for an integer direction w with nonzero entries of magnitudes 1 or 2 drawn from the patterns in the verifier, certify a chamber slice is strictly within 30 degrees of w as described below. If all chambers of a signed mask lie in the same such cap, use it as an additional incompatibility test. Two outsider masks whose genuine points always share a strict 30-degree cap cannot coexist. The main census is:

| rejection test, in order | classes |
|:---|---:|
| fewer than eleven masks | 145,599 |
| an omitted root has fewer than two masks | 25,292 |
| an omitted root has no compatible pair of masks | 473 |
| no candidate negative edge | 126 |
| no compatible eleven-clique | 142 |
| no such clique with two blockers for every omitted root | 1 |
| left | 4 |

**One chamber per actual point.** Pairwise compatible signed masks can use inconsistent chamber choices. In the remaining cases keep a variable for the particular signed permutation chamber realizing each outsider, impose all pairwise compatibility constraints simultaneously, and require the selected negative edge to remain possible in the same chosen chambers. Before that search a stronger exchange test is available. For every nonempty subset W of U at least |W|+1 of the eleven points must block a member of W. Otherwise restoring all roots of W and deleting the at most |W| blockers gives at least 41 points and fewer omissions, contrary to the preceding bound. If extra points need to be discarded, discard outsiders, not the restored roots.

For the angle checks, write the canonical chamber coordinates as a. To show a cell lies in the open cap of aperture θ about w, retain only points violating the asserted lower bound on a·w and prove the resulting polytope has no genuine nonroot sphere point with the prescribed strict mask. Use the halfspace
```
(2a)·w ≤ ceil(64 sqrt(cθ ‖w‖²))/64 ,
```
where cθ is an exact rational upper bound on 8cos²θ. For θ=15°,30°,45°,60°,75°,90° the verifier uses respectively 7465/1000, 6, 4, 2, 536/1000, 0. The ceiling is evaluated by integer comparison. Clipped-polytope vertices are among retained old vertices and intersections of the cutting plane with vertex pairs straddling it (enumerating all pairs includes all edges). Compare each squared norm exactly with 2 by clearing denominators. If the largest norm is ≤√2 and every equality vertex is either a root or lacks the strict mask, strict convexity proves the required absence.

For kissing incompatibility one may use two strict caps with the same center and apertures totaling at most 60° (15°+45° or 30°+30°). To exclude a negative edge the corresponding total is 120° (30°+90°, 45°+75°, or 60°+60°). All possible signed-permutation relative chambers are overcounted, never sampled. The leaf search selects one chamber per point by exact finite backtracking, pruning a choice only when no remaining allowed chamber for some other point exists. A genuine configuration would give a consistent complete assignment.

In the four cases the numbers of possible negative-edge pairs after the angular refinement are 2, 4, 30, 17 in the order printed by the checker. One case already fails strict exchange. In each of the other three no eleven-clique with the required negative edge has a consistent chamber assignment. Thus all ten-omission configurations are excluded.

[Standalone Node verifier](verify-kissing-5d-ten-omissions.js), no dependencies. Polyhedral determinants use integers of arbitrary precision. Remaining five-coordinate dot, cap-cut and comparison operations use integers exactly representable in binary64: generator coordinates scaled by 192 are at most 288 in magnitude, uncut vertices scaled by two are at most 3, direction entries at most 2, and cut affine numerators and denominators bounded by 64·(5·3·2)+ceil(64√(8·20))≤2731 in absolute value before taking weighted differences. These imply ample room below 2⁵³ in all squared comparisons.
