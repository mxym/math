# Fifty-five arbitrary signed roots of an $E_6$ frame suffice

**Theorem.** If a six-dimensional kissing configuration contains at least 55 of the 72 signed roots of a fixed copy of $E_6$, then it has at most 72 points. No pattern of missing signs is prescribed. The other points may be arbitrary real vectors. Equivalently, a hypothetical 73-point code would overlap every orthogonal copy of $E_6$ in at most 54 points. This lowers the previous [sufficient threshold 56](KissingSixSixteenArbitraryOmissions.md); it is not the unrestricted kissing-number conjecture.

Use squared length two and inner-product cutoff one. Each of the 36 original axes consists of two signed roots.

## Restoration and the last case

The 56-root result leaves 55 retained original signs and 17 omissions. A code larger than 73 can be reduced to 73 while keeping every original root. In a 73-point candidate there are exactly 18 outsiders (points not in the original frame). The blocker mask of an outsider consists of the original signed roots having inner product strictly greater than one with it. Every missing sign must belong to the masks of at least **two mutually compatible outsiders**: otherwise restore that root and discard its sole blocker, or discard any outsider if it has none. The resulting 73-point code with 56 original roots is impossible.

Let $z$ count axes missing both signs. There are $36-17+z=19+z$ axes present in both signs. If $z=0$, every axis is represented, and the [full-axis theorem](KissingE6EighteenPairs.md) already excludes 18 or more original pairs. If $z\ge2$, at least 21 original pairs are present, contrary to the [21-integral-axis theorem](KissingSixTwentyOneIntegralAxes.md). Thus **$z=1$**: there are 20 paired axes and 16 weak axes, of which precisely one is missing both signs.

## Certificate on continuous outsider positions

The [standalone exact replay](verify-kissing-six-55-root-retention.js) reconstructs the [signed blocker-mask dictionary](KissingE6GlobalMaskCapacity.md). The mask cells cover all real outsiders, and two simultaneous outsiders cannot have the same mask. Incompatibility of two cells is asserted only after a chamber bound excludes every relative realization. Hence an 18-outsider configuration needs 18 distinct pairwise compatible cells, all with blockers supported on the 17 missing signs.

The 16 weak axes have **149,490** projective Weyl-group orbits. The replay generates the representatives with a $D_5$ stabilizer and independently checks the count with Burnside's formula, as in the [integral-core proof](KissingSixIntegralPairCore.md). Some orbits contain a $D_5$ equator with at most one weak axis, covered by the [38-of-40 theorem](KissingPartialD5D6Equators.md). Others admit a coloring of the entire possible site list by blockers, where geometrically compatible sites receive distinct signed roots; matching and Hall branching can also verify the injection subset by subset. Seventeen missing roots cannot receive 18 distinct assignments.

For the remaining large lists, choose the weak axis missing both signs and fix one other sign by global inversion. There are $16\cdot 2^{14}=262{,}144$ sign orientations per orbit before empty orientations are dropped. For each orientation:

1. Retain only the cells whose entire blocker mask is missing. Fewer than 18 eligible cells is already impossible.
2. Reject orientations with a missing sign supported fewer than twice. When needed, check whether its supporting cells actually contain a pair not already known to be incompatible.
3. Partition the cells into classes of pairwise incompatible cells. Fewer than 18 classes suffice. Otherwise, a recursive exclusion tests for a compatible 18-set: a clique selecting a cell from a class can contain no other cell of that class, and all later choices must be compatible with it. Reordering a fixed site set can reduce the search; the replay checks that each alternative order contains exactly the same cells.
4. A budget limit never certifies a case. If the signed routine does not close an orbit, the global Hall proof must close it or the replay aborts.

**Complete census.** Three disjoint replay runs covered all 149,490 unsigned orbits, with no unresolved case: 3 equatorial, 2,837 empty, 124,352 directly colored, 1,102 recolored, 21,094 settled by general matching/Hall branching, and 102 by the signed orientation routine. These 102 had 19,292,603 nonempty orientations: 13,639,893 with too few sites, 5,639,234 with insufficient signed support, 13,456 with an immediate coloring, and 20 handled by the final compatibility tests. Empty orientations have no eligible outsider placements.

**Replay.** Run `node verify-kissing-six-55-root-retention.js` for the whole census, or pass the start and end of a zero-based half-open orbit interval after the filename. For example the intervals `0 50000`, `50000 100000`, `100000 149490` partition the census; each run verifies its interval size and the full Burnside count. Node.js is the only dependency. This sign-sensitive test does **not** establish the corresponding statement for an arbitrary core of 20 paired axes.
