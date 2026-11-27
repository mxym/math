# Six-dimensional kissing with 56 retained E₆ roots

**Theorem.** Any six-dimensional kissing configuration containing **56 or more of the 72 signed roots** of a fixed E₆ has at most **72 points**. Thus a 73-point code, if it exists, overlaps every orthogonal copy of E₆ in at most 55 points. Every nonretained axis may lose one sign or both, and all outsider positions are arbitrary real vectors. This does not determine the unrestricted kissing number.

The [fifteen-omission theorem and proof](KissingSixFifteenArbitraryOmissions.md) handle overlaps of 57 or more. Only m=16 omissions need be added. Maximize root overlap among such 73-point candidates for the same fixed E₆. Every missing root must have two distinct, mutually kissing-compatible outsider blockers; otherwise it can be restored. If there is no fully missing axis the [full-axis pair bound](KissingE6EighteenPairs.md) already excludes 36−16=20 or more pairs.

For a fully missing signed pair ±r choose two outsider blockers of each sign. On each side let P be their combined mask; mark its pole. Let a,o count the *other* roots in P with inner product 1 and 0 with the pole. The rooted charge w=2a+o is at least 10 by the previous theorem. The two charges sum to at most 2(m−2)=28. In particular each is at most 18; orient the axis so the lower charge is at the positive pole.

The [standalone exact replay](verify-kissing-e6-sixteen-arbitrary-omissions.js) extends the previous catalogue, requiring only Node.js. It enumerates all pairs of signed sphere-cell masks through the same marked root up to charge 18 and drops only pairs with rigorous chamber angular exclusion. This gives **1,610 orbits of possible unions** and **1,690,215 signed unions** over a fixed marked root. For each eligible pair of union orbits, enumerate relative positions with the root stabilizer, retaining unions of both sides of size at most 16. Complete to size 16 with arbitrary additional signed roots.

Three inexpensive exclusions precede the final clique search:

* Apply the minimum rooted charge 10 at **every** missing signed root, not merely at the chosen opposite pair. Even its full available local neighborhood inside the deletion set must meet this bound.
* Use the [D₅](KissingPartialD5D6Equators.md) and [A₅](KissingE6PunctureHull.md) equator bounds for every such E₆ section. For A₅ with exactly two missing signs only nonpositive mutual inner product is excluded.
* For each missing signed root require not just two formally possible masks, but at least one pair through it that passes the chamber compatibility test. Finally require **17** pairwise compatible distinct masks by exact colored clique backtracking.

| Result at m=16 | Count |
|---|---:|
| Base-union templates explored after stabilizer reduction | 69,470 |
| Completed deletion-set checks | 1,874,437 |
| Local charge, section or raw mask-count exclusions | 1,088,470 |
| No eligible pair at a missing signed root | 687,814 |
| No 17-clique | 98,153 |
| Surviving deletion sets | **0** |

The duplicate-work cache is periodically cleared to bound memory: the work totals are not minimal symmetry-orbit counts. The largest tested candidate mask dictionary before the last two filters has 624 entries. All filters are necessary conditions. The finite angular test uses the exact rational outer bounds of the [E₆ blocker geometry](KissingE6GlobalMaskCapacity.md), not a sample of continuous positions. Together with the preceding result this proves the claim.
