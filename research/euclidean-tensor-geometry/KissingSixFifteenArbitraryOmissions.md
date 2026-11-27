# Fifty-seven retained E₆ roots force the six-dimensional kissing bound

**Theorem.** If a six-dimensional kissing configuration contains at least **57 of the 72 signed points of a fixed E₆ root system**, then its total size is at most **72**. Equivalently, a hypothetical 73-point code must omit at least 16 points from *every* orthogonal copy of E₆. There is no requirement to retain an orientation on each original root line, and all other points range over the continuous sphere. The threshold 57 is sufficient, not claimed optimal. This is not an unrestricted kissing-number upper bound.

Use squared norm two, so distinct code points have dot product at most one. A signed root is a blocker of an outsider x when x·r>1. We use the [complete E₆ mask catalogue](KissingE6ExactBlockerSpectrum.md), [one-point capacity of every mask](KissingE6GlobalMaskCapacity.md), and the conservative pairwise angular incompatibility test described in [the previous chamber proof](KissingE6EighteenPairs.md). These facts are local and do not require that all axes be represented. [Standalone replay](verify-kissing-e6-fifteen-arbitrary-omissions.js), no dependencies beyond Node.js.

## Choose the best root overlap

From a counterexample one can keep 73 points while retaining all of its original roots. Choose a 73-point counterexample maximizing the number of retained roots, relative to the same fixed E₆. Write M for its m≤15 omissions. There are exactly m+1 outsiders and their signed blocker masks are distinct subsets of M. Each r∈M is blocked by at least two outsiders: otherwise add r and drop its one blocker (or an arbitrary outsider if there is none), increasing the overlap without breaking the kissing bound.

If M contains no opposite pair then all 36 root axes are represented, with 36−m≥21 fully paired axes. This contradicts the [complete-axis bound of at most 17 pairs](KissingE6EighteenPairs.md). So fix an opposite pair r,−r∈M. The remaining argument treats this new case; it allows arbitrarily many additional opposite pairs.

## Charge the two sides of a missing line

Two outsiders blocking r must coexist in the kissing code. Let P be the union of their masks. Apart from r, every root s∈P has r·s either 1 (acute) or 0 (orthogonal): two roots both within an open 60° cap cannot have angular separation at least 120°. Set a(P)=number of acute roots, o(P)=number of orthogonal roots, w(P)=2a(P)+o(P). Define N likewise for a pair blocking −r, using that pole as reference. The two acute pools are disjoint and can never mix with either orthogonal pool. Hence
`2(m−2) ≥ w(P)+w(N).`

The exact chamber test finds **no** compatible rooted pair of distinct masks with weight below **10**. This immediately rules out m≤11. For m≤15 any needed rooted pair therefore has weight at most 2(15−2)−10=16. Here are the finite search details:

1. Enumerate all signed blocker orbits. Fix the first mask to an orbit representative and let r vary through its members. For the second mask enumerate the group translates of each realizable mask, deduplicating signed masks. Discard identical masks, masks not containing r, and those exceeding the budget. The existing rational outer chamber test only discards pairs certified to have inner product strictly above one for all realizations. At weight at most 16 there are 392 symmetry orbits of surviving **unions** around a fixed root, with 355,455 distinct signed unions. True coexistent pairs are included; we need not certify that all the retained pairs can coexist.
2. Orient the missing axis so the lower-weight union is at the positive pole and transport that union to its orbit representative at a fixed r. Enumerate the signed negative unions of every eligible weight. Retain P∪N only if its size is at most m; the stabilizer of the positive union within the 1,440 automorphisms fixing r identifies equivalent negatives. Extend each base by all subsets of the remaining signed roots to exactly m omissions. This never assumes signs on uncovered axes.
3. A deletion set leaving at least 38 roots in any D₅ equator is impossible by the [two-puncture equator theorem](KissingPartialD5D6Equators.md). The verifier checks all 27 translates of one such section, and also the [one-hole and nonacute two-hole A₅ bounds](KissingE6PunctureHull.md) on the 36 sections perpendicular to a root axis. Otherwise generate all candidate outsider masks contained in M. Reject if fewer than m+1 exist, or if some omitted root is covered fewer than twice. Finally require a clique of m+1 distinct masks whose pairs survive the angular test. A proper coloring gives a rigorous clique upper bound in the exact backtracking search.

| m | opposite-union base representatives | completed sets tested¹ | section or routine count exclusion | missing root blocked fewer than twice | no required clique | surviving |
|---:|---:|---:|---:|---:|---:|---:|
| 12 | 1 | 1 | 1 | 0 | 0 | 0 |
| 13 | 20 | 76 | 28 | 23 | 25 | 0 |
| 14 | 434 | 2,993 | 657 | 1,692 | 644 | 0 |
| 15 | 6,147 | 79,718 | 16,483 | 52,613 | 10,622 | 0 |

¹ These are deduplicated within the enumerated representatives, not a count of all labeled subsets or a claim of a minimal orbit transversal. For m=15 the largest remaining candidate dictionary before the degree and clique filters has 357 masks. Discarded geometry is one-sided throughout: false positives could make the search inconclusive, but none survives. This proves the threshold.
