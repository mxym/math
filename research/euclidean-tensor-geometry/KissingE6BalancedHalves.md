# A balanced half of E6 cannot belong to a 73-point kissing code

**Theorem.** Let T contain one signed root from each of the 36 antipodal root pairs of an E6 system in R⁶. Suppose its vector sum is zero. Any kissing configuration containing T has at most 72 points. More precisely, its points outside the original E6 system number at most 12, and can be injected into the set of unused roots of E6 so that each outsider is matched to an original root it blocks. Normalize all squared lengths to two and the maximum allowed pairwise product to one.

The assumption concerns the existence of such a transversal *within the configuration*, not the sum of the whole code. This result is independent of the earlier bounds on true antipodal pairs. [Bannai–Zhao–Zhu–Zhu–Zhu](https://arxiv.org/abs/1710.10619) studied whether a zero-sum half exists for fixed antipodal designs. Here we bound arbitrary continuous additions to every zero-sum E6 half, without assuming an antipodal extension. Full E6 gives equality at 72; the upper bound 12 for nonroots is not claimed sharp.

## Enumerating every balanced half

Fix positive roots P (one from each axis), and write ρ=ΣP/2 in the simple-root coordinate basis. The selected signs of a half are specified by a subset F of P moved to its negatives. Its sum is zero exactly when ΣF=ρ. Split the 36 roots into two groups of 18, enumerate all 2¹⁸ subsets on each side, and join complementary sums. Six-coordinate group sums are encoded in base 64; each coordinate of ΣP is less than 64 and all positive-root coefficients are nonnegative. There are exactly 13,697,920 such signings. Under the six simple reflections and the Dynkin diagram involution they fall into 156 orbits. The enumeration applies the seven generators directly to a 36-bit choice, including sign flips, and removes one orbit at a time. The opposite U=−T is balanced as well; use it as the set of original roots that are not already forbidden as blockers by T.

## One legal color per outsider

For a nonroot x let B(x)={r : x·r>1}. The [local mask theorem](KissingE6GlobalMaskCapacity.md) gives 5≤|B(x)|≤16 and at most one kissing outsider for any fixed signed mask. All blockers belong to U. As in the [signed-mask census](KissingE6NineteenPairs.md), enumerate every candidate mask within U by generating signed upward ideals; keep the unrealizable second five-ideal as an intermediate seed so that larger ideals are not accidentally omitted. For distinct masks C,D certify incompatibility only when every relative chamber puts every pair of actual sphere points at product >1. The rational chamber enclosures and equality rules are the same as in the [seven-mask lemma](KissingE6SevenBlockers.md). Unresolved pairs are treated as possibly compatible, an outer relaxation.

In each of the 156 cases, an explicit greedy construction assigns each candidate mask C a color r∈C, with all masks of the same color pairwise certified incompatible. The [standalone verifier](verify-kissing-e6-balanced-halves.js) reconstructs and checks every list-coloring, testing membership, complete coverage, and pairwise incompatibility in each class. Any mutually kissing outsiders therefore have **distinct colors**. All these colors are unused original roots: the color r∈B(x) cannot belong to the code. Hence all points of the code can be injected into the original 72 signed roots (retain each original point and send each outsider to its color). This proves the bound.

Independently, exact branching with proper-color bounds finds maximum clique size at most 12 in every one of these relaxed compatibility graphs. The graph maxima and counts of signing orbits are:

| maximum | 0 | 3 | 4 | 5 | 6 | 7 | 8 | 9 | 12 |
|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|
| orbits | 2 | 1 | 9 | 23 | 53 | 39 | 10 | 15 | 4 |

These are maxima of necessary combinatorial conditions, not realizability statements. Reproduce with `node verify-kissing-e6-balanced-halves.js`.
