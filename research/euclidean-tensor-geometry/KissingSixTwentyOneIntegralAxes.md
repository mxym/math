# Twenty-one paired integral axes suffice for the six-dimensional kissing bound

Let $C$ be a six-dimensional kissing configuration. If it contains **21 antipodal pairs** whose axes have pairwise acute angles $60^\circ$ or $90^\circ$, then **$|C|\le72$**. There is no condition on the other points. The bound 72 is attained by $E_6$; 21 is a sufficient size for the core, not asserted optimal. This improves the [22-pair core theorem](KissingSixIntegralPairCore.md). It does not identify the unrestricted six-dimensional kissing number. See the distinct [angle-free 19-point energy bound](KissingNineteenPointEnergy.md) when no integral angles are assumed.

Normalize squared lengths to two, so different code points have inner product at most one. The acute-angle condition means the absolute scalar products between different selected lines are zero or one.

## Reduction to four root systems

The selected representatives generate an even integral lattice in their span. In fact, a basis chosen among the representatives has an integral nonsingular Gram matrix; its inverse bounds the coordinate denominators of every generator. Its norm-two vectors form a simply-laced root system because reflection in any such vector preserves the lattice. By the [ADE classification](https://ocw.mit.edu/courses/18-745-lie-groups-and-lie-algebras-i-fall-2020/mit18_745_f20_lec_full.pdf), the only rank-at-most-six possibilities with at least 21 axes are $E_6,D_6,A_6,D_5+A_1$.

The last two have exactly 21 axes, hence are present in both signs. A full $D_5$ equator suffices by the [equatorial theorem](KissingPartialD5D6Equators.md). For $A_6$ use the roots $e_i-e_j$ in the zero-sum hyperplane of seven coordinates. Any extra point would have coordinate range at most one. If $t,u$ are its minimum and maximum, summing $(x_i-t)(u-x_i)\ge0$ gives $\sum_i x_i^2\le-7tu\le7(u-t)^2/4\le7/4$, contradicting its squared length two.

## The exceptional frame

Choose exactly 21 paired $E_6$ axes; the other 15 axes are called weak, whether or not extra original signs actually occur there. An outsider is any point not among the 72 original signed roots. Its blocker mask consists of original roots with inner product greater than one against it. Every blocker must be absent, and all blockers lie on weak axes. The [continuous mask theorem](KissingE6GlobalMaskCapacity.md) gives the angular cells and proves that no two simultaneous outsiders can share a mask.

The [exact $E_6$ replay](verify-kissing-six-21-integral-e6.js) reconstructs 357,444 conservative signed sites. Two sites are marked incompatible only when their simultaneous realization by kissing points has been geometrically excluded over all relative Weyl placements. The procedure of the [22-pair proof](KissingSixIntegralPairCore.md) tries to assign each site one of its blockers, allowing equal assignments only for incompatible sites. This gives a simultaneous injection from all actual outsiders to missing original roots. When a universal coloring is unnecessary or unavailable the replay checks Hall's condition on compatible subsets by matching and branching. A $D_5$ equator with at most one weak axis is already covered by the equatorial theorem.

The projective-Weyl orbit census of the 15 weak axes is independently checked by Burnside. All **114,666** orbits are accounted for:

| Proof used | Orbits |
|---|---:|
| Near-complete equator | 9 |
| Empty outsider list | 6,385 |
| Direct list coloring | 82,918 |
| Recoloring | 161 |
| Matching and Hall branching | 25,190 |
| Supplied list colorings | 3 |

For each supplied coloring the replay checks that the list length is correct, every color belongs to the site's own blocker mask, and every equal-color pair is incompatible. A SAT solver was used to propose these three lists, but is not required or trusted for verification. Thus the number of outsiders cannot exceed the number of missing roots.

## The classical frame

Choose the 21 prescribed paired axes among the 30 lines $e_i\pm e_j$; let $W$ be the nine weak axes. Every sphere point other than the 42 prescribed roots lies in the box $[-3/2,3/2]^6$ with $|r\cdot x|\le1$ on every prescribed axis (the box also follows directly from $\|x\|=\sqrt2$).

The [exact $D_6$ replay](verify-kissing-six-21-integral-d6.js) enumerates all **1,306** weak-axis orbits under signed coordinate permutations. Seven have a $D_5$ equator with at most one weak axis. For the other **1,299** the data give at most 15 nonzero integer directions $h$. The verification clips the above polytope by the slabs
\[
 |h\cdot x|\le \lceil4096\sqrt{3(h\cdot h)/2}\rceil/4096 .
\]
Every vertex remaining after clipping has squared norm strictly less than two. Therefore every admissible sphere point belongs to an **open** cap of radius $30^\circ$ about some $h$ or $-h$. A cap cannot contain two kissing points, even at equality in the required $60^\circ$ separation, so there are at most $42+2\cdot15=72$ points. The exact starting half-grid, active-facet rank checks and integer edge clipping are justified in the 22-pair proof. This certifies the whole continuous sphere section, not merely the samples used to discover directions.

**Replay:** run the two linked JavaScript files with Node.js; neither uses network access, nonstandard packages, or an external optimization solver. Each aborts on a missing or unverified case.
