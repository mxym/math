# A calibrating square in every non-prism triangle-wing component

Fix a triangle, its induced cubic 36-site wing graph D and the 60 far vertices X. A **calibrating wedge** is a center q in D and two of its D-neighbors i,k that are nonadjacent and that have no other common neighbor in D. The three D-neighbors of q belong to three different physical wings, so i,k have no common vertex in the original triangle. They are nonadjacent and already have q as a common neighbor; μ=2 forces a **unique** y in X meeting both. This y does not meet q, since then either qi or qk or qy would have incompatible common-neighbor counts: more directly q and y already share both i and k, hence cannot be adjacent by λ=1. By μ=2 again, **every far neighbor of q is nonadjacent to y**.

**Rank-independent lemma.** Every component other than a triangular prism contains a calibrating wedge. To prove this, suppose a component has none. Then every two-edge walk with distinct endpoints closes to a triangle or four-cycle. Suppose first it has a triangle xyz. Each vertex has exactly one neighbor outside the triangle, denoted a,b,c respectively. These are distinct and none can be adjacent to two triangle sites, since an edge of the triangle is already capped. The nonadjacent pair a,y needs a second component common neighbor after x; among the neighbors x,z,b of y the only possible one is b. Thus a is adjacent to b; similarly a is adjacent to c and b to c. The six vertices are saturated in the cubic component, which is a prism.

Otherwise the component is triangle-free. At q with neighbors a,b,c each pair has a second common neighbor, written x_ab, x_ac, x_bc. The three new vertices are distinct from q,a,b,c by simplicity and triangle-freeness, and distinct from one another: a coincidence would give q and that vertex three common neighbors. Each x_ab has exactly one unused neighbor after a and b. At a, the nonadjacent pair x_ab,x_ac must have a second component common neighbor after a. It is not b (q and x_ac would then share a,b,c), nor c for the same reason; consequently it is the unused neighbor of both x_ab and x_ac. Similarly at b and c all three x's have the same unused neighbor. It is not q, since q already has neighbors a,b,c; not a,b,c by simplicity or the previous common-neighbor bound; not one of the x's, since it is adjacent to all three. These eight vertices now have their full three neighbors and form the cube. But every triangle-wing component has size divisible by six, by [the three matchings and within-wing mates](triangle-complement.md). A cube is impossible, proving the lemma. Conversely every wedge in a prism closes inside a triangle or square; this statement does not rule out prism components.

## The all-unit split with two flat 12-components at rank 36

F denotes the unique allowed flat seven-unit 12-type: the three internal mate matchings are (01)(23), (02)(13), (03)(12), and the cross-return is the identity. At mod-seven Seidel rank 36 no triangle has wing split **F+F+U** for any of the eleven seven-unit 12-types U. This is independent of the [known triangle spread from a saturated line](covered-spread.md); no spread classification or graph symmetry is assumed. The eleven unordered multisets here are disjoint from the [two hexagonal-prism-wing exclusions](hhu-cap-boundary.md).

Orient the U by a global naming of the physical wings. Both F have one ordered template up to site names, checked by minimizing the adjacency code under the 24 choices of first-wing labels for each of six wing permutations. In each anchored U choose one calibrating wedge. In a 12+12+12 split every far word has two contacts per component and two per physical wing. Its calibrated y therefore has U contacts exactly i,k. At the ten far neighbors of q, the exact multiplicity of each U tag (q,b) is
`c_qb=2−D_qb−(D²)_qb−[q,b in same wing]`.
An actual x with this tag has exactly `1−D_qb` neighbors among the same ten: q,x form an edge; b is the only possible known common neighbor in D, and x has no triangle-root contact. Moreover for every partner site a in either F, the ten words must collectively contain a exactly `2−[q,a in the same wing]` times, since q,a have no neighbors in common in D. The ten-star search enforces these integer upper bounds; because its ten words have exactly 20 contacts in each partner, these upper bounds are also exact margins.

The [two-dimensional residual calibration and literal pair-capacity tests](hhu-cap-boundary.md) apply unchanged. Enumerate all lifts of y up to residual isometry, explicitly keeping both zero and nonzero isotropic when applicable. Calibrate ten words z by `ρ_z·ρ_y=4−g_zy`, since the wedge makes all ten known nonneighbors of y. In particular a zero pivot enforces the full equality g_zy=4. Search one word/lift per ten required tag occurrences jointly, requiring their individual matching degrees, the partner-site margins and exact forced adjacency; repeated tags are ordered by distinct raw words. Relabel the two F independently within physical wings and exchange them to gauge the source. All actual choices are included, without requiring the other 49 far vertices or any automorphism of the 99-graph. The numerical rows below report only counts of exact integer witnesses *tested*, with none completing the ten-star, not graphs:

|U (script order)|Raw seeds|Representatives|Tree calls|Maximum|
|---:|---:|---:|---:|---:|
|0|384|15|53403|4129|
|1|384|15|57007|5653|
|2|384|15|63300|6263|
|3|384|15|49549|3995|
|4|384|15|44395|3881|
|5|384|15|63014|5409|
|6|384|15|58460|5975|
|7|544|21|63199|3832|
|8|384|15|49416|3979|
|9|416|16|51520|4089|
|10|448|19|56728|4699|

The [standalone NumPy replay](ffu_calibrating_wedge.py) uses exact finite-field, bitset and integer arithmetic. Total: 176 seeds after the prescribed local gauges and 609,991 recursive calls in about 31 seconds. This excludes eleven specified multisets, not the whole rank or even all unit-only splits.
