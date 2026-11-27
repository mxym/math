# The energy-twelve E6 band and a common projection of at least √48

Let X be a hypothetical 73-point six-dimensional kissing configuration representing all 36 axes of a fixed E₆ (root squared norm two). For any transversal T that selects one actually present signed root on each axis, let S(T) be its vector sum. Then

* every squared sum ‖S(T)‖² is at least **56**;
* the convex hull of all such sums has squared distance at least **48** from the origin; in particular there is one unit n with n·S(T)≥√48 simultaneously for every T.

The [previous exclusion](KissingE6BiasedTransversals.md) handles ‖S(T)/2‖²≤10. Here is the immediate next band, using the same signed orientation and conservative chamber compatibility certificates. Let λ be the dominant-plane representative of −S(T)/2. In the two possible stabilizer classes at ‖λ‖²=12, the numbers of complete orientations are:

|Dominant simple products|Raw orientations at that dominant sum|Orientation orbits|
|:---|--:|--:|
|(0,0,0,0,3,0)|2,386,560|1,243|
|(0,1,0,1,0,0)|2,392,624|50,313|

The [standalone exact replay](verify-kissing-e6-energy-twelve.js) regenerates all 51,556 classes by meet-in-the-middle matching on 18+18 root axes, using the Weyl stabilizer and the diagram involution when applicable. For an orientation U=−T, each outsider has a distinct blocker mask entirely in U. There must be k≥20 outsiders, whose combined blockers consume at most k−1 signs. Conservative pairwise compatibility and proper-color pruning leave **554** orientation classes with a possible clique of size at least 20. In each, the replay computes its relaxed maximum M and, for each k=20,…,M, does a fresh exact clique search requiring the blocker union to have size at most k−1. None passes. Thus no squared half-sum up to 12 occurs. The half-sum lies in the even E₆ root lattice, so the next possible value is at least 14 and ‖S(T)‖²≥56.

For the convex hull, write the sums as a translate of all sign choices on the paired E₆ root directions. At any point z in that zonotope the [sharp E₆ rounding theorem](ReflectionZonotopeRounding.md) gives a distribution on allowed sign sums with mean z and E‖S−z‖²≤8. Therefore 56≤E‖S‖²≤‖z‖²+8. At the nearest point z to zero, the normal n=z/‖z‖ has n·S≥‖z‖ for all S in the zonotope.

This is a necessary asymmetry of the hypothetical full-axis branch, not a solution of the unrestricted kissing number.