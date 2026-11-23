# Cubic ten-site supports consume extra original charge-one norm-79 marks

This is a rank-free graph-to-shell inequality, not a Conway 99 resolution. Let A be the adjacency matrix of a hypothetical graph. Write C_old(a,t) for the *zero original seven-class* population with positive charge a and raw squared coordinate norm t on the old −4 side, and write x_j^+ for the scaled complementary dual scalar coefficients of the [+3 rank-56 construction](../complementary-rank56/README.md). Let A_10 be the number of actual vertex subsets C of size ten inducing a cubic graph, without orientation. These ten-site supports are connected because each nonempty induced cubic component has at least six vertices.

Put E_10=C_old(1,79)−29,360,331. Then, writing D_10 for the number of unordered pairs of anticomplete cubic ten-site supports,

    A_10 ≤ 3 E_10,
    x_10^+ ≥ 2 D_10 ≥ max(0, 2 A_10−2 E_10, 4 A_10−6 E_10).

The first term x_10^+ counts many other populations besides these literal pairs. In particular these inequalities do not assume that A_10 or D_10 is nonzero.

## Their old marks are not the small-support marks

Use [the old marks](../maximal-marked-lattice/README.md) with Gram 3I−A+J/9, and write w(c)=Σ_i c_i u_i. For a cubic ten-set C, w(1_C) has squared norm 100/9, input mass ten, and hence normalized charge +1 and raw cost t=(7·100+11)/9=79. This is a zero original seven-class mark: w(1_C)−u_0 is a sum of differences u_i−u_0 plus 9u_0 in the original integral lattice.

The mandatory reference populations here come from c=1_P−1_Q with disjoint P,Q, sum c=1 and at most five sites. To classify a collision suppose w(1_C)=w(c). Then k=1_C−c has mass nine and (A−3I)k=1. Each negative coordinate of k is −1, and there are at most three. A negative site requires neighbour sum −2, so if there is any negative site there are exactly three, all mutually adjacent and anticomplete to the positive support. As all three negative sites are precisely P in that case, P is a triangle and there is no P−Q edge. The five-site cost t=79 requires e(P)+e(Q)−e(P,Q)=2 by the short-mark cost formula t=21·5−14(e(P)+e(Q)−e(P,Q))+2. But the triangle already gives at least three. Thus there are no negative sites of k in a collision.

If k is nonnegative then it has no coefficient at least two: every neighbour of any such coefficient would have to be nonzero because a zero has neighbour sum one, contrary to the total mass nine. Thus k is a nine-set indicator, induces degree four, and has all outside degrees to it equal to one. By the [ordinary unique rook-grid argument](../complementary-rank56/README.md#2-dual-label-dictionary) it is a grid G. It follows that C=(G∖Q)∪P, with Q inside G and P outside. If |P|≤2, each p∈P has at most one neighbour in G∖Q and at most one in P, contrary to cubicity. If |P|=3, cubicity forces P to be a triangle, and each p already has its one G neighbour in G∖Q, so there are no P−Q edges. Again the five-site cost demands the impossible e(P)+e(Q)=2. This proves disjointness in all cases.

## The exact earlier population and class bound

There are precisely 100,485 signed three-site inputs and 29,259,846 signed five-site inputs of this cost and charge. Their sum is 29,360,331. The full induced census [already used for old mandatory marks](../rank-34-short-support/count_marks.py) applies unchanged: for input size n and positive count (n+1)/2, keep only masks with t=21n−14(e(P)+e(Q)−e(P,Q))+2=79 and divide by the within-sign factorials. A short standalone-replay patch is described below. The inputs give distinct marks, since equal images would have difference in the +3 neutral space and positive and negative masses each at most five, excluded by [the complementary minimum-mass argument](../complementary-rank56/tail-budget.md). Both charge-one input masses here are exactly one; no use of a congruence alone as a collision test is made.

For equal-size cubic supports C,D, equality of w(1_C), w(1_D) is exactly equality of their normalized shadows. By [the cubic shadow theorem](normalized-cubic-shadow-classes.md), each such class consists of disjoint anticomplete cubic supports, with total size at most 36 if there is more than one. Therefore each ten-site class has size at most three and there are at most E_10 classes. Interpreting an unordered pair as the oriented signed neutral field 1_C−1_D gives 2 D_10 actual distinct unit norm-20 fields on the complementary side, hence x_10^+≥2 D_10. If m is the number of supports in a class, 0≤m≤3 and m(m−1)≥0, 2m−2, 4m−6. Pad to E_10 classes if needed and sum to get the asserted inequalities.

## Replaying the reference count

The [standalone standard-library replay](cubic_ten_old_mark_count.py) reuses the exact degree-0/1/2 deletion and equal-vertex quotient rules of the linked earlier census. It only changes the final aggregation to count the literal signed inputs of sizes three and five. Run `python3 cubic_ten_old_mark_count.py`: the two entries for t=79 are 100485 and 29259846, and the control t=51 entries are 49896 and 55440. No reconstruction of the 99-site graph is used.
