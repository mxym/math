# A nonstar triple yields an actual unit (1,27) mark

At a positive-root norm-18 seed, assume the three markings t1,t2,t3 share three positive pair labels X and have pairwise dot eight. A star X is impossible by the [fourth-marking proof](norm18-dot8-star.md). If X is not a star, the graph has an actual **unit (1,27)** mark. This implication for the triple itself requires no rank or missing-shell assumption.

## The spare pair slot

Use root o and negative parents Q. Pairwise differences have squared norm 20 and are unit, so opposite sign conflicts are impossible. Each of the three pairs of markings already coincides on the eight sites o, Q and X, with precisely four positive and four negative sites. Dot eight thus shows all other supports are pairwise disjoint: five private positive and five private negative sites per marking. Each marking uses at least a fourth one of the six pair labels at the root. No two can use the same extra label, so the other three labels belong to positive private sites, one per marking. In particular every non-root site seeing two members of Q is already in the union.

Identify X with its three parent pairs on Q. At any x∈X exactly two common negative sites touch x (its parent pair, since o and x cannot have more than two common neighbors), so x has exactly two neighbors among each private negative five-set. The six incidences of X with each such five-set force at least one common-neighbor *pair slot* of X used in that set. There are six slots for all pairs of X (X is independent), of which one is already used whenever two of the three parent pairs meet. For a nonstar these pairs form either a triangle or a four-vertex path: respectively three or two intersecting pairs. The available slots outside Q number three or four, and the three distinct private negative sets use at least three. Thus at most one of the intersecting pairs has its residual slot unoccupied by the union. There are at least two intersecting pairs, so pick x,x′ at common parent p whose two common neighbors are both in the union. The third label in X misses p, by the nonstar assumption.

## The transfer is unit, not just raw

Let Y=Q minus p, and set
```
b=t1+t2+t3 − d_x−d_x′ + sum_(y∈Y)d_y,    d_i=(3I−A)e_i.
```
Its charge is 1. For z=1_Y−1_{x,x′}, one has sum z=1, z²=5, zᵗAz=−4 because each selected x touches exactly one member of Y. Hence (Dz)²=7(15+4)+2=135. Its dot with each t_i is 7 z·t_i=−35. The three markings sum to cost 102, giving b²=102+135−210=27.

On the three common positive labels b has values −1,−1,+1: the third has both parents in Y. At o the value is 0; at p it is −1. A vertex q∈Y has value 1 if it parents x or x′, zero otherwise, since x,x′ have only p in common among their parent pairs. Outside the eight common sites, b equals the signed private contribution (0,1 or −1) plus the number of neighbors in {x,x′} minus the number in Y. A private positive never touches x,x′ and at most two Y. A private negative never touches Y and at most two of x,x′. A site outside the union sees at most one Y (all six pair labels lie in the union) and at most one of x,x′ (the two common neighbors are in the union). Thus every value of b is 0 or ±1.

Under N16=U127=0 this proves that **every triple among the six labels is contained in at most two seed markings**, since two markings containing such a triple have dot eight by the panel theorem. Distinct markings also determine distinct shrunk four-subsets, as in [the star count](norm18-dot8-star.md). The only further step in a population cap is the finite four-subset packing count over the 2,048 seed supercharts. No absence of norm 20 or positive-charge (2,28) is used.

## The resulting graph-wide upper bound

The [standalone exact checker](norm18_dot8_nonstar.py) uses every combination of the four parent-matching choices and three disjoint-pair flags, as in the original star proof. For a fixed chart it branches only over the at most fifteen independent four-subsets of its six labels. Select or omit each four-subset, maintaining the at-most-two demand on each of the twenty three-subsets. It verifies the local capacity bound **3m+4j+4k≤28** across all 2,048 charts; the largest possible m at each pair (j,k) is also checked.

Summing over the same true root seeds, using the previously proved prism incidence counts and P≤851, gives
```
27 N18 ≤ 28·55440 − 32(99·84−6P) − 4(99·336+6P)
       ≤ 1,296,120.
```
Thus **N18≤48,004** in the actual graph when N16=U127=0, at any rank and with no assumption on the other ten selected types. This is the oriented norm-18 count, not the number of support subsets. The argument does not exclude an entire rank.
