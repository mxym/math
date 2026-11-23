# A triple at a norm-18 root has all three inner products seven

Suppose the Conway graph has no norm-16 or norm-20 integral neutral fields, and no unit types (1,27) or (2,30). No symmetry or Seidel-rank assumption is needed. A seed is an actual positive root o with four specified independent neighbors Q. At most three oriented norm-18 markings have this seed. If three occur, their pairwise raw inner products are all seven, and together they give a true raw (4,44) field. Consequently
$$
  9N_{18}\le 110880+44G_{4,44}.
$$
Here N counts both orientations, and G counts the positive charge only.

**Preliminaries.** Use [the three-label theorem](panel-heights.md#the-three-label-exclusion-and-the-rank-38-contradiction) and its cited rooted distance bounds. The 9+9 supports are 4-regular bipartite. For two distinct markings at the seed there is no opposite-sign overlap (their difference is unit); their dot is seven or nine; and they share at most two of the six positive pair labels. The six labels are the respective second common neighbors of the pairs in Q. A label has exactly those two contacts in N(o) by the common-neighbor quota. Each marking uses at least four of the six labels (the four Q rows send twelve contacts to the other eight positive sites, each receiving at most two). For three markings their omitted subsets must be three pairwise disjoint two-sets partitioning the six labels: the pairwise intersection bound first forces every used subset to have size four, and complements of pairs to be disjoint. A fourth marking is impossible. In a triple, any two distinct pair labels occur together in at least one marking and so are nonadjacent.

**Dot-nine exclusion.** Write E_i={x,y} for the labels omitted by t_i, and d_v=(3I-A)e_v. For {i,j,k}={1,2,3}, consider the actual charge-two field
$$
  u_i=t_i-t_j-t_k+d_x+d_y.
$$
At x,y the neutral summand equals −2, and d_x+d_y has norm 50 since x,y are nonadjacent. Thus u_i has value +1 at both and cost
$$
48+2(t_j\cdot t_k-t_i\cdot t_j-t_i\cdot t_k).
$$
If exactly one pair has dot nine, choose an endpoint i of that pair. If three pairs have dot nine, choose any i. The resulting cost 30 is impossible: a raw (2,30) field is unit (a positive doubled entry translates down to charge one of cost at most 17 by subtracting d_v; a negative doubled entry translates up to charge three of cost at most 33, with a positive pivot in the equality case, contradicting sum −33), and that unit type is absent.

If there are exactly two nine pairs, choose their common endpoint i. The cost is now 26. This (2,26) field is signed-unit, with exactly two positives, x and y. The [positive-pair structure](u226-positive-pair.md) and its absence-of-(1,27) transfer imply it has subtype c=0: both common neighbors of x,y are zero, and every negative meeting neither positive is adjacent to exactly one of these two common zeros. (Equivalently, in the c=0 core each of the eight isolated negatives meets one of the two pure diagonal wings.) The site o is negative and misses x,y. If the parent pairs of x and y overlap, the shared parent q is itself a common neighbor, yet u_i(q)=1−2=−1, impossible. If the parent pairs are disjoint, no common neighbor of x and y lies in N(o), contradicting the isolated-negative property at o. This exhausts the possibilities.

**A true (4,44) field.** With all dots seven, put b=t_1+t_2+t_3+Σ_{q∈Q}d_q. The neutral sum has squared norm 96, the translation 116, and their inner product is −84. Thus the charge is four and cost 44; since the coordinate sum is −44, b equals −1 on exactly 44 sites and vanishes elsewhere. In particular b_o=−1. On N(o), the sum of the t_i has value −3 on Q and zero elsewhere. The negative neighbors of o in b are therefore exactly the four partners of Q in the seven disjoint edges of N(o). These recover Q uniquely from b and o. Thus any b accounts for at most 44 distinct triple seeds. Every oriented norm-18 marking has nine positive roots, each with its unique seed; there are 99·560=55,440 seeds. Even allowing two markings at every seed gives the asserted inequality.

**Rank-38 consequence, on the specific support contained in {N18,N24,U226}.** The [second norm-18 row](norm18-u226-graph-cap.md) under the same support, averaged over all maximal seven-extensions, implies
$$
 48N_{18}+12G_{2,26}\ge 2058\cdot344+10G_{4,44}.
$$
Indeed (4,44) has nonzero original discriminant norm (44−11·16/9) mod 7, so its eligible normalized count averages to its literal positive-charge graph count divided by 344, just like (2,26) and (0,18). Every omitted term on the right is nonnegative. The already established bound G_{2,26}≤4,158 now gives
$$
 2022N_{18}\ge44(2058\cdot344-12\cdot4158)-1108800=27845664.
$$
Equivalently before rounding N_{18}≥(44(2058·344−12·4158)−1,108,800)/2022; it is even by antipodality. Consequently N_{18}≥13,772, at least 13,068 seed triples occur, and at least 297 distinct true positive-charge (4,44) fields occur. The known same-oriented upper bound is 16,166, so this does not by itself exclude the support.

**Norm-22 multiplicity.** A [second count of the ordered triple differences](norm18-norm22-root-capacity.md) forces one actual oriented norm-22 field to occur at least 16 times across at most eleven roots. The same-root collisions have three possible intersection types. A contradictory upper bound on multiplicity has not yet been established.
