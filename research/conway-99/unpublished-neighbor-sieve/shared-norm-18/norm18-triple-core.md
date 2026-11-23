# A 38-site obstruction at a shared norm-18 root

Suppose a Conway graph has no neutral norm 16 or 20 and no signed-unit types (1,27), (2,30), or (3,37). There is no root with three norm-18 markings sharing its four negative neighbors. Consequently, **N18 ≤ 12,320**, where the two orientations of a neutral field are counted separately. In particular **rank 38 is impossible on any selected support contained in {018,024,125,226,228}**. Nothing here excludes rank 38 without the support assumption.

## The actual core

Use the previously proved [three-marking theorem](rooted-norm18-triples.md), which needs only the first four exclusions. If there are three markings at a common positive root o with four independent neighbors Q, call them t_i (i=1,2,3). Each is signed-unit on a 4-regular bipartite support (9 positive and 9 negative); each pair has scalar product 7, no opposite-sign intersection, and coincides in sign at exactly seven sites. The six actual pair-centers are the second common neighbors of the six pairs from Q. They are all distinct and not adjacent to o; each meets exactly its two named parents in Q, since a third would give three common neighbors with o. Each t_i uses four centers. Its two omitted centers form a pair L_i, and the three L_i partition the six. Any two distinct centers occur together in some positive side and so are not adjacent.

For a pair t_i,t_j the seven already shared sites are o, the two centers in the remaining L_k, and Q. Therefore the rest of the supports are private: four positive leaves P_i, five negative sites N_i. The whole core has 1+4+6+12+15=38 sites. The four parent rows in Q together use twelve contacts besides o with the other eight positives of t_i; four centers consume eight contacts, hence the four leaves take one apiece (no further site can touch two parents). The number of P_i leaves at a given q equals its multiplicity among the four endpoints of the two parent pairs indexed by L_i.

The two signs of the difference t_i−t_j independently induce empty graphs. Indeed the difference is a signed-unit neutral norm-22 field. At two adjacent positive sites x,y its sum with −d_x−d_y has charge −2 and cost 22+36−28=30; a negative pair is treated by negation. All raw (2,30) fields are unit by the pivot argument in the [three-marking theorem](rooted-norm18-triples.md); this unit type is absent. In particular N_i cannot meet a P_j for j≠i or a center in L_i. Nothing connects o or Q to N_i, by sign independence in t_i and the four negative neighbors already at o.

For x in L_i, the t_j,t_k support laws give two neighbors in Q, two in N_j, and two in N_k. Its t_i-balance, with no remaining possible positive source except P_i, gives exactly two leaf neighbors there. Each leaf p in P_i has one neighbor in Q and three in N_i. For j≠i, balance at p in t_j allows only one positive neighbor, since the only negative neighbor in t_j is its parent q. The two L_i together send four contacts into P_i; hence each leaf receives exactly one, and there are no positive-leaf edges in any two groups. The two leaves attached to the same center have distinct q parents: each has three neighbors among five N_i so they have a common N_i neighbor and the center already. A common q would be a third witness. These rules specify **all** edges among o,Q, the six L centers and the twelve leaves, not just a chosen subgraph.

Now for L_i={x,y} use the actual field u_i=t_i−t_j−t_k+d_x+d_y. It has charge 2 and squared norm 34 by the earlier cost formula at three dot products seven. If an **outside** vertex v is a common neighbor of x and y, all t fields vanish there and u_i(v)=−2. Then b=u_i+d_v has charge 3 and squared norm 34+23+2(−14+4)=37. Every raw (3,37) is signed-unit: subtracting d at a positive doubled site gives cost at most 20 below the charge-2 sum bound 22; adding d at a negative doubled site gives charge 4 and cost at most 44, with equality requiring all entries nonpositive but leaving a positive pivot. Thus U337=0 implies both common neighbors of each omitted center pair lie in the 38-site core.

## Exact 34-chart check

Run `python norm18_triple_core.py` (Python 3.10+, NumPy; tested with 2.3.5). Supply zero-based chart IDs to replay individual cases. Both the [source](norm18_triple_core.py) and [per-chart counts](norm18-triple-core-transcript.txt) are included.

1. Label Q by 0..3. Split its six edges into three unordered pairs, giving 15 possibilities. For every omitted pair, assign the four parent slots of its four leaves to the two actual centers, preserving the known parent multiset, requiring distinct parents at each center and treating its two leaves as unordered. This gives 424 diagrams. A diagram is fully encoded by its unordered triple of pairs of records (center's parent pair, its leaves' parent pair). Taking the lexicographic minimum over the 24 relabelings of Q gives 34 diagrams; this is only a labeling quotient, not graph symmetry.
2. A site of N_i contacts four of eight possible positive-core sites (four private leaves, the four centers outside L_i). Its five rows have column totals (3,3,3,3,2,2,2,2). Distinct rows overlap at most twice, hence cannot coincide. Generate all 5-subsets of the 4-subsets of eight slots with these column sums, removing only violations of the common-neighbor upper bounds 2−adjacency on a partial core. Sort rows to label N_i. For the three groups jointly, discard a violated core-pair bound or a common-neighbor deficit for an L_i pair. The two leaves attached to the two different L_i centers are disjoint, so the only common witnesses there are their shared parents and sites in private N groups.
3. The N_i are internally independent. Between N_i and N_j, the row degree of v in N_i equals the number of its positive-core neighbors in t_j, by the t_j eigen-equation at v where t_j=0. Column degrees follow by interchanging i,j. The checker exhausts binary 5-by-5 matrices with those margins at each of the three interfaces. Partial and final pruning uses only the exact common-neighbor capacities; no isomorphism of row assignments is assumed across different groups.
4. For every remaining complete adjacency matrix A on the 38 positions, set F=12I+2J−A−A² and d=14·1−A·1. In any completion, the actual 38-by-61 exterior incidence matrix B would satisfy F=BBᵀ and d=B·1, so **61F−ddᵀ is positive semidefinite**. The code tests this with symmetric fraction-free Schur complements in arbitrary-width integers. A negative pivot, or a zero pivot with a nonzero entry remaining in its row, refutes the matrix. Every division is checked for exactness. NumPy integer products used before this step have dimensions at most 38, binary incidence entries and small degrees; the final scaled entries have absolute value below 4,000. No eigensolver or floating comparison is used.

**Replay totals:** 2,105,696 triples of private-side tables; 145,532 survive the 23-core capacities and three paired-center saturations. All 145,532 pass the other early table-existence filters. There are 38,181 completed 38-site matrices satisfying the pairwise codegree caps (counted with the stated chart/row normalizations). Zero pass the exact exterior Gram test.

## The same oriented count at rank 38

There are 99·560=55,440 possible seeds (choose four of the seven neighborhood mates and one endpoint of each) and nine positive root choices for each oriented norm-18 marking. Thus 9N18≤2·55,440.

On rank-38 support contained in {018,024,125,226,228}, the [full native scalar row](norm18-u226-graph-cap.md) gives at each eligible determinant-49 extension
```
48V018 +12V226 −2V125 −19V228
  = 2058+98W014+11S+10W444 ≥ 2058.
```
The retained unit types have nonzero original discriminant norm, so multiplying their mean by 344 recovers their graph counts (positive charge for a>0, both orientations for N18). The [rank-free bound](norm16-height-two-edge.md) is G226≤4,158 when U127 is absent. It follows that 48N18 ≥ 2058·344−12·4158=658,056, hence the even integer N18 is at least 13,710. This contradicts 12,320 for precisely the same count. The argument does not assert that other supports, rank 38, or the full graph are impossible.

More generally, allowing 026 and 121 as well gives the necessary rank-38 inequality
```
3U026+81U121 ≥ 66,696+2U125+19U228
```
by using 48·12,320 and 12·4,158 in the same row; this is a pressure inequality, not a larger-support exclusion.

**Fewer shell absences.** The [exterior-incidence strengthening](norm18-triple-exterior.md) proves the same 12,320 upper bound assuming only N16=N20=U230=0, and extends the rank-38 contradiction to the six-type family that also permits (3,37).
