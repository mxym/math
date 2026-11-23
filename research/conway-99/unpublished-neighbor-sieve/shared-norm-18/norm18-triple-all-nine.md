# A shared norm-18 seed cannot have all three scalar products nine

Assume N16=N20=0 in a hypothetical SRG(99,14,1,2). All positive-charge fields, including (2,30), may occur, and the Seidel rank is arbitrary. At an actual positive root o with a specified four-set Q of negative neighbors, three norm-18 fields cannot have all three pairwise scalar products nine. The proof is a 33-site, subsecond, exact finite exhaustion; it does not search for a whole graph or assume an automorphism.

## Three exclusive singleton leaves

Use the [three-marking and dot-nine common-panel rules](panel-heights.md#the-three-label-exclusion-and-the-rank-38-contradiction), or the [six-center derivation](norm18-triple-exterior.md#partial-cores-and-the-missing-neighbors). Each of the three fields t_i has a 4-regular bipartite support on nine positive and nine negative sites. Each omits a pair L_i of the six centers labeled by the pairs of Q, and the L_i partition those centers. Besides o and its four used centers, t_i has four positive leaves, each adjacent to exactly one parent in Q and three of its five private negatives (meaning off Q, not necessarily off the other fields). Every two centers are nonadjacent. For every field-pair in this case there are no opposite-sign overlaps, four common positives (o, two centers, one singleton leaf) and five common negatives (the four parents and one further negative). Their difference is itself a true unit norm-18 field, with both signs independent.

If t_i's two shared singleton leaves with the other fields were different, only two of its leaves would be exclusive to it. Its omitted centers x,y are positive in both satellites, so neither can see any nonexclusive positive of t_i. But each sees two negative parents and hence must see both exclusive leaves. Those leaves share a third common site among the five private negatives, contradiction. The three pairwise common leaves must therefore all be the same site a. Write B,C,D for the remaining three exclusive leaves of t_i. Each omitted center sees at least two of them, but the two centers cannot both see the same two leaves by the same shared-negative argument. Thus their exclusive-leaf neighbors are exactly B,C at x and B,D at y after choosing names. Each center sees exactly the two parents as negatives of t_i, no further i-negative. In their triples of private negative neighbors, B,C meet exactly once (x is another common neighbor), and likewise B,D. Therefore C,D both see the two private negatives missing B and use *different* third sites in B's triple. The parents of B,C,D are distinct: B,C have x and their one negative witness, B,D have y and their one negative witness, and C,D have their two negatives.

Let q0 be a's parent. The number of singleton leaves attached to a given q equals its number of occurrences among the four endpoints of L_i, by the degree-four law at q. Each L_i must contain q0 and these three counts sum to three in K4. Thus q0 occurs exactly once per L_i, taken by a, and each of the three other parents occurs once, taken by B,C,D. Consequently L_1,L_2,L_3 are exactly the three perfect matchings of K4.

Write n_ij for the sole shared negative of i,j outside Q. If two of the three n_ij coincide, then all three do. This common negative would miss all six centers (each L_i misses the off-Q i-negatives), and misses o. Its four positive neighbors in t_i would have to be all four leaves; this contradicts the distinct singleton intersections of B,C and B,D. So all three n_ij are distinct. The remaining three off-Q negatives of t_i are exclusive to it; call their set E_i. We now have exactly 33 distinct sites: o,Q, six centers, a, nine exclusive positive leaves, three pair-shared negatives, nine exclusive negatives.

## Why the remaining interfaces are small

Assign a nonempty membership subset of {1,2,3} to each of these sites, with its common sign. An edge of one sign can only connect disjoint membership sets, by independence of each t_i sign. For opposite signs their sets must be comparable: otherwise the two endpoints have the same nonzero sign in some t_i−t_j, also impossible. These rules are only necessary and suffice to specify the choices below.

Fix i and the other indices j,k. B has both L_i centers as neighbors. In t_j it is zero and requires at least two j-negative neighbors. By mask comparability every j-negative neighbor at B must also be i-negative, so it is B's one parent or n_ij. Both are needed, and analogously B meets n_ik. Write the five i-private negatives as (n_ij,n_ik,u,v,w), with u the third neighbor of B. The negative triples of C,D thus both contain v,w and different third sites chosen among n_ij,n_ik,u.

For a noncentral leaf C or D, there is exactly one L_i neighbor. Its neighbors among the j-positives are that center and possibly j-exclusive leaves; it cannot meet o,a or any center used by i. The j-negative neighbors are its parent and, if selected, n_ij. Thus it has a j-exclusive neighbor precisely if it meets n_ij, and then exactly one. At most one noncentral i-leaf takes n_ij. The two groups therefore either have no positive-leaf cross edge or **the unique edge** between their corresponding noncentral leaves. B has none, by the same equality with its two centers.

The four used centers in group i each need two of the five private negatives to complement their two parent contacts. A center in L_j cannot meet n_ij since it sees no j-negative outside Q, and similarly with k. The shared leaf a needs any three private i-negatives, subject to the shared identifications across groups. These choices, with four positive neighbors required at every private i-negative, complete all edges in the true bipartite support of t_i.

The only unknown negative-negative edges are those between two E-groups or between n_ij and E_k for the remaining k. The latter site n_ij is zero in t_k. Its only possible k-positive neighbor is a: by comparability k-exclusive leaves and the k-used centers with two incomparable memberships cannot neighbor it, and o already has its four negatives Q. Thus n_ij needs one neighbor in E_k if adjacent to a, and none otherwise. Finally, for x∈E_i the balance in t_j at x gives the degree into E_j as its already known neighbors in the positive side of t_j minus its already known neighbors in the negative side. This prescribes both margins of each of the remaining three binary 3×3 interfaces.

## Independent replay

Run [norm18_triple_all_nine.py](norm18_triple_all_nine.py), requiring only Python 3.10+ standard library. Partial adjacencies are pruned only by codegree plus adjacency ≤2 for distinct sites. Normalize Q by placing q0 first and listing its three perfect matchings in the fixed order. Label the three exclusive leaves by their distinct parents; try all six positions of the central B and the leaves C,D on the two named centers. Within E_i, u is the neighbor of B, while v,w may be interchanged; the checker sorts only this pair. For each group it generates the choices above, including all pairs of negative neighbors for each used center. At a join it identifies precisely the same n_ij, requiring agreement on its a contact and its two possible common used centers in L_k, and installs the forced cross-leaf edge if present. It then tries the permitted n_ij-to-E_k neighbors and every binary negative-interface table with prescribed row and column sums. No graph symmetries, floating arithmetic or external tables are used.

Expected transcript:
```
local [128, 128, 128]
compat 0 1 880
compat 0 2 880
compat 1 2 880
joined 84 30
residual 48 complete 0
```
Here 84 passes pairwise joins and 30 also passes joint codegrees; 48 extensions by the n_ij-to-E_k decisions pass partial codegrees. Zero survive all three remaining interfaces with the necessary capacities. Extra vertices cannot repair an exceeded internal pair capacity or a wrong neighbor balance, because every t_i vanishes outside the 33 sites.

## Stronger count with (2,30) allowed

In the [edge-pressure theorem](norm18-u230-edge-pressure.md), three-nine seeds no longer contribute. The surviving one-nine seeds each give two marked (2,30) fields, in each case at an *isolated* pair of positives. A B0 field has at most six such pairs and a B1 field just one, each with at most twelve candidate roots; a B2 field has none. Thus T9≤36B0+6B1, while the original all-seven bound T7≤15B1+30B2+(3/2)n1 stays valid. Consequently
```
9N18 ≤110880+36B0+21B1+30B2+(3/2)n1.
```
The maximum U230 coefficient in this row is now 36, so the same folded scalar argument at rank 38 gives
```
9U026+243U121+102U127+606U230 ≥200088+6U125+57U228+9U337 .
```
These remain necessary quantitative conditions, not categorical rank exclusions. The separate [triple prohibition](norm18-triple-exterior.md) when U230=0 is stronger on that special face.
