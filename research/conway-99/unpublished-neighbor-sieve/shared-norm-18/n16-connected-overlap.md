# The height-two overlap multigraph of any norm-sixteen field is connected

This uses no rank hypothesis. For the eight height-two words W_i⊂P∪N of an actual norm-sixteen field, form a multigraph Σ on the eight words: each of the sixteen signed sites gives one edge between the two words that contact it. Thus Σ_ij=|W_i∩W_j|≤2 for i≠j. Color by sign. Each color is a 2-factor with even cycles: it is the edge-dual of the corresponding [shore deficiency multigraph](../n16-zero-star-forest.md), with double edges preserved. This differs from the simple conflict graph (only multiplicity-two pairs). Write Z for the eleven zero-height sites and Y for the sixty-four height-one sites.

Every nonempty closed component has even size and cannot have size two: that would require multiplicity four. If Σ were disconnected, a four-word set U would be closed. Its six pairs can have at most twelve common-neighbor incidences; eight are already occupied by signed common sites (eight internal Σ edges). On the other hand each word sees at least four Z by d_Z(i)=4+d_H(i). The ≥16 incidences give at least five common Z-pair incidences because ∑_z binom(d_U(z),2)≥∑_z(d_U(z)−1)≥16−11. This exceeds the four unspent slots. Hence Σ is connected.

Both colors have even cut size. An odd-size set must have a crossing in each color since each color has only even circuits. A two-site set cannot have a boundary of size two because its internal multiplicity is at most two. Thus the only possible cut of size two is 4|4, with both edge colors the same, and each four-set contains seven internal Σ edges. In that case all inequalities on EACH shore are equalities: all its vertices have exactly four Z neighbors, the 16 contacts give exactly five same-shore pair incidences in Z, and every one of the eleven Z has one or two contacts on the shore. The within-shore pair ij has exactly 2−Σ_ij common Z's; no Y meets two H sites on either shore. Also H is edgeless by d_Z=4+d_H. (If any H edge existed, its endpoint would have at least five Z neighbors.) For each side S the eleven Z traces are five two-subsets determined with multiplicity 2−Σ_ij and six singleton traces determined from the four contacts at every H vertex. The true Z patterns pair the two eleven-token families, not necessarily in any prescribed order. Hence every z has total H degree 2,3 or4 and d_Z=0,1 or2; no claw can occur.

For reproducibility compute the minimum 4|4 cut of each of the 466 [necessary overlays](n16-five-shore-cores.md). The [exact overlay checker](n16-five-shore-cores.py) uses a 70-subset test per old orbit:

|deficiency deck|min 0|min 2|min 4|min 6|min 8|
|---|---:|---:|---:|---:|---:|
|8|0|0|127|114|2|
|6+2|0|0|83|35|0|
|4+4|3|0|48|20|6|
|4+2+2|2|4|18|2|0|
|2+2+2+2|0|0|2|0|0|

Exactly five formerly necessary abstract overlays cannot be realized. Among the remaining 461 all are 4-edge-connected except for four abstract 4+2+2 cases, whose 4|4 contacts obey the rigid description above. The table is a necessary filter, not evidence for existence in the retained cases.
