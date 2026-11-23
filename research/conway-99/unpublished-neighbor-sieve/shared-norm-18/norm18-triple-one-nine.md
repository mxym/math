# A shared norm-18 triple has no scalar product nine

In any SRG(99,14,1,2) with N16=N20=0, **every triple of distinct oriented norm-18 fields with the same positive root and the same four negative neighbors has all three pairwise products seven**. There is no restriction on charge-one, charge-two or charge-three fields, or on rank. This does not rule out an all-seven triple whose norm-22 differences have edges. The [two-nine obstruction](norm18-triple-exterior.md#partial-cores-and-the-missing-neighbors) and [all-nine obstruction](norm18-triple-all-nine.md) leave only a unique nine to exclude here.

## The two endpoints

Call the positive root o, its four prescribed negative neighbors Q, and the six pair centers the second common neighbors of pairs of Q. Use the [standard triple panel](norm18-triple-exterior.md#partial-cores-and-the-missing-neighbors): each t_i uses o, four centers, and four singleton positive leaves with one parent in Q and three neighbors among the five negatives off Q. Its omitted center pair L_i partitions the six with the other two pairs. The centers are mutually nonadjacent. Let t_0,t_1 have dot nine, the other two pairs dot seven. The pair at dot nine has exactly one extra common positive singleton a and one extra negative n off Q. The two dot-seven pairs have no such extra shared sites. No opposite conflicts arise. On each of the three distinct supports the positive and negative sides are independent and the cross degree is four; this holds also for the true norm-18 difference t_0−t_1.

At each endpoint i=0,1, the other three singleton leaves are exclusive. Its two omitted centers must each see at least two exclusive leaves, since they see two negative parents and are positive in both other fields. They cannot both see the same two leaves: those leaves would also have a common i-negative among the private five. So their leaf contacts are B,C and B,D, respectively. Neither center sees any i-negative outside Q. Among the five private i-negatives the triples of B,C and B,D have exactly one common vertex apiece, and these two vertices are different (C,D both take the two private negatives missing B). The three parents of B,C,D are distinct by the same common-neighbor count. Thus the endpoints of L_i consist of these three distinct parents and the parent q0 of a: the number of leaves at any parent equals its occurrence count in L_i. Either both L_0,L_1 are perfect matchings, or just one is a two-edge path with center q0. They cannot both use q0 twice (only three incident pairs in K4). Up to labels, fix Q=1,2,3,4, q0=1 and take
```
(L0,L1,L2) = (12/34,13/24,14/23)   or   (12/13,14/23,24/34).
```

At B the other nine-endpoint j is zero. The two L_i sites are j-positive neighbors. By independence of each sign of t_i−t_j, the only neighbor of B negative in j besides its parent can be n (any other would have the same nonzero sign in the difference as B). Hence B meets n, and no j-exclusive positive leaf. Name its i-private negative triple n,u,v, and call the two negatives outside it w,z. Each of C,D sees w,z and a distinct further site from n,u,v. At a noncentral leaf the j-balance now prescribes exactly one cross-leaf edge if it meets n, none otherwise. There is at most one such leaf on each side, so the corresponding edge, if needed, is forced.

For each endpoint enumerate all B,C,D assignments to its three named leaves, both choices of the distinct third contacts of C,D, the three private neighbors of a, and two private neighbors at each of the four used centers. A center in L_j cannot meet n; one in L_2 can. Require each private negative to have exactly four positive neighbors and every pair to have codegree plus adjacency at most two. The four possible swaps of u,v and w,z identify only choices of names. Join the two tables requiring identical incidences from n to a and L_2, and installing the forced cross-leaf edge. The only additional edges inside the 27-site union of the two supports are between their two four-site groups of exclusive negatives. The row and column degrees of this binary 4×4 matrix are fixed by the other field's balance at each such negative, where that field vanishes. This exhausts all induced 27-site cores; no symmetry of the graph is assumed.

## Adding the four positive leaves of the satellite

The unit neutral norm-22 differences r_i=t_i−t_2 have at most two edges in each sign, and the edges form a matching. Indeed the [height-zero budget](norm18-u230-edge-pressure.md#charging-all-seven-triples-through-edged-differences) gives 0≤11−5e−J_P−J_N. If three positive vertices span at least two edges, subtract their three d-marks. The resulting charge −3 field has cost at most 22+53−42=33 and sum +33; a path endpoint would become −1 (and a triangle gives cost 19). This is impossible. Negate for the other sign.

The four satellite leaves Y have their parent multiset fixed by the four endpoints of L_2. For each y let l(y) be its number of neighbors in L_2; y may touch a and may touch noncentral endpoint leaves. Within a fixed endpoint i, balance at B, which sees both L_i centers, gives at least one negative satellite neighbor off Q. Each such edge lies in the positive sign of r_i. Since that sign is a matching, there is exactly one such neighbor, and B meets no satellite leaf. At C or D, its number of satellite leaf neighbors equals its number of satellite negative neighbors off Q (one L_i positive balances its parent). At most one C/D-to-Y edge is possible **across the whole endpoint group**, by e(r_i)≤2 and the already charged B. At a, its number of Y-neighbors is one plus its number of private satellite negative neighbors; hence one or two.

For each y the remaining contacts to the i-negative group off Q have cardinality
```
g_i(y)=l(y)+[y adjacent to a]+[y adjacent to C or D in i]−1.
```
They lie in the **negative** sign of r_i, so g_i∈{0,1}, their total over Y is at most two, and none of the chosen negative sites can be reused for two leaves. The same shared n can supply both endpoint incidences. No other contacts from y to the known 27 sites are possible: y and all used satellite centers, as well as o and other satellite leaves, are on the same independent sign. A leaf must have exactly its specified parent in Q.

If τ is the number of edges from L_2 to the satellite's five private negatives, satellite balance at the two omitted centers gives Σ_Y l(y)=4+τ and both centers have at least two Y-neighbors. Every such τ edge also belongs to the positive sign of each r_i; hence τ≤1, and the combined positive-edge cost for group i is τ+1+(deg_Y(a)−1)+the number of its C/D-to-Y edges, at most two. Finally any two Y leaves have a common neighbor among their triples in the private five, so their sets of **known** contacts intersect in at most one site. These are exactly the restrictions used to generate the new four rows, in addition to the common-neighbor caps. Only leaves with an identical parent are sorted to avoid artificial label duplicates.

## Exact marked spectral test, then five-site completion

Let A be the induced adjacency on these 31 sites and t the restriction of t_2. The two matrices
```
54I−18A+2J−7ttᵀ,       44I+11A−2J
```
are positive semidefinite in every graph. The original eigenspace projectors are (3I−A_full+J/9)/7 and (4I+A_full−2J/11)/7. From the first one may subtract the rank-one projector t_2 t_2ᵀ/18 **before** restricting to any sites. For each 27-core the [checker](norm18_triple_one_nine.py) eliminates its fixed block once per sign by integer fraction-free Schur steps, keeping cross entries for each possible one-leaf contact word. A negative pivot or a zero pivot with nonzero *core* entries refutes the 27-core; a zero pivot with nonzero cross entry rules out that particular leaf, not other leaves. The remaining block for four selected leaves is then only 4×4. Couplings between distinct candidate leaves are computed with no leaf-to-leaf edge, as required only when the rows are used together. Distinct leaves cannot have identical words because each word has at least two sites and distinct words used together overlap at most once. Every division affecting a possible selected principal block is checked for exactness, all integers have arbitrary precision, and there is no numerical cutoff.

For a surviving 31-core, write F_ij=2−A_ij−(A²)_ij for i≠j. The five remaining sites are the private negatives of t_2; their column sums across the 31 sites must give the row targets h=(A+4I)t. Each column w chooses **four** neighbors among the four satellite leaves and its four used centers. The other possible neighbors must have h_i>0. Enforce F_ij>0 for each selected pair, Aw+w≤2, equality of positive and negative hits for both original endpoints, and per-side height at most three for each of t_0,t_1,t_0−t_1 (each vanishes at this new site and is a norm-18 field). The five words must sum to h and have pairwise intersection at most two, since their sites lie on an independent sign. Exhaust every five-word choice by choosing the unresolved row i with the fewest subsets of the required size, trying them all, then deleting i-containing words before proceeding. Identical words would already share four satellite-positive sites and are impossible. Lastly, each pair L_i (i=0,1) must get **all** its remaining F_xy common neighbors among these five negatives: outside the full 36-core the true field t_i−t_j−t_2+d_x+d_y would take value −2 at a common neighbor of x,y∈L_i, whereas its norm is 30 and every such charge-two field is signed-unit by the [pivot argument](rooted-norm18-triples.md#dot-nine-exclusion). Add the full five columns, with no mutual edges, and recheck all core codegrees.

Run `python norm18_triple_one_nine.py` with Python 3.10+ standard library only; optional argument 0 or 1 selects one chart. The joint native replay took 37 seconds. Exact transcript:
```
single endpoint tables 156 156
compatible endpoint tables 773
pair cores, positive extensions, spectral survivors, full cores: 322 186824 602 0
single endpoint tables 60 124
compatible endpoint tables 84
pair cores, positive extensions, spectral survivors, full cores: 98 14192 0 0
```
There is no 36-site completion on either chart. Outside vertices cannot repair a failed marked Gram, a pair-cap excess, or a degree requirement for one of the three fields, all of whose supports lie in the 36 sites.

## An affine support with no exceptional-angle hypothesis

Now every true triple has all three dots seven. If T is the number of triple seeds, the [sum-and-four-marks map](rooted-norm18-triples.md#a-true-444-field) gives a true charge-four norm-44 field, and each such output determines the seed once its marked negative root o is supplied. This works with U230 and U127 arbitrary:
```
9N18−110880 ≤ T ≤ min(44G444, 15B1+30B2−(55/2)H2+(3/2)n1).
```
The other upper bound is the [edged norm-22 incidence budget](norm18-triple-all-nine.md#an-edged-difference-is-forced-even-in-the-one-nine-case), with B_j the positive-charge (2,30) matching subtypes, H2 the oriented norm-22 fields with two positive edges, and n1 the true (2,26) subtype with one negative common neighbor of its two positives. Counts concern actual graph fields, not modular averages. In particular N18≤12320 whenever G444=0, independently of the (2,30) shell. No full rank exclusion follows.
