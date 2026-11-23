# The rank-42 norm-18/norm-24 two-type face is impossible

This excludes the shortlisted two-type face only: it does not exclude rank 42 with a different support, or an unrestricted Conway graph. The argument is analytic and assumes no graph automorphisms. Here graph-coordinate norms are ordinary squared Euclidean norms on true integer fields. An unoriented line is one antipodal pair of actual fields, not a line of residues.

## A lower bound from all four class centroids

Use the four signed norm-18 classes represented by (1,0),(0,1),(2,2),(2,−2) in the anisotropic residual plane with form 4I modulo 7. This is only a coordinate choice. Their populations are equal to n=50,51,52,53, respectively for the [four surviving tuples](two-type-true-hoffman.md) \(S=2,5,8,11\), where \(S\) is the number of extra unit \((1,23)\) markings; opposite signed classes are not included. Denote by A_1,...,A_4 the actual vector sums in the chosen classes. Put L=N22/2 and let D count double original-zero norm-28 lines, as in the [norm-22 Johnson-graph theorem](norm22-johnson-double-graph.md). That theorem identifies the vertices of this graph with L oriented-up-to-sign norm-22 labels, and at a vertex with m true norm-18 decompositions q=a_i+b_i the incident edges are the binom(m,2) differences a_i−a_j. Thus the sum of those degrees is 2D; m≤6. In each fixed signed class, two distinct norm-18 fields have product 4 or −3. Its dot-four unordered pairs inject into norm-28 lines, apart from the one repeat for each possible double over the four classes. If e_i is the number of such pairs in class i then
```
T := sum_i ||A_i||² = 14 sum_i e_i − 12n(n−7)
                   ≤ 14(−693+45n+L+D) − 12n(n−7).
```
We used the [true scalar relation](norm22-johnson-positive-mass.md) N28/2=−693+45n+L.

The four cross blocks (1,3),(1,4),(2,3),(2,4) have residue products 1,1,1,−1. After multiplying ordinary dots in the last block by −1 their values can only be 1 or −6: distinct norm-18 fields on this face have absolute product ≤7. If E is the total number of exceptional (absolute-six) cross pairs, summing all products gives the exact identity
```
7E = 4n² − (A_1+A_2)·A_3 − (A_1−A_2)·A_4.
```
There is no fourfold allowance in 2E≤N24. For each exceptional pair choose the relative sign giving product −6; the sign of the sum is irrelevant, and its squared norm is 24. A fixed oriented such sum z determines its unordered pair of source residues: each source u has norm 4 modulo 7 and u·[z]=12 modulo 7, a line meeting the anisotropic circle in at most two points; the known two source residues are distinct. Two distinct decompositions aligned by the same first signed residue would give a·a' in {4,−3} and a·(z−a')=12−a·a'≥8, violating the field angular bound. Simultaneous negation only reverses the choice of signed z, and the original four chosen signed classes pick just one field per source antipode. Hence the map from all four blocks to antipodal norm-24 lines is injective, giving 2E≤N24 as claimed. Cauchy and the parallelogram identity now give
```
B := 4n²−7N24/2 ≤ (A_1+A_2)·A_3+(A_1−A_2)·A_4 ≤ T/√2.
```
The [scalar rows](two-type-scalar-bridge.py) 2W335=172+3S−L and W024−W335=13n/2−93, N24=8W024, give N24/2=−28+6S+26n−2L, with L even at most 178,186,196,204. (The calculation below also works with the older floors 178,187,196,205.)

## A center which blocks the opposite wedge

For a center q choose q=a_i+b_i with first sources in a common signed class and second sources in its perpendicular class. For i≠j, a_i·a_j=b_i·b_j=4, a_i·b_j=7. The opposite endpoint of the difference c_ij=a_i−a_j is s_ij=a_i+a_j−q. Each q and s_ij is signed-unit (nonzero entries ±1). Write Q=supp(q), so |Q|=22, and P_i={x∈Q:a_i(x)=q(x)}. There is no cancellation on Q and |P_i|=11. Off Q, no two a sources can agree nontrivially since s_ij is unit. Thus |P_i∩P_j|=4+d_ij where d_ij counts doubled sites of c_ij. Let h_q=sum_{i<j} d_ij. By the established six-positive-site inverse for nonunit original N28, sum_q h_q≤12S (each graph edge has two ends, each actual slot is one of at most 6S over all lines).

Locally on the m source indices draw the edges with d_ij=0, called unit edges. Let w_q count the local unit edges contained in no unit triangle. Call a center clean if m=4 and all six of its differences are unit, and let F count the clean centers. Each has an actual 50-site union: the 22 sites of Q and one 7-site panel per decomposition off Q, pairwise disjoint since neither agreement (s_ij unit) nor opposition (c_ij unit) is possible off Q.

We claim sum_q w_q≥3F. At a clean q write k(x)=#{i:x∈P_i}. Then sum_Q k=44 and sum_Q binom(k,2)=24. Consequently sum_Q(k−2)=0 and sum_Q(k−2)²=4: exactly two sites have k=3, two have k=1, and eighteen have k=2 (in particular no fourfold overlap). The four triple populations r_ijk=|P_i∩P_j∩P_k| thus consist either of 1,1,0,0, or of 2,0,0,0.

For clarity, the actual opposite-endpoint constraint is as follows. If ij is a unit edge at a clean q, with remaining indices k,l, and the same edge admits a unit triangle at its opposite endpoint s, then r_ijk=r_ijl∈{0,1}. Relabel ij=12, write s=a_1+a_2−q, and choose one further source decomposition q=a+b and one s=a'−b' making unit wedges at both ends (the signs place a,a' and b,b' respectively in the same original signed source classes). Since a·a_1=a·a_2=a'·a_1=a'·a_2=4, and a·q=a'·s=11, we obtain s·a=q·a'=−3. Also s·q=0, so
```
b·b'=(q−a)·(a'−s)=−6−a·a'.
```
The only possible products within each common signed class are 4,−3 or 18 (equality); thus a·a'=b·b'=−3. Each sum a+a', b+b' has norm30 and is signed-unit on this face: its only possible nonunit coordinate magnitude is two, which after orienting and subtracting a root mark gives the forbidden raw \((1,25)\) shell. Hence both pairs meet in exactly three sites, opposite in sign at each such site. Put X=P_1∩P_2, of size four. On X one has q=s=a_1=a_2, with b_1=b_2=0. All three b/b' intersections are there. Indeed neither b nor b' can oppose b_1 or b_2 due to the unit wedges (the coherent orientations at s use −b' and −b_1,−b_2). An opposite overlap of b,b' therefore requires b_1=b_2=0. Outside X where these two vanish, all four base sources vanish; there b=−a and b'=a', so that an opposite overlap of b,b' would be a forbidden same-sign overlap of a,a'. Finally on X, a and a' cannot both be active (they would agree in sign), and a site is chosen by neither precisely when b,b' are both active. So the numbers of X sites chosen by a and a' sum to |X|−3=1. Keeping the same a' and applying this to a=a_k and a_l proves the required equality of triple populations.

The six local index edges at a clean q correspond bijectively to the six unordered pairs of the four triple populations by selecting the two triples containing that index edge. For the profile 1,1,0,0 at least four such pairs fail the equal-0-or-1 condition; for 2,0,0,0 at least three fail. Each failure forces the opposite local unit edge to be in no unit triangle. No two charges use the same opposite incidence: the Johnson edge and its opposite endpoint determine the charging incidence at q. This proves sum_q w_q≥3F.

## The global upper bound and contradiction

The following pointwise bound is useful (I_q denotes the clean indicator):
```
binom(m,2)+w_q−3I_q ≤ 3+(7/2)h_q.
```
For m≤3 this is immediate: at h=0 only m=2 contributes one wedge-free edge, and at h≥1 trivially w≤2. At clean m=4 it is equality. At m=4 with one nonunit difference every other edge lies in a triangle of K4 minus that edge. With two or more nonunit differences w≤4 and h≥2. For m=5,6 the lower bounds h≥4,6 follow by distributing the 11m incidences of the P_i across 22 sites and using sum_Q binom(k,2)=4 binom(m,2)+h. The w edges form a triangle-free graph, so w≤6,9 respectively by Mantel. These bounds give 10+6≤3+14 and 15+9=3+21. Summing and using the proved opposite-edge charge gives
```
2D ≤ 3L+42S.
```
Combining this with the centroid upper bound, a necessary inequality is
```
√2 B ≤ T ≤ T_max := 14(−693+45n+(5/2)L+21S)−12n(n−7).
```
As a function of L, T_max−√2 B has positive slope 35−14√2, so it suffices to test at the largest allowed L in each tuple. The following is an exact integer computation, with both compared quantities positive:
```
 n   S   Lmax    B     T_max     2B²−T_max²
50   2    178   3504   2816       16626176
51   5    186   3712   3480       15447488
52   8    196   3956   4190       13743772
53  11    204   4180   4806       11847164
```
Every final entry is strictly positive, a contradiction in all four cases. No enumeration of hypothetical graphs or additional symmetry assumptions enter the proof.

Run `python3 two-type-scalar-bridge.py` with the same dependencies as the earlier scalar checker to replay the shell identities and all four final integer comparisons.
