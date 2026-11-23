# A forced 36-site signed core and its three allowed directed decks

Scope: rank 42, only the two short unit types N18 and N24. From the [double-norm-28 Johnson bound](norm22-johnson-positive-mass.md) there are at least 109,135,165,195 actual double norm-28 *lines*, indexed by S=2,5,8,11. At most 6S lines of the whole norm-28 shell can have a nonunit coordinate. Therefore every tuple has a signed-unit double c=x+y=x'+y'. Regard t_0=x,t_1=y,t_2=−x',t_3=−y' as four signed-unit norm-18 fields summing to zero. At a marked site the four entries cannot be two positives and two negatives: if x,y agree nontrivially then c is nonunit, while if x,y cancel and x',y' cancel then either x−x' or x−y' is nonunit, impossible as both are norm 22. Thus a marked site is exactly an arc i→j, meaning t_i=1,t_j=−1. All other entries are zero. Each of the four colors occurs as a tail nine times and as a head nine times. The unordered arc multiplicities are determined by −t_i·t_j: four on 01,23; seven on each of 02,03,12,13. There are 36 marked sites and 63 other vertices. Orientations of individual sites are not chosen freely; only permutations of the four colors preserving the small matching and reversing all four field signs are used for normalization.

The sign sides of all four norm-18 fields are independent. So are the two sign sides of q=t_0+t_2 and s=t_0+t_3: from a same-positive edge uv an actual neutral norm-22 field b would give d_u+d_v−b of charge 2, squared norm 36+22−28=30, absent on this face; negate b for a negative edge. Consequently the neighbors of any vertex cannot share its nonzero coordinate sign in any of these six signed fields. For a norm-18 field, every support vertex has exactly four opposite-sign neighbors, and every outside vertex has equal positive/negative height h≤3: for its 9-set P of positive sites, A²1_P=12·1_P−A1_P+18·1; the h negative neighbors each require four positives. Similarly h≤4 on an outside site of either independent norm-22 field (replace 18 by 22).

**Analytic capacity of parallel arcs.** For the a vertices of type i→j, let b count the reverse arc. The opposite norm-18 side for i (heads i) and for j (tails j) both have size 9, overlapping in just these b reverse sites. Let their A-neighbor counts be r_1,…,r_b, each ≤4. Each nonoverlap group of size 9−b has 4a−Σr total contacts. Put F(k,n)=minimum ΣC(h_i,2) over n nonnegative integral counts totaling k: it is attained by the balanced counts floor(k/n), ceil(k/n). All pairs inside the a parallel arcs have exactly two common neighbors, hence
```
Σ C(r_i,2)+2F(4a−Σr,9−b) ≤ 2 C(a,2),
r_i+r_j ≤ a+2   (i≠j).
```
The latter follows from at most two shared A-neighbors of the two reverse sites. In particular a≥6 is impossible, and so is (4,0). At (a,b)=(5,2), r_1=r_2=3 is the unique feasible pair: all fourteen other opposite targets have exactly two A-neighbors and the full pair budget is consumed, so any other vertex has at most one. This elementary ceiling check is enumerated with arbitrary-width Python integers. Together with the exact four in/out balances and matching normalization it retains 5 of the 19 potential mass decks.

**Colored two-walk certificate.** Cell indices 0 through 11 are the lexicographically ordered arcs, cell 12 the 63 zeros. A vertex of type v has h_i neighbors in cell i, with Σh_i=14. Enumerate all possibilities independently for each v, imposing the six sign constraints above, the cell capacities, and the (5,2) rule. Before the latter filters there are only 65 patterns on each arc type, 2008 at the unmarked sites. No sampling or graph automorphism is used. For multiplicities x(v,h)≥0 of true vertices with those profiles, the following 169 equations hold:
- Thirteen population counts equal their fixed deck d_v;
- In lexicographic unordered distinct cell pairs i<j, opposing directed-edge counts agree;
- In lexicographic i≤j among the twelve nonzero cells,
```
Σ_(v,h) x(v,h)[h_i(h_j−[i=j])+[v=i]h_j] = 2d_i(d_j−[i=j]).
```
The last row sums the true common-neighbor count plus the adjacency correction over ordered distinct sites in the indicated cells: every pair has 2−A_xy common neighbors. Multiplying the 169 equations by the displayed integer column certificate gives nonnegative coefficient on every possible profile x but a strictly negative right side on each of two further decks. The checker uses only fixed integer arithmetic and the Python standard library. The remaining formal decks (entries in order 01,02,03,10,12,13,20,21,23,30,31,32) are
```
(1,3,5,3,3,3,4,4,1,2,4,3)
(1,4,4,3,3,3,3,4,2,3,4,2)
(2,3,4,2,4,3,4,3,2,3,4,2).
```
This is a three-deck necessary condition for every signed-unit double, and each tuple must realize at least one such double. No actual 36-site core or full graph is asserted.

Run `python3 unit-double-four-arcs.py` (Python 3.10+, standard library) to verify all 19 mass decks and the two fixed integer certificates. The script does not enumerate graphs.
