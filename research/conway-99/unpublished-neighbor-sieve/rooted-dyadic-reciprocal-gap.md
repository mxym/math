# The reciprocal zero-star cusp starts in degree 21

Use the 7-extended, dyadically unsaturated rooted lattice F and the [230-signature atlas](rooted-unsaturated-dyadic.md). Let F^{*7} denote its dual at seven only, unchanged at all other primes, and put A=√7 F^{*7}. An A-vector of norm 2j comes from x∈F^{*7} with x²=2j/7; its 84 evaluations y, extended by zero on the root and neighbors, form an integral neutral minus-four eigenfield. Indeed F^{*7}⊂F*, and the original frame marks belong to F. The squared evaluation norm is 56x²=16j. The evaluations still satisfy the same mod-eight image condition and the same fourteen zero row sums because the original frame lattice, F and F^{*7} agree locally at two. Nothing requires the signed classes of nonzero seven-residues to be uniform.

We claim there is no nonzero such evaluation of squared norm below 336. A zero residue would give y=8t for a nonzero integral neutral eigenfield t of squared norm below 336/64<6, contrary to the graph's [short-support bound](../short-support-packing/README.md). For nonzero residue, the complete atlas and its integer duals leave just (00)^6(26) below 336: the two other classes with row bound 320 have strengthened bounds 432 and 448, and the rest start at 336 or higher.

In the remaining class, with global negation or formal relabeling if necessary, the 12 entries at the first active mate are all 2 mod 8, and the 12 at the second all −2 mod 8. A zero-sum row of the first kind has squared norm at least 144 (nine 2's and three −6's attain the row minimum), and the same bound applies to the opposite row. These rows have disjoint coordinates, since no exterior label contains two mate root neighbors. Their union is the 24-site two-wing subgraph. Every other coordinate is 0 mod 8; if any is nonzero, its square adds at least 64, for total at least 352. If none is nonzero, y is a nonzero minus-four eigenfield supported on the two-wing subgraph, impossible since its maximum degree is two. This proves the claim.

Consequently
```
[q^j] theta(A)=0       (1≤j≤20).
```
The remaining seven-discriminant plane of F is anisotropic. If x∈F^{*7} has integral even square, its class has quadratic value zero mod 1, so x belongs to F. Therefore [q^(7j)]theta(A)=[q^j]theta(F) at every j, in particular A_21=F_3≤30+f_o by the signed-cell Gram bound, where f_o counts H-compatible oriented norm-14 fields nonzero at the root. In terms of B=√8 F^{*2}, this proves min(B*)≥42/56=3/4, because √56 B*=A. This is a necessary condition at every root and every H, not a proof that the (separate) minimum of B itself is at most six.

## Two universal omitted coefficients and a sparse-face four-term gap

Continue with n=16j, the ordinary evaluation norm for A_j in the reciprocal dyadic gap theorem. For lifts l_i of any shape, put t_ij=l_i+l_j on all 84 nonmate pair labels. Because D y=0, y·t=0; also (y−t)/8 has integer coordinates with sum −3(sum_i l_i)/2. Since an integer vector's squared norm is congruent to its sum modulo two,
```
n + sum_(ij) (l_i+l_j)^2 + 96 sum_i l_i = 0 mod 128.
```
This is a necessary condition regardless of graph symmetry, valid for every signed representative. Filtering the already verified 230 shape representatives by the rowwise lower bound in the dyadic theorem and this congruence leaves zero candidates at j=22,25. Therefore A22=A25=0 at every rank/palette.

The survivors at j=23,24 have explicit scalar pullbacks. Extend y by zero on the closed star. Choose c_i congruent to l_i mod 8 (or the uniform +4 shift), with 3c_i−c_mate congruent to c_o for every axis and 3c_o−sum_i c_i congruent to 0. Then
```
b=(y+c_o d_o+sum c_i d_i)/8,
a=(c_o+sum c_i)/8,
64 b² = n + 7 sum_axes(3u²−2uv+3v²) + 35c_o²−112ac_o+128a².
```
Here u,v are the two chosen c_i on an axis. This is a genuine integer graph field of charge a: exterior coordinates equal (y_ij−c_i−c_j)/8, and the closed-star congruences give integrality there. Its seven class is H-compatible since the d_i have zero seven class and 8 is a seven-unit. The norm uses orthogonality of y to the d_i on the star, together with d_i·d_j=21I_ij−7A_ij+2.

The complete list (including all formal shapes after the two necessary filters) is:
```
j=23   (02)^4(15)(77)^2: take c-pairs (0,2)^4(1,5)(−1,−1)^2 and c_o=6 → (a,t)=(2,26).
j=24   (00)^7: y/8 is neutral of norm 6, impossible.
       (00)^6(44): take (0,0)^6(−4,4), c_o=0 → (0,20).
       (00)^3(26)^4: take (0,0)^3(2,−2)^4, c_o=0 → (0,20).
       (04)^3(17)^4: take (0,−4)^3(1,−1)^4, c_o=−4 → (−2,28).
```
All conclusions tolerate the representative's overall sign and all formal mate/axis relabelings. Wherever actual raw G(2,26), N20, and G(2,28) are absent, in particular on the remaining [rank-42 two-type face](shared-norm-18/two-type-true-hoffman.md#exact-derivation-and-scope-of-the-mark), A22=A23=A24=A25=0. This certainly does not assert the nonexistence of that face.

Run `python3 rooted-dyadic-reciprocal-extra.py` beside the existing atlas checker to replay the congruence and four lifts with the standard library.
