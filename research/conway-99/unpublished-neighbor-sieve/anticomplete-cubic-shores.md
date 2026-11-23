# A 36-site cap for two anticomplete cubic shores

Let G be a hypothetical strongly regular graph with parameters (99,14,1,2). If P and N are two nonempty anticomplete vertex sets (no edge between them) whose induced graphs both have minimum degree at least three, then both induced graphs are cubic and

    |P|+|N| ≤ 36.

This is rank-free. It does not assert that such a pair of size 36 exists or that both shores are connected.

At equality the unordered shore sizes are exactly among (6,30), (12,24), (18,18). In the (6,30) case the shores together form the entire wing of a triangle, with each shore a union of its components. For (12,24) the same conclusion follows if any outside vertex has 12 neighbours in the two shores combined; otherwise the contact counts below hold. For (18,18) the same conclusion follows if any outside vertex has six neighbours in each shore. The case with at most five neighbours into each 18-shore remains open in this argument.

## Centering and the two contact moments

For p=|P| and n=|N|, the real vector g=n 1_P−p 1_N is centered. Anticompleteness and minimum degree three give g^T A g ≥ 3||g||². The largest centered eigenvalue of A is 3, so equality holds; each shore must be cubic and Ag=3g. In particular p and n are both even. Let p=da and n=db with d=gcd(p,n), so a,b are coprime and positive. At a vertex x outside both shores, Ag=0 forces its numbers of P- and N-neighbours to be a h_x and b h_x for an integer h_x ≥ 0. Extend h by zero on both shores. Then

    (A−3I)1_P=a h,       A h=2d 1−4h,
    Σ h_x=11d,          Σ h_x²=2d².

Indeed, (A+4I)(A−3I)=2J and (A−3I)^2=−7(A−3I)+2J. Also 1_P^T(A−3I)1_P=0 because P is cubic. Summing (A−3I)1_P gives the first moment; taking its squared norm gives the second.

Cauchy's inequality gives 121d² ≤ (99−p−n)2d², hence p+n≤38. If p+n=38, the even integer d divides 38 and is less than 38, so d=2 and a+b=19. But every positive contact height then requires more than 14 neighbours, contrary to the first moment. Therefore p+n≤36.

At p+n=36 cubic shores have at least six vertices each: order four would be a forbidden K4, and order is even. The seven unordered size possibilities are (6,30), (8,28), (10,26), (12,24), (14,22), (16,20), (18,18). The pairs (10,26) and (14,22) have a+b=18 and hence can have no positive height. The pairs (8,28) and (16,20) have a+b=9 and d=4, so h≤1 and the two moments (44 and 32) would have to agree.

## Recognizing a triangle wing at high height

For (6,30), the reduced sizes are (a,b)=(1,5), d=6 and h≤2. The moment equations on 63 outside vertices give exactly three sites at height two and sixty at height one. Each height-two site has 12 support neighbours with h=0, leaving two outside neighbours; Ah=12−8=4 forces both to be height two. Thus the three sites are a triangle T. At every support vertex there are three support neighbours and eleven outside neighbours. The required height sum 12 there forces exactly one neighbour in T. The union of the two shores is therefore exactly the 36-site wing of T. Both induced shores are cubic and anticomplete, so each is a union of entire wing components.

For (12,24), the reduced sizes are (1,2) and d=12. Now h≤4 and

    Σ_Z(h−2)=6,       Σ_Z(h−2)²=12,

where Z is the 63-site set outside the shores. If a height-four site occurs, its 12 support contacts leave two outside neighbours. Both have height four because Ah=24−16=8. The variance allows at most three height-four sites, so they make a triangle T; variance is exhausted and all other outside heights are two. As above, every support site has exactly one T neighbour, because its eleven outside neighbours have total height 24. Thus T identifies the two wing unions.

If h≤3 instead, write n_j for the numbers at heights j. The two moments give 3n_0+n_1=3. The case n_0=1,n_1=0 is impossible: the lone height-zero outside site would see fourteen other outside vertices of height at least two, but Ah=24 there. Thus (n_0,n_1,n_2,n_3)=(0,3,51,9). Each height-one site has three support neighbours and eleven outside neighbours, whose height sum must be 20. They include both of the other height-one sites and no height-three sites (relative to baseline height two, two units of deficit are needed). The three height-one sites are a triangle, anticomplete to the height-three layer. Each height-three site has nine support contacts and five outside neighbours, whose required sum is 12, giving precisely two height-three neighbours. Thus the nine-site layer induces a 2-factor. This is a necessary alternative, not a realizability assertion.

For (18,18), use a=b=1 and d=18. Heights are at most six: a putative height-seven outside vertex would split its fourteen neighbours into two anticomplete seven-sets, but every neighbourhood is a union of seven disjoint mate edges. On the 63 outside sites the two moments give

    Σ_Z(h−3)=9,       Σ_Z(h−3)²=27.

Any height-six site has exactly two outside neighbours, both height six since Ah=36−24=12. The variance allows at most three such sites, hence they form a triangle, all other outside sites have height three, and each support site sees exactly one triangle site by its equation Ah=36. Thus the shores are unions of this triangle's wing components; if both are connected they are the two components of an 18+18 split. If no height-six site occurs, one additional unconditional consequence is that no height-zero site occurs. In fact writing n_j for the outside height counts, the two moments imply 6n_0+3n_1+n_2+n_5=9. If n_0=1 then 2n_1+n_2≤3, but at this lone height-zero site all fourteen neighbours are outside and the required height sum 36 needs deficit at least six from the baseline sum 42. This is impossible. The remaining positive-height alternatives are not excluded.

## Relation to the complementary fields

Any neutral signed-unit +3 field with anticomplete sign shores has cubic shores of equal size, so its ordinary squared norm is at most 36. Conversely a pair of equal-size anticomplete cubic shores automatically produces such a field by the same centered Rayleigh argument. At norm 36, the fields produced by pairs of complementary size-18 wing unions are exactly those with an outside site of height six; the recovering triangle is unique. This strengthens the one-way support injection in [the complementary wing-union correspondence](plus22-twelve-wing-unions.md) on this literal maximal-height subtype only. It is not an upper bound of 36 on all +3 shell values, nor a proof that a large wing must occur.

**Five-prism rigidity.** Five pairwise anticomplete induced prisms [force their unique sixth prism and central triangle](five-anticomplete-prisms.md). No existence of such a family is implied.
