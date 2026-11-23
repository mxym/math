# Higher literal wing-union fields and the charge-one norm-27 incidence

This rank-free companion uses the notation in the [complementary norm-22 wing correspondence](plus22-twelve-wing-unions.md) and the [complementary rank-56 construction](../complementary-rank56/README.md). Fix 2 ≤ k ≤ 6, allowing raw charges before their reduction modulo 11. Consider integral fields b such that Ab=3b+k 1, sum b=9k, and ||b||²=6k+3k², with at least three entries equal to k. Such a field is exactly

    b=k 1_T+1_U,

where T is its uniquely determined triangle and U is any union of components of the wing of T having size 6k. For k=3 this yields an exact special subtype in a lower theta shell.

Indeed, the three entries k exhaust the excess sum b_i(b_i−1)=3k(k−1), leaving exactly 6k unit entries and zeros. Write e for the edge count on the three distinguished sites. Their total contact count into the units is 12k−2ke, from neighbour sum 4k at each. Each unit meeting r of the distinguished sites contributes choose(r,2) ≥ r−1 pair witnesses. All units therefore supply at least 2k(3−e) common-neighbour slots for the three pairs. By strong regularity the pairs have only 6−e slots in all. If e=0 or 1 this is already impossible. If e=2 the middle distinguished site supplies a common witness of the nonadjacent ends, leaving just three slots for units, less than 2k. Hence e=3. No pair of triangle sites can have a unit common neighbour, so each unit has exactly one contact to T. It then sees exactly three other units, yielding a union of components of the cubic wing. The converse follows from equal component size in the three wings and the fixed exterior contacts (each component of size 6ℓ receives ℓ contacts from every far site). The special value k at three sites recovers T.

Let R count true charge-one norm-27 fields with a −1 site that neighbours two sites of value +2. Translate at any such site i by d_i=(4I+A)e_i. The charge rises to 3 and the norm becomes 27+30+2(−7+1)=45, with three +3 sites. By the above theorem these are precisely the three triangle sites, and their wing union has size 18. Conversely subtracting d_i at any triangle site of such a mass-27 field gives a charge-one norm-27 field with the two other sites now +2 and i now −1. The only sites of value +2 are those two, which are adjacent and thus have unique common neighbour i. There is no extra choice of pivot or sign. Hence, writing c_j(T) for the number of size-j wing components,

    R = 3 Σ_T [ c_18(T) + c_12(T)c_6(T) + choose(c_6(T),3) ].

The bracket is the number of wing unions of size 18; the three possible component partitions are 18, 12+6, and 6+6+6. The complementary scaled dual coefficient x_15 contains at least four copies of every F^+(1,27) field, including both signs across the two binary choices (1,1), (−1,0) for charge +1. For either pair the binary norm numerator is 6, so the charged term's total norm is 27+(42−9)/11=30. In particular

    x_15 ≥ 4R = 12 Σ_T [ c_18(T) + c_12(T)c_6(T) + choose(c_6(T),3) ].

Combining with x_11/8 ≥ Σ_T [c_12(T)+choose(c_6(T),2)], every triangle whose largest wing component has size at most 24 contributes at least one to at least one of these two sums. In the unit partition of six, an entry of two or three gives a direct contribution; otherwise an entry four has leftover two among ones, or every entry is one. The only partitions without a size-two or size-three union are (5,1) and (6). Writing b_{≥30} for the number of triangles with a wing component of size at least 30, we get the necessary whole-graph inventory inequality

    x_11/8 + x_15/12 + b_{≥30} ≥ 231.

Also any actual 24-component yields a size-12 wing union by complement, hence the number of actual 24-components is at most x_11/8. These are literal graph-to-theta counts, not estimates that either shell must be small and not exclusions of any rank.
