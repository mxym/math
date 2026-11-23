# A 33-set with twelve Hoffman sites has no cycle missing the Hoffman coclique

Use the rank-42 two-type face. Let T be an actual G(3,33) 33-set. Let C be the unique Hoffman coclique, Δ=|T∩C|=5 or 12, and x=1_(T∩C) on the 33 sites of T. Write L=A_T, a union of cycle adjacency matrices, and H=3I−L. This extends the [two-mark residual result](simultaneous-hoffman-33-residual.md) by using all 33 individual marks.

**Full cross-Gram.** The T-site mark Gram is H+J/9 and their pairings with the actual mark m_C=(3/√7)(1_C−2/9) of norm 22 form v=3x−(2/3)1. All 33 site marks are independent because H is positive definite. Since H1=1, their inverse Gram is H^{-1}−J/42. The squared norm of m_C projected to the 11-dimensional orthogonal complement of all these sites is therefore

    22−vᵗ(H^{-1}−J/42)v=9((Δ²+4Δ+88)/42−X),   X=xᵗH^{-1}x.

This proves X≤19/6 at Δ5 and X≤20/3 at Δ12. At Δ5 more is true: the same residual has squared norm at least 3/2.

**Cyclic gap kernel.** Let r=(3−√5)/2. On a cycle of length k the Green kernel has entries at cyclic distance d equal to (1/√5) sum_(m in Z) r^|d+mk|. This follows by periodizing the inverse of the tridiagonal infinite-line operator (3−r−r^{-1}=0, 3−2r=√5). Traverse each component which meets C in either orientation. Let g_i≥2 be the gap in forward edges from the ith marked site to the next marked site of that same component (with a full-cycle gap for a sole marked site). Index cyclically in that component, and let m=sum g_i be the total number of sites of T in touched cycle components. Then

    √5 X=Δ+2 sum_(h≥1) sum_i r^(g_i+...+g_(i+h−1)).

All terms are positive. The Δ exponents in the h-th inner sum have sum hm even across disconnected cycle components. For fixed integer sum their exponential sum is minimized when all differ by at most one, by convexity. At Δ=12, if m≤28 then the first two inner sums alone give

    √5 X ≥12+2(8r²+4r³+4r⁴+8r⁵) > (20/3)√5.

Thus m≥29 and at most four vertices lie in untouched components. A T-cycle cannot have length four on this face by the norm-30 charge-two shift; at Δ=12 an untouched triangle is already forbidden by the triangle flip. These are prior results. Therefore **all 33 sites lie on components touched by C**.

At Δ=5, since every gap is at least two, the kernel gives the automatic X≤(5/√5)(1+r²)/(1−r²)=3. This proves the claimed positive squared residual ≥9(19/6−3)=3/2, and shows why the scalar upper does not prune any additional Δ5 cycle deck.

**Spacing at Δ=12.** There are at most eight gaps of length two. If ten exist, then already √5 X≥12+20r²>(20/3)√5. If exactly nine exist, among twelve cyclically arranged gaps at least six successive pairs are both length two, and at least three successive triples are all two (union bound over cyclic permutation of twelve gaps). Thus the graph-site distances four and six contribute at least six and three times respectively. At least one of the three remaining gaps is ≤5, since otherwise the total would be ≥36>33. Such a gap of length 3,4 or5 gives a distinct additional ordered forward occurrence, separate from the paired or tripled 2-gaps. Consequently √5 X≥12+2(9r²+6r⁴+3r⁶+r⁵)>(20/3)√5. The companion standard-library checker verifies all three strict comparisons using rational bounds on √5. Equivalently T\C is a union of twelve nonempty paths of total length 21 in vertices, at most eight of which are isolated vertices.

**Exact best placement for each marked cycle deck.** For a cycle of length k with j>0 marked sites, take the marks at floor(ik/j), i=0,...,j−1. The h-step successive gaps then differ by at most one for EVERY h, simultaneously attaining the integer convexity bound above. This is an exact minimum of xᵗH^{-1}x among that cycle's independent j-subsets (and is zero for j=0). It can be computed rationally from 3r'_0−2r'_1=1 and r'_(d+1)=3r'_d−r'_(d−1), r'_k=r'_0, for the first row of the finite inverse H^{-1}. Add the independent component minima for a fixed deck. Of the 7089 and 2494 previously surviving formal decks (after the integer cycle-subset gap), 7089 and 1718 pass this further necessary test; the latter have at most nine triangles. The 1718 count classifies only length/occupancy decks for this one scalar cross-Gram condition, not graph realizations or an exclusion of a full tuple.

Run `python3 all-cycles-hit.py` for the exact rational comparisons and optional formal cycle-deck counts.
