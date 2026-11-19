# Optional forced-rank anchor (separate addendum; not part of the initial review)

In a poset already imposing x<y<z, put a=1+|(x,y)|, b=1+|(y,z)|, where the parentheses denote strict open poset intervals. Then for i≥a,j≥b,

    F(a,b)F(i,j) ≤ F(i,b)F(a,j).                          (S)

These are the separate minimum possible positive successive gaps, not an arbitrary anchor. They need not be attained simultaneously; when they are not, (S) is vacuous.

Filter lemma with compulsory set. In a poset fix z, a set D of d elements each strictly below z, and filters A,B both containing D∪{z}. Put r=d+1, H=A∩B, Y=A∪B. For all j≥r,

    f_r(A)f_j(B) ≤ f_r(H)f_j(Y).                           (L)

Induct on j, simultaneously for every D with d<j. If f_r(A)>0, the full set of predecessors of z in A must be precisely D. Consequently D is an ideal there, α=f_r(A)=e(D)e(A−D−z), and η=f_r(H)=e(D)e(H−D−z). For j=r the inequality is immediate if f_r(B)=0; otherwise D is the entire predecessor set in B and Y too, and Fishburn for A−D−z and B−D−z (filters) gives the claim.

If j>r, expand f_j(B) by its first item b∈min(B)−{z}. For each of the following distinct branches, the RHS budget is η times an f_{j−1} first-item summand in Y.

* If b∈D then b is minimal in D and minimal in A as D is the entire ideal of elements below z there. Thus it is minimal in Y. Apply induction to D−b, A−b, B−b, with anchor r−1 and upper rank j−1. The ratios f_r(A)/f_{r−1}(A−b)=f_r(H)/f_{r−1}(H−b)=e(D)/e(D−b) cancel, giving the required budget with first item b. The case d=0 has no such b.
* If b∉A then b is minimal in Y, and D stays in both reduced filters. Apply induction to D,A,B−b (now j−1≥r) for the desired budget with first item b.
* For the remaining set T=(min(B)∩A)−(D∪{z}), use the coupling of the original filter proof, with p,q now first-item laws in A−D−z,H−D−z. Both are nonempty when T is nonempty. In either filter the removed D∪{z} is an ideal, so the reduced sets are filters and q dominates p on the smaller one as before. Couple such that w∈H implies w=b. For π(w,b)>0 with b∈T, w is minimal in Y: if w=b it has no predecessor in D∪{z} by minimality of b in B; if w∉B it cannot be above any member of D∪{z}⊂B. Minimality in A−D−z extends to A; minimality in B or its upward closure deals with that side too. D is disjoint from w,b. Applying induction to D,A−w,B−b yields αp_w f_{j−1}(B−b)≤ηq_b f_{j−1}(Y−w). The same π(w,b)/(p_w q_b) summation spends at most one full budget for each w∈A−D−z, disjoint from both previous kinds of b. This proves (L).

Apply (L) to the BFT upper-filter factor with D the elements strictly between y and z; they belong to U and hence every U∪T. Apply its dual to the lower-ideal factor, compulsory elements between x and y. The same four-functions comparison yields (S). If marks were initially not in a forced correct order, impose that order first and take open intervals in the enlarged poset. The separate minimum for two comparable elements is 1 plus their open-interval size: contract the order-convex closed interval to appear as one consecutive block in an extension, which remains acyclic. No promise of simultaneous attainment is needed.
