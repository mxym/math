# The anchored cross-product inequality for linear extensions

For *every* finite poset and every triple of distinct marked elements, let F(i,j) be the number of linear extensions with positive successive rank differences i,j in the specified order. We prove

    F(1,1) F(i,j) ≤ F(i,1) F(1,j)             for all i,j≥1.     (C)

This is the all-index inequality suggested at the end of §3 by Brightwell, Felsner and Trotter (Order 12, 1995, p. 338), after their proof of the case i=j=2. The rectangle is anchored at (1,1): (C) does *not* establish the general cross-product conjecture comparing neighboring cells at an arbitrary positive location.

## Filter lemma

Write e(S) for the number of linear extensions of the induced subposet on S, with e(∅)=1. Fix an element z. For a filter (up-set) S containing z, write f_j(S) for the number with z in position j, taken as zero beyond its range. For filters A,B containing z, write H=A∩B, Y=A∪B. We claim

    f_1(A) f_j(B) ≤ f_1(H) f_j(Y)               (j≥1).           (1)

We use Fishburn's extension-count inequality e(E)e(D)≤e(E∩D)e(E∪D) for two filters of a finite poset (the weak, unnormalized part of BFT Theorem 3.4). One consequence: if E⊆D are nonempty filters, then for any b∈E the first-item probability in a uniform extension of E is at least that in D. Indeed, when b is minimal in D apply Fishburn to E and D−b to get e(E)e(D−b)≤e(E−b)e(D); otherwise the probability for D is zero.

If f_1(A)=0 the claim is automatic. Otherwise z is minimal in A and hence in H; put α=f_1(A)=e(A−z) and η=f_1(H)=e(H−z). For j=1, the result is automatic if f_1(B)=0; otherwise z is minimal also in B,Y, and Fishburn applied to A−z,B−z proves (1). We now induct from j=h to j=h+1 for all pairs of filters in the given host.

Expand f_{h+1}(B) according to its first element b∈min(B)−{z}: the summand is f_h(B−b). If b∉A then b is minimal in Y, since any predecessor in A would put b in A. Applying the hypothesis to A and B−b gives

    α f_h(B−b) ≤ η f_h(Y−b).

These b are distinct and use only elements outside A. It remains to bound the sum over b in T=(min(B)−{z})∩A; if T is empty there is nothing to check. In the remaining case H−z and A−z are nonempty. Let p be the first-item law in A−z and q the first-item law in H−z. These sets are filters because z is minimal there before deletion. For every b∈H−z, p_b≤q_b by the consequence of Fishburn above. Couple w~p and b~q with joint weights π(w,b) so that w∈H implies w=b: put p_b on the common diagonal, and couple remaining mass on w∈A−H arbitrarily to the q_b−p_b deficits. Both residual masses are equal, and nothing more is required if they vanish. Each b∈T has q_b>0.

For a pair with π(w,b)>0 and b∈T, w is minimal in Y. Indeed, either w=b, minimal in B, or w∉B, which by upward closure rules out a predecessor in B. In both cases w is minimal in A−z; w cannot be above z, since in the first case b was minimal in B, and in the second case B contains z but not w. Consequently w is also minimal in A, and the sets A−w and B−b are filters still containing z. Their union is Y−w and their intersection is H−b, both when w=b and when w∉B. The inductive hypothesis gives

    α p_w f_h(B−b) = f_1(A−w) f_h(B−b)
        ≤ f_1(H−b) f_h(Y−w) = η q_b f_h(Y−w).

Multiply this inequality by π(w,b)/(p_w q_b) and sum over b∈T and positive-mass w. On the left, for each b the coefficient is ∑_w π(w,b)/q_b=1. On the right, for each w the coefficient is ∑_{b∈T}π(w,b)/p_w≤1. Thus the remaining sum uses at most η f_h(Y−w) for each of a subset of the minimal w∈A. These are disjoint from the previously used b∈B−A. Adding all terms and using the analogous first-item expansion in Y proves (1).

## The four-functions step

If no extension orders the marks x,y,z as specified, all counts vanish. Otherwise impose x<y<z and close transitively, which leaves every count at positive gaps unchanged. Partition the remaining points relative to y as D={v:v<y}, U={v:y<v}, I={v:v∥y}. For an up-set T in the induced poset on I, let

    f_j(T) = rank-j count of z in U∪T;
    g_i(Tᶜ) = rank-i count of x counting from the top in D∪Tᶜ,

where complement is in I. Each extension is obtained uniquely by choosing T (the incomparable elements after y), concatenating an extension of D∪Tᶜ, then y, then an extension of U∪T. There is no crossing relation contrary to this concatenation, by the filter property and the definitions of D,U,I. Hence

    F(i,j)=∑_T g_i(Tᶜ) f_j(T).

The sets U∪T are filters in the poset induced on U∪I; the sets D∪Tᶜ are ideals in D∪I, so after reversal the same filter lemma applies. For two up-sets A,B of I, lemma (1) and its dual give

    f_1(A) f_j(B) ≤ f_j(A∪B) f_1(A∩B),
    g_1(Aᶜ) g_i(Bᶜ) ≤ g_1(Aᶜ∩Bᶜ) g_i(Aᶜ∪Bᶜ).

Their product is the pointwise hypothesis of the Ahlswede–Daykin four-functions theorem on the distributive lattice of up-sets of I. Summation yields (C). This last decomposition and four-functions argument is BFT's established mechanism; the change is the all-j filter inequality with the first-item coupling. No unverified stronger nesting or signed-gap result is needed.
