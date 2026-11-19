# Separated ranks in filters and interior cross-products of linear extensions

For a finite poset P with three marked elements x,y,z, let F(k,l) count the linear extensions with the prescribed successive differences k,l≥1. If no extension places x,y,z in that order, the assertions below are trivial; otherwise add x<y<z and close transitively, leaving all positive-gap counts unchanged. Take I to be the subposet of points incomparable with y in this resulting poset, and Δ the maximum over b∈I of the number of elements of I incomparable with b (zero if I is empty).

**Theorem.** For all k,l≥1 and positive r,s≥Δ,

    F(k,l)F(k+r,l+s) ≤ F(k+r,l)F(k,l+s).                         (1)

In particular the original adjacent-cell cross-product inequality at *every* positive interior location holds if Δ≤1. This includes I a chain, and allows arbitrarily large poset width outside I. It recovers the positive rectangular width-two theorem: in a two-chain partition the points incomparable to y form part of the chain not containing y. The result does not settle all positive adjacent cells when Δ>1.

## Separated-rank lemma

For a filter (up-set) A containing z let f_u(A) count extensions of the induced order with z in position u; out-of-range counts are zero. For any two such filters A,B in a common poset, put H=A∩B and Y=A∪B. We prove that for 1≤i≤j,

    j−i ≥ |B\A|   ⇒   f_i(A)f_j(B) ≤ f_i(H)f_j(Y).              (2)

In particular, letting B⊆A shows that enlargement from a smaller filter to a larger filter shifts the marked rank upward in likelihood-ratio order (the order is defined by these cross-products, and normalizing by extension totals does not change it).

We use the compulsory-anchor filter lemma in [the anchored note](https://github.com/mxym/math/blob/37109641b5a68ea627f77cc67bc5d0a29da50a05/research/anchored-poset-cross-products/SHIFTED.md): if a set D of d predecessors of z is contained in A and B, then the conclusion in (2) holds at i=d+1 for *every* j≥i. Its proof uses Fishburn's inequality and an endpoint coupling. The ordinary anchored case appears there separately. For any poset S containing z, the possible ranks of z are all integers from 1+#predecessors to |S|−#successors: the endpoints are attainable by topological sorting, and adjacent incomparable swaps connect the linear extensions without skipping ranks.

Induct on j simultaneously over all pairs of filters and all 1≤i≤j satisfying the hypothesis. Zero left products are immediate. For i=j one has B⊆A and equality. Thus assume j>i. The feasible lower endpoint in H is at most i since H⊆A and f_i(A)>0. Restricting an extension counted by f_j(B) to H gives a z-rank at least j−|B\A|≥i, so f_i(H)>0. If i is the minimum rank in H, the set D of all predecessors of z in H is contained in both filters and has size i−1; the compulsory-anchor lemma proves (2). Otherwise i>minrank(H) and in particular i≥2.

Write α=f_i(A), η=f_i(H). Let p and q be the first-element laws of uniform extensions of A and H respectively, each conditioned on rank(z)=i. They sum to one and assign zero mass to z. For b∈H we have p_b≤q_b. This is automatic if p_b=0. Otherwise b is minimal in A and in H, and

    p_b = f_{i−1}(A−b)/α,     q_b = f_{i−1}(H−b)/η.

The inequality between these follows by the induction hypothesis applied to the filters A−b and H with lower index i−1 and upper index i: their union is A, their intersection is H−b, and |H\(A−b)|=1. This is a strictly earlier upper index since i<j. Couple w~p and b~q so that every w∈H is paired with b=w: assign p_b on the common diagonal and distribute the remaining mass p(A−H) to deficits q_b−p_b. Write π(w,b) for the joint weights.

Expand f_j(B) by its first b∈min B−{z}. If b∉A, it is minimal in Y, and the pair A,B−b has |(B−b)\A|=|B\A|−1. Induction at (i,j−1) gives

    α f_{j−1}(B−b) ≤ η f_{j−1}(Y−b).                             (3)

For the remaining b∈T=(min B−{z})∩A, b is minimal in H. We need q_b>0, even if p_b=0. Indeed b is not above z; deleting b decreases the maximum possible z-rank by one, and does not increase the minimum rank. Since i exceeds minrank(H), the rank i−1 is feasible in H−b, giving q_b>0. For π(w,b)>0 with b∈T, w is minimal in A and either w=b, minimal also in B, or w∉B, with no predecessor in B by the filter condition. Hence w is minimal in Y. Removing w from A and b from B gives filters containing z, with intersection H−b, union Y−w, and

    |(B−b)\(A−w)|=|B\A|.

The inductive hypothesis at (i−1,j−1) gives

    α p_w f_{j−1}(B−b) ≤ η q_b f_{j−1}(Y−w).

Multiply by π(w,b)/(p_w q_b) and sum over b∈T and positive-mass w. For each b the α term is used exactly once, and for each w the η term is used at most once, by the marginals. These w all lie in A and are disjoint from the b∉A in (3). Summing the first-element expansion in Y proves (2).

The numerical threshold in this *filter lemma* cannot in general be lowered by one: take i≥2, |H|=i−1, all points including z incomparable, |A−H|=1 and |B−H|=j−i+1. Both left factors are positive and f_i(H)=0. This does not assert necessity of Δ in the poset cross-product theorem.

## Transfer to gap counts

Use the Brightwell–Felsner–Trotter cut at y: split the incomparable points into an upper filter T⊆I and its complement, put U={v:v>y}, D={v:v<y}, and write h_l(T) for the rank-l count of z in U∪T and g_k(Tᶜ) for the rank-k count from the top of x in D∪Tᶜ. The extension concatenation gives F(k,l)=∑_T h_l(T)g_k(Tᶜ). For filters A,B⊆I compare h_l(A)h_{l+s}(B) with h_l(A∩B)h_{l+s}(A∪B). If A⊆B this is equality; if B⊆A it follows from the nested case of (2). For incomparable filters, pick a∈A−B: every element of B−A is incomparable with a, so |B−A|≤Δ, and (2) applies since s≥Δ. Similarly the dual lower filters give g_k(Aᶜ)g_{k+r}(Bᶜ)≤g_k(Aᶜ∩Bᶜ)g_{k+r}(Aᶜ∪Bᶜ), using the reverse order and r≥Δ. Multiplying and invoking the Ahlswede–Daykin four-functions theorem on the filter lattice yields (1). The two nested orientations can alternatively be handled uniformly by (2) whenever |B−A| is small, but no such cardinality bound is needed for either nested orientation.
