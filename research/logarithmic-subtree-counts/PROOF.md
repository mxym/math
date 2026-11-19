# Logarithmic-order subcubic trees with a prescribed subtree count

Let tr(G) count the nonempty tree subgraphs of a finite simple graph, including each singleton. Subgraphs are actual vertex/edge subsets, not isomorphism classes. For a tree T they are exactly its nonempty connected vertex sets. For every sufficiently large integer k there exists a **connected tree of maximum degree three** with exactly k subtrees and at most 298 log₁₇ k vertices. The logarithmic order is best possible (not the constant): a tree on n vertices has at most 2ⁿ−1 subtrees. Even unrestricted simple planar graphs cannot improve the order, since there are at most n+2^{3n} tree subgraphs (a nonsingleton subtree is determined by its edge set and a simple planar graph has at most 3n edges).

In particular the planar all-tree-subgraph function in Chan–Pak, §6.8, Conjecture 6.5, is concise. That literal polylogarithmic assertion already has a short proof: tr is additive across disjoint components, and a star with t leaves has 2ᵗ+t subtrees. Starting with k, greedily take the largest star count not exceeding the remainder. Successive star counts satisfy 2^{t+1}+t+1 ≤ 3(2ᵗ+t), so this removes at least one third on each step. The single vertex (t=0) has count one. This gives O(log²(2k)) vertices. Our stronger assertion is about one connected subcubic tree and optimal logarithmic order, not the known general connected-tree spectrum. For the finitely many k below our connected theorem's range the k isolated vertices suffice for planar existence, so one can also take O(log(2k)) vertices for all k on the planar class after adjusting an absolute constant.

## A single transferable unit

Write [r,t] for the number of root-containing subtrees and the number of all subtrees of a rooted tree. If the child trees have data [rᵢ,tᵢ], the parent tree has [∏(1+rᵢ), ∏(1+rᵢ)+Σtᵢ]. This standard rooted count is used e.g. by Czabarka–Székely–Wagner. Let L be one vertex; U(X) gives X a new unary root; B(X,Y) gives disjoint copies of X,Y a new binary root. Put V=B(L,L). The two branches

    R₀ = U(B(U(L),V)),       R₁ = B(L,U(U(U(V))))

have 7 and 8 vertices respectively, maximum degree ≤3, root degree ≤2, and data [16,40], [16,41]. Indeed V=[4,6], U(L)=[2,3]; B(U(L),V)=[15,24], U³(V)=[7,24].

## An 18-digit alphabet

For digit d in {0,…,17} put s=17d, u=17−d. Take a path with marked left and right endpoints b,t and an intermediate vertex v at distances s,u from them (v may be an endpoint). Hang the root of R_ε from v by one edge, ε∈{0,1}. Call this block H_{d,ε}; it uses (s+u+1)+|R_ε|≤298 vertices. Within each block:

* Subtrees containing both endpoints must contain the whole path, so there are 1+16=17.
* Those containing b number s+17(u+1)=306, independent of the digit. Those containing t number b_d=u+17(s+1)=34+288d.
* All subtrees number H_d+ε, where for p=s+u+1,
  H_d=40+p(p+1)/2+16(s+1)(u+1). These three terms count the subtrees entirely in the hanging tree, entirely in the path, and meeting both.

Concatenate m disjoint blocks in the order of a word, adding one edge from the previous right port to the next left port; make the last right port the new root. The result is a tree of maximum degree ≤3 (ports are distinct and receive at most one external edge each, including when v is a port). With empty initial data F=T=0, adding digit d and switch ε changes root-containing and all-subtree counts by

    F' = 17F+b_d,       T' = T+306F+H_d+ε.                       (1)

The only new copies not confined to one side use the joining edge. The first block obeys the same formula without an edge. Put g_j=(17ʲ−1)/16 and w_j(d)=H_d+306 g_j b_d. Unrolling (1), when digits are indexed by j=0 at the right end (the last-added block), gives

    T = Σ_{j=0}^{m−1} w_j(d_j) + Σ ε_j.                          (2)

For every fixed word all integer offsets from 0 to m are thus available **in connected trees**, not by adding isolated vertices.

## Interval coverage

For each j, w_j is increasing on the digits, since H_{d+1}−H_d=5032−288d>0 for 0≤d≤16. Write W_j=w_j(17)−w_j(0)=46376+306·4896 g_j (H₀=499, H₁₇=46875). At a cut in lexicographic order of the length-m words where the digit in place j increases d→d+1 and all j trailing digits change from 17 to 0, the change in the base sum is

    D_j(d) = w_j(d+1)−w_j(d)−Σ_{i<j} W_i.                       (3)

This need not be positive. Because g_{j+1}−g_j=17ʲ, direct subtraction gives, independently of d,

    D_{j+1}(d)−D_j(d) = 47260−5508·17ʲ.

This is positive only for j=0, so max_{j,d}D_j(d)=D_1(0)=5032+41752=46784. For m≥46783 the integer intervals [base,base+m] therefore cover continuously from the first word's lower endpoint to the last word's upper endpoint: upward steps have size ≤m+1, while downward steps cannot introduce a hole in that span (alternatively, for a target take the first base sum exceeding it). The base sums can genuinely jump backwards; no monotonicity of the lexicographic list is assumed.

Let L_m=Σ_{i<m}w_i(0) and U_m=Σ_{i<m}w_i(17). All integers in [L_m,U_m+m] are realized. To pass between lengths, put E_m=L_{m+1}−U_m=w_m(0)−Σ_{i<m}W_i. Then E_0=499, and

    E_{m+1}−E_m = 47260−83232·17^m.

Thus E_m<0 for all m≥1. Since L_m is increasing and unbounded, **every integer k≥L_{46783} is covered**. This threshold is just an explicit sufficient one. Each chosen length m obeys k≥L_m≥17^m for m≥1: the all-zero tree has F=34(17^m−1)/16≥17^m, and T≥F. Consequently the number of vertices is at most 298m≤298 log₁₇ k. No classification of smaller subcubic counts is claimed. The argument can be made constructive without scanning all words: recursively union prefix intervals, with suffix digits all zero and all 17 for endpoints. Inductively for each fixed prefix the span between these endpoints (plus m at the upper end) is covered, by (3) on the remaining positions; each child interval's lower and upper endpoints increase with its leading digit. One can choose an interval containing the target at each step, then place the required number of unit switches.
