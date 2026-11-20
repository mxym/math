**Stronger numerical bound:** [the order-nine induced-subgraph certificate](../../order-nine-flags/README.md) gives n₃≥1602. The edge-transport method below is kept for its separate structural conclusions.

# Triangle transport defects and an unrestricted bound for Conway's 99-graph

**Theorem.** In any strongly regular graph with parameters (99,14,1,2), at least **864** unordered pairs of disjoint triangles have exactly two cross edges. Thus its number of induced hexagons is at least **210150**, using [Reimbayev's formula](https://arxiv.org/abs/2409.10620) 209286+n₃. Neither the existence nor the nonexistence of the graph follows. No automorphism or coclique hypothesis is used.

The key new local fact here is stronger than the scalar update: the mixed tensor column at an edge has its minimum norm **if and only if** the unique triangle on that edge has all twelve prism partners. Moreover **no vertex** has an entire minimum tensor slice. This makes the equality configurations at n₃=858 and 861 unnecessary; it does not contradict the earlier implications conditional on those configurations.

## Definitions and input identities

Let A denote adjacency; A²+A=12I+2J. The restricted eigenvalues are 3 and −4 with multiplicities 54 and 44. Write g=7E=3I−A+J/9 for seven times the orthogonal projector onto the −4 space V, and g_i=g e_i. Its columns span V; g²=7g and Σ_i g_i g_iᵀ=49I on V. Write N for the vertex/triangle incidence matrix. Each vertex lies in seven triangles, each edge in one, and NNᵀ=7I+A. For each triangle T let n_T be its indicator, w_T=g n_T, and s_T=w_T−1/3·1. The integer s_T equals +1 on T, −1 on the 36 neighboring vertices, and 0 elsewhere. The w_T sum to zero and Σ_T w_T w_Tᵀ=147I on V. The triangle Gram M=(1/7)(w_T·w_U) is integral, of diagonal 4, vanishes on distinct intersecting triangles, and equals 1 minus the cross-edge count on disjoint ones; M²=21M. These are the [Wave 20 identities](https://github.com/YesterdaysLemon/conway-99-research/blob/main/agents/2026-07-23-wave20-global-schur.md).

Set q_ij=Σ_T w_T(i)w_T(j)w_T and define the self-adjoint D_i=(1/7)Σ_T w_T(i) w_T w_Tᵀ on V. Then D_i g_j=q_ij, since w_T·g_j=7w_T(j). Also q_ij belongs to gℤ⁹⁹: expansion gives
    q_ij=g [ Σ_T s_T(i)s_T(j)n_T + 7(e_i+e_j) ],
because Σ_T s_T(i)w_T=21g_i. The degree t (sum of entries) of the displayed integral vector is −1 mod9: indeed Σ_T s_T(i)s_T(j)=21g_ij+231/9=28−21A_ij+63δ_ij. Therefore q_ij has zero sum and coordinates in −1/9+ℤ, giving squared norm ≥88/9 by discrete balancing. For any z∈ℤ⁹⁹ of degree t, ||gz||²=7[3||z||²−zᵀAz+t²/9]. At t≡−1 mod9 the bracket's first two terms plus (t²−1)/9 have odd parity: 3||z||²≡t mod2, zᵀAz is even, (t²−1)/9≡t−1 mod2. Thus ||gz||²≡70/9 mod14. Above the coordinate floor 88/9 the first allowed value is 196/9, also the squared norm of every g_j. Define the nonnegative integer d_ij by
    ||q_ij||²=196/9+14d_ij.
It follows from the 49-tight g_j frame that tr(D_i²)≥44, with equality exactly when d_ij=0 for all j.

For completeness tr(D_i²)∈4ℤ. In the normalization u_T=w_T/√7 one has D_i=7I+Σ_T s_T(i)u_Tu_Tᵀ. Its squared trace modulo 4 is sᵀ(M∘M)s with s=(s_T(i))_T: the other terms are divisible by 4 (in particular the middle one has factor 14·4). Write M∘M=M+2F, where F is integral symmetric with even diagonal 6. Therefore sᵀ(M∘M)s≡sᵀMs=||21g_i||²/7=1372≡0 mod4.

Cyclicity/direct summation gives
    Σ_i tr(D_i²)=(1/49)Σ_T,U (w_T·w_U)³=7Σ_T,U M_TU³=28(n₃−693).
To see the last step, if a_j counts triangles disjoint from T with j cross edges, the row sum and squared row length 84 give 4+a₀−a₂−2a₃=0, 16+a₀+a₂+4a₃=84. Hence a₂=36−3a₃, Σ_U M_TU³=2a₂−12, and Σ_T a₂=2n₃. In particular 3 divides n₃. The preceding local trace/coordinate identities are those used in the previously established 858/slice argument; what follows is a refinement using the actual graph edges.

## An edge column records the exact triangular matching defect

For T={i,j,k}, let X_i,X_j,X_k be its three disjoint arms of size 12, the outside vertices neighboring the specified vertex of T. Any two different arms are joined by a perfect matching: x∈X_i is nonadjacent to j, already has i as a common neighbor, and its unique other common neighbor with j lies in X_j. Each arm's internal edges form a perfect matching by the local triangle rule at its center.

For every edge of the X_i to X_j matching, take its unique triangle. Its third point is either in X_k or in the far set disjoint from T and its arms (no other point of X_i or X_j can work by the matching property). Those third points in X_k are all distinct by the same arm matchings. Their triangles are exactly the triangular-prism partners of T. Put q=12−a₃(T), let C⊂X_k be the q missed points and F be the **multiset** of q far third points; put d=1_F−1_C (counting multiplicities in F). No far point has multiplicity above two: it sees at most two points of X_i by μ=2 applied against i. Then
    q_ij=−g_k+g d.                                             (1)
Indeed the multiplier s_U(i)s_U(j) is +1 on T, on the other six triangles through k, and on the twelve matching triangles just described. It is −1 on the other six triangles through i or j respectively, and zero otherwise. One has Σ_{U∋v}w_U=3g_v, and Σ_{x∈X_i∪X_j∪X_k}g_x=g(A−2I)n_T=−6w_T. Substituting in the expansion of q_ij gives (1). Since d has zero sum, g_k·d=q, and g_i·d=g_j·d=0, we have
    14 d_ij=||gd||²−14q
           =7[3||d||²−dᵀAd−2q].                            (2)

**Rigidity at an edge.** q=0 clearly gives d_ij=0. Conversely, if q≥5 note gd is orthogonal to g_i,g_j. The component of g_k perpendicular to them has squared norm 84/5 (their Gram has diagonal 196/9, pairwise off-diagonal −56/9). Its pairing with gd is 7q. Thus
    d_ij≥(5/24)q²−q>0.
For 1≤q≤4 use (2) directly. Let b be the number of repeated points of F (multiplicity two), so ||d||²=2q+2b. Write e(F) for the weighted internal edge count on distinct support vertices of F, with edge weight the product of multiplicities. Since X_k is matched,
    d_ij ≥ 2q+3b−e(F)−⌊q/2⌋.
For distinct F of size q=1,2,3,4 the edge bounds are 0,1,3,4 respectively: five edges on four vertices would give a diamond and violate λ=1. In the repeated cases (q,b)=(2,1),(3,1),(4,1),(4,2) the bounds are 0,2,5,4, by multiplying the sizes of distinct support classes. Every resulting lower bound is positive. In fact 1≤q≤4 gives d_ij≥2. Hence the edge has d_ij=0 precisely for q(T)=0.

## The second-neighborhood cycles contradict a minimum slice

Fix i. Its neighbors are seven matched pairs (axes). Every second neighbor is uniquely labeled by two neighbors of i from distinct axes: such a pair has exactly one common point besides i. For each x∈N(i), the 12 exterior vertices labeled with x are matched internally by their triangles through x. The union of these 14 matchings is a simple 2-factor R on 84 exterior labels; each exterior vertex occurs in two of the matchings by its two labels, and an edge cannot be used twice by λ=1.

Suppose tr(D_i²)=44. Every incident edge then has d_ij=0, so every triangle through i has q=0. For axes a,b and a chosen point x of axis a, apply q=0 to the triangle consisting of i and the two endpoints b,b′ of axis b. Its arm vertex x is joined in its prism to its unique matches in the arms at b and b′, precisely the two exterior labels {x,b} and {x,b′}. Those two labels are therefore matched at x. Applying this to both choices in either axis shows that R consists exactly of the 21 disjoint four-cycles on the four labels of each axis pair. In particular R has precisely 21 negative eigenvalues.

Let V₀ be the subspace of V vanishing on i and its 14 neighbors, hence identified with vectors on the 84 exterior vertices. Its dimension is ≥30: the 15 vanishing coordinate conditions have the relation Σ_{j∼i}v_j=−4v_i, and dim V=44. For any v∈V₀, using the formula for D_i and w_T·v=7 n_T·v gives
    (v,D_i v)/7 = ||v||² − Σ_{ab∈R}(v_a+v_b)²
                 = −||v||²−(v,Rv).
Indeed all seven triangles through i sum to zero on v; the triangles with s_T(i)=−1 consist precisely of one root neighbor and an edge of R. Since the nonnegative spectral space of R has codimension 21 in ℝ⁸⁴, it intersects V₀ in dimension at least 9. On this intersection the Rayleigh quotient of D_i is at most −7. The min-max theorem gives at least nine eigenvalues ≤−7, contradicting tr(D_i²)=44. This argument only uses a *compression*: V₀ need not be invariant under D_i.

Therefore every tr(D_i²) is at least 48. Summation yields 28(n₃−693)≥99·48, i.e. n₃≥863; divisibility by three gives **n₃≥864**. This does not exclude the 864 endpoint or imply nonexistence.

Run `python3 -O check.py` for auxiliary exact arithmetic. The proof is analytical and does not depend on a search.

Further local obstruction: [no vertex of the hypothetical graph is partner-regular](../../partner-regular-kg/README.md), independently of whether its mixed tensor slice is minimum.
